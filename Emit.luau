--!nocheck
-- Tovek (Luau port) :: Emit.luau
-- Pretty printer: turns the structured AST into Luau source.

local Emit = {}

local KEYWORDS = {}
for _, k in ipairs({ "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in", "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while", "continue" }) do
	KEYWORDS[k] = true
end
Emit.KEYWORDS = KEYWORDS

local function isIdent(s)
	return type(s) == "string" and s:match("^[%a_][%w_]*$") ~= nil and not KEYWORDS[s]
end
Emit.isIdent = isIdent

-- functions that are known to always return exactly one value
local SINGLE_GLOBALS = {
	tostring = true, tonumber = true, type = true, typeof = true, rawget = true, rawequal = true, rawlen = true,
	setmetatable = true, getmetatable = true, tick = true, time = true, require = true, newproxy = true,
}
local SINGLE_LIBS = { math = true, bit32 = true, buffer = true, utf8 = false }
local SINGLE_FIELDS = {
	["string.format"] = true, ["string.rep"] = true, ["string.sub"] = true, ["string.lower"] = true, ["string.upper"] = true,
	["string.len"] = true, ["string.char"] = true, ["string.reverse"] = true, ["table.concat"] = true, ["table.create"] = true,
	["table.clone"] = true, ["table.freeze"] = true, ["os.time"] = true, ["os.clock"] = true, ["os.date"] = true,
	["Instance.new"] = true,
}
local SINGLE_METHODS = {
	GetService = true, FindFirstChild = true, WaitForChild = true, FindFirstChildOfClass = true, FindFirstChildWhichIsA = true,
	FindFirstAncestor = true, FindFirstAncestorOfClass = true, FindFirstAncestorWhichIsA = true, Clone = true, GetChildren = true,
	GetDescendants = true, IsA = true, Connect = true, Once = true, GetAttribute = true, GetPropertyChangedSignal = true,
	IsDescendantOf = true, GetFullName = true, Lerp = true, Destroy = false, format = true, rep = true, sub = true,
	lower = true, upper = true,
}

local function knownSingle(e)
	if e.t == "call" then
		local f = e.fn
		if f.t == "global" then
			return SINGLE_GLOBALS[f.name] == true
		elseif f.t == "index" and f.obj.t == "global" and f.key.t == "str" then
			if SINGLE_LIBS[f.obj.name] then
				return true
			end
			return SINGLE_FIELDS[f.obj.name .. "." .. f.key.v] == true
		end
		return false
	elseif e.t == "mcall" then
		return SINGLE_METHODS[e.name] == true
	end
	return false
end

---------------------------------------------------------------------------------------------------
-- literals
---------------------------------------------------------------------------------------------------

local function quote(s)
	local validUtf8 = utf8 and utf8.len and utf8.len(s) ~= nil
	local out = s:gsub('[%c"\\\128-\255]', function(c)
		if c == "\n" then
			return "\\n"
		elseif c == "\r" then
			return "\\r"
		elseif c == "\t" then
			return "\\t"
		elseif c == '"' then
			return '\\"'
		elseif c == "\\" then
			return "\\\\"
		elseif c:byte() >= 128 then
			if validUtf8 then
				return c
			end
			return string.format("\\%03d", c:byte())
		end
		return string.format("\\%03d", c:byte())
	end)
	return '"' .. out .. '"'
end
Emit.quote = quote

local function formatNumber(v)
	if v ~= v then
		return "(0/0)"
	elseif v == math.huge then
		return "math.huge"
	elseif v == -math.huge then
		return "-math.huge"
	end
	if v == 0 then
		if 1 / v < 0 then
			return "-0"
		end
		return "0"
	end
	if v % 1 == 0 and math.abs(v) < 1e15 then
		return string.format("%d", v)
	end
	for p = 14, 17 do
		local s = string.format("%." .. p .. "g", v)
		if tonumber(s) == v then
			return s
		end
	end
	return string.format("%.17g", v)
end

---------------------------------------------------------------------------------------------------
-- expressions
---------------------------------------------------------------------------------------------------

local PREC = {
	["or"] = 1, ["and"] = 2,
	["<"] = 3, [">"] = 3, ["<="] = 3, [">="] = 3, ["~="] = 3, ["=="] = 3,
	[".."] = 4, ["+"] = 5, ["-"] = 5, ["*"] = 6, ["/"] = 6, ["//"] = 6, ["%"] = 6,
	["^"] = 8,
}
local UNARY = 7
local ATOM = 100

local P = {}
P.__index = P

local function name(v)
	return v.name or ("v" .. tostring(v.id))
end

local function prefixPrec(e)
	local t = e.t
	if t == "var" or t == "global" or t == "index" or t == "call" or t == "mcall" then
		return ATOM
	end
	return 0
end

function P:funcBody(fn, ind)
	local params = {}
	for i, v in ipairs(fn.params or {}) do
		params[i] = name(v)
	end
	if fn.isVararg then
		params[#params + 1] = "..."
	end
	local head = "(" .. table.concat(params, ", ") .. ")"
	local saved = self.out
	self.out = {}
	self:block(fn.body or {}, ind + 1)
	local lines = self.out
	self.out = saved
	if #lines == 0 then
		return head .. " end"
	end
	return head .. "\n" .. table.concat(lines, "\n") .. "\n" .. string.rep("\t", ind) .. "end"
end

-- returns text, precedence
function P:expr(e, ind)
	local t = e.t
	if t == "nil" then
		return "nil", ATOM
	elseif t == "bool" then
		return e.v and "true" or "false", ATOM
	elseif t == "num" then
		local s = formatNumber(e.v)
		if s:sub(1, 1) == "-" then
			return s, UNARY
		end
		return s, ATOM
	elseif t == "str" then
		return quote(e.v), ATOM
	elseif t == "vec" then
		if e.w == 0 then
			return string.format("Vector3.new(%s, %s, %s)", formatNumber(e.x), formatNumber(e.y), formatNumber(e.z)), ATOM
		end
		return string.format("vector.create(%s, %s, %s, %s)", formatNumber(e.x), formatNumber(e.y), formatNumber(e.z), formatNumber(e.w)), ATOM
	elseif t == "var" then
		return name(e.var), ATOM
	elseif t == "global" then
		return e.name, ATOM
	elseif t == "vararg" then
		return "...", ATOM
	elseif t == "pending" then
		return "nil", ATOM
	elseif t == "index" then
		local o = self:operand(e.obj, ind)
		if e.key.t == "str" and isIdent(e.key.v) then
			return o .. "." .. e.key.v, ATOM
		end
		return o .. "[" .. self:plain(e.key, ind) .. "]", ATOM
	elseif t == "call" then
		return self:operand(e.fn, ind) .. "(" .. self:list(e.args, ind, true) .. ")", ATOM
	elseif t == "mcall" then
		local n = e.name
		local o = self:operand(e.obj, ind)
		if isIdent(n) then
			return o .. ":" .. n .. "(" .. self:list(e.args, ind, true) .. ")", ATOM
		end
		return o .. "[" .. quote(n) .. "](" .. self:list(e.args, ind, true) .. ")", ATOM
	elseif t == "un" then
		local s = self:wrap(e.e, UNARY, ind)
		if e.op == "not" then
			return "not " .. s, UNARY
		end
		if e.op == "-" and s:sub(1, 1) == "-" then
			s = "(" .. s .. ")"
		end
		return e.op .. s, UNARY
	elseif t == "bin" then
		local MIRROR = { ["<"] = ">", ["<="] = ">=", [">"] = "<", [">="] = "<=" }
		if MIRROR[e.op] and (e.l.t == "num" or e.l.t == "str") and e.r.t ~= "num" and e.r.t ~= "str" then
			e = { t = "bin", op = MIRROR[e.op], l = e.r, r = e.l }
		end
		local p = PREC[e.op]
		local rightAssoc = e.op == "^"
		local l = self:wrap(e.l, rightAssoc and p + 1 or p, ind)
		local r = self:wrap(e.r, rightAssoc and p or p + 1, ind)
		return l .. " " .. e.op .. " " .. r, p
	elseif t == "concat" then
		local parts = {}
		local n = #e.parts
		for i, x in ipairs(e.parts) do
			-- `..` is right associative: only the last part may be another concat/same-level expression
			parts[i] = self:wrap(x, i == n and 4 or 5, ind)
		end
		return table.concat(parts, " .. "), 4
	elseif t == "table" then
		return self:tableCtor(e, ind), ATOM
	elseif t == "closure" then
		local fn = e.func
		if not fn then
			return "function(...) --[[ not decompiled ]] end", ATOM
		end
		return "function" .. self:funcBody(fn, ind), ATOM
	end
	error("cannot print expression kind " .. tostring(t))
end

function P:wrap(e, minPrec, ind)
	local s, p = self:expr(e, ind)
	if p < minPrec then
		return "(" .. s .. ")"
	end
	return s
end

function P:plain(e, ind)
	return (self:expr(e, ind))
end

-- expression used as the prefix of an index / call
function P:operand(e, ind)
	local s = self:expr(e, ind)
	if prefixPrec(e) < ATOM then
		return "(" .. s .. ")"
	end
	return s
end

-- expression list; `multi` = last element expands, so single-valued calls need parentheses
function P:list(list, ind, multi)
	local parts = {}
	local n = #list
	for i, e in ipairs(list) do
		local s = self:plain(e, ind)
		if multi and i == n and (e.t == "call" or e.t == "mcall" or e.t == "vararg") and e.single and not knownSingle(e) then
			s = "(" .. s .. ")"
		end
		parts[i] = s
	end
	return table.concat(parts, ", ")
end

function P:tableCtor(e, ind)
	local fields = e.fields
	if #fields == 0 then
		return "{}"
	end
	local items = {}
	local multiline = false
	local n = #fields
	for i, f in ipairs(fields) do
		local v = self:plain(f.val, ind + 1)
		if not f.key and i == n and (f.val.t == "call" or f.val.t == "mcall" or f.val.t == "vararg") and f.val.single and not knownSingle(f.val) then
			v = "(" .. v .. ")"
		end
		if f.key then
			if f.key.t == "str" and isIdent(f.key.v) then
				items[i] = f.key.v .. " = " .. v
			else
				items[i] = "[" .. self:plain(f.key, ind + 1) .. "] = " .. v
			end
		else
			items[i] = v
		end
		if v:find("\n", 1, true) then
			multiline = true
		end
	end
	local oneLine = "{ " .. table.concat(items, ", ") .. " }"
	if not multiline and #oneLine <= 100 then
		return oneLine
	end
	local pad = string.rep("\t", ind + 1)
	return "{\n" .. pad .. table.concat(items, ",\n" .. pad) .. ",\n" .. string.rep("\t", ind) .. "}"
end

---------------------------------------------------------------------------------------------------
-- statements
---------------------------------------------------------------------------------------------------

function P:line(ind, text)
	local out = self.out
	out[#out + 1] = string.rep("\t", ind) .. text
end

function P:lvalue(e, ind)
	if e.t == "var" then
		return name(e.var)
	elseif e.t == "global" then
		return e.name
	end
	return self:plain(e, ind)
end

function P:stmt(S, ind)
	local t = S.t
	if t == "assign" then
		local targets = {}
		for i, tg in ipairs(S.targets) do
			targets[i] = self:lvalue(tg, ind)
		end
		-- a function assigned to a global / field keeps its natural form
		local v = S.values[1]
		if #S.values == 1 and v.t == "closure" and v.func and #S.targets == 1 and S.targets[1].t == "global" then
			self:line(ind, "function " .. targets[1] .. self:funcBody(v.func, ind))
			return
		end
		self:line(ind, table.concat(targets, ", ") .. " = " .. self:list(S.values, ind, #S.targets > 1 or false))
	elseif t == "local" then
		local names = {}
		for i, v in ipairs(S.vars) do
			names[i] = name(v)
		end
		if #S.values == 0 then
			self:line(ind, "local " .. table.concat(names, ", "))
		else
			self:line(ind, "local " .. table.concat(names, ", ") .. " = " .. self:list(S.values, ind, #S.vars > 1))
		end
	elseif t == "localfunc" then
		self:line(ind, "local function " .. name(S.var) .. self:funcBody(S.e.func, ind))
	elseif t == "call" then
		self:line(ind, self:plain(S.e, ind))
	elseif t == "setlist" then
		local o = self:operand(S.obj, ind)
		for i, v in ipairs(S.values) do
			self:line(ind, string.format("%s[%d] = %s", o, S.start + i - 1, self:plain(v, ind)))
		end
	elseif t == "if" then
		self:line(ind, "if " .. self:plain(S.cond, ind) .. " then")
		self:block(S.th, ind + 1)
		local el = S.el
		while el do
			if #el == 1 and el[1].t == "if" then
				local nested = el[1]
				self:line(ind, "elseif " .. self:plain(nested.cond, ind) .. " then")
				self:block(nested.th, ind + 1)
				el = nested.el
			else
				self:line(ind, "else")
				self:block(el, ind + 1)
				el = nil
			end
		end
		self:line(ind, "end")
	elseif t == "while" then
		self:line(ind, "while " .. self:plain(S.cond, ind) .. " do")
		self:block(S.body, ind + 1)
		self:line(ind, "end")
	elseif t == "repeat" then
		self:line(ind, "repeat")
		self:block(S.body, ind + 1)
		self:line(ind, "until " .. self:plain(S.cond, ind))
	elseif t == "fornum" then
		local head = "for " .. name(S.var) .. " = " .. self:plain(S.start, ind) .. ", " .. self:plain(S.limit, ind)
		if S.step then
			head = head .. ", " .. self:plain(S.step, ind)
		end
		self:line(ind, head .. " do")
		self:block(S.body, ind + 1)
		self:line(ind, "end")
	elseif t == "forin" then
		local names = {}
		for i, v in ipairs(S.vars) do
			names[i] = name(v)
		end
		self:line(ind, "for " .. table.concat(names, ", ") .. " in " .. self:list(S.exprs, ind, false) .. " do")
		self:block(S.body, ind + 1)
		self:line(ind, "end")
	elseif t == "return" then
		if #S.values == 0 then
			self:line(ind, "return")
		else
			self:line(ind, "return " .. self:list(S.values, ind, true))
		end
	elseif t == "break" then
		self:line(ind, "break")
	elseif t == "continue" then
		self:line(ind, "continue")
	elseif t == "comment" then
		for l in (S.text .. "\n"):gmatch("(.-)\n") do
			self:line(ind, "-- " .. l)
		end
	else
		error("cannot print statement kind " .. tostring(t))
	end
end

function P:block(list, ind)
	for _, S in ipairs(list) do
		local before = #self.out
		self:stmt(S, ind)
		-- guard against ambiguous `f()\n(g)()` sequences
		local first = self.out[before + 1]
		if first and before > 0 and first:match("^%s*%(") then
			self.out[before + 1] = first:gsub("^(%s*)%(", "%1;(", 1)
		end
	end
end

-- func = { params, isVararg, body }
function Emit.render(func, header)
	local p = setmetatable({ out = {} }, P)
	if header then
		for l in (header .. "\n"):gmatch("(.-)\n") do
			p.out[#p.out + 1] = l
		end
	end
	p:block(func.body, 0)
	return table.concat(p.out, "\n") .. "\n"
end

return Emit
