--!nocheck
-- Tovek (Luau port) :: Post.luau
-- Post-structuring passes: and/or peepholes, `local` declaration placement and naming.

local import = ...
local A = import("Ast")
local Simplify = import("Simplify")
local Emit = import("Emit")

local Post = {}

---------------------------------------------------------------------------------------------------
-- generic walkers
---------------------------------------------------------------------------------------------------

-- fn(container, key) for every expression slot of the statement (not nested statements)
local function stmtSlots(S, fn)
	Simplify.slots(S, fn, true)
end

local function subLists(S)
	local t = S.t
	if t == "if" then
		return { S.th, S.el }
	elseif t == "while" or t == "repeat" or t == "fornum" or t == "forin" then
		return { S.body }
	end
	return {}
end

-- visit every closure expression (descending into expressions only)
local function eachClosure(list, fn)
	local function walkExpr(c, k)
		local e = c[k]
		if e.t == "closure" then
			fn(e)
		else
			A.forEachChild(e, walkExpr)
		end
	end
	local function walkList(l)
		for _, S in ipairs(l) do
			stmtSlots(S, walkExpr)
			for _, sl in ipairs(subLists(S)) do
				walkList(sl)
			end
		end
	end
	walkList(list)
end
Post.eachClosure = eachClosure

---------------------------------------------------------------------------------------------------
-- peepholes
---------------------------------------------------------------------------------------------------

local CMP = { ["=="] = true, ["~="] = true, ["<"] = true, ["<="] = true, [">"] = true, [">="] = true }

local function isBoolish(e)
	return (e.t == "bin" and CMP[e.op]) or (e.t == "un" and e.op == "not") or e.t == "bool"
end

local function singleVarAssign(S)
	if S.t == "assign" and #S.targets == 1 and S.targets[1].t == "var" and #S.values == 1 and not S.multi then
		return S.targets[1].var
	end
	return nil
end

local function peephole(list)
	for _, S in ipairs(list) do
		for _, sl in ipairs(subLists(S)) do
			peephole(sl)
		end
	end
	local i = 1
	while i <= #list do
		local S = list[i]
		-- if C then v = true else v = false end  ->  v = C
		if S.t == "if" and S.el and #S.th == 1 and #S.el == 1 and isBoolish(S.cond) then
			local v1, v2 = singleVarAssign(S.th[1]), singleVarAssign(S.el[1])
			local a = v1 and S.th[1].values[1]
			local b = v2 and S.el[1].values[1]
			if v1 and v1 == v2 and a.t == "bool" and b.t == "bool" and a.v ~= b.v then
				local value = a.v and S.cond or A.negate(S.cond)
				list[i] = { t = "assign", targets = { A.varE(v1) }, values = { value } }
				S = list[i]
			end
		end
		-- v = A ; if v then v = B end  ->  v = A and B   (and the `not v` / `or` form)
		local v = singleVarAssign(S)
		local nxt = list[i + 1]
		if v and nxt and nxt.t == "if" and not nxt.el and #nxt.th == 1 then
			local inner = nxt.th[1]
			if singleVarAssign(inner) == v and not A.refs(inner.values[1], v) then
				local c = nxt.cond
				local op
				if S.values[1].t == "bool" and S.values[1].v == false and isBoolish(c) and c.t ~= "bool" then
					-- v = false ; if C then v = B end  ->  v = C and B   (C is a boolean expression)
					S.values[1] = A.binE("and", c, inner.values[1])
					table.remove(list, i + 1)
					i = i - 1
					op = nil
				elseif c.t == "var" and c.var == v then
					op = "and"
				elseif c.t == "un" and c.op == "not" and c.e.t == "var" and c.e.var == v then
					op = "or"
				end
				if op then
					S.values[1] = A.binE(op, S.values[1], inner.values[1])
					table.remove(list, i + 1)
					i = i - 1 -- re-examine this statement for chained forms
				end
			end
		end
		i = i + 1
	end
end

---------------------------------------------------------------------------------------------------
-- tail returns
---------------------------------------------------------------------------------------------------

local function endsWithBareReturn(list)
	local last = list[#list]
	return last ~= nil and last.t == "return" and #last.values == 0
end

-- `list` sits at the very end of the function: a bare `return` there is redundant, and
-- `if c then A return end <rest>` can become `if c then A else <rest> end`.
local function tailify(list)
	for i = 1, #list - 1 do
		local S = list[i]
		if S.t == "if" and not S.el and endsWithBareReturn(S.th) and #S.th > 1 and (#list - i) <= 6 then
			local rest = {}
			for j = i + 1, #list do
				rest[#rest + 1] = list[j]
				list[j] = nil
			end
			S.th[#S.th] = nil
			S.el = rest
			tailify(S.th)
			tailify(S.el)
			return
		end
	end
	local last = list[#list]
	if not last then
		return
	end
	if last.t == "return" and #last.values == 0 then
		list[#list] = nil
		tailify(list)
	elseif last.t == "if" then
		tailify(last.th)
		if last.el then
			tailify(last.el)
		end
	end
end

---------------------------------------------------------------------------------------------------
-- declarations
---------------------------------------------------------------------------------------------------

local function copyPath(p)
	local c = {}
	for i, e in ipairs(p) do
		c[i] = { list = e.list, idx = e.idx, loop = e.loop }
	end
	return c
end

local function mergePath(P, Q)
	local n = 0
	local res
	local m = math.min(#P, #Q)
	for k = 1, m do
		if P[k].list ~= Q[k].list then
			break
		end
		n = k
		if P[k].idx ~= Q[k].idx then
			res = copyPath(P)
			res[k].idx = math.min(P[k].idx, Q[k].idx)
			res[k].loop = P[k].loop
			for j = #res, k + 1, -1 do
				res[j] = nil
			end
			return res
		end
	end
	res = {}
	for k = 1, n do
		res[k] = { list = P[k].list, idx = P[k].idx, loop = P[k].loop }
	end
	if #res == 0 then
		return copyPath(P)
	end
	-- paths agree up to level n; keep the shorter (the statement containing both)
	return res
end

local function declarable(S, v)
	if S.t ~= "assign" then
		return false
	end
	local direct = false
	for _, tg in ipairs(S.targets) do
		if tg.t == "var" and tg.var == v then
			direct = true
		end
	end
	if not direct then
		return false
	end
	for _, val in ipairs(S.values) do
		if A.refs(val, v) then
			-- `local function f` may reference itself
			if #S.targets == 1 and val.t == "closure" and not S.multi then
				return true
			end
			return false
		end
	end
	for _, tg in ipairs(S.targets) do
		if tg.t == "index" and (A.refs(tg.obj, v) or A.refs(tg.key, v)) then
			return false
		end
	end
	return true
end

local function declareFunction(F, body)
	local info = {}
	local path = {}
	for _, v in ipairs(F.vars) do
		if v.kind == "for" then
			v.reads = 0
		end
	end
	local function note(v, isDef)
		if v.owner == F and v.kind == "for" then
			if not isDef then
				v.reads = (v.reads or 0) + 1
			end
			return
		end
		if v.owner ~= F or v.kind ~= "local" then
			return
		end
		local rec = info[v]
		if not rec then
			rec = { path = copyPath(path), reads = 0 }
			info[v] = rec
		else
			rec.path = mergePath(rec.path, path)
		end
		if not isDef then
			rec.reads = rec.reads + 1
		end
	end
	local function noteExpr(c, k)
		A.eachVar(c[k], function(v)
			note(v, false)
		end, function(v)
			note(v, false)
		end)
	end
	local function visitStmt(S)
		if S.t == "assign" then
			for k, tg in ipairs(S.targets) do
				if tg.t == "var" then
					note(tg.var, true)
					-- remember the first real value: it names variables declared as `local x` / `= nil`
					local v = tg.var
					if v.owner == F and v.hintVal == nil then
						local val = S.values[#S.values == 1 and 1 or k]
						if val and val.t ~= "nil" then
							v.hintVal = val
							v.hintSlot = (#S.values == 1 and #S.targets > 1) and k or nil
						end
					end
				end
			end
		end
		if S.t == "local" then
			for _, v in ipairs(S.vars) do
				note(v, true)
			end
		end
		stmtSlots(S, noteExpr)
	end
	local walkList
	walkList = function(list, loop)
		for i, S in ipairs(list) do
			path[#path + 1] = { list = list, idx = i, loop = loop }
			visitStmt(S)
			if S.t == "if" then
				walkList(S.th, false)
				if S.el then
					walkList(S.el, false)
				end
			elseif S.t == "while" or S.t == "fornum" or S.t == "forin" then
				walkList(S.body, true)
			elseif S.t == "repeat" then
				walkList(S.body, true)
				path[#path + 1] = { list = S.body, idx = #S.body + 1, loop = true }
				A.eachVar(S.cond, function(v)
					note(v, false)
				end, function(v)
					note(v, false)
				end)
				path[#path] = nil
			end
			path[#path] = nil
		end
	end
	walkList(body, false)

	local pre = {} -- list -> idx -> vars
	local order = {}
	for v in pairs(info) do
		order[#order + 1] = v
	end
	table.sort(order, function(a, b)
		return a.id < b.id
	end)
	for _, v in ipairs(order) do
		local rec = info[v]
		local P = rec.path
		local n = #P
		v.reads = rec.reads
		local first = P[n].list[P[n].idx]
		while n > 1 and P[n].loop and not (first and declarable(first, v)) do
			n = n - 1
			first = P[n].list[P[n].idx]
		end
		local list, idx = P[n].list, P[n].idx
		first = list[idx]
		if first and declarable(first, v) then
			first.declares = first.declares or {}
			first.declares[v] = true
		else
			pre[list] = pre[list] or {}
			pre[list][idx] = pre[list][idx] or {}
			table.insert(pre[list][idx], v)
		end
	end

	local function rewrite(list)
		local out = {}
		for i, S in ipairs(list) do
			for _, sl in ipairs(subLists(S)) do
				rewrite(sl)
			end
			local p = pre[list] and pre[list][i]
			if S.declares then
				local all = true
				for _, tg in ipairs(S.targets) do
					if not (tg.t == "var" and S.declares[tg.var]) then
						all = false
					end
				end
				if all then
					local vars = {}
					for k, tg in ipairs(S.targets) do
						vars[k] = tg.var
					end
					if #vars == 1 and S.values[1].t == "closure" and not S.multi then
						S = { t = "localfunc", var = vars[1], e = S.values[1] }
					else
						S = { t = "local", vars = vars, values = S.values, multi = S.multi }
					end
				else
					p = p or {}
					for _, tg in ipairs(S.targets) do
						if tg.t == "var" and S.declares[tg.var] then
							table.insert(p, tg.var)
						end
					end
				end
			end
			if p then
				out[#out + 1] = { t = "local", vars = p, values = {} }
			end
			out[#out + 1] = S
		end
		for k in pairs(list) do
			list[k] = nil
		end
		for k, S in ipairs(out) do
			list[k] = S
		end
	end
	rewrite(body)
end

---------------------------------------------------------------------------------------------------
-- naming
---------------------------------------------------------------------------------------------------

local function sanitize(s)
	if type(s) ~= "string" then
		return nil
	end
	s = s:gsub("[^%w_]", "")
	if s == "" or s:match("^%d") then
		return nil
	end
	if #s > 48 then
		s = s:sub(1, 48)
	end
	return s
end

local function lowerFirst(s)
	return s:sub(1, 1):lower() .. s:sub(2)
end

local CHILD_METHODS = {
	WaitForChild = true, FindFirstChild = true, FindFirstChildOfClass = true, FindFirstChildWhichIsA = true,
	FindFirstAncestor = true, FindFirstAncestorOfClass = true, FindFirstAncestorWhichIsA = true,
}

local function isGenericName(n)
	return n == nil or n:match("^v%d+$") or n:match("^p%d+") or n:match("^tbl%d*$") or n == "_" or n:match("^func%d*$")
end

local function hintFor(e, protoNames, slot)
	if not e then
		return nil
	end
	if e.t == "call" and e.fn.t == "global" and (e.fn.name == "pcall" or e.fn.name == "xpcall") and slot then
		return slot == 1 and "success" or (slot == 2 and "result" or nil)
	end
	if e.t == "mcall" and (e.name == "Connect" or e.name == "Once" or e.name == "ConnectParallel") then
		return "connection"
	end
	if e.t == "mcall" and e.name:match("^Get%u") and #e.args == 0 and e.name ~= "GetChildren" and e.name ~= "GetDescendants" then
		return sanitize(lowerFirst(e.name:sub(4)))
	end
	if e.t == "call" and e.fn.t == "index" and e.fn.key.t == "str" and e.fn.key.v == "new" then
		local o = e.fn.obj
		local base = (o.t == "global" and o.name) or (o.t == "var" and o.var.name) or nil
		if base and base ~= "Instance" and not isGenericName(base) then
			return sanitize(lowerFirst(base))
		end
	end
	if e.t == "mcall" then
		local a1 = e.args[1]
		if a1 and a1.t == "str" then
			if e.name == "GetService" then
				return sanitize(a1.v)
			elseif CHILD_METHODS[e.name] then
				return sanitize(a1.v)
			end
		end
		if e.name == "Clone" then
			return "clone"
		elseif e.name == "GetChildren" then
			return "children"
		elseif e.name == "GetDescendants" then
			return "descendants"
		end
	elseif e.t == "call" then
		local f = e.fn
		if f.t == "global" and f.name == "require" and e.args[1] then
			local a = e.args[1]
			if a.t == "index" and a.key.t == "str" then
				return sanitize(a.key.v)
			elseif a.t == "mcall" and CHILD_METHODS[a.name] and a.args[1] and a.args[1].t == "str" then
				return sanitize(a.args[1].v)
			end
			return nil
		end
		if f.t == "index" and f.obj.t == "global" and f.obj.name == "Instance" and f.key.t == "str" and f.key.v == "new" and e.args[1] and e.args[1].t == "str" then
			local s = sanitize(e.args[1].v)
			return s and lowerFirst(s)
		end
		if f.t == "global" and (f.name == "tostring" or f.name == "tonumber") then
			return nil
		end
	elseif e.t == "index" and e.key.t == "str" then
		local s = sanitize(e.key.v)
		return s and lowerFirst(s)
	elseif e.t == "closure" then
		local p = protoNames[e.proto]
		return p and sanitize(p)
	elseif e.t == "table" then
		return "tbl"
	elseif e.t == "str" then
		return nil
	end
	return nil
end

local function collectGlobals(func, set)
	local function walkExpr(c, k)
		local e = c[k]
		if e.t == "global" then
			set[e.name] = true
		elseif e.t == "closure" then
			if e.func then
				Post.walkFuncGlobals(e.func, set)
			end
		else
			A.forEachChild(e, walkExpr)
		end
	end
	local function walkList(l)
		for _, S in ipairs(l) do
			stmtSlots(S, walkExpr)
			if S.t == "assign" then
				for _, tg in ipairs(S.targets) do
					if tg.t == "global" then
						set[tg.name] = true
					end
				end
			elseif S.t == "localfunc" then
				walkExpr(S, "e")
			end
			for _, sl in ipairs(subLists(S)) do
				walkList(sl)
			end
			if S.t == "repeat" then
				walkExpr(S, "cond")
			end
		end
	end
	walkList(func.body)
end
function Post.walkFuncGlobals(func, set)
	collectGlobals(func, set)
end

local function nameTree(root, protoNames)
	local reserved = {}
	for k in pairs(Emit.KEYWORDS) do
		reserved[k] = true
	end
	collectGlobals(root, reserved)

	local scopes = {}
	local function visible(n)
		if reserved[n] then
			return true
		end
		for i = #scopes, 1, -1 do
			if scopes[i][n] then
				return true
			end
		end
		return false
	end

	local function declare(v, base, counter)
		if v.name then
			scopes[#scopes][v.name] = true
			return
		end
		local n
		if base and not visible(base) then
			n = base
		elseif base then
			local sep = base:match("%d$") and "_" or ""
			local k = 2
			while visible(base .. sep .. k) do
				k = k + 1
			end
			n = base .. sep .. k
		else
			while visible("v" .. counter.n) do
				counter.n = counter.n + 1
			end
			n = "v" .. counter.n
			counter.n = counter.n + 1
		end
		v.name = n
		scopes[#scopes][n] = true
	end

	local nameFunc, nameList

	local function nameExpr(c, k, counter)
		local e = c[k]
		if e.t == "closure" then
			if e.func then
				nameFunc(e.func)
			end
		else
			A.forEachChild(e, function(cc, kk)
				nameExpr(cc, kk, counter)
			end)
		end
	end

	local function nameSlots(S, counter)
		stmtSlots(S, function(c, k)
			nameExpr(c, k, counter)
		end)
	end

	local LOOP_NUM = { "i", "j", "k", "l", "n", "m" }

	-- `tail` runs while the list's scope is still open (used for repeat-until conditions)
	nameList = function(list, counter, tail)
		scopes[#scopes + 1] = {}
		for _, S in ipairs(list) do
			local t = S.t
			if t == "local" then
				for k, v in ipairs(S.vars) do
					local hint = (#S.vars == #S.values or k == 1 or #S.values == 1) and hintFor(S.values[#S.values == 1 and 1 or k], counter.protoNames, #S.values == 1 and #S.vars > 1 and k or nil) or nil
					if #S.vars > 1 and #S.values > 0 and (v.reads or 0) == 0 then
						v.name = v.name or "_"
					end
					if hint == nil and v.hintVal then
						hint = hintFor(v.hintVal, counter.protoNames, v.hintSlot)
					end
					declare(v, hint, counter)
					if v.name == "_" then
						scopes[#scopes]["_"] = nil
					end
				end
				nameSlots(S, counter)
			elseif t == "localfunc" then
				declare(S.var, hintFor(S.e, counter.protoNames) or "func", counter)
				nameExpr(S, "e", counter)
			elseif t == "fornum" then
				nameSlots(S, counter)
				scopes[#scopes + 1] = {}
				local chosen
				for _, c in ipairs(LOOP_NUM) do
					if not visible(c) then
						chosen = c
						break
					end
				end
				if (S.var.reads or 0) == 0 then
					S.var.name = "_"
				end
				declare(S.var, chosen, counter)
				if S.var.name == "_" then
					scopes[#scopes]["_"] = nil
				end
				nameList(S.body, counter)
				scopes[#scopes] = nil
			elseif t == "forin" then
				nameSlots(S, counter)
				scopes[#scopes + 1] = {}
				local e1 = S.exprs[1]
				local isIpairs = e1 and e1.t == "call" and e1.fn.t == "global" and e1.fn.name == "ipairs"
				for k, v in ipairs(S.vars) do
					local base
					if k == 1 then
						base = isIpairs and "i" or "k"
					elseif k == 2 then
						base = "v"
					end
					if (v.reads or 0) == 0 and (k < #S.vars or #S.vars == 1) then
						v.name = "_"
					end
					declare(v, base, counter)
					if v.name == "_" then
						scopes[#scopes]["_"] = nil
					end
				end
				nameList(S.body, counter)
				scopes[#scopes] = nil
			elseif t == "if" then
				nameSlots(S, counter)
				nameList(S.th, counter)
				if S.el then
					nameList(S.el, counter)
				end
			elseif t == "while" then
				nameSlots(S, counter)
				nameList(S.body, counter)
			elseif t == "repeat" then
				nameList(S.body, counter, function()
					nameExpr(S, "cond", counter)
				end)
			else
				nameSlots(S, counter)
			end
		end
		if tail then
			tail()
		end
		scopes[#scopes] = nil
	end

	nameFunc = function(func)
		local counter = { n = 1, protoNames = protoNames }
		scopes[#scopes + 1] = {}
		for i, v in ipairs(func.params) do
			declare(v, "p" .. i, counter)
		end
		nameList(func.body, counter)
		scopes[#scopes] = nil
	end

	nameFunc(root)
end

---------------------------------------------------------------------------------------------------

-- run after a function body has been structured (children not yet attached)
function Post.structured(F, body)
	peephole(body)
	Simplify.astPass(F, body)
	peephole(body)
	tailify(body)
end

-- run once on the complete tree: declarations, then names
function Post.finish(root, protoNames)
	local function decl(func)
		declareFunction(func.F, func.body)
		eachClosure(func.body, function(c)
			if c.func then
				decl(c.func)
			end
		end)
	end
	decl(root)
	nameTree(root, protoNames or {})
end

return Post
