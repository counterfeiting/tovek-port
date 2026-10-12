--!nocheck
-- Tovek (Luau port) :: Ast.luau
-- Expression / statement node constructors and traversal helpers.
--
-- Expression nodes (field `t`):
--   nil, bool(v), num(v), str(v), vec(x,y,z,w), var(var), global(name), vararg(single),
--   index(obj,key), call(fn,args,single), mcall(obj,name,args,single), bin(op,l,r), un(op,e),
--   concat(parts), table(fields={ {key=?,val=} }), closure(proto,upvals,func), pending
-- Statement nodes:
--   assign(targets,values,multi), call(e), setlist(obj,start,values,multi),
--   local(vars,values), localfunc(var,e), if(cond,th,el), while(cond,body), repeat(body,cond),
--   fornum(var,start,limit,step,body), forin(vars,exprs,body), return(values), break, continue,
--   comment(text)

local A = {}

function A.nilE() return { t = "nil" } end
function A.boolE(v) return { t = "bool", v = v } end
function A.numE(v) return { t = "num", v = v } end
function A.strE(v) return { t = "str", v = v } end
function A.varE(v) return { t = "var", var = v } end
function A.globalE(n) return { t = "global", name = n } end
function A.indexE(o, k) return { t = "index", obj = o, key = k } end
function A.callE(f, args, single) return { t = "call", fn = f, args = args, single = single } end
function A.mcallE(o, n, args, single) return { t = "mcall", obj = o, name = n, args = args, single = single } end
function A.binE(op, l, r) return { t = "bin", op = op, l = l, r = r } end
function A.unE(op, e) return { t = "un", op = op, e = e } end

---------------------------------------------------------------------------------------------------
-- children traversal (evaluation order). fn(container, key) for every direct sub-expression slot.
---------------------------------------------------------------------------------------------------

local function forEachChild(e, fn)
	local t = e.t
	if t == "index" then
		fn(e, "obj")
		fn(e, "key")
	elseif t == "call" then
		fn(e, "fn")
		local args = e.args
		for i = 1, #args do
			fn(args, i)
		end
	elseif t == "mcall" then
		fn(e, "obj")
		local args = e.args
		for i = 1, #args do
			fn(args, i)
		end
	elseif t == "bin" then
		fn(e, "l")
		fn(e, "r")
	elseif t == "un" then
		fn(e, "e")
	elseif t == "concat" then
		local p = e.parts
		for i = 1, #p do
			fn(p, i)
		end
	elseif t == "table" then
		local fields = e.fields
		for i = 1, #fields do
			local f = fields[i]
			if f.key then
				fn(f, "key")
			end
			fn(f, "val")
		end
	end
end
A.forEachChild = forEachChild

-- class of the node itself (not recursive): 2 = effect (call), 1 = reads state, 0 = pure
-- `game.Players`, `math.floor`: chains of constant keys over a global are order-neutral
local function isImportPath(e)
	while e.t == "index" do
		if e.key.t ~= "str" then
			return false
		end
		e = e.obj
	end
	return e.t == "global"
end

local function ownClass(e)
	local t = e.t
	if t == "call" or t == "mcall" then
		return 2
	elseif t == "index" then
		if isImportPath(e) then
			return 0
		end
		return 1
	elseif t == "bin" or t == "un" or t == "concat" then
		return 1
	end
	return 0
end
A.ownClass = ownClass

-- deepest class in the expression tree
function A.classify(e)
	local cls = ownClass(e)
	if cls == 2 then
		return 2
	end
	local function walk(c, k)
		local x = c[k]
		if x.t == "pending" then
			return
		end
		local y = ownClass(x)
		if y > cls then
			cls = y
		end
		if cls < 2 then
			forEachChild(x, walk)
		end
	end
	forEachChild(e, walk)
	return cls
end

-- does the expression tree reference the variable?
function A.refs(e, var)
	if e.t == "var" then
		return e.var == var
	end
	local found = false
	local function walk(c, k)
		if found then
			return
		end
		local x = c[k]
		if x.t == "var" then
			if x.var == var then
				found = true
			end
		elseif x.t == "closure" then
			for _, u in ipairs(x.upvals or {}) do
				if u == var then
					found = true
				end
			end
		else
			forEachChild(x, walk)
		end
	end
	forEachChild(e, walk)
	if e.t == "closure" then
		for _, u in ipairs(e.upvals or {}) do
			if u == var then
				return true
			end
		end
	end
	return found
end

-- visit every var reference (including closure captures) in an expression
function A.eachVar(e, fn, captureFn)
	if e.t == "var" then
		fn(e.var, e)
		return
	elseif e.t == "closure" then
		if captureFn then
			for _, u in ipairs(e.upvals or {}) do
				captureFn(u)
			end
		end
		return
	end
	local function walk(c, k)
		A.eachVar(c[k], fn, captureFn)
	end
	forEachChild(e, walk)
end

local COMPARE_NEG = { ["=="] = "~=", ["~="] = "==", ["<"] = ">=", [">="] = "<", ["<="] = ">", [">"] = "<=" }

local function simplifiesOnNegate(e)
	return (e.t == "un" and e.op == "not") or (e.t == "bin" and COMPARE_NEG[e.op] ~= nil) or e.t == "bool"
		or (e.t == "bin" and (e.op == "and" or e.op == "or") and (simplifiesOnNegate(e.l) or simplifiesOnNegate(e.r)))
end

function A.negate(e)
	if e.t == "bin" and (e.op == "and" or e.op == "or") and simplifiesOnNegate(e) then
		-- De Morgan: not (a or b) == not a and not b
		return { t = "bin", op = (e.op == "and") and "or" or "and", l = A.negate(e.l), r = A.negate(e.r) }
	end
	if e.t == "un" and e.op == "not" then
		return e.e
	elseif e.t == "bin" and COMPARE_NEG[e.op] then
		return { t = "bin", op = COMPARE_NEG[e.op], l = e.l, r = e.r }
	elseif e.t == "bool" then
		return { t = "bool", v = not e.v }
	elseif e.t == "nil" then
		return { t = "bool", v = true }
	end
	return { t = "un", op = "not", e = e }
end

-- expression that is statically a constant
function A.isConst(e)
	local t = e.t
	return t == "nil" or t == "bool" or t == "num" or t == "str"
end

return A
