--!nocheck
-- Tovek (Luau port) :: Simplify.luau
-- Block-level clean-up: use counting, dead stores, inlining of single-use temporaries (while
-- preserving evaluation order) and merging of table constructors.

local import = ...
local A = import("Ast")

local Simplify = {}

---------------------------------------------------------------------------------------------------
-- statement expression slots (evaluation order)
---------------------------------------------------------------------------------------------------

-- fn(container, key) for each expression slot evaluated once, in order.
-- `all` = also report slots that must not receive substituted values (loop conditions).
local function slots(S, fn, all)
	local t = S.t
	if t == "assign" then
		for _, tg in ipairs(S.targets) do
			if tg.t == "index" then
				fn(tg, "obj")
				fn(tg, "key")
			end
		end
		for i = 1, #S.values do
			fn(S.values, i)
		end
	elseif t == "call" then
		fn(S, "e")
	elseif t == "setlist" then
		fn(S, "obj")
		for i = 1, #S.values do
			fn(S.values, i)
		end
	elseif t == "if" then
		fn(S, "cond")
	elseif t == "while" or t == "repeat" then
		if all then
			fn(S, "cond")
		end
		return false
	elseif t == "fornum" then
		fn(S, "start")
		fn(S, "limit")
		if S.step then
			fn(S, "step")
		end
	elseif t == "forin" then
		for i = 1, #S.exprs do
			fn(S.exprs, i)
		end
	elseif t == "return" then
		for i = 1, #S.values do
			fn(S.values, i)
		end
	elseif t == "local" then
		for i = 1, #S.values do
			fn(S.values, i)
		end
	elseif t == "localfunc" then
		fn(S, "e")
	elseif t == "__term" then
		local term = S.term
		local k = term.k
		if k == "ret" then
			for i = 1, #term.values do
				fn(term.values, i)
			end
		elseif k == "cond" then
			fn(term, "cond")
		elseif k == "forn" then
			fn(term, "start")
			fn(term, "limit")
			fn(term, "step")
		elseif k == "forg_prep" then
			for i = 1, #term.exprs do
				fn(term.exprs, i)
			end
		end
	end
	return true
end
Simplify.slots = slots

---------------------------------------------------------------------------------------------------
-- counting
---------------------------------------------------------------------------------------------------

local function countStmt(F, S)
	local function slotFn(c, k)
		A.eachVar(c[k], function(v)
			if v.owner == F then
				v.uses = v.uses + 1
			end
		end, function(v)
			if v.owner == F then
				v.uses = v.uses + 2
			end
		end)
	end
	slots(S, slotFn, true)
	if S.t == "assign" then
		for _, tg in ipairs(S.targets) do
			if tg.t == "var" and tg.var.owner == F then
				tg.var.defs = tg.var.defs + 1
			end
		end
	end
end

function Simplify.recount(F)
	for _, v in ipairs(F.vars) do
		v.defs, v.uses = 0, 0
	end
	for _, b in ipairs(F.blocks) do
		for _, S in ipairs(b.stmts) do
			countStmt(F, S)
		end
		countStmt(F, { t = "__term", term = b.term })
	end
	-- loop variables are defined by their construct
	for _, b in ipairs(F.blocks) do
		local term = b.term
		if term.k == "forn" then
			term.var.defs = term.var.defs + 1
		elseif term.k == "forg_prep" then
			for _, v in ipairs(term.vars) do
				v.defs = v.defs + 1
			end
		end
	end
end

---------------------------------------------------------------------------------------------------
-- dead stores
---------------------------------------------------------------------------------------------------

local function removeDead(F)
	local removed = false
	for _, b in ipairs(F.blocks) do
		local out = {}
		for _, S in ipairs(b.stmts) do
			local keep = true
			if S.t == "assign" then
				local allDead = true
				for _, tg in ipairs(S.targets) do
					if not (tg.t == "var" and tg.var.owner == F and tg.var.kind == "local" and tg.var.uses == 0) then
						allDead = false
					end
				end
				if allDead then
					local v = S.values[1]
					if v.t == "call" or v.t == "mcall" then
						S = { t = "call", e = v }
						removed = true
					elseif A.classify(v) < 2 then
						keep = false
						removed = true
					end
				end
			end
			if keep then
				out[#out + 1] = S
			end
		end
		b.stmts = out
	end
	return removed
end

---------------------------------------------------------------------------------------------------
-- substitution of single-use temporaries
---------------------------------------------------------------------------------------------------

local function collect(S)
	local ev = {}
	local function walk(c, k)
		local e = c[k]
		if e.t == "var" then
			ev[#ev + 1] = { k = "use", var = e.var, c = c, key = k }
			return
		end
		if e.t == "pending" then
			return
		end
		A.forEachChild(e, walk)
		if A.ownClass(e) > 0 then
			ev[#ev + 1] = { k = "ev" }
		end
	end
	if slots(S, walk) == false then
		return nil
	end
	return ev
end

local function candidate(F, C)
	if C and C.t == "assign" and not C.multi and #C.targets == 1 and #C.values == 1 then
		local tg = C.targets[1]
		if tg.t == "var" then
			local v = tg.var
			if v.owner == F and v.kind == "local" and v.defs == 1 and v.uses == 1 then
				return v
			end
		end
	end
	return nil
end

local function readsAssigned(E, assigned)
	local bad = false
	A.eachVar(E, function(v)
		if assigned[v] then
			bad = true
		end
	end, function(v)
		if assigned[v] then
			bad = true
		end
	end)
	return bad
end

local function trySubst(F, list, si)
	local S = list[si]
	if not S then
		return
	end
	local ev = collect(S)
	if not ev then
		return
	end
	local any = false
	for _, e in ipairs(ev) do
		if e.k == "use" then
			any = true
			break
		end
	end
	if not any then
		return
	end
	local blocked, budget = false, 0
	local assigned = {}
	local j = si - 1
	while j >= 1 do
		local C = list[j]
		if C ~= false then
			local v = candidate(F, C)
			local pos
			if v then
				for idx, e in ipairs(ev) do
					if e.k == "use" and e.var == v then
						pos = idx
						break
					end
				end
			end
			local ok = false
			if v and pos then
				local E = C.values[1]
				local cls = A.classify(E)
				if not blocked then
					ok = true
					if cls > 0 then
						for idx = 1, pos - 1 do
							if ev[idx].k == "ev" then
								ok = false
								break
							end
						end
					end
				else
					ok = cls == 0 and not readsAssigned(E, assigned)
				end
			end
			if ok then
				local e = ev[pos]
				e.c[e.key] = C.values[1]
				list[j] = false
				ev = collect(S)
			else
				blocked = true
				budget = budget + 1
				if budget > 8 then
					break
				end
				if C.t == "assign" then
					for _, tg in ipairs(C.targets) do
						if tg.t == "var" then
							assigned[tg.var] = true
						end
					end
				end
			end
		end
		j = j - 1
	end
end

function Simplify.list(F, list)
	for si = 1, #list do
		trySubst(F, list, si)
	end
end

local function substituteBlock(F, b)
	local list = {}
	for _, s in ipairs(b.stmts) do
		list[#list + 1] = s
	end
	list[#list + 1] = { t = "__term", term = b.term }
	for si = 1, #list do
		trySubst(F, list, si)
	end
	local out = {}
	for i = 1, #list - 1 do
		if list[i] then
			out[#out + 1] = list[i]
		end
	end
	b.stmts = out
end

---------------------------------------------------------------------------------------------------
-- table constructors
---------------------------------------------------------------------------------------------------

local function positional(tbl)
	local n = 0
	for _, f in ipairs(tbl.fields) do
		if not f.key then
			n = n + 1
		end
	end
	return n
end

local function hasStrKey(tbl, s)
	for _, f in ipairs(tbl.fields) do
		if f.key and f.key.t == "str" and f.key.v == s then
			return f
		end
	end
	return nil
end

local function tryMerge(tv, tbl, N)
	if N.t == "assign" and #N.targets == 1 and #N.values == 1 then
		local tg = N.targets[1]
		if tg.t == "index" and tg.obj.t == "var" and tg.obj.var == tv then
			local val, key = N.values[1], tg.key
			if A.refs(val, tv) or A.refs(key, tv) then
				return false
			end
			if key.t == "str" then
				local f = hasStrKey(tbl, key.v)
				if f then
					if f.val.t == "pending" then
						f.val = val
						return true
					end
					return false
				end
				tbl.fields[#tbl.fields + 1] = { key = key, val = val }
				return true
			elseif key.t == "num" and key.v == positional(tbl) + 1 and key.v % 1 == 0 then
				tbl.fields[#tbl.fields + 1] = { val = val }
				return true
			elseif A.isConst(key) then
				tbl.fields[#tbl.fields + 1] = { key = key, val = val }
				return true
			end
		end
	elseif N.t == "setlist" and N.obj.t == "var" and N.obj.var == tv then
		if N.start ~= positional(tbl) + 1 then
			return false
		end
		for _, v in ipairs(N.values) do
			if A.refs(v, tv) then
				return false
			end
		end
		for _, v in ipairs(N.values) do
			tbl.fields[#tbl.fields + 1] = { val = v }
		end
		return true
	end
	return false
end

local function mergeCtors(stmts)
	local out = {}
	local i = 1
	local n = #stmts
	while i <= n do
		local S = stmts[i]
		out[#out + 1] = S
		i = i + 1
		if S.t == "assign" and #S.targets == 1 and S.targets[1].t == "var" and #S.values == 1 and S.values[1].t == "table" then
			local tv, tbl = S.targets[1].var, S.values[1]
			while i <= n do
				if tryMerge(tv, tbl, stmts[i]) then
					tv.uses = tv.uses - 1
					i = i + 1
				else
					break
				end
			end
		end
	end
	return out
end

---------------------------------------------------------------------------------------------------

-- `for k, v in pairs(t)`: the 3-result call feeding FORGPREP becomes the loop's expression list
local function fuseForIn(F)
	for _, b in ipairs(F.blocks) do
		local term = b.term
		if term.k == "forg_prep" and #term.exprs == 3 then
			local S = b.stmts[#b.stmts]
			if S and S.t == "assign" and S.multi and #S.targets == 3 then
				local ok = true
				for n = 1, 3 do
					local tg, ex = S.targets[n], term.exprs[n]
					if not (ex.t == "var" and tg.var == ex.var and tg.var.uses == 1) then
						ok = false
					end
				end
				if ok then
					term.exprs = { S.values[1] }
					b.stmts[#b.stmts] = nil
				end
			end
		end
	end
end

function Simplify.run(F)
	Simplify.recount(F)
	fuseForIn(F)
	for _ = 1, 4 do
		Simplify.recount(F)
		local removed = removeDead(F)
		if removed then
			Simplify.recount(F)
		end
		for _, b in ipairs(F.blocks) do
			substituteBlock(F, b)
			b.stmts = mergeCtors(b.stmts)
		end
	end
	Simplify.recount(F)
	removeDead(F)
	Simplify.recount(F)
end

---------------------------------------------------------------------------------------------------
-- AST level (after structuring)
---------------------------------------------------------------------------------------------------

local function subListsOf(S)
	local k = S.t
	if k == "if" then
		return { S.th, S.el }
	elseif k == "while" or k == "repeat" or k == "fornum" or k == "forin" then
		return { S.body }
	end
	return {}
end

function Simplify.astPass(F, body)
	local function count(list)
		for _, S in ipairs(list) do
			countStmt(F, S)
			for _, sl in ipairs(subListsOf(S)) do
				count(sl)
			end
			if S.t == "fornum" then
				S.var.defs = S.var.defs + 1
			elseif S.t == "forin" then
				for _, v in ipairs(S.vars) do
					v.defs = v.defs + 1
				end
			end
		end
	end
	for _, v in ipairs(F.vars) do
		v.defs, v.uses = 0, 0
	end
	count(body)
	local function pass(list)
		for _, S in ipairs(list) do
			for _, sl in ipairs(subListsOf(S)) do
				pass(sl)
			end
		end
		Simplify.list(F, list)
		local out = {}
		for _, S in ipairs(list) do
			if S then
				out[#out + 1] = S
			end
		end
		for k = #list, 1, -1 do
			list[k] = nil
		end
		for k, S in ipairs(out) do
			list[k] = S
		end
	end
	pass(body)
end

return Simplify
