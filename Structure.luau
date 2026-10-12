--!nocheck
-- Tovek (Luau port) :: Structure.luau
-- Control-flow structuring: folds short-circuit conditions and boolean diamonds, finds loops and
-- rebuilds if / while / repeat / numeric-for / generic-for statements from the block graph.
-- The merge point of an `if` is the nearest block both branches reach such that the blocks before it
-- cannot also be reached from it; paths that leave through break / continue / return are ignored.

local import = ...
local A = import("Ast")

local Structure = {}

local function termSuccs(term)
	local k = term.k
	if k == "goto" then
		return { term.to }
	elseif k == "cond" then
		return { term.t, term.f }
	elseif k == "forn" or k == "forn_latch" or k == "forg_latch" then
		return { term.body, term.exit }
	elseif k == "forg_prep" then
		return { term.to }
	end
	return {}
end

local function rebuild(F)
	local live = {}
	for _, b in ipairs(F.blocks) do
		if not b.dead then
			live[#live + 1] = b
			b.preds = {}
		end
	end
	for _, b in ipairs(live) do
		b.succs = termSuccs(b.term)
	end
	for _, b in ipairs(live) do
		for _, s in ipairs(b.succs) do
			s.preds[#s.preds + 1] = b
		end
	end
	F.blocks = live
end

---------------------------------------------------------------------------------------------------
-- short-circuit condition folding
---------------------------------------------------------------------------------------------------

local function foldConds(F)
	local changed = true
	while changed do
		changed = false
		rebuild(F)
		for _, b1 in ipairs(F.blocks) do
			local t1 = b1.term
			if t1.k == "cond" and t1.t ~= t1.f then
				for _, side in ipairs({ "f", "t" }) do
					local s = t1[side]
					if s ~= b1 and s ~= F.entry and s.term.k == "cond" and #s.stmts == 0 and #s.preds == 1 and s.term.t ~= s.term.f then
						local t2 = s.term
						local E1, E2 = t1.cond, t2.cond
						local new
						if side == "f" then
							if t2.t == t1.t then
								new = { k = "cond", cond = A.binE("or", E1, E2), t = t1.t, f = t2.f }
							elseif t2.f == t1.t then
								new = { k = "cond", cond = A.binE("or", E1, A.negate(E2)), t = t1.t, f = t2.t }
							end
						else
							if t2.f == t1.f then
								new = { k = "cond", cond = A.binE("and", E1, E2), t = t2.t, f = t1.f }
							elseif t2.t == t1.f then
								new = { k = "cond", cond = A.binE("and", E1, A.negate(E2)), t = t2.f, f = t1.f }
							end
						end
						if new then
							b1.term = new
							s.dead = true
							changed = true
							break
						end
					end
				end
				if changed then
					break
				end
			end
		end
	end
end


---------------------------------------------------------------------------------------------------
-- boolean value diamonds:  cond ? (v = true) : (v = false)   =>   v = cond
---------------------------------------------------------------------------------------------------

local function retarget(term, from, to)
	for _, key in ipairs({ "to", "t", "f", "body", "exit" }) do
		if term[key] == from then
			term[key] = to
		end
	end
end

-- block that only does `v = <bool>` and jumps to a block
local function trivialBool(b)
	if #b.stmts == 1 and b.term.k == "goto" then
		local S = b.stmts[1]
		if S.t == "assign" and #S.targets == 1 and S.targets[1].t == "var" and #S.values == 1 and S.values[1].t == "bool" and not S.multi then
			return S.targets[1].var, S.values[1].v, b.term.to
		end
	end
	return nil
end

local function boolish(e)
	if e.t == "bin" then
		if e.op == "and" or e.op == "or" then
			return boolish(e.l) and boolish(e.r)
		end
		return e.op == "==" or e.op == "~=" or e.op == "<" or e.op == "<=" or e.op == ">" or e.op == ">="
	end
	return e.t == "un" and e.op == "not" or e.t == "bool"
end

local function foldBoolDiamonds(F)
	local changed = false
	rebuild(F)
	for _, c in ipairs(F.blocks) do
		local t = c.term
		if not c.dead and t.k == "cond" and t.t ~= t.f and boolish(t.cond) then
			local v1, a, j1 = trivialBool(t.t)
			local v2, b, j2 = trivialBool(t.f)
			if v1 and v1 == v2 and j1 == j2 and a ~= b and #t.t.preds == 1 and #t.f.preds == 1 then
				local value = a and t.cond or A.negate(t.cond)
				c.stmts[#c.stmts + 1] = { t = "assign", targets = { A.varE(v1) }, values = { value } }
				c.term = { k = "goto", to = j1 }
				t.t.dead = true
				t.f.dead = true
				changed = true
				rebuild(F)
			end
		end
	end
	return changed
end

---------------------------------------------------------------------------------------------------
-- emission
---------------------------------------------------------------------------------------------------

local Emitter = {}
Emitter.__index = Emitter

local function copySet(s)
	local c = {}
	for k, v in pairs(s) do
		c[k] = v
	end
	return c
end

local function append(dst, src)
	for _, s in ipairs(src) do
		dst[#dst + 1] = s
	end
end

local function isTerminal(stmts)
	local last = stmts[#stmts]
	return last ~= nil and (last.t == "return" or last.t == "break" or last.t == "continue")
end

local function cloneNode(e)
	local c = {}
	for k, v in pairs(e) do
		if k == "var" or k == "func" or k == "proto" or k == "upvals" or k == "vars" then
			c[k] = v
		elseif type(v) == "table" then
			c[k] = cloneNode(v)
		else
			c[k] = v
		end
	end
	return c
end

-- tiny blocks (a couple of simple statements and a plain jump / return) may be duplicated
local function isDup(b)
	local k = b.term.k
	return #b.stmts <= 2 and (k == "goto" or k == "ret")
end

local function fail(msg)
	error("structure: " .. msg, 0)
end

function Emitter:emit(b, stops, lc, skipStart)
	local out = {}
	local first = skipStart
	while b do
		if stops[b] and not first then
			return out, b
		end
		first = false
		if self.isHeader[b] and not self.entered[b] then
			local stmts, nextb = self:emitLoop(b, stops, lc)
			append(out, stmts)
			b = nextb
		else
			local reuse = self.done[b]
			if reuse and not isDup(b) then
				fail("block revisited (pc " .. tostring(b.pc) .. ")")
			end
			self.done[b] = true
			if reuse then
				for _, st in ipairs(b.stmts) do
					out[#out + 1] = cloneNode(st)
				end
			else
				append(out, b.stmts)
			end
			local t = b.term
			local k = t.k
			if k == "goto" then
				b = t.to
			elseif k == "ret" then
				out[#out + 1] = { t = "return", values = reuse and cloneNode(t.values) or t.values }
				return out, nil
			elseif k == "cond" then
				local stmts, cont = self:emitIf(b, t, stops, lc)
				append(out, stmts)
				if cont == nil then
					return out, nil
				end
				b = cont
			elseif k == "forn" then
				local stmt, nextb = self:emitForNum(b, t, stops)
				out[#out + 1] = stmt
				b = nextb
			elseif k == "forg_prep" then
				local stmt, nextb = self:emitForIn(b, t, stops)
				out[#out + 1] = stmt
				b = nextb
			else
				fail("unexpected terminator " .. tostring(k))
			end
		end
	end
	return out, nil
end

-- nearest block (by pc) that both branches can reach without crossing a stop
local function reachSet(start, stops)
	local set, hit = {}, {}
	if stops[start] then
		hit[start] = true
		return set, hit
	end
	set[start] = true
	local work = { start }
	while #work > 0 do
		local n = table.remove(work)
		for _, s in ipairs(termSuccs(n.term)) do
			if stops[s] then
				hit[s] = true
			elseif not set[s] then
				set[s] = true
				work[#work + 1] = s
			end
		end
	end
	return set, hit
end

function Emitter:findMerge(b, tb, fb, stops, lc)
	local ra = reachSet(tb, stops)
	local rc = reachSet(fb, stops)
	local cands = {}
	for n in pairs(ra) do
		if rc[n] and n.pc > b.pc then
			cands[#cands + 1] = n
		end
	end
	if #cands == 0 then
		return nil
	end
	table.sort(cands, function(x, y)
		return x.pc < y.pc
	end)
	for _, n in ipairs(cands) do
		-- blocks reachable from the branches without passing through `n` must not
		-- also be reachable from `n` (otherwise `n` is not the point where paths join)
		local withN = stops
		withN = setmetatable({ [n] = true }, { __index = stops })
		local before = {}
		local ok = true
		for _, start in ipairs({ tb, fb }) do
			local set, hit = reachSet(start, withN)
			for k in pairs(set) do
				before[k] = true
			end
			-- a path that jumps straight to an enclosing merge skips `n`
			for st in pairs(hit) do
				if st ~= n and not (lc and (st == lc.exit or st == lc.cont)) then
					ok = false
				end
			end
		end
		local after = reachSet(n, stops)
		for k in pairs(after) do
			if before[k] then
				ok = false
				break
			end
		end
		if ok then
			return n
		end
	end
	return nil
end

function Emitter:emitIf(b, t, stops, lc)
	if t.t == t.f then
		return {}, t.t
	end
	local m = self:findMerge(b, t.t, t.f, stops, lc)
	local inner = stops
	if m and not stops[m] then
		inner = copySet(stops)
		inner[m] = true
	end
	local thenS, thenEnd = self:emit(t.t, inner, lc)
	local elseS, elseEnd = self:emit(t.f, inner, lc)

	local cont
	if m then
		cont = m
	elseif thenEnd == elseEnd then
		cont = thenEnd
	elseif thenEnd == nil then
		cont = elseEnd
	elseif elseEnd == nil then
		cont = thenEnd
	else
		local function rank(x)
			if lc and x == lc.exit then
				return 1
			elseif lc and x == lc.cont then
				return 2
			end
			return 3
		end
		local rt, re = rank(thenEnd), rank(elseEnd)
		if rt == re and rt == 3 then
			fail("unresolvable branch continuation")
		end
		cont = (rt > re) and thenEnd or elseEnd
	end

	local function fix(stmts, endStop)
		if endStop ~= nil and endStop ~= cont then
			if lc and endStop == lc.exit then
				stmts[#stmts + 1] = { t = "break" }
			elseif lc and endStop == lc.cont then
				stmts[#stmts + 1] = { t = "continue" }
			else
				fail("jump out of nested structure")
			end
		end
	end
	fix(thenS, thenEnd)
	fix(elseS, elseEnd)

	local cnd = t.cond
	local res = {}
	if #thenS == 0 and #elseS == 0 then
		if A.classify(cnd) == 2 then
			res[1] = { t = "if", cond = cnd, th = {} }
		end
		return res, cont
	end
	if #thenS == 0 then
		cnd = A.negate(cnd)
		thenS, elseS = elseS, thenS
	end
	if #elseS > 0 and isTerminal(thenS) and isTerminal(elseS) and #elseS < #thenS then
		res[1] = { t = "if", cond = A.negate(cnd), th = elseS }
		append(res, thenS)
	elseif #elseS > 0 and isTerminal(thenS) then
		res[1] = { t = "if", cond = cnd, th = thenS }
		append(res, elseS)
	elseif #elseS > 0 and isTerminal(elseS) then
		res[1] = { t = "if", cond = A.negate(cnd), th = elseS }
		append(res, thenS)
	elseif #elseS > 0 then
		res[1] = { t = "if", cond = cnd, th = thenS, el = elseS }
	else
		res[1] = { t = "if", cond = cnd, th = thenS }
	end
	return res, cont
end

function Emitter:emitForNum(b, t, stops)
	local X, body0 = t.exit, t.body
	local L
	for _, blk in ipairs(self.F.blocks) do
		if blk.term.k == "forn_latch" and blk.term.body == body0 then
			L = blk
			break
		end
	end
	if not L then
		fail("numeric for without latch")
	end
	local inner = copySet(stops)
	inner[X] = true
	inner[L] = true
	self.entered[body0] = true
	local body, endStop = self:emit(body0, inner, { exit = X, cont = L })
	if endStop == X then
		body[#body + 1] = { t = "break" }
	elseif endStop == L then
		self.done[L] = true
		append(body, L.stmts)
	elseif endStop ~= nil then
		fail("numeric for body ends outside loop")
	end
	local step = t.step
	if step and step.t == "num" and step.v == 1 then
		step = nil
	end
	return { t = "fornum", var = t.var, start = t.start, limit = t.limit, step = step, body = body }, X
end

function Emitter:emitForIn(b, t, stops)
	local G = t.to
	local gt = G.term
	if gt.k ~= "forg_latch" then
		fail("generic for without loop block")
	end
	local body0, X = gt.body, gt.exit
	local inner = copySet(stops)
	inner[G] = true
	inner[X] = true
	self.entered[G] = true
	local body, endStop = self:emit(body0, inner, { exit = X, cont = G })
	if endStop == X then
		body[#body + 1] = { t = "break" }
	elseif endStop ~= nil and endStop ~= G then
		fail("generic for body ends outside loop")
	end
	if endStop == G then
		self.done[G] = true
		append(body, G.stmts)
	end
	local exprs = {}
	for i, e in ipairs(t.exprs) do
		exprs[i] = e
	end
	while #exprs > 1 and exprs[#exprs].t == "nil" do
		exprs[#exprs] = nil
	end
	return { t = "forin", vars = t.vars, exprs = exprs, body = body }, X
end

function Emitter:emitLoop(h, stops, lc)
	local loop = self.loops[h]
	local set = loop.set
	-- exit target
	local X
	for _, blk in ipairs(self.F.blocks) do
		if set[blk] then
			for _, s in ipairs(blk.succs) do
				if not set[s] and (X == nil or s.pc < X.pc) then
					X = s
				end
			end
		end
	end
	self.entered[h] = true
	local inner = copySet(stops)
	if X then
		inner[X] = true
	end
	local ht = h.term

	-- while <cond> do ... end
	if ht.k == "cond" and #h.stmts == 0 and X then
		local tIn, fIn = set[ht.t], set[ht.f]
		if (tIn and not fIn and ht.f == X) or (fIn and not tIn and ht.t == X) then
			self.done[h] = true
			local entry = tIn and ht.t or ht.f
			local cnd = tIn and ht.cond or A.negate(ht.cond)
			inner[h] = true
			local body, endStop = self:emit(entry, inner, { exit = X, cont = h })
			if endStop == X then
				body[#body + 1] = { t = "break" }
			elseif endStop ~= nil and endStop ~= h then
				fail("while body ends outside loop")
			end
			return { { t = "while", cond = cnd, body = body } }, X
		end
	end

	-- repeat ... until <cond>
	local latch
	local nsources = 0
	for _, u in ipairs(loop.sources) do
		nsources = nsources + 1
		latch = u
	end
	if nsources == 1 and X and latch.term.k == "cond" and (latch.term.t == h or latch.term.f == h) and not (ht.k == "cond" and ((set[ht.t] and not set[ht.f]) or (set[ht.f] and not set[ht.t]))) then
		local lt = latch.term
		local other = (lt.t == h) and lt.f or lt.t
		if other == X or not set[other] then
			local untilCond = (lt.f == h) and lt.cond or A.negate(lt.cond)
			local body
			if latch == h then
				self.done[h] = true
				body = {}
				append(body, h.stmts)
			else
				local inner2 = copySet(inner)
				inner2[latch] = true
				local endStop
				body, endStop = self:emit(h, inner2, { exit = X, cont = latch })
				if endStop == X then
					body[#body + 1] = { t = "break" }
				elseif endStop == latch then
					self.done[latch] = true
					append(body, latch.stmts)
				elseif endStop ~= nil then
					fail("repeat body ends outside loop")
				end
			end
			return { { t = "repeat", body = body, cond = untilCond } }, X
		end
	end

	-- while true do ... end
	inner[h] = true
	local body, endStop = self:emit(h, inner, { exit = X, cont = h }, true)
	if endStop == X then
		body[#body + 1] = { t = "break" }
	elseif endStop ~= nil and endStop ~= h then
		fail("loop body ends outside loop")
	end
	return { { t = "while", cond = A.boolE(true), body = body } }, X
end

---------------------------------------------------------------------------------------------------

local function findLoops(F)
	local entry = F.entry
	local color = {}
	local sources = {}
	local stack = { { b = entry, i = 1, s = termSuccs(entry.term) } }
	color[entry] = 1
	while #stack > 0 do
		local fr = stack[#stack]
		local s = fr.s[fr.i]
		if s then
			fr.i = fr.i + 1
			if color[s] == 1 then
				sources[s] = sources[s] or {}
				table.insert(sources[s], fr.b)
			elseif not color[s] then
				color[s] = 1
				stack[#stack + 1] = { b = s, i = 1, s = termSuccs(s.term) }
			end
		else
			color[fr.b] = 2
			stack[#stack] = nil
		end
	end
	local loops, isHeader = {}, {}
	for h, srcs in pairs(sources) do
		local set = { [h] = true }
		local work = {}
		for _, u in ipairs(srcs) do
			if not set[u] then
				set[u] = true
				work[#work + 1] = u
			end
		end
		while #work > 0 do
			local n = table.remove(work)
			for _, p in ipairs(n.preds) do
				if not set[p] then
					set[p] = true
					work[#work + 1] = p
				end
			end
		end
		loops[h] = { set = set, sources = srcs }
		isHeader[h] = true
	end
	return loops, isHeader
end

-- returns the structured statement list for the function body
function Structure.run(F)
	rebuild(F)
	for _ = 1, 8 do
		rebuild(F)
		foldConds(F)
		if not foldBoolDiamonds(F) then
			break
		end
	end
	rebuild(F)
	local loops, isHeader = findLoops(F)
	local em = setmetatable({
		F = F,
		loops = loops,
		isHeader = isHeader,
		entered = {},
		done = {},
	}, Emitter)
	local body, endStop = em:emit(F.entry, {}, nil)
	if endStop ~= nil then
		fail("function body does not end in a return")
	end
	local last = body[#body]
	if last and last.t == "return" and #last.values == 0 then
		body[#body] = nil
	end
	return body
end

return Structure
