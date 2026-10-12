--!nocheck
-- Tovek (Luau port) :: Lift.luau
-- Turns one bytecode prototype into a control-flow graph of basic blocks. Every register is
-- resolved into a "web" (a Var) through reaching-definitions analysis, and every instruction is
-- lowered into statements that read/write those Vars. Later passes inline temporaries.

local import = ...
local Bytecode = import("Bytecode")
local A = import("Ast")
local O = Bytecode.OP

local floor = math.floor

local Lift = {}

---------------------------------------------------------------------------------------------------
-- per-instruction register reads/writes
---------------------------------------------------------------------------------------------------

local function setOf(names)
	local s = {}
	for _, n in ipairs(names) do
		s[O[n]] = true
	end
	return s
end

local WRITE_A = setOf({ "LOADNIL", "LOADB", "LOADN", "LOADK", "LOADKX", "GETGLOBAL", "GETUPVAL", "GETIMPORT", "NEWCLOSURE", "DUPCLOSURE", "NEWTABLE", "DUPTABLE" })
local READ_A = setOf({ "SETGLOBAL", "SETUPVAL", "JUMPIF", "JUMPIFNOT", "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS" })
local RB_WA = setOf({ "MOVE", "GETTABLEKS", "GETUDATAKS", "GETTABLEN", "NOT", "MINUS", "LENGTH", "ADDK", "SUBK", "MULK", "DIVK", "MODK", "POWK", "IDIVK", "ANDK", "ORK" })
local RBC_WA = setOf({ "GETTABLE", "ADD", "SUB", "MUL", "DIV", "MOD", "POW", "IDIV", "AND", "OR" })
local RAB = setOf({ "SETTABLEKS", "SETUDATAKS", "SETTABLEN" })
local CMP_JUMPS = setOf({ "JUMPIFEQ", "JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ", "JUMPIFNOTLE", "JUMPIFNOTLT" })
local XEQ_JUMPS = setOf({ "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS" })
local FORG_PREP = setOf({ "FORGPREP", "FORGPREP_NEXT", "FORGPREP_INEXT" })
local NOOPS = setOf({ "NOP", "BREAK", "COVERAGE", "PREPVARARGS", "CLOSEUPVALS", "FASTCALL", "FASTCALL1", "FASTCALL2", "FASTCALL2K", "FASTCALL3", "FASTPCALL", "NATIVECALL", "CMPPROTO", "NEWCLASSMEMBER", "CAPTURE" })

local function analyze(i)
	local op, a, b, c = i.op, i.a, i.b, i.c
	local rd, wr = {}, {}
	if WRITE_A[op] then
		wr[1] = a
	elseif READ_A[op] then
		rd[1] = a
	elseif RB_WA[op] then
		rd[1] = b
		wr[1] = a
	elseif RBC_WA[op] then
		rd[1] = b
		rd[2] = c
		wr[1] = a
	elseif op == O.SUBRK or op == O.DIVRK then
		rd[1] = c
		wr[1] = a
	elseif RAB[op] then
		rd[1] = a
		rd[2] = b
	elseif op == O.SETTABLE then
		rd[1], rd[2], rd[3] = a, b, c
	elseif op == O.NAMECALL or op == O.NAMECALLUDATA then
		rd[1] = b
		wr[1] = a
		wr[2] = a + 1
	elseif op == O.CALL or op == O.CALLFB then
		local last
		if b == 0 then
			last = i.topReg or a
		else
			last = a + b - 1
		end
		for r = a, last do
			rd[#rd + 1] = r
		end
		if c == 0 then
			wr[1] = a
		else
			for r = a, a + c - 2 do
				wr[#wr + 1] = r
			end
		end
	elseif op == O.RETURN then
		local last
		if b == 0 then
			last = i.topReg or (a - 1)
		else
			last = a + b - 2
		end
		for r = a, last do
			rd[#rd + 1] = r
		end
	elseif CMP_JUMPS[op] then
		rd[1] = a
		rd[2] = i.aux % 256
	elseif op == O.CONCAT then
		for r = b, c do
			rd[#rd + 1] = r
		end
		wr[1] = a
	elseif op == O.SETLIST then
		rd[1] = a
		local last
		if c == 0 then
			last = i.topReg or (b - 1)
		else
			last = b + c - 2
		end
		for r = b, last do
			rd[#rd + 1] = r
		end
	elseif op == O.FORNPREP then
		rd[1], rd[2], rd[3] = a, a + 1, a + 2
		wr[1] = a + 3
	elseif op == O.FORNLOOP then
		wr[1] = a + 3
	elseif FORG_PREP[op] then
		rd[1], rd[2], rd[3] = a, a + 1, a + 2
	elseif op == O.FORGLOOP then
		local n = i.aux % 256
		for r = a + 3, a + 2 + n do
			wr[#wr + 1] = r
		end
	elseif op == O.CAPTURE then
		if a <= 1 then
			rd[1] = b
		end
	elseif op == O.GETVARARGS then
		if b == 0 then
			wr[1] = a
		else
			for r = a, a + b - 2 do
				wr[#wr + 1] = r
			end
		end
	end
	i.rd, i.wr = rd, wr
end

---------------------------------------------------------------------------------------------------
-- basic blocks
---------------------------------------------------------------------------------------------------

local function isJump(op)
	return op == O.JUMP or op == O.JUMPBACK or op == O.JUMPX
end

local function buildBlocks(proto)
	local insn = proto.insn
	local n = proto.sizecode
	local leader = { [0] = true }
	local function mark(pc)
		if pc >= 0 and pc < n and insn[pc] then
			leader[pc] = true
		else
			error("jump target out of range: " .. tostring(pc))
		end
	end
	local function markNext(pc)
		if pc < n then
			leader[pc] = true
		end
	end
	local list = {}
	local pc = 0
	while pc < n do
		local i = insn[pc]
		list[#list + 1] = i
		local op = i.op
		local nextpc = pc + i.size
		if op == O.JUMP or op == O.JUMPBACK then
			mark(pc + 1 + i.d)
			markNext(nextpc)
		elseif op == O.JUMPX then
			mark(pc + 1 + i.e)
			markNext(nextpc)
		elseif op == O.JUMPIF or op == O.JUMPIFNOT or CMP_JUMPS[op] or XEQ_JUMPS[op] then
			mark(pc + 1 + i.d)
			markNext(nextpc)
		elseif op == O.LOADB and i.c ~= 0 then
			mark(pc + 1 + i.c)
			markNext(nextpc)
		elseif op == O.FORNPREP or op == O.FORNLOOP or FORG_PREP[op] or op == O.FORGLOOP then
			mark(pc + 1 + i.d)
			markNext(nextpc)
			if op == O.FORNPREP or FORG_PREP[op] then
				markNext(pc + 1)
			end
		elseif op == O.RETURN then
			markNext(nextpc)
		end
		pc = nextpc
	end

	local blocks, byPc = {}, {}
	local cur
	for _, i in ipairs(list) do
		if leader[i.pc] then
			cur = { id = #blocks + 1, pc = i.pc, insns = {}, stmts = {}, preds = {}, succs = {} }
			blocks[#blocks + 1] = cur
			byPc[i.pc] = cur
		end
		cur.insns[#cur.insns + 1] = i
	end
	return blocks, byPc
end

-- successors (as blocks) based on the last instruction of the block
local function blockSuccs(b, byPc, n)
	local last = b.insns[#b.insns]
	local op = last.op
	local pc = last.pc
	local nextpc = pc + last.size
	local s = {}
	local function add(target)
		local blk = byPc[target]
		if not blk then
			error("missing block at pc " .. tostring(target))
		end
		s[#s + 1] = blk
	end
	if op == O.JUMP or op == O.JUMPBACK then
		add(pc + 1 + last.d)
	elseif op == O.JUMPX then
		add(pc + 1 + last.e)
	elseif op == O.JUMPIF or op == O.JUMPIFNOT or CMP_JUMPS[op] or XEQ_JUMPS[op] then
		add(pc + 1 + last.d)
		add(nextpc)
	elseif op == O.LOADB and last.c ~= 0 then
		add(pc + 1 + last.c)
	elseif op == O.FORNPREP then
		add(pc + 1)
		add(pc + 1 + last.d)
	elseif op == O.FORNLOOP then
		add(pc + 1 + last.d)
		add(nextpc)
	elseif FORG_PREP[op] then
		add(pc + 1 + last.d)
	elseif op == O.FORGLOOP then
		add(pc + 1 + last.d)
		add(nextpc)
	elseif op == O.RETURN then
		-- none
	else
		if nextpc < n then
			add(nextpc)
		end
	end
	return s
end

---------------------------------------------------------------------------------------------------
-- reaching definitions / webs
---------------------------------------------------------------------------------------------------

local function analyzeFlow(F, blocks, entry, proto)
	local uf = {}
	local function find(x)
		local root = x
		while uf[root] ~= nil and uf[root] ~= root do
			root = uf[root]
		end
		while x ~= root do
			local nx = uf[x]
			uf[x] = root
			x = nx
		end
		return root
	end
	local function union(x, y)
		local rx, ry = find(x), find(y)
		if rx ~= ry then
			uf[rx] = ry
		end
	end

	-- gen sets
	local gen = {}
	for _, b in ipairs(blocks) do
		local g = {}
		for _, i in ipairs(b.insns) do
			for _, w in ipairs(i.wr) do
				g[w] = i.pc * 256 + w
			end
		end
		gen[b] = g
	end

	local IN, OUT = {}, {}
	for _, b in ipairs(blocks) do
		IN[b] = {}
	end
	for r = 0, proto.numParams - 1 do
		IN[entry][r] = { [-256 + r] = true }
	end

	local function computeOut(b)
		local out = {}
		for r, set in pairs(IN[b]) do
			out[r] = set
		end
		for r, d in pairs(gen[b]) do
			out[r] = { [d] = true }
		end
		return out
	end

	local changed = true
	local guard = 0
	while changed do
		changed = false
		guard = guard + 1
		if guard > 200 then
			error("dataflow did not converge")
		end
		for _, b in ipairs(blocks) do
			local inb = IN[b]
			for _, p in ipairs(b.preds) do
				local po = OUT[p]
				if po then
					for r, set in pairs(po) do
						local dst = inb[r]
						if not dst then
							dst = {}
							inb[r] = dst
						end
						for d in pairs(set) do
							if not dst[d] then
								dst[d] = true
								changed = true
							end
						end
					end
				end
			end
			OUT[b] = computeOut(b)
		end
	end

	-- read resolution
	local readDef = {}
	local undefCount = 0
	for _, b in ipairs(blocks) do
		local cur = {}
		local inb = IN[b]
		for _, i in ipairs(b.insns) do
			for _, r in ipairs(i.rd) do
				local key = i.pc * 256 + r
				local d = cur[r]
				if d == nil then
					local set = inb[r]
					if set then
						local first
						for x in pairs(set) do
							if first == nil then
								first = x
							else
								union(first, x)
							end
						end
						d = first
					end
					if d == nil then
						undefCount = undefCount + 1
						d = -1000000 - undefCount
					end
				end
				readDef[key] = d
			end
			for _, w in ipairs(i.wr) do
				cur[w] = i.pc * 256 + w
			end
		end
	end

	-- loop variables: numeric for prep/loop defs are one variable
	for _, b in ipairs(blocks) do
		for _, i in ipairs(b.insns) do
			if i.op == O.FORNLOOP then
				local bodyPc = i.pc + 1 + i.d
				local prep = proto.insn[bodyPc - 1]
				if prep and prep.op == O.FORNPREP then
					union(prep.pc * 256 + prep.a + 3, i.pc * 256 + i.a + 3)
				end
			end
		end
	end

	-- by-reference captures: the variable stays the same variable until its scope closes
	for _, b in ipairs(blocks) do
		for idx, i in ipairs(b.insns) do
			if i.op == O.CAPTURE and i.a == 1 then
				local reg = i.b
				local d0 = readDef[i.pc * 256 + reg]
				local visited = { [b] = false }
				local stack = { { b, idx + 1 } }
				while #stack > 0 do
					local item = table.remove(stack)
					local blk, start = item[1], item[2]
					local stop = false
					for k = start, #blk.insns do
						local ins = blk.insns[k]
						if ins.op == O.CLOSEUPVALS and ins.a <= reg then
							stop = true
							break
						end
						for _, w in ipairs(ins.wr) do
							if w == reg then
								union(d0, ins.pc * 256 + reg)
							end
						end
					end
					if not stop then
						for _, s in ipairs(blk.succs) do
							if not visited[s] then
								visited[s] = true
								stack[#stack + 1] = { s, 1 }
							end
						end
					end
				end
			end
		end
	end

	local rootVar = {}
	local function varOfDef(d)
		local root = find(d)
		local v = rootVar[root]
		if not v then
			v = { id = #F.vars + 1, kind = "local", owner = F, defs = 0, uses = 0 }
			F.vars[v.id] = v
			rootVar[root] = v
		end
		return v
	end
	return readDef, varOfDef
end

---------------------------------------------------------------------------------------------------
-- instruction lifting
---------------------------------------------------------------------------------------------------

local ARITH = {
	[O.ADD] = "+", [O.SUB] = "-", [O.MUL] = "*", [O.DIV] = "/", [O.MOD] = "%", [O.POW] = "^", [O.IDIV] = "//",
}
local ARITHK = {
	[O.ADDK] = "+", [O.SUBK] = "-", [O.MULK] = "*", [O.DIVK] = "/", [O.MODK] = "%", [O.POWK] = "^", [O.IDIVK] = "//",
}

local function importExpr(L, id)
	local n = floor(id / 1073741824) % 4
	local i1 = floor(id / 1048576) % 1024
	local i2 = floor(id / 1024) % 1024
	local i3 = id % 1024
	local K = L.K
	local e = A.globalE(K[i1].value)
	if n >= 2 then
		e = A.indexE(e, A.strE(K[i2].value))
	end
	if n >= 3 then
		e = A.indexE(e, A.strE(K[i3].value))
	end
	return e
end

local function constExpr(L, k)
	if not k then
		error("bad constant index")
	end
	local tag = k.tag
	if tag == "nil" then
		return A.nilE()
	elseif tag == "boolean" then
		return A.boolE(k.value)
	elseif tag == "number" then
		return A.numE(k.value)
	elseif tag == "string" then
		return A.strE(k.value)
	elseif tag == "vector" then
		return { t = "vec", x = k.x, y = k.y, z = k.z, w = k.w }
	elseif tag == "import" then
		return importExpr(L, k.id)
	end
	error("unsupported constant kind " .. tostring(tag))
end

local function R(L, i, reg)
	local d = L.readDef[i.pc * 256 + reg]
	if d == nil then
		error("internal: unresolved read r" .. reg .. " at pc " .. i.pc)
	end
	return A.varE(L.varOfDef(d))
end

local function W(L, i, reg)
	return A.varE(L.varOfDef(i.pc * 256 + reg))
end

local function emit(L, s)
	local out = L.out
	out[#out + 1] = s
end

local function assign(L, target, value)
	emit(L, { t = "assign", targets = { target }, values = { value } })
end

local function blk(L, pc)
	local b = L.byPc[pc]
	if not b then
		error("missing target block at pc " .. tostring(pc))
	end
	return b
end

local function kStr(L, idx)
	local k = L.K[idx]
	if not k or k.tag ~= "string" then
		error("expected string constant")
	end
	return k.value
end

local H = {}

for op in pairs(NOOPS) do
	H[op] = function() end
end

H[O.LOADNIL] = function(L, i) assign(L, W(L, i, i.a), A.nilE()) end
H[O.LOADB] = function(L, i)
	assign(L, W(L, i, i.a), A.boolE(i.b ~= 0))
	if i.c ~= 0 then
		L.term = { k = "goto", to = blk(L, i.pc + 1 + i.c) }
	end
end
H[O.LOADN] = function(L, i) assign(L, W(L, i, i.a), A.numE(i.d)) end
H[O.LOADK] = function(L, i) assign(L, W(L, i, i.a), constExpr(L, L.K[i.d])) end
H[O.LOADKX] = function(L, i) assign(L, W(L, i, i.a), constExpr(L, L.K[i.aux])) end
H[O.MOVE] = function(L, i) assign(L, W(L, i, i.a), R(L, i, i.b)) end
H[O.GETGLOBAL] = function(L, i) assign(L, W(L, i, i.a), A.globalE(kStr(L, i.aux))) end
H[O.SETGLOBAL] = function(L, i) assign(L, A.globalE(kStr(L, i.aux)), R(L, i, i.a)) end
H[O.GETUPVAL] = function(L, i)
	local v = L.F.upvalVars[i.b + 1]
	if not v then
		error("missing upvalue " .. i.b)
	end
	assign(L, W(L, i, i.a), A.varE(v))
end
H[O.SETUPVAL] = function(L, i)
	local v = L.F.upvalVars[i.b + 1]
	if not v then
		error("missing upvalue " .. i.b)
	end
	assign(L, A.varE(v), R(L, i, i.a))
end
H[O.GETIMPORT] = function(L, i) assign(L, W(L, i, i.a), importExpr(L, i.aux)) end
H[O.GETTABLE] = function(L, i) assign(L, W(L, i, i.a), A.indexE(R(L, i, i.b), R(L, i, i.c))) end
H[O.SETTABLE] = function(L, i) assign(L, A.indexE(R(L, i, i.b), R(L, i, i.c)), R(L, i, i.a)) end
H[O.GETTABLEKS] = function(L, i) assign(L, W(L, i, i.a), A.indexE(R(L, i, i.b), A.strE(kStr(L, i.aux)))) end
H[O.SETTABLEKS] = function(L, i) assign(L, A.indexE(R(L, i, i.b), A.strE(kStr(L, i.aux))), R(L, i, i.a)) end
H[O.GETUDATAKS] = function(L, i) assign(L, W(L, i, i.a), A.indexE(R(L, i, i.b), A.strE(kStr(L, i.aux % 65536)))) end
H[O.SETUDATAKS] = function(L, i) assign(L, A.indexE(R(L, i, i.b), A.strE(kStr(L, i.aux % 65536))), R(L, i, i.a)) end
H[O.GETTABLEN] = function(L, i) assign(L, W(L, i, i.a), A.indexE(R(L, i, i.b), A.numE(i.c + 1))) end
H[O.SETTABLEN] = function(L, i) assign(L, A.indexE(R(L, i, i.b), A.numE(i.c + 1)), R(L, i, i.a)) end

local function closure(L, i, childId)
	local child = L.chunk.protos[childId]
	if not child then
		error("missing child prototype " .. tostring(childId))
	end
	local upvals = {}
	local cp = i.pc + i.size
	for k = 1, child.numUpvals do
		local ci = L.proto.insn[cp]
		if not ci or ci.op ~= O.CAPTURE then
			error("expected CAPTURE after closure creation")
		end
		if ci.a == 2 then
			upvals[k] = L.F.upvalVars[ci.b + 1]
			if not upvals[k] then
				error("missing captured upvalue")
			end
		else
			upvals[k] = R(L, ci, ci.b).var
		end
		cp = cp + ci.size
	end
	assign(L, W(L, i, i.a), { t = "closure", proto = childId, upvals = upvals })
end
H[O.NEWCLOSURE] = function(L, i) closure(L, i, L.proto.children[i.d + 1]) end
H[O.DUPCLOSURE] = function(L, i)
	local k = L.K[i.d]
	if not k or k.tag ~= "closure" then
		error("DUPCLOSURE of non-closure constant")
	end
	closure(L, i, k.proto)
end

H[O.NAMECALL] = function(L, i)
	-- the receiver is copied to a+1; the method name is recovered at the CALL
	assign(L, W(L, i, i.a + 1), R(L, i, i.b))
end
H[O.NAMECALLUDATA] = H[O.NAMECALL]

local function topExpr(L, what)
	local top = L.top
	if not top then
		error("multiple-result consumer without producer in " .. what)
	end
	L.top = nil
	return top
end

local function call(L, i)
	local a, b, c = i.a, i.b, i.c
	local defId = L.readDef[i.pc * 256 + a]
	local nc = defId and L.ncDef[defId]
	local first = a + 1
	local lastArg
	if b == 0 then
		lastArg = (i.topReg or a) - 1
	else
		lastArg = a + b - 1
	end
	local fn, recv, name
	if nc then
		recv = R(L, i, a + 1)
		first = a + 2
		name = nc
	else
		fn = R(L, i, a)
	end
	local args = {}
	for r = first, lastArg do
		args[#args + 1] = R(L, i, r)
	end
	if b == 0 then
		local top = topExpr(L, "CALL")
		args[#args + 1] = top.expr
	end
	local node
	if nc then
		node = A.mcallE(recv, name, args, c == 2)
	else
		node = A.callE(fn, args, c == 2)
	end
	if c == 0 then
		node.single = false
		L.top = { expr = node }
	elseif c == 1 then
		emit(L, { t = "call", e = node })
	elseif c == 2 then
		assign(L, W(L, i, a), node)
	else
		local targets = {}
		for r = a, a + c - 2 do
			targets[#targets + 1] = W(L, i, r)
		end
		emit(L, { t = "assign", targets = targets, values = { node }, multi = true })
	end
end
H[O.CALL] = call
H[O.CALLFB] = call

H[O.RETURN] = function(L, i)
	local a, b = i.a, i.b
	local values = {}
	local last
	if b == 0 then
		last = (i.topReg or a) - 1
	else
		last = a + b - 2
	end
	for r = a, last do
		values[#values + 1] = R(L, i, r)
	end
	if b == 0 then
		values[#values + 1] = topExpr(L, "RETURN").expr
	end
	L.term = { k = "ret", values = values }
end

H[O.JUMP] = function(L, i) L.term = { k = "goto", to = blk(L, i.pc + 1 + i.d) } end
H[O.JUMPBACK] = H[O.JUMP]
H[O.JUMPX] = function(L, i) L.term = { k = "goto", to = blk(L, i.pc + 1 + i.e) } end

local function cond(L, i, c, tPc, fPc)
	local tb, fb = blk(L, tPc), blk(L, fPc)
	L.term = { k = "cond", cond = c, t = tb, f = fb }
end

H[O.JUMPIF] = function(L, i) cond(L, i, R(L, i, i.a), i.pc + 1 + i.d, i.pc + i.size) end
H[O.JUMPIFNOT] = function(L, i) cond(L, i, R(L, i, i.a), i.pc + i.size, i.pc + 1 + i.d) end

local function cmpJump(opname, negated)
	return function(L, i)
		local c = A.binE(opname, R(L, i, i.a), R(L, i, i.aux % 256))
		if negated then
			cond(L, i, c, i.pc + i.size, i.pc + 1 + i.d)
		else
			cond(L, i, c, i.pc + 1 + i.d, i.pc + i.size)
		end
	end
end
H[O.JUMPIFEQ] = cmpJump("==", false)
H[O.JUMPIFNOTEQ] = cmpJump("==", true)
H[O.JUMPIFLE] = cmpJump("<=", false)
H[O.JUMPIFNOTLE] = cmpJump("<=", true)
H[O.JUMPIFLT] = cmpJump("<", false)
H[O.JUMPIFNOTLT] = cmpJump("<", true)

local function xeq(L, i, rhs)
	local c = A.binE("==", R(L, i, i.a), rhs)
	if i.aux >= 2147483648 then
		cond(L, i, c, i.pc + i.size, i.pc + 1 + i.d)
	else
		cond(L, i, c, i.pc + 1 + i.d, i.pc + i.size)
	end
end
H[O.JUMPXEQKNIL] = function(L, i) xeq(L, i, A.nilE()) end
H[O.JUMPXEQKB] = function(L, i) xeq(L, i, A.boolE(i.aux % 2 == 1)) end
H[O.JUMPXEQKN] = function(L, i) xeq(L, i, constExpr(L, L.K[i.aux % 16777216])) end
H[O.JUMPXEQKS] = function(L, i) xeq(L, i, constExpr(L, L.K[i.aux % 16777216])) end

for op, sym in pairs(ARITH) do
	H[op] = function(L, i) assign(L, W(L, i, i.a), A.binE(sym, R(L, i, i.b), R(L, i, i.c))) end
end
for op, sym in pairs(ARITHK) do
	H[op] = function(L, i) assign(L, W(L, i, i.a), A.binE(sym, R(L, i, i.b), constExpr(L, L.K[i.c]))) end
end
H[O.SUBRK] = function(L, i) assign(L, W(L, i, i.a), A.binE("-", constExpr(L, L.K[i.b]), R(L, i, i.c))) end
H[O.DIVRK] = function(L, i) assign(L, W(L, i, i.a), A.binE("/", constExpr(L, L.K[i.b]), R(L, i, i.c))) end
H[O.AND] = function(L, i) assign(L, W(L, i, i.a), A.binE("and", R(L, i, i.b), R(L, i, i.c))) end
H[O.OR] = function(L, i) assign(L, W(L, i, i.a), A.binE("or", R(L, i, i.b), R(L, i, i.c))) end
H[O.ANDK] = function(L, i) assign(L, W(L, i, i.a), A.binE("and", R(L, i, i.b), constExpr(L, L.K[i.c]))) end
H[O.ORK] = function(L, i) assign(L, W(L, i, i.a), A.binE("or", R(L, i, i.b), constExpr(L, L.K[i.c]))) end
H[O.NOT] = function(L, i) assign(L, W(L, i, i.a), A.unE("not", R(L, i, i.b))) end
H[O.MINUS] = function(L, i) assign(L, W(L, i, i.a), A.unE("-", R(L, i, i.b))) end
H[O.LENGTH] = function(L, i) assign(L, W(L, i, i.a), A.unE("#", R(L, i, i.b))) end
H[O.CONCAT] = function(L, i)
	local parts = {}
	for r = i.b, i.c do
		parts[#parts + 1] = R(L, i, r)
	end
	assign(L, W(L, i, i.a), { t = "concat", parts = parts })
end

H[O.NEWTABLE] = function(L, i) assign(L, W(L, i, i.a), { t = "table", fields = {} }) end
H[O.DUPTABLE] = function(L, i)
	local k = L.K[i.d]
	local fields = {}
	if k and k.tag == "table" then
		for n, keyIdx in ipairs(k.keys) do
			fields[n] = { key = A.strE(kStr(L, keyIdx)), val = { t = "pending" } }
		end
	elseif k and k.tag == "tablek" then
		for n, keyIdx in ipairs(k.keys) do
			local vi = k.values[n]
			local val
			if vi >= 0 then
				val = constExpr(L, L.K[vi])
			else
				val = { t = "pending" }
			end
			fields[n] = { key = A.strE(kStr(L, keyIdx)), val = val }
		end
	else
		error("DUPTABLE with a non-table constant")
	end
	assign(L, W(L, i, i.a), { t = "table", fields = fields, template = true })
end
H[O.SETLIST] = function(L, i)
	local values = {}
	local last
	if i.c == 0 then
		last = (i.topReg or i.b) - 1
	else
		last = i.b + i.c - 2
	end
	for r = i.b, last do
		values[#values + 1] = R(L, i, r)
	end
	local multi = false
	if i.c == 0 then
		values[#values + 1] = topExpr(L, "SETLIST").expr
		multi = true
	end
	emit(L, { t = "setlist", obj = R(L, i, i.a), start = i.aux, values = values, multi = multi })
end

H[O.GETVARARGS] = function(L, i)
	local a, b = i.a, i.b
	if b == 0 then
		L.top = { expr = { t = "vararg", single = false } }
	elseif b == 2 then
		assign(L, W(L, i, a), { t = "vararg", single = true })
	elseif b > 2 then
		local targets = {}
		for r = a, a + b - 2 do
			targets[#targets + 1] = W(L, i, r)
		end
		emit(L, { t = "assign", targets = targets, values = { { t = "vararg", single = false } }, multi = true })
	end
end

H[O.FORNPREP] = function(L, i)
	local a = i.a
	L.term = {
		k = "forn",
		var = W(L, i, a + 3).var,
		start = R(L, i, a + 2),
		limit = R(L, i, a),
		step = R(L, i, a + 1),
		body = blk(L, i.pc + 1),
		exit = blk(L, i.pc + 1 + i.d),
	}
	L.term.var.kind = "for"
end
H[O.FORNLOOP] = function(L, i)
	L.term = { k = "forn_latch", body = blk(L, i.pc + 1 + i.d), exit = blk(L, i.pc + i.size) }
end

local function forgprep(L, i)
	local a = i.a
	local loopPc = i.pc + 1 + i.d
	local loopInsn = L.proto.insn[loopPc]
	if not loopInsn or loopInsn.op ~= O.FORGLOOP then
		error("FORGPREP target is not FORGLOOP")
	end
	local n = loopInsn.aux % 256
	local vars = {}
	for j = 1, n do
		local v = L.varOfDef(loopPc * 256 + a + 2 + j)
		v.kind = "for"
		vars[j] = v
	end
	L.term = {
		k = "forg_prep",
		exprs = { R(L, i, a), R(L, i, a + 1), R(L, i, a + 2) },
		vars = vars,
		to = blk(L, loopPc),
	}
end
for op in pairs(FORG_PREP) do
	H[op] = forgprep
end
H[O.FORGLOOP] = function(L, i)
	L.term = { k = "forg_latch", body = blk(L, i.pc + 1 + i.d), exit = blk(L, i.pc + 2) }
end

---------------------------------------------------------------------------------------------------
-- entry point
---------------------------------------------------------------------------------------------------

-- chunk: parsed bytecode; proto: prototype; upvalVars: array of Var objects owned by the parent
function Lift.lift(chunk, proto, upvalVars)
	local F = {
		chunk = chunk,
		proto = proto,
		vars = {},
		upvalVars = upvalVars or {},
		isVararg = proto.isVararg,
		numParams = proto.numParams,
	}

	local blocks, byPc = buildBlocks(proto)
	local n = proto.sizecode

	-- multi-result tracking and register analysis
	for _, b in ipairs(blocks) do
		local top
		for _, i in ipairs(b.insns) do
			local op = i.op
			if (op == O.CALL or op == O.CALLFB) and i.b == 0 then
				i.topReg = top
			elseif op == O.RETURN and i.b == 0 then
				i.topReg = top
			elseif op == O.SETLIST and i.c == 0 then
				i.topReg = top
			end
			if ((op == O.CALL or op == O.CALLFB) and i.c == 0) or (op == O.GETVARARGS and i.b == 0) then
				top = i.a
			end
			analyze(i)
		end
	end

	-- edges + reachability
	for _, b in ipairs(blocks) do
		b.succs = blockSuccs(b, byPc, n)
	end
	local entry = blocks[1]
	local reach = { [entry] = true }
	local stack = { entry }
	while #stack > 0 do
		local b = table.remove(stack)
		for _, s in ipairs(b.succs) do
			if not reach[s] then
				reach[s] = true
				stack[#stack + 1] = s
			end
		end
	end
	local live = {}
	for _, b in ipairs(blocks) do
		if reach[b] then
			live[#live + 1] = b
		else
			byPc[b.pc] = nil
		end
	end
	for _, b in ipairs(live) do
		b.preds = {}
	end
	for _, b in ipairs(live) do
		for _, s in ipairs(b.succs) do
			s.preds[#s.preds + 1] = b
		end
	end
	for k, b in ipairs(live) do
		b.id = k
	end
	blocks = live

	local readDef, varOfDef = analyzeFlow(F, blocks, entry, proto)

	-- NAMECALL defs (so CALL can recognise method calls without carrying state)
	local ncDef = {}
	for _, b in ipairs(blocks) do
		for _, i in ipairs(b.insns) do
			if i.op == O.NAMECALL then
				ncDef[i.pc * 256 + i.a] = (function()
					local k = proto.k[i.aux]
					if not k or k.tag ~= "string" then
						error("NAMECALL with a non-string method")
					end
					return k.value
				end)()
			elseif i.op == O.NAMECALLUDATA then
				local k = proto.k[i.aux % 65536]
				if not k or k.tag ~= "string" then
					error("NAMECALLUDATA with a non-string method")
				end
				ncDef[i.pc * 256 + i.a] = k.value
			end
		end
	end

	F.params = {}
	for r = 0, proto.numParams - 1 do
		local v = varOfDef(-256 + r)
		v.kind = "param"
		v.paramIndex = r + 1
		F.params[r + 1] = v
	end

	local L = {
		F = F,
		chunk = chunk,
		proto = proto,
		K = proto.k,
		readDef = readDef,
		varOfDef = varOfDef,
		byPc = byPc,
		ncDef = ncDef,
	}

	for _, b in ipairs(blocks) do
		L.out = b.stmts
		L.term = nil
		L.top = nil
		for _, i in ipairs(b.insns) do
			local h = H[i.op]
			if not h then
				error("no handler for opcode " .. tostring(Bytecode.NAMES[i.op]))
			end
			h(L, i)
		end
		if not b.term then
			if L.term then
				b.term = L.term
			else
				local last = b.insns[#b.insns]
				local nextBlock = byPc[last.pc + last.size]
				if not nextBlock then
					error("control flow falls off the end of the function")
				end
				b.term = { k = "goto", to = nextBlock }
			end
		end
	end

	F.blocks = blocks
	F.entry = entry
	F.byPc = byPc
	return F
end

return Lift
