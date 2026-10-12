--!nocheck
-- Tovek (Luau port) :: Bytecode.luau
-- Luau bytecode deserializer. Supports bytecode versions 4..14, Roblox's opcode
-- encoding (decode key 203) and plain compiler output (key 1).

local Bytecode = {}

local NAMES = {
	[0] = "NOP", "BREAK", "LOADNIL", "LOADB", "LOADN", "LOADK", "MOVE", "GETGLOBAL", "SETGLOBAL",
	"GETUPVAL", "SETUPVAL", "CLOSEUPVALS", "GETIMPORT", "GETTABLE", "SETTABLE", "GETTABLEKS",
	"SETTABLEKS", "GETTABLEN", "SETTABLEN", "NEWCLOSURE", "NAMECALL", "CALL", "RETURN", "JUMP",
	"JUMPBACK", "JUMPIF", "JUMPIFNOT", "JUMPIFEQ", "JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ",
	"JUMPIFNOTLE", "JUMPIFNOTLT", "ADD", "SUB", "MUL", "DIV", "MOD", "POW", "ADDK", "SUBK", "MULK",
	"DIVK", "MODK", "POWK", "AND", "OR", "ANDK", "ORK", "CONCAT", "NOT", "MINUS", "LENGTH",
	"NEWTABLE", "DUPTABLE", "SETLIST", "FORNPREP", "FORNLOOP", "FORGLOOP", "FORGPREP_INEXT",
	"FASTCALL3", "FORGPREP_NEXT", "NATIVECALL", "GETVARARGS", "DUPCLOSURE", "PREPVARARGS", "LOADKX",
	"JUMPX", "FASTCALL", "COVERAGE", "CAPTURE", "SUBRK", "DIVRK", "FASTCALL1", "FASTCALL2",
	"FASTCALL2K", "FORGPREP", "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS", "IDIV", "IDIVK",
	"GETUDATAKS", "SETUDATAKS", "NAMECALLUDATA", "NEWCLASSMEMBER", "CALLFB", "CMPPROTO", "FASTPCALL",
}
local OP = {}
for i = 0, 89 do
	OP[NAMES[i]] = i
end
Bytecode.NAMES = NAMES
Bytecode.OP = OP

-- instruction encodings
local FORM = {}
local function setForm(form, list)
	for _, o in ipairs(list) do
		FORM[o] = form
	end
end
local function range(a, b)
	local t = {}
	for i = a, b do
		t[#t + 1] = i
	end
	return t
end
setForm("ABC", { 0, 1, 2, 3, 55, 60, 62, 63, 65, 66, 68, 70, 81, 82, 89 })
setForm("ABC", range(6, 11))
setForm("ABC", range(13, 18))
setForm("ABC", range(20, 22))
setForm("ABC", range(33, 53))
setForm("ABC", range(71, 75))
setForm("ABC", range(83, 87))
setForm("AD", { 4, 5, 12, 19, 54, 61, 64, 88 })
setForm("AD", range(23, 32))
setForm("AD", range(56, 59))
setForm("AD", range(76, 80))
setForm("E", { 67, 69 })

local HAS_AUX = {}
for _, name in ipairs({
	"GETGLOBAL", "SETGLOBAL", "GETIMPORT", "GETTABLEKS", "SETTABLEKS", "NAMECALL", "JUMPIFEQ",
	"JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ", "JUMPIFNOTLE", "JUMPIFNOTLT", "NEWTABLE", "SETLIST",
	"FORGLOOP", "LOADKX", "FASTCALL2", "FASTCALL2K", "FASTCALL3", "JUMPXEQKNIL", "JUMPXEQKB",
	"JUMPXEQKN", "JUMPXEQKS", "GETUDATAKS", "SETUDATAKS", "NAMECALLUDATA", "NEWCLASSMEMBER",
	"CALLFB", "CMPPROTO",
}) do
	HAS_AUX[OP[name]] = true
end
Bytecode.HAS_AUX = HAS_AUX

---------------------------------------------------------------------------------------------------
-- binary reader
---------------------------------------------------------------------------------------------------

local byte, sub = string.byte, string.sub
local floor = math.floor

local function decodeDouble(s, p)
	local b1, b2, b3, b4, b5, b6, b7, b8 = byte(s, p, p + 7)
	if not b8 then
		error("unexpected end of bytecode")
	end
	local lo = b1 + b2 * 256 + b3 * 65536 + b4 * 16777216
	local hi = b5 + b6 * 256 + b7 * 65536 + b8 * 16777216
	local sign = (hi >= 2147483648) and -1 or 1
	local exp = floor(hi / 1048576) % 2048
	local mant = (hi % 1048576) * 4294967296 + lo
	if exp == 0 then
		return sign * mant * 2 ^ -1074
	elseif exp == 2047 then
		if mant == 0 then
			return sign * math.huge
		end
		return 0 / 0
	end
	return sign * (1 + mant / 4503599627370496) * 2 ^ (exp - 1023)
end

local function decodeFloat(s, p)
	local b1, b2, b3, b4 = byte(s, p, p + 3)
	if not b4 then
		error("unexpected end of bytecode")
	end
	local v = b1 + b2 * 256 + b3 * 65536 + b4 * 16777216
	local sign = (v >= 2147483648) and -1 or 1
	local exp = floor(v / 8388608) % 256
	local mant = v % 8388608
	if exp == 0 then
		return sign * mant * 2 ^ -149
	elseif exp == 255 then
		if mant == 0 then
			return sign * math.huge
		end
		return 0 / 0
	end
	return sign * (1 + mant / 8388608) * 2 ^ (exp - 127)
end

local unpack_ = string.unpack
local function readDouble(s, p)
	if unpack_ then
		local ok, v = pcall(unpack_, "<d", s, p)
		if ok then
			return v
		end
	end
	return decodeDouble(s, p)
end
local function readFloat(s, p)
	if unpack_ then
		local ok, v = pcall(unpack_, "<f", s, p)
		if ok then
			return v
		end
	end
	return decodeFloat(s, p)
end

local Reader = {}
Reader.__index = Reader

local function newReader(s)
	return setmetatable({ s = s, pos = 1, len = #s }, Reader)
end

function Reader:u8()
	local p = self.pos
	local b = byte(self.s, p)
	if not b then
		error("unexpected end of bytecode")
	end
	self.pos = p + 1
	return b
end

function Reader:u32()
	local p = self.pos
	local b1, b2, b3, b4 = byte(self.s, p, p + 3)
	if not b4 then
		error("unexpected end of bytecode")
	end
	self.pos = p + 4
	return b1 + b2 * 256 + b3 * 65536 + b4 * 16777216
end

function Reader:i32()
	local v = self:u32()
	if v >= 2147483648 then
		v = v - 4294967296
	end
	return v
end

function Reader:varint()
	local result, shift = 0, 0
	local s, p = self.s, self.pos
	while true do
		local b = byte(s, p)
		if not b then
			error("unexpected end of bytecode")
		end
		p = p + 1
		result = result + (b % 128) * 2 ^ shift
		if b < 128 then
			break
		end
		shift = shift + 7
		if shift > 63 then
			error("varint too long")
		end
	end
	self.pos = p
	return result
end

function Reader:bytes(n)
	local p = self.pos
	if p + n - 1 > self.len then
		error("unexpected end of bytecode")
	end
	self.pos = p + n
	return sub(self.s, p, p + n - 1)
end

function Reader:f64()
	local v = readDouble(self.s, self.pos)
	self.pos = self.pos + 8
	return v
end

function Reader:f32()
	local v = readFloat(self.s, self.pos)
	self.pos = self.pos + 4
	return v
end

---------------------------------------------------------------------------------------------------
-- constants / prototypes
---------------------------------------------------------------------------------------------------

local function readConstant(r, version, strings)
	local tag = r:u8()
	if tag == 0 then
		return { tag = "nil" }
	elseif tag == 1 then
		return { tag = "boolean", value = r:u8() ~= 0 }
	elseif tag == 2 then
		return { tag = "number", value = r:f64() }
	elseif tag == 3 then
		local idx = r:varint()
		return { tag = "string", value = strings[idx] or "", index = idx }
	elseif tag == 4 then
		return { tag = "import", id = r:u32() }
	elseif tag == 5 then
		local n = r:varint()
		local keys = {}
		for i = 1, n do
			keys[i] = r:varint()
		end
		return { tag = "table", keys = keys }
	elseif tag == 6 then
		return { tag = "closure", proto = r:varint() }
	elseif tag == 7 then
		local x, y, z, w = r:f32(), r:f32(), r:f32(), r:f32()
		return { tag = "vector", x = x, y = y, z = z, w = w }
	elseif tag == 8 then
		local n = r:varint()
		local keys, values = {}, {}
		for i = 1, n do
			keys[i] = r:varint()
			values[i] = r:i32()
		end
		return { tag = "tablek", keys = keys, values = values }
	elseif tag == 9 then
		local neg = r:u8()
		local mag = r:varint()
		if neg ~= 0 then
			mag = -mag
		end
		return { tag = "number", value = mag, integer = true }
	elseif tag == 10 then
		r:varint()
		local np, nm = r:varint(), r:varint()
		for _ = 1, np + nm do
			r:varint()
		end
		return { tag = "class" }
	elseif tag == 11 then
		if version < 13 then
			error("vector double constant in old bytecode")
		end
		local x, y, z, w = r:f64(), r:f64(), r:f64(), r:f64()
		return { tag = "vector", x = x, y = y, z = z, w = w }
	end
	error("unknown constant tag " .. tostring(tag))
end

local function readProto(r, version, strings, key, id)
	local p = { id = id }
	p.maxStack = r:u8()
	p.numParams = r:u8()
	p.numUpvals = r:u8()
	p.isVararg = r:u8() ~= 0
	p.flags = r:u8()
	local typeLen = r:varint()
	r:bytes(typeLen)

	local sizecode = r:varint()
	if sizecode == 0 then
		error("empty function")
	end
	local words = {}
	p.wordsPos = r.pos
	for i = 0, sizecode - 1 do
		words[i] = r:u32()
	end

	-- decode instructions (raw word index == pc)
	local insn = {}
	local pc = 0
	while pc < sizecode do
		local w = words[pc]
		local opByte = w % 256
		local op = (opByte * key) % 256
		if op == 97 then
			op = 0
		end
		local form = FORM[op]
		if not form then
			error("invalid opcode " .. op .. " at pc " .. pc)
		end
		local i = { op = op, pc = pc, size = 1 }
		if form == "ABC" then
			i.a = floor(w / 256) % 256
			i.b = floor(w / 65536) % 256
			i.c = floor(w / 16777216) % 256
		elseif form == "AD" then
			i.a = floor(w / 256) % 256
			local d = floor(w / 65536)
			if d >= 32768 then
				d = d - 65536
			end
			i.d = d
		else
			local e = floor(w / 256)
			if e >= 8388608 then
				e = e - 16777216
			end
			i.e = e
		end
		if HAS_AUX[op] then
			if pc + 1 >= sizecode then
				error("missing aux word")
			end
			i.aux = words[pc + 1]
			i.size = 2
		end
		insn[pc] = i
		pc = pc + i.size
	end
	p.sizecode = sizecode
	p.insn = insn

	local nk = r:varint()
	local ks = {}
	for i = 0, nk - 1 do
		ks[i] = readConstant(r, version, strings)
	end
	p.k = ks
	p.nk = nk

	local np = r:varint()
	local children = {}
	for i = 1, np do
		children[i] = r:varint()
	end
	p.children = children

	p.lineDefined = r:varint()
	local nameIdx = r:varint()
	p.debugName = nameIdx ~= 0 and strings[nameIdx] or nil

	local hasLine = r:u8()
	if hasLine ~= 0 then
		local gap = r:u8()
		r:bytes(sizecode)
		local nabs = floor((sizecode - 1) / 2 ^ gap) + 1
		r:bytes(nabs * 4)
	end

	local hasDebug = r:u8()
	p.locals = {}
	p.upvalueNames = {}
	if hasDebug ~= 0 then
		local nl = r:varint()
		for i = 1, nl do
			local nIdx = r:varint()
			local s, e = r:varint(), r:varint()
			local reg = r:u8()
			p.locals[i] = { name = nIdx ~= 0 and strings[nIdx] or nil, startpc = s, endpc = e, reg = reg }
		end
		local nu = r:varint()
		for i = 1, nu do
			local nIdx = r:varint()
			p.upvalueNames[i] = nIdx ~= 0 and strings[nIdx] or nil
		end
	end
	p.hasDebug = hasDebug ~= 0

	if version >= 11 then
		local nf = r:varint()
		for _ = 1, nf do
			local slotType = r:u8()
			if slotType ~= 0 then
				error("unknown feedback slot type")
			end
			r:varint()
		end
	end
	if version >= 12 and (p.flags % 16) >= 8 then
		r:varint() -- inlinable cost model
	end
	return p
end

local function parseWith(bytes, key)
	local r = newReader(bytes)
	local version = r:u8()
	if version == 0 then
		return nil, "compile error: " .. sub(bytes, 2)
	end
	if version < 4 or version > 14 then
		error("unsupported bytecode version " .. version)
	end
	local typesVersion = r:u8()
	if typesVersion > 3 then
		error("unsupported types version " .. typesVersion)
	end
	local nstr = r:varint()
	local strings = {}
	for i = 1, nstr do
		strings[i] = r:bytes(r:varint())
	end
	if typesVersion == 3 then
		while true do
			local idx = r:u8()
			if idx == 0 then
				break
			end
			r:varint()
		end
	end
	local np = r:varint()
	local protos = {}
	for i = 0, np - 1 do
		if version >= 12 then
			local size = r:varint()
			local stop = r.pos + size
			protos[i] = readProto(r, version, strings, key, i)
			if r.pos > stop then
				error("prototype overran its declared size")
			end
			r.pos = stop
		else
			protos[i] = readProto(r, version, strings, key, i)
		end
	end
	local main = r:varint()
	if not protos[main] then
		error("invalid main prototype")
	end

	-- validation: every function must end with RETURN (this also verifies the opcode key)
	for i = 0, np - 1 do
		local p = protos[i]
		local last
		for pc = p.sizecode - 1, 0, -1 do
			if p.insn[pc] then
				last = p.insn[pc]
				break
			end
		end
		if not last or (last.op ~= OP.RETURN and last.op ~= OP.JUMP and last.op ~= OP.JUMPBACK and last.op ~= OP.JUMPX) then
			error("opcode key mismatch")
		end
	end
	return {
		version = version,
		typesVersion = typesVersion,
		strings = strings,
		protos = protos,
		nprotos = np,
		main = main,
		key = key,
	}
end

-- bytes: raw bytecode string. key: optional opcode decode key (203 = Roblox client, 1 = plain).
function Bytecode.parse(bytes, key)
	if type(bytes) ~= "string" or #bytes < 2 then
		return nil, "empty bytecode"
	end
	local candidates = key and { key } or { 203, 1 }
	local lastErr
	for _, k in ipairs(candidates) do
		local ok, res, err = pcall(parseWith, bytes, k)
		if ok then
			if res then
				return res
			end
			return nil, err
		end
		lastErr = res
	end
	return nil, tostring(lastErr)
end

---------------------------------------------------------------------------------------------------
-- disassembler (used for the fallback output when structuring a function fails)
---------------------------------------------------------------------------------------------------

local function constText(k)
	if not k then
		return "?"
	end
	if k.tag == "string" then
		return string.format("%q", k.value)
	elseif k.tag == "number" or k.tag == "boolean" then
		return tostring(k.value)
	elseif k.tag == "nil" then
		return "nil"
	end
	return "<" .. k.tag .. ">"
end

function Bytecode.disasm(proto)
	local lines = {}
	local pc = 0
	while pc < proto.sizecode do
		local i = proto.insn[pc]
		if not i then
			break
		end
		local s = string.format("[%04d] %-14s", pc, NAMES[i.op] or "?")
		if i.a then
			s = s .. " A=" .. i.a
		end
		if i.b then
			s = s .. " B=" .. i.b
		end
		if i.c then
			s = s .. " C=" .. i.c
		end
		if i.d then
			s = s .. " D=" .. i.d
		end
		if i.e then
			s = s .. " E=" .. i.e
		end
		if i.aux then
			s = s .. string.format(" AUX=0x%X", i.aux)
		end
		if i.op == OP.LOADK then
			s = s .. "  ; " .. constText(proto.k[i.d])
		elseif i.op == OP.GETTABLEKS or i.op == OP.SETTABLEKS or i.op == OP.NAMECALL or i.op == OP.GETGLOBAL or i.op == OP.SETGLOBAL then
			s = s .. "  ; " .. constText(proto.k[i.aux])
		end
		lines[#lines + 1] = s
		pc = pc + i.size
	end
	return lines
end

return Bytecode
