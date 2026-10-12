--!nocheck
-- Tovek (Luau port) :: Decompile.luau
-- Orchestrates the pipeline: deserialize -> lift -> simplify -> structure -> declare/name -> print.

local import = ...
local Bytecode = import("Bytecode")
local Lift = import("Lift")
local Simplify = import("Simplify")
local Structure = import("Structure")
local Post = import("Post")
local Emit = import("Emit")

local Decompile = {}

local function fallbackFunction(proto, err)
	local params = {}
	for i = 1, proto.numParams do
		params[i] = { id = -i, kind = "param", name = "p" .. i, defs = 0, uses = 0 }
	end
	local body = {
		{ t = "comment", text = "Tovek could not structure this function: " .. tostring(err) },
		{ t = "comment", text = "Raw bytecode listing follows." },
	}
	for _, line in ipairs(Bytecode.disasm(proto)) do
		body[#body + 1] = { t = "comment", text = line }
	end
	return { F = { vars = {} }, params = params, isVararg = proto.isVararg, body = body, failed = true }
end

local function build(chunk, id, upvalVars, state)
	local proto = chunk.protos[id]
	local func
	local ok, err = pcall(function()
		local F = Lift.lift(chunk, proto, upvalVars)
		Simplify.run(F)
		local body = Structure.run(F)
		Post.structured(F, body)
		func = { F = F, params = F.params, isVararg = F.isVararg, body = body }
	end)
	if not ok then
		func = fallbackFunction(proto, err)
		state.failures = state.failures + 1
	end
	func.proto = id
	state.count = state.count + 1
	if state.onProgress and state.count % 25 == 0 then
		state.onProgress(state.count, chunk.nprotos)
	end
	Post.eachClosure(func.body, function(c)
		if not c.func then
			c.func = build(chunk, c.proto, c.upvals, state)
		end
	end)
	return func
end

-- bytes: raw bytecode (string). options: { key = number?, header = string?, onProgress = function? }
-- returns source, stats
function Decompile.decompile(bytes, options)
	options = options or {}
	local chunk, err = Bytecode.parse(bytes, options.key)
	if not chunk then
		return "-- Tovek: failed to read bytecode: " .. tostring(err) .. "\n", { failures = 1, error = err }
	end
	local protoNames = {}
	for i = 0, chunk.nprotos - 1 do
		protoNames[i] = chunk.protos[i].debugName
	end
	local state = { failures = 0, count = 0, onProgress = options.onProgress }
	local root = build(chunk, chunk.main, {}, state)
	local ok, perr = pcall(Post.finish, root, protoNames)
	if not ok then
		state.failures = state.failures + 1
		state.finishError = perr
	end
	local header = options.header
	if header == nil then
		header = "-- Decompiled with Tovek (Luau port)"
	end
	if header == false then
		header = nil
	end
	local rok, src = pcall(Emit.render, root, header)
	if not rok then
		return "-- Tovek: failed to print output: " .. tostring(src) .. "\n", { failures = state.failures + 1, error = src }
	end
	return src, { failures = state.failures, functions = state.count, finishError = state.finishError, version = chunk.version }
end

return Decompile
