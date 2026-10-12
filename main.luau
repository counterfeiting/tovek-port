--!nocheck
-- Tovek (Luau port) :: main.luau
-- Entry point for executors. Run this file; it defines `getgenv().decompile2`.
--
--   loadstring(game:HttpGet("https://raw.githubusercontent.com/<user>/<repo>/main/main.luau"))()
--   print(decompile2(game.Players.LocalPlayer.PlayerScripts.SomeScript))
--   print(decompile2("game.ReplicatedStorage.Modules.Util"))
--
-- Every other module (Bytecode, Ast, Lift, Simplify, Structure, Post, Emit, Decompile) is fetched
-- with loadstring(game:HttpGet(...)) from BASE_URL.

local BASE_URL = "https://raw.githubusercontent.com/counterfeiting/tovek-port/main/"
local EXTENSION = ".luau"

local env = (getgenv and getgenv()) or _G
BASE_URL = env.TOVEK_BASE_URL or BASE_URL

---------------------------------------------------------------------------------------------------
-- module loader
---------------------------------------------------------------------------------------------------

local cache = env.__TOVEK_MODULES or {}
env.__TOVEK_MODULES = cache

local function import(name)
	local mod = cache[name]
	if mod ~= nil then
		return mod
	end
	local url = BASE_URL .. name .. EXTENSION
	local okGet, src = pcall(function()
		return game:HttpGet(url)
	end)
	if not okGet or type(src) ~= "string" or src == "" then
		error("Tovek: could not download " .. url .. " (" .. tostring(src) .. ")", 0)
	end
	local fn, err = loadstring(src, "=Tovek/" .. name)
	if not fn then
		error("Tovek: " .. name .. " failed to compile: " .. tostring(err), 0)
	end
	mod = fn(import)
	cache[name] = mod
	return mod
end

---------------------------------------------------------------------------------------------------
-- script path resolution
---------------------------------------------------------------------------------------------------

-- "game.Workspace.Folder[\"My Script\"]" -> { "Workspace", "Folder", "My Script" }
local function parsePath(path)
	local tokens = {}
	local i, n = 1, #path
	while i <= n do
		local c = path:sub(i, i)
		if c == "." then
			i = i + 1
		elseif c == "[" then
			local q = path:sub(i + 1, i + 1)
			if q ~= '"' and q ~= "'" then
				error("Tovek: malformed path near position " .. i, 0)
			end
			local close = path:find(q .. "]", i + 2, true)
			if not close then
				error("Tovek: unterminated [..] in path", 0)
			end
			tokens[#tokens + 1] = path:sub(i + 2, close - 1)
			i = close + 2
		else
			local j = path:find("[%.%[]", i) or (n + 1)
			tokens[#tokens + 1] = path:sub(i, j - 1)
			i = j
		end
	end
	return tokens
end

local function resolve(target)
	if typeof(target) == "Instance" then
		return target
	end
	if type(target) ~= "string" then
		error("decompile2: expected a script Instance or a path string, got " .. typeof(target), 0)
	end
	local tokens = parsePath(target)
	if tokens[1] == "game" then
		table.remove(tokens, 1)
	end
	local cur = game
	for index, name in ipairs(tokens) do
		local child = cur:FindFirstChild(name)
		if not child and cur == game then
			local ok, svc = pcall(function()
				return game:GetService(name)
			end)
			if ok then
				child = svc
			end
		end
		if not child then
			error(('decompile2: "%s" is not a child of %s'):format(name, cur:GetFullName()), 0)
		end
		cur = child
	end
	return cur
end

---------------------------------------------------------------------------------------------------
-- decompile2
---------------------------------------------------------------------------------------------------

-- decompile2(script | "path.to.script" | rawBytecode, options?)
--   options.key     : force an opcode decode key (default: auto, 203 for Roblox / 1 for plain)
--   options.header  : custom header comment, or false for none
-- Returns the decompiled source as a string.
local function decompile2(target, options)
	options = options or {}
	local bytecode, label

	-- raw bytecode strings start with a version byte (< 15); a path never does
	if type(target) == "string" and #target > 0 and target:byte(1) <= 14 then
		bytecode, label = target, "raw bytecode"
	else
		local inst = resolve(target)
		if type(getscriptbytecode) ~= "function" then
			error("decompile2: this executor does not provide getscriptbytecode", 0)
		end
		local ok, result = pcall(getscriptbytecode, inst)
		if not ok then
			error("decompile2: getscriptbytecode failed: " .. tostring(result), 0)
		end
		if type(result) ~= "string" or #result == 0 then
			error("decompile2: " .. inst:GetFullName() .. " has no bytecode", 0)
		end
		bytecode = result
		local okName, full = pcall(function()
			return inst:GetFullName()
		end)
		label = okName and full or inst.Name
	end

	local Decompile = import("Decompile")
	local header = options.header
	if header == nil then
		header = "-- Decompiled with Tovek (Luau port): " .. label
	end
	local source, stats = Decompile.decompile(bytecode, { key = options.key, header = header })
	if stats and stats.failures and stats.failures > 0 and options.quiet ~= true then
		warn(("decompile2: %d function(s) could not be structured and were emitted as raw listings"):format(stats.failures))
	end
	return source, stats
end

env.decompile2 = decompile2
env.Tovek = {
	decompile = decompile2,
	import = import,
	baseUrl = BASE_URL,
	clearCache = function()
		for k in pairs(cache) do
			cache[k] = nil
		end
	end,
}

return decompile2
