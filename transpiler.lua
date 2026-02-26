-- transpiler.lua  v12
-- made by macsipac, Apache 2.0 licence
-- Lua -> C AOT transpiler
-- Usage: lua transpiler.lua input.lua  =>  output.c
-- v12: bug fixes from v11 review:
--   * #table now tracks contiguous array boundary (array_len) not hash entry count
--   * Anonymous function (closure) now emits a runtime error instead of silent nil
--   * Runtime error system: lua_runtime_error() for type/call/index errors
--   * value_call / table_call abort with "attempt to call a X value" on non-func
--   * table_get aborts with "attempt to index a X value" on non-table
--   * value_add type-checks operands and aborts with arithmetic error
--   * Numeric for loop supports float bounds (dual int/double codegen)
--   * table_resize: moves entries without double-free risk; notes power-of-two invariant
--   * power-of-two cap invariant documented in table_raw_set
--   * realloc safety: old pointer saved before realloc to avoid leak on failure
--   * Global retbuf non-reentrancy documented

local input_path  = arg[1] or "input.lua"
local output_path = "output.c"

-- ---------------------------------------------------------------------------
-- Tiny utilities
-- ---------------------------------------------------------------------------
local function trim(s) return (s or ""):match("^%s*(.-)%s*$") end
local LONG_STR_NL = "\1"

local function escape_c(s)
    return s:gsub("\\","\\\\"):gsub('"','\\"')
             :gsub("\1","\\n"):gsub("\n","\\n"):gsub("\r","\\r")
end
local function lua_str_inner(expr)
    local d, inner = expr:sub(1,1), expr:sub(2,-2)
    inner = inner:gsub("\1","\\n")
    if d == "'" then inner = inner:gsub("\\'","'"):gsub('"','\\"') end
    return inner
end
local function is_int(s)  return s:match("^%-?%d+$") end
local function is_flt(s)  return s:match("^%-?%d+%.%d+$") end
local function is_str(s)  return s:match('^".*"$') or s:match("^'.*'$") or s:match("^%[%[.-%]%]$") end
local function is_id(s)   return s:match("^[A-Za-z_][A-Za-z0-9_]*$") end

local function skip_str(e, i)
    local q = e:sub(i,i); i = i+1
    while i <= #e do
        local c = e:sub(i,i)
        if c == '\\' then i = i+2 elseif c == q then return i+1 else i = i+1 end
    end
    return i
end

-- Generic depth-aware scanner; cb(i, ch) -> truthy to stop, returns stop_i, extra
local function depth_scan(e, cb)
    local d, i = 0, 1
    while i <= #e do
        local ch = e:sub(i,i)
        if ch == '"' or ch == "'" then i = skip_str(e,i)
        elseif ch=='(' or ch=='[' or ch=='{' then d=d+1; i=i+1
        elseif ch==')' or ch==']' or ch=='}' then d=d-1; i=i+1
        else
            if d == 0 then local r1,r2 = cb(i,ch); if r1 then return r1,r2 end end
            i = i+1
        end
    end
end

local function find_op(expr, ops)
    local len = #expr
    return depth_scan(expr, function(i)
        for _,op in ipairs(ops) do
            local ol = #op
            if i+ol-1 <= len and expr:sub(i,i+ol-1) == op then
                if op:match("%a") then
                    local ls = op:find("%S") or 1
                    local le = op:find("%s*$") - 1
                    local kw_start = i + ls - 1
                    local kw_end   = i + le - 1
                    local bef = expr:sub(kw_start-1, kw_start-1)
                    local aft = expr:sub(kw_end+1,   kw_end+1)
                    if (bef=="" or bef:match("%W")) and (aft=="" or aft:match("%W")) then return i,op end
                else return i,op end
            end
        end
    end)
end

local function split_args(s)
    local args, cur, d = {}, "", 0
    local i = 1
    while i <= #s do
        local ch = s:sub(i,i)
        if ch=='"' or ch=="'" then
            local j = skip_str(s,i); cur = cur..s:sub(i,j-1); i = j
        elseif ch=='(' or ch=='[' or ch=='{' then d=d+1; cur=cur..ch; i=i+1
        elseif ch==')' or ch==']' or ch=='}' then d=d-1; cur=cur..ch; i=i+1
        elseif ch==',' and d==0 then table.insert(args, trim(cur)); cur=""; i=i+1
        else cur=cur..ch; i=i+1 end
    end
    if trim(cur) ~= "" then table.insert(args, trim(cur)) end
    return args
end

local function last_additive(expr)
    local last_i, last_op, d = nil, nil, 0
    local i = 1
    while i <= #expr do
        local ch = expr:sub(i,i)
        if ch=='"' or ch=="'" then i=skip_str(expr,i)
        elseif ch=='(' or ch=='[' or ch=='{' then d=d+1; i=i+1
        elseif ch==')' or ch==']' or ch=='}' then d=d-1; i=i+1
        elseif d==0 and (ch=='+' or ch=='-') and trim(expr:sub(1,i-1)) ~= "" then
            last_i=i; last_op=ch; i=i+1
        else i=i+1 end
    end
    return last_i, last_op
end

local function last_muldiv(expr)
    local last_i, last_op, d = nil, nil, 0
    local i = 1
    while i <= #expr do
        local ch = expr:sub(i,i)
        if ch=='"' or ch=="'" then i=skip_str(expr,i)
        elseif ch=='(' or ch=='[' or ch=='{' then d=d+1; i=i+1
        elseif ch==')' or ch==']' or ch=='}' then d=d-1; i=i+1
        elseif d==0 and (ch=='*' or ch=='/' or ch=='%') then
            last_i=i; last_op=ch; i=i+1
        else i=i+1 end
    end
    return last_i, last_op
end

-- ---------------------------------------------------------------------------
-- Temp var counter + array-call builder
-- ---------------------------------------------------------------------------
local tmp_counter = 0
local function newtmp() tmp_counter=tmp_counter+1; return "__tmp"..tmp_counter end

-- Build a GNU statement-expression that creates a Value[] and calls fn(n, arr)
local function build_array_call(fn_name, args_t)
    local n = #args_t
    if n == 0 then return "", ("%s(0,NULL)"):format(fn_name) end
    local arr = newtmp()
    local init = table.concat(args_t, ",")
    return "", ("(__extension__({Value %s[%d]={%s};%s(%d,%s);}))"):format(arr,n,init,fn_name,n,arr)
end

-- ---------------------------------------------------------------------------
-- Expression translator
-- ---------------------------------------------------------------------------
local current_fn_fixed_argc = 0
local fn_names = {}

local function translate_expr(expr)
    expr = trim(expr)
    if expr == "" then return "make_int(0)" end

    -- Anonymous function literal: closures not supported in AOT; emit runtime error.
    if expr:match("^function%s*%(") then
        return '(__extension__({lua_runtime_error("attempt to use closure (anonymous function): not supported in AOT compilation");LUA_UNREACHABLE();make_nil();}))'
    end

    -- select('#',...) / select(n,...)
    do local inner = expr:match("^select%s*%((.+)%)$")
        if inner then
            local sa = split_args(inner)
            if #sa >= 1 then
                local sel = trim(sa[1])
                if sel=='"#"' or sel=="'#'" then
                    return ("make_int(__nargs - %d)"):format(current_fn_fixed_argc)
                elseif is_int(sel) then
                    local n = tonumber(sel)
                    if n and n > 0 then
                        return ("(__nargs > %d ? value_copy(__args[%d]) : make_nil())"):format(
                            current_fn_fixed_argc+n-1, current_fn_fixed_argc+n-1)
                    elseif n and n < 0 then
                        return ("(__nargs > %d ? value_copy(__args[__nargs+%d]) : make_nil())"):format(
                            current_fn_fixed_argc, n)
                    end
                else
                    return ("lua_select_vararg(%s,%d,__nargs,__args)"):format(
                        translate_expr(sel), current_fn_fixed_argc)
                end
            end
        end
    end

    if expr == "..." then
        return ("(__nargs > %d ? value_copy(__args[%d]) : make_nil())"):format(
            current_fn_fixed_argc, current_fn_fixed_argc)
    end

    if expr:match("^not%s+") then
        return ("value_not(%s)"):format(translate_expr(expr:match("^not%s+(.+)$")))
    end
    if expr:sub(1,1)=='-' and is_int(expr:sub(2)) then return "make_int("..expr..")" end
    if expr:sub(1,1)=='-' and is_flt(expr:sub(2)) then return "make_double("..expr..")" end

    do local i = find_op(expr,{" or "})
        if i then return ("value_or(%s,%s)"):format(
            translate_expr(trim(expr:sub(1,i-1))), translate_expr(trim(expr:sub(i+4)))) end end
    do local i = find_op(expr,{" and "})
        if i then return ("value_and(%s,%s)"):format(
            translate_expr(trim(expr:sub(1,i-1))), translate_expr(trim(expr:sub(i+5)))) end end
    do local i,op = find_op(expr,{"==","~=","<=",">=","<",">"})
        if i then
            local fn = ({["=="]="value_eq",["~="]="value_neq",["<="]="value_le",
                         [">="]="value_ge",["<"]="value_lt",[">"]="value_gt"})[op]
            return ("%s(%s,%s)"):format(fn,
                translate_expr(trim(expr:sub(1,i-1))), translate_expr(trim(expr:sub(i+#op))))
        end end
    do local i = find_op(expr,{".."})
        if i then return ("value_concat(%s,%s)"):format(
            translate_expr(trim(expr:sub(1,i-1))), translate_expr(trim(expr:sub(i+2)))) end end

    -- Power operator ^ (right-associative: scan left-to-right finds leftmost = base)
    do local i = find_op(expr,{"^"})
        if i then return ("value_pow(%s,%s)"):format(
            translate_expr(trim(expr:sub(1,i-1))), translate_expr(trim(expr:sub(i+1)))) end end

    do local li, lo = last_additive(expr)
        if li then
            return (lo=='+' and "value_add" or "value_sub").."("..
                translate_expr(trim(expr:sub(1,li-1)))..",\z
"..translate_expr(trim(expr:sub(li+1)))..")"
        end end

    do local li, lo = last_muldiv(expr)
        if li then
            return ({["*"]="value_mul",["/"]="value_div",["%"]="value_mod"})[lo].."("..
                translate_expr(trim(expr:sub(1,li-1)))..",\z
"..translate_expr(trim(expr:sub(li+1)))..")"
        end end

    if expr:sub(1,1)=='#' then return ("value_len(%s)"):format(translate_expr(expr:sub(2))) end
    if expr:match("^%[%[") then
        local s = expr:match("^%[%[(.-)%]%]$")
        if s then return ('make_string("%s")'):format(escape_c(s)) end
    end
    if is_str(expr)  then return ('make_string("%s")'):format(lua_str_inner(expr)) end
    if is_int(expr)  then return "make_int("..expr..")" end
    if is_flt(expr)  then return "make_double("..expr..")" end
    if expr == "true"  then return "make_bool(1)" end
    if expr == "false" then return "make_bool(0)" end
    if expr == "nil"   then return "make_nil()" end

    -- table constructor
    if expr:sub(1,1) == '{' then
        local d, close = 0, #expr
        for i2=1,#expr do local ch=expr:sub(i2,i2)
            if ch=='{' then d=d+1 elseif ch=='}' then d=d-1 end
            if d==0 then close=i2; break end end
        local inner = trim(expr:sub(2,close-1))
        if inner == "" then return "make_table()" end
        if trim(inner) == "..." then
            local tbl = newtmp()
            local fixed = current_fn_fixed_argc
            return ("(__extension__({Value %s=make_table();for(int __vi=%d;__vi<__nargs;__vi++)table_raw_set(%s.tbl,make_int(__vi-%d+1),value_copy(__args[__vi]));%s;}))"):format(
                tbl, fixed, tbl, fixed, tbl)
        end
        local parts, ai = {}, 1
        for _,field in ipairs(split_args(inner)) do
            field = trim(field)
            local k,v = field:match("^([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
            if k and v then
                table.insert(parts, ('make_string("%s")'):format(escape_c(k)))
                table.insert(parts, translate_expr(v))
            else
                local ke,ve = field:match("^%[(.+)%]%s*=%s*(.+)$")
                if ke and ve then
                    table.insert(parts, translate_expr(ke)); table.insert(parts, translate_expr(ve))
                else
                    table.insert(parts, "make_int("..ai..")"); table.insert(parts, translate_expr(field)); ai=ai+1
                end
            end
        end
        return ("table_init(%d,%s)"):format(#parts/2, table.concat(parts,","))
    end

    -- builtins that return Value
    local simple_builtins = {
        {pat="^error%s*%((.*)%)$",      fn=function(a) return ("lua_error(%s)"):format(a[1] and translate_expr(trim(a[1])) or 'make_string("error")') end},
        {pat="^assert%s*%((.*)%)$",     fn=function(a) return ("lua_assert(%s,%s)"):format(translate_expr(trim(a[1] or "")), a[2] and translate_expr(trim(a[2])) or 'make_string("assertion failed!")') end},
        {pat="^tostring%s*%((.+)%)$",   fn=function(a) return ("lua_tostring(%s)"):format(translate_expr(a[1])) end, raw=true},
        {pat="^tonumber%s*%((.+)%)$",   fn=function(a) return ("lua_tonumber(%s)"):format(translate_expr(a[1])) end, raw=true},
        {pat="^type%s*%((.+)%)$",       fn=function(a) return ("lua_type(%s)"):format(translate_expr(a[1])) end, raw=true},
        {pat="^ipairs%s*%((.+)%)$",     fn=function(a) return ("value_copy(%s)"):format(translate_expr(a[1])) end, raw=true},
        {pat="^pairs%s*%((.+)%)$",      fn=function(a) return ("value_copy(%s)"):format(translate_expr(a[1])) end, raw=true},
    }
    for _,b in ipairs(simple_builtins) do
        local inner = expr:match(b.pat)
        if inner then
            local a = b.raw and {inner} or split_args(inner)
            return b.fn(a)
        end
    end

    do local inner = expr:match("^rawget%s*%((.+)%)$")
        if inner then
            local ga = split_args(inner)
            return ("table_get(%s,%s)"):format(translate_expr(trim(ga[1] or "")), translate_expr(trim(ga[2] or "")))
        end end

    -- string.X(...) dispatched via array-based call
    do local fn, fa = expr:match("^string%.([A-Za-z_][A-Za-z0-9_]*)%s*%((.*)%)$")
        if fn then
            local args = split_args(fa); local p = {}
            for _,a in ipairs(args) do table.insert(p, translate_expr(trim(a))) end
            local _,call = build_array_call("lua_string_"..fn, p)
            return call
        end end

    -- method call obj:method(args)
    do local found
        depth_scan(expr, function(i, ch)
            if ch == ':' then
                local obj  = trim(expr:sub(1,i-1))
                local rest = trim(expr:sub(i+1))
                local meth, as = rest:match("^([A-Za-z_][A-Za-z0-9_]*)%s*%((.*)%)$")
                if meth then
                    local args = split_args(as); local p = {}
                    for _,a in ipairs(args) do table.insert(p, translate_expr(trim(a))) end
                    local str_methods = {find=1,match=1,gmatch=1,gsub=1,sub=1,
                        len=1,format=1,rep=1,reverse=1,upper=1,lower=1,byte=1,char=1,dump=1}
                    if str_methods[meth] then
                        local all = {translate_expr(obj)}
                        for _,pa in ipairs(p) do table.insert(all, pa) end
                        local _,call = build_array_call("lua_string_"..meth, all)
                        found = call
                    else
                        found = ("value_method_call(%s,\"%s\",%d%s)"):format(
                            translate_expr(obj), meth, #args,
                            #args>0 and ","..table.concat(p,",") or "")
                    end
                    return true
                end
            end
        end)
        if found then return found end end

    -- suffix walker: call / index / dot
    do
        local ss, st, d2 = nil, nil, 0
        local i = 1
        while i <= #expr do
            local ch = expr:sub(i,i)
            if ch=='"' or ch=="'" then i=skip_str(expr,i)
            elseif ch=='(' or ch=='[' or ch=='{' then
                if d2==0 and i>1 then
                    if ch=='(' then ss=i; st='call' elseif ch=='[' then ss=i; st='index' end
                end
                d2=d2+1; i=i+1
            elseif ch==')' or ch==']' or ch=='}' then d2=d2-1; i=i+1
            elseif ch=='.' and d2==0 and i>1 then
                local rest = expr:sub(i+1)
                local key  = rest:match("^([A-Za-z_][A-Za-z0-9_]*)")
                if key and rest:sub(#key+1,#key+1) ~= '(' then ss=i; st='dot' end
                i=i+1
            else i=i+1 end
        end

        if ss and st=='call' then
            local d3, cp = 0, #expr
            for j=ss,#expr do local ch=expr:sub(j,j)
                if ch=='(' then d3=d3+1 elseif ch==')' then d3=d3-1 end
                if d3==0 then cp=j; break end end
            local fn_e = trim(expr:sub(1,ss-1))
            local as   = trim(expr:sub(ss+1,cp-1))
            local args = as ~= "" and split_args(as) or {}
            local parts = {}
            for ai,a in ipairs(args) do
                if trim(a)=="..." and ai==#args then
                    table.insert(parts, ("__nargs - %d"):format(current_fn_fixed_argc))
                    table.insert(parts, ("__args + %d"):format(current_fn_fixed_argc))
                    local sep = table.concat(parts,",")
                    local dobj, dkey = fn_e:match("^(.+)%.([A-Za-z_][A-Za-z0-9_]*)$")
                    if dobj then
                        return ("table_call_splice(%s,make_string(\"%s\"),%s)"):format(
                            translate_expr(dobj), escape_c(dkey), sep)
                    end
                    local fn_val = fn_names[fn_e] and ("make_func(%s)"):format(fn_e) or ("value_copy(%s)"):format(fn_e)
                    return ("value_call_splice(%s,%s)"):format(fn_val, sep)
                else
                    table.insert(parts, translate_expr(trim(a)))
                end
            end
            local sep = #parts>0 and ","..table.concat(parts,",") or ""
            local dobj, dkey = fn_e:match("^(.+)%.([A-Za-z_][A-Za-z0-9_]*)$")
            if dobj then
                return ("table_call(%s,make_string(\"%s\"),%d%s)"):format(
                    translate_expr(dobj), escape_c(dkey), #parts, sep)
            end
            local fn_val = fn_names[fn_e] and ("make_func(%s)"):format(fn_e) or ("value_copy(%s)"):format(fn_e)
            return ("value_call(%s,%d%s)"):format(fn_val, #parts, sep)

        elseif ss and st=='index' then
            local d3, cb = 0, #expr
            for j=ss,#expr do local ch=expr:sub(j,j)
                if ch=='[' then d3=d3+1 elseif ch==']' then d3=d3-1 end
                if d3==0 then cb=j; break end end
            return ("table_get(%s,%s)"):format(
                translate_expr(trim(expr:sub(1,ss-1))),
                translate_expr(trim(expr:sub(ss+1,cb-1))))

        elseif ss and st=='dot' then
            local te  = trim(expr:sub(1,ss-1))
            local key = expr:sub(ss+1):match("^([A-Za-z_][A-Za-z0-9_]*)")
            if key and te ~= "" then
                return ('table_get(%s,make_string("%s"))'):format(translate_expr(te), escape_c(key))
            end
        end
    end

    if is_id(expr) then
        if fn_names[expr] then return ("make_func(%s)"):format(expr) end
        return "value_copy("..expr..")"
    end
    do local inner = expr:match("^%((.+)%)$"); if inner then return translate_expr(inner) end end
    return expr
end

-- ---------------------------------------------------------------------------
-- Source pre-processing
-- ---------------------------------------------------------------------------
local raw_src = assert(io.open(input_path)):read("*a")
raw_src = raw_src:gsub('\\z[ \t]*\n[ \t]*','')
raw_src = raw_src:gsub("%[%[(.-)%]%]", function(s)
    return '"'..s:gsub("\\","\\\\"):gsub('"','\\"')
                 :gsub("\r\n",LONG_STR_NL):gsub("\n",LONG_STR_NL):gsub("\r",LONG_STR_NL)..'"'
end)
local raw_lines = {}
for l in (raw_src.."\n"):gmatch("([^\n]*)\n") do table.insert(raw_lines,l) end

local function brace_depth(line)
    local depth, i, in_s, sq = 0, 1, false, nil
    while i <= #line do
        local ch = line:sub(i,i)
        if in_s then
            if ch=='\\' then i=i+2 elseif ch==sq then in_s=false; i=i+1 else i=i+1 end
        else
            if ch=='"' or ch=="'" then in_s=true; sq=ch; i=i+1
            elseif ch=='{' then depth=depth+1; i=i+1
            elseif ch=='}' then depth=depth-1; i=i+1
            elseif ch=='-' and line:sub(i,i+1)=='--' then break
            else i=i+1 end
        end
    end
    return depth
end

local lines = {}
do local i = 1
    while i <= #raw_lines do
        local combined = raw_lines[i]; local depth = brace_depth(combined)
        while depth > 0 and i < #raw_lines do
            i=i+1; combined=combined.." "..trim(raw_lines[i]); depth=depth+brace_depth(raw_lines[i])
        end
        table.insert(lines, combined); i=i+1
    end
end

local function line_block_delta(s)
    local delta = 0; local i = 1
    local s_trimmed = s:match("^%s*(.-)%s*$") or s
    local starts_with_do = s_trimmed:match("^do%s") or s_trimmed == "do"
    while i <= #s do
        local ch = s:sub(i,i)
        if ch=='"' or ch=="'" then i=skip_str(s,i)
        elseif ch=='-' and s:sub(i,i+1)=='--' then break
        else
            local kw = s:sub(i):match("^([A-Za-z_][A-Za-z0-9_]*)")
            if kw then
                local prev = i>1 and s:sub(i-1,i-1) or ""
                if not prev:match("[A-Za-z0-9_]") then
                    if kw=="function" or kw=="if" or kw=="for"
                    or kw=="while"   or kw=="repeat" then delta=delta+1
                    elseif kw=="do" and starts_with_do then delta=delta+1
                    elseif kw=="end" or kw=="until" then delta=delta-1 end
                end
                i=i+#kw
            else i=i+1 end
        end
    end
    return delta
end

local functions, topstmts = {}, {}

local function opens_block(ts)
    return ts:match("^if%s") or ts:match("^for%s") or ts:match("^while%s")
        or ts:match("^function%s") or ts:match("^local%s+function%s")
        or ts=="do" or ts:match("^do%s") or ts:match("^repeat$") or ts:match("^repeat%s")
end

local i, n = 1, #lines
while i <= n do
    local line = lines[i]; local s = trim(line)
    if s=="" or s:match("^%-%-") then i=i+1
    elseif s:match("^function%s") or s:match("^local%s+function%s") then
        local name, args = s:match("^%s*function%s+([A-Za-z_][A-Za-z0-9_]*)%s*%((.-)%)")
        if not name then name,args = s:match("^%s*local%s+function%s+([A-Za-z_][A-Za-z0-9_]*)%s*%((.-)%)") end
        if not name then
            local t2,m2,ma = s:match("^%s*function%s+([A-Za-z_][A-Za-z0-9_]*)[.:]([A-Za-z_][A-Za-z0-9_]*)%s*%((.-)%)")
            if t2 then name=t2.."__"..m2; args=ma end
        end
        args = trim(args or "")
        local body = {}
        local is_single = false
        do
            local fn_pos = s:find("function%s")
            local op = fn_pos and s:find("%(", fn_pos)
            if op then
                local pd, pi = 0, op
                while pi <= #s do
                    local pc = s:sub(pi,pi)
                    if pc=='(' then pd=pd+1 elseif pc==')' then pd=pd-1; if pd==0 then break end end
                    pi=pi+1
                end
                local after = trim(s:sub(pi+1))
                local bstr  = after:match("^(.-)%s*end$")
                if bstr ~= nil then is_single=true; if trim(bstr)~="" then body={trim(bstr)} end end
            end
        end
        if is_single then
            functions[#functions+1]={name=name,args=args,body=body}; fn_names[name]=true; i=i+1
        else
            i=i+1; local depth=1
            while i<=n do
                local ts2=trim(lines[i]); depth=depth+line_block_delta(ts2)
                if depth==0 then i=i+1; break end
                table.insert(body,lines[i]); i=i+1
            end
            functions[#functions+1]={name=name,args=args,body=body}; fn_names[name]=true
        end
    else table.insert(topstmts,line); i=i+1 end
end

local globals, builtin_globals = {}, {math=true,os=true,io=true,arg=true,string=true}
for _,line in ipairs(topstmts) do
    local s = trim(line)
    local v = s:match("^local%s+([A-Za-z_][A-Za-z0-9_]*)") or s:match("^([A-Za-z_][A-Za-z0-9_]*)%s*=")
    if v and not builtin_globals[v] then globals[v]=true end
    local vlist_str = s:match("^local%s+([A-Za-z_][A-Za-z0-9_]*%s*,.+)$")
        or s:match("^([A-Za-z_][A-Za-z0-9_]*%s*,[A-Za-z0-9_%s,]*)%s*=")
    if vlist_str then
        vlist_str = vlist_str:match("^(.-)%s*=.*$") or vlist_str
        for vname in vlist_str:gmatch("[A-Za-z_][A-Za-z0-9_]*") do
            if not builtin_globals[vname] then globals[vname]=true end
        end
    end
end

-- collect_block: returns body table and number of lines consumed (including the `end`)
local function collect_block(src, si)
    local body = {}; local depth = 1; local j = si
    while j <= #src do
        local L = trim(src[j]); depth = depth + line_block_delta(L)
        if depth == 0 then return body, (j - si + 1) end
        table.insert(body, src[j]); j=j+1
    end
    return body, (j - si)
end

-- ---------------------------------------------------------------------------
-- Code generation
-- ---------------------------------------------------------------------------
local gen_stmt

-- Emit free_value for all tracked locals in ctx.
local function emit_scope_cleanup(ctx)
    local code = ""
    if ctx.local_vars then
        for v in pairs(ctx.local_vars) do
            code = code..("    free_value(%s);\n"):format(v)
        end
    end
    return code
end

local function gen_print(pargs)
    local args = split_args(pargs); local nn = #args; local arr = newtmp()
    local code = ("    Value %s[%d];\n"):format(arr, math.max(nn,1))
    for ii,a in ipairs(args) do code=code..("    %s[%d]=%s;\n"):format(arr,ii-1,translate_expr(trim(a))) end
    return code..("    print_values(%d,%s);\n"):format(nn,arr)
end

local function gen_assert_stmt(s)
    local args = split_args(s:match("^assert%s*%((.*)%)$"))
    local ce = translate_expr(trim(args[1] or ""))
    local me = args[2] and translate_expr(trim(args[2])) or 'make_string("assertion failed!")'
    local tmp = newtmp()
    return ("    Value %s=lua_assert(%s,%s);\n    free_value(%s);\n"):format(tmp,ce,me,tmp)
end

local function find_then(str)
    local then_pos
    local d, i = 0, 1
    while i <= #str do
        local ch = str:sub(i,i)
        if ch=='"' or ch=="'" then i=skip_str(str,i)
        elseif ch=='(' or ch=='[' or ch=='{' then d=d+1; i=i+1
        elseif ch==')' or ch==']' or ch=='}' then d=d-1; i=i+1
        elseif d==0 and str:sub(i,i+4)==" then" then
            local af = str:sub(i+5,i+5)
            if af=="" or af==" " or af=="\t" then then_pos=i; break end
            i=i+1
        else i=i+1 end
    end
    return then_pos
end

local function gen_if(s, ctx, idx, src)
    if s:match("%send$") or s=="end" then
        local tp = find_then(s)
        if tp then
            local cond = trim(s:sub(4,tp-1)); local rest = trim(s:sub(tp+5))
            if rest:match("end$") then
                rest = trim(rest:sub(1,-4))
                local ep
                do local d3,i3=0,1; while i3<=#rest do
                    local ch=rest:sub(i3,i3)
                    if ch=='"' or ch=="'" then i3=skip_str(rest,i3)
                    elseif ch=='(' or ch=='[' or ch=='{' then d3=d3+1; i3=i3+1
                    elseif ch==')' or ch==']' or ch=='}' then d3=d3-1; i3=i3+1
                    elseif d3==0 and rest:sub(i3,i3+5)==" else " then ep=i3; break
                    else i3=i3+1 end
                end end
                local function gs2(st_list)
                    local code = ""
                    for _,st2 in ipairs(st_list) do if trim(st2)~="" then
                        local r = gen_stmt({st2},1,ctx); code=code..r end end
                    return code
                end
                local tmp,cv = newtmp(), newtmp()
                local code = ("    Value %s=%s;\n    int %s=value_is_truthy(%s);\n    free_value(%s);\n    if(%s){\n"):format(
                    tmp, translate_expr(cond), cv, tmp, tmp, cv)
                if ep then
                    code = code..gs2({trim(rest:sub(1,ep-1))}).."    }else{\n"..gs2({trim(rest:sub(ep+6))}).."    }\n"
                else code = code..gs2({rest}).."    }\n" end
                return code, 1
            end
        end
    end

    local cond, inline_body_line
    do
        local tp = find_then(s)
        if tp then
            cond = trim(s:sub(4,tp-1)); inline_body_line = trim(s:sub(tp+5))
        else cond = trim(s:match("^if%s+(.+)$") or ""); inline_body_line = "" end
    end

    local clauses = {{kind="if",cond=cond,body={}}}
    if inline_body_line ~= "" then table.insert(clauses[1].body, inline_body_line) end
    local depth = 1; local j = idx+1
    while j <= #src do
        local L = trim(src[j])
        if opens_block(L) then depth=depth+1; table.insert(clauses[#clauses].body,src[j]); j=j+1
        elseif depth > 1 then
            if L=="end" then depth=depth-1 end
            table.insert(clauses[#clauses].body,src[j]); j=j+1
        else
            if L:match("^elseif%s") then
                local etp = find_then(L)
                local ec, eb
                if etp then ec=trim(L:sub(8,etp-1)); eb=trim(L:sub(etp+5))
                else ec=trim(L:match("^elseif%s+(.+)$") or ""); eb="" end
                clauses[#clauses+1]={kind="elseif",cond=ec,body={}}; j=j+1
                if eb ~= "" then table.insert(clauses[#clauses].body, eb) end
            elseif L=="else" or L:match("^else%s*$") then
                clauses[#clauses+1]={kind="else",body={}}; j=j+1
            elseif L=="end" then j=j+1; break
            else table.insert(clauses[#clauses].body,src[j]); j=j+1 end
        end
    end

    local function gen_body(b)
        local bc=""; local bi=1
        while bi<=#b do local st,c2=gen_stmt(b,bi,ctx); bc=bc..st; bi=bi+c2 end
        return bc
    end
    local function gen_clauses(cls, ci)
        if ci > #cls then return "" end; local cl = cls[ci]
        if cl.kind=="if" or cl.kind=="elseif" then
            local tmp,cv = newtmp(), newtmp()
            local code = ("    Value %s=%s;\n    int %s=value_is_truthy(%s);\n    free_value(%s);\n    if(%s){\n"):format(
                tmp, translate_expr(cl.cond), cv, tmp, tmp, cv)
            code = code..gen_body(cl.body)
            if ci < #cls then return code.."    }else{\n"..gen_clauses(cls,ci+1).."    }\n"
            else return code.."    }\n" end
        else return gen_body(cl.body) end
    end
    return gen_clauses(clauses, 1), (j-idx)
end

-- Save/restore context around loops
local function loop_save(ctx)
    local saved_lv = {}
    if ctx.local_vars then for k,v in pairs(ctx.local_vars) do saved_lv[k]=v end end
    local saved_am = {}; for k,v in pairs(ctx.assigned) do saved_am[k]=v end
    local before = {}
    if ctx.local_vars then for k in pairs(ctx.local_vars) do before[k]=true end end
    return saved_lv, saved_am, before
end

local function loop_restore(ctx, saved_lv, saved_am, before, loop_vars, indent)
    local code = ""
    if ctx.local_vars then
        for v in pairs(ctx.local_vars) do
            if not before[v] then code=code..(indent.."free_value(%s);\n"):format(v) end
        end
        ctx.local_vars = saved_lv
        for _,lv in ipairs(loop_vars) do if ctx.local_vars then ctx.local_vars[lv]=nil end end
    end
    ctx.assigned = saved_am
    return code
end

-- Generate a for..in loop body for ipairs-like iteration (table indexed 1..n)
local function gen_ipairs_loop(tbl_expr, vars, for_body, ctx)
    local tbl_tmp = newtmp()
    local ivar = vars[1] or "_"
    local vvar = vars[2]
    local idx_c = newtmp()
    local code = ("    Value %s=%s;\n"):format(tbl_tmp, tbl_expr)
    code = code..("    for(int64_t %s=1;;%s++){\n"):format(idx_c, idx_c)
    code = code..("        Value %s=make_int(%s);\n"):format(ivar, idx_c)
    if vvar then
        code = code..("        Value %s=table_get(value_copy(%s),make_int(%s));\n"):format(vvar, tbl_tmp, idx_c)
        code = code..("        if(%s.t==T_NIL){free_value(%s);free_value(%s);break;}\n"):format(vvar, ivar, vvar)
    else
        local chk = newtmp()
        code = code..("        Value %s=table_get(value_copy(%s),make_int(%s));\n"):format(chk, tbl_tmp, idx_c)
        code = code..("        if(%s.t==T_NIL){free_value(%s);free_value(%s);break;}\n"):format(chk, ivar, chk)
        code = code..("        free_value(%s);\n"):format(chk)
    end

    local saved_lv, saved_am, before = loop_save(ctx)
    if ctx.local_vars then
        ctx.local_vars[ivar] = true
        if vvar then ctx.local_vars[vvar] = true end
    end
    local bi = 1
    while bi <= #for_body do local st,c2=gen_stmt(for_body,bi,ctx); code=code..st; bi=bi+c2 end

    local lvars = {ivar}; if vvar then lvars[#lvars+1]=vvar end
    local cleanup = loop_restore(ctx, saved_lv, saved_am, before, lvars, "        ")
    code = code..cleanup
    code = code..("        free_value(%s);\n"):format(ivar)
    if vvar then code=code..("        free_value(%s);\n"):format(vvar) end
    code = code.."    }\n"
    code = code..("    free_value(%s);\n"):format(tbl_tmp)
    return code
end

local function gen_for(s, ctx, idx, src)
    -- numeric for
    local var,se,le,ste = s:match("^for%s+([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.-)%s*,%s*(.-)%s*,%s*(.-)%s+do$")
    if not var then var,se,le = s:match("^for%s+([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.-)%s*,%s*(.-)%s+do$") end
    if var then
        local for_body, consumed = collect_block(src, idx+1)
        local sv,lv,stv = newtmp(), newtmp(), newtmp()
        local code = ("    Value %s=%s;\n    Value %s=%s;\n    Value %s=%s;\n"):format(
            sv,translate_expr(se), lv,translate_expr(le), stv, ste and translate_expr(ste) or "make_int(1)")

        -- ── FIX 4: dual codepath for float vs integer loop bounds ──────────
        -- If any bound is a double at runtime, use double arithmetic throughout.
        -- This correctly handles: for i = 1.2, 5.8, 0.5 do ... end
        -- FIX 9: step == 0 is a runtime error in Lua
        code = code..("    if(%s.t==T_DOUBLE||%s.t==T_DOUBLE||%s.t==T_DOUBLE){\n"):format(sv,lv,stv)
        code = code..("        if(numval(%s)==0.0){free_value(%s);free_value(%s);free_value(%s);lua_runtime_error(\"'for' step is zero\");}\n"):format(stv,sv,lv,stv)
        -- float branch
        code = code..("        double __fs_%s=numval(%s),__fl_%s=numval(%s),__fst_%s=numval(%s);\n"):format(var,sv,var,lv,var,stv)
        code = code..("        for(double __fd_%s=__fs_%s;(__fst_%s>=0?__fd_%s<=__fl_%s:__fd_%s>=__fl_%s);__fd_%s+=__fst_%s){\n"):format(var,var,var,var,var,var,var,var,var)
        code = code..("            Value %s=make_double(__fd_%s);\n"):format(var,var)
        local saved_lv2,saved_am2,before2 = loop_save(ctx)
        -- Do NOT add var to ctx.local_vars: loop_restore runs outside the C loop
        -- brace and cannot see the per-iteration Value. We free it explicitly below.
        local bi2 = 1
        while bi2 <= #for_body do local st2,c3=gen_stmt(for_body,bi2,ctx); code=code..st2; bi2=bi2+c3 end
        -- cleanup inner locals declared inside body (not var itself)
        local cleanup2 = loop_restore(ctx, saved_lv2, saved_am2, before2, {}, "            ")
        code = code..cleanup2..("            free_value(%s);\n        }\n    }else{\n"):format(var)
        -- integer branch
        code = code..("        if(%s.i==0){free_value(%s);free_value(%s);free_value(%s);lua_runtime_error(\"'for' step is zero\");}\n"):format(stv,sv,lv,stv)
        code = code..("        for(int64_t __i_%s=%s.i;(%s.i>=0?__i_%s<=%s.i:__i_%s>=%s.i);__i_%s+=%s.i){\n"):format(
            var,sv, stv,var,lv,var,lv,var,stv)
        code = code..("            Value %s=make_int(__i_%s);\n"):format(var,var)

        local saved_lv,saved_am,before = loop_save(ctx)
        -- Same: do NOT add var to ctx.local_vars; free explicitly inside loop.

        local bi = 1
        while bi <= #for_body do local st,c2=gen_stmt(for_body,bi,ctx); code=code..st; bi=bi+c2 end

        -- cleanup inner locals; var excluded — freed explicitly per iteration
        local cleanup = loop_restore(ctx, saved_lv, saved_am, before, {}, "            ")
        return code..cleanup..("            free_value(%s);\n        }\n    }\n"):format(var)
            ..("    free_value(%s);free_value(%s);free_value(%s);\n"):format(sv,lv,stv), 1+consumed
    end

    -- generic for
    local vars_str, iter_expr = s:match("^for%s+(.-)%s+in%s+(.-)%s+do$")
    if vars_str and iter_expr then
        iter_expr = trim(iter_expr)
        local vars = split_args(vars_str)
        local for_body, consumed = collect_block(src, idx+1)

        -- s:gmatch(pat) form
        do local gm_self, gm_pat = iter_expr:match("^(.-)%s*:%s*gmatch%s*%((.+)%)$")
            if gm_self and gm_pat then
                local self_t = translate_expr(trim(gm_self))
                local pat_t  = translate_expr(trim(gm_pat))
                local _,call = build_array_call("lua_string_gmatch", {self_t, pat_t})
                return gen_ipairs_loop(call, vars, for_body, ctx), 1+consumed
            end end

        -- ipairs / string.gmatch(s,p)
        local ipairs_inner = iter_expr:match("^ipairs%s*%((.+)%)$")
        local gmatch_inner = iter_expr:match("^string%.gmatch%s*%((.+)%)$")
        if ipairs_inner then
            return gen_ipairs_loop(translate_expr(ipairs_inner), vars, for_body, ctx), 1+consumed
        end
        if gmatch_inner then
            local gargs = split_args(gmatch_inner); local ga = {}
            for _,a in ipairs(gargs) do table.insert(ga, translate_expr(trim(a))) end
            local _,call = build_array_call("lua_string_gmatch", ga)
            return gen_ipairs_loop(call, vars, for_body, ctx), 1+consumed
        end

        -- pairs
        local pairs_inner = iter_expr:match("^pairs%s*%((.+)%)$")
        if pairs_inner then
            local tbl_tmp = newtmp()
            local kvar = vars[1] or "_"
            local vvar = vars[2]
            local pidx = newtmp()
            local code = ("    Value %s=%s;\n"):format(tbl_tmp, translate_expr(pairs_inner))
            code = code..("    if(%s.t==T_TABLE&&%s.tbl){\n"):format(tbl_tmp, tbl_tmp)
            code = code..("    for(int %s=0;%s<%s.tbl->cap;%s++){\n"):format(pidx,pidx,tbl_tmp,pidx)
            code = code..("        if(!%s.tbl->entries[%s].used)continue;\n"):format(tbl_tmp,pidx)
            code = code..("        Value %s=value_copy(%s.tbl->entries[%s].key);\n"):format(kvar,tbl_tmp,pidx)
            if vvar then
                code = code..("        Value %s=value_copy(%s.tbl->entries[%s].val);\n"):format(vvar,tbl_tmp,pidx)
            end

            local saved_lv, saved_am, before = loop_save(ctx)
            if ctx.local_vars then
                ctx.local_vars[kvar]=true; if vvar then ctx.local_vars[vvar]=true end
            end

            local bi = 1
            while bi <= #for_body do local st,c2=gen_stmt(for_body,bi,ctx); code=code..st; bi=bi+c2 end

            local lvars = {kvar}; if vvar then lvars[#lvars+1]=vvar end
            local cleanup = loop_restore(ctx, saved_lv, saved_am, before, lvars, "        ")
            code = code..cleanup
            code = code..("        free_value(%s);\n"):format(kvar)
            if vvar then code=code..("        free_value(%s);\n"):format(vvar) end
            code = code.."    }\n    }\n"
            code = code..("    free_value(%s);\n"):format(tbl_tmp)
            return code, 1+consumed
        end
    end
    return nil
end

local function try_table_assign(s)
    local tbl,key,rhs = s:match("^([A-Za-z_][A-Za-z0-9_]*)%.([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
    if tbl then
        return ("    table_set(value_copy(%s),make_string(\"%s\"),%s);\n"):format(tbl,escape_c(key),translate_expr(rhs))
    end
    local t2,k2,r2 = s:match("^([A-Za-z_][A-Za-z0-9_]*)%[(.+)%]%s*=%s*(.+)$")
    if t2 then
        return ("    table_set(value_copy(%s),%s,%s);\n"):format(t2,translate_expr(k2),translate_expr(r2))
    end
end

local function is_call_expr(e)
    e = trim(e); if e:sub(-1)~=')' then return false end; return e:find("%(") ~= nil
end

local function is_single_call(e)
    e = trim(e)
    if not e:match("%(") or e:sub(-1)~=')' then return false end
    local found = false
    depth_scan(e, function(_,ch) if ch==',' then found=true; return true end end)
    return not found
end

gen_stmt = function(src, idx, ctx)
    local s = trim(src[idx] or ""); if s=="" then return "",1 end
    local lv = ctx.local_vars; local am = ctx.assigned; local gt = ctx.globals_tbl

    if s:match("^%-%-") then return "",1 end
    if s == "break" then return "    break;\n",1 end

    -- skip nested function definitions (already hoisted)
    if s:match("^local%s+function%s") or (s:match("^function%s") and lv) then
        local fn_pos = s:find("function%s")
        local op2 = fn_pos and s:find("%(", fn_pos)
        if op2 then
            local pd,pi=0,op2
            while pi<=#s do local pc=s:sub(pi,pi)
                if pc=='(' then pd=pd+1 elseif pc==')' then pd=pd-1; if pd==0 then break end end; pi=pi+1 end
            local after=trim(s:sub(pi+1))
            if after:match("^(.-)%s*end$") then return "    /* nested fn skipped */\n",1 end
        end
        local _,consumed = collect_block(src, idx+1)
        return "    /* nested fn skipped */\n", 1+consumed
    end

    -- while
    local wcond = s:match("^while%s+(.-)%s+do$")
    if wcond then
        local while_body, consumed = collect_block(src, idx+1)
        local tmp,cv = newtmp(), newtmp()
        local code = ("    while(1){\n        Value %s=%s;\n        int %s=value_is_truthy(%s);\n        free_value(%s);\n        if(!%s)break;\n"):format(
            tmp, translate_expr(wcond), cv, tmp, tmp, cv)
        local saved_lv,saved_am,before = loop_save(ctx)
        local bi=1
        while bi<=#while_body do local st,c2=gen_stmt(while_body,bi,ctx); code=code..st; bi=bi+c2 end
        local cleanup = loop_restore(ctx, saved_lv, saved_am, before, {}, "        ")
        return code..cleanup.."    }\n", 1+consumed
    end
    if s == "do" then
        local do_body, consumed = collect_block(src, idx+1)
        local code = "    {\n"
        local saved_lv,saved_am,before = loop_save(ctx)
        local bi=1
        while bi<=#do_body do local st,c2=gen_stmt(do_body,bi,ctx); code=code..st; bi=bi+c2 end
        local cleanup = loop_restore(ctx, saved_lv, saved_am, before, {}, "    ")
        return code..cleanup.."    }\n", 1+consumed
    end

    -- repeat..until
    if s == "repeat" then
        local rep_body,rep_j = {}, idx+1; local dr=1
        while rep_j <= #src do
            local RL = trim(src[rep_j])
            if opens_block(RL) then dr=dr+1 end
            if RL:match("^until%s") and dr==1 then break end
            if RL=="end" then dr=dr-1 end
            table.insert(rep_body, src[rep_j]); rep_j=rep_j+1
        end
        local ucond = trim(src[rep_j] or ""):match("^until%s+(.+)$") or "false"
        local code = "    do{\n"
        local saved_lv,saved_am,before = loop_save(ctx)
        local bi=1
        while bi<=#rep_body do local st,c2=gen_stmt(rep_body,bi,ctx); code=code..st; bi=bi+c2 end
        local cleanup = loop_restore(ctx, saved_lv, saved_am, before, {}, "    ")
        local tmp,cv = newtmp(), newtmp()
        code = code..cleanup
        code = code..("        Value %s=%s;\n        int %s=value_is_truthy(%s);\n        free_value(%s);\n        if(%s)break;\n"):format(
            tmp, translate_expr(ucond), cv, tmp, tmp, cv)
        return code.."    }while(1);\n", (rep_j-idx+1)
    end

    -- return
    if s == "return" then
        local cleanup = emit_scope_cleanup(ctx)
        ctx.returned = true
        return cleanup.."    __retncount=0;\n    return make_nil();\n", 1
    end
    local ret = s:match("^return%s+(.+)$")
    if ret then
        local retvals = split_args(ret)
        local code = ""
        local tmps = {}

        if #retvals==1 and is_single_call(trim(retvals[1])) then
            local tmp = newtmp()
            code = ("    Value %s=%s;\n"):format(tmp, translate_expr(trim(retvals[1])))
            local cleanup = emit_scope_cleanup(ctx)
            ctx.returned = true
            return code..cleanup..("    return %s;\n"):format(tmp), 1
        end

        for ri,rv in ipairs(retvals) do
            local tmp = newtmp()
            code = code..("    Value %s=%s;\n"):format(tmp, translate_expr(trim(rv)))
            tmps[ri] = tmp
        end
        local cleanup = emit_scope_cleanup(ctx)
        ctx.returned = true
        code = code..cleanup
        code = code.."    for(int __ri=1;__ri<__retncount&&__ri<__retbuf_cap;__ri++)free_value(__retbuf[__ri]);\n"
        code = code..("    __retncount=%d;\n"):format(#tmps)
        for ri,tmp in ipairs(tmps) do
            if ri==1 then code=code..("    __retbuf[0]=%s;\n"):format(tmp)
            else code=code..("    if(%d<__retbuf_cap)__retbuf[%d]=%s;else free_value(%s);\n"):format(ri-1,ri-1,tmp,tmp) end
        end
        if #tmps==0 then return code.."    return make_nil();\n",1 end
        return code.."    return __retbuf[0];\n",1
    end

    if s:match("^assert%s*%(") then return gen_assert_stmt(s),1 end

    -- local multi-var
    do local rest_loc = s:match("^local%s+(.+)$")
        if rest_loc then
            local eq_idx
            for ci=1,#rest_loc do
                local cc=rest_loc:sub(ci,ci)
                if cc=='=' then
                    local prev=rest_loc:sub(ci-1,ci-1)
                    if prev~='=' and prev~='<' and prev~='>' and prev~='~' then
                        local nxt=rest_loc:sub(ci+1,ci+1)
                        if nxt~='=' then eq_idx=ci; break end
                    end
                end
            end
            local var_part = trim(eq_idx and rest_loc:sub(1,eq_idx-1) or rest_loc)
            local rhs_part = eq_idx and trim(rest_loc:sub(eq_idx+1)) or nil
            if var_part:find(",") then
                local vlist = split_args(var_part); local code = ""
                if rhs_part and is_call_expr(rhs_part) and not rhs_part:find(",") then
                    local first_tmp = newtmp()
                    code = code..("    Value %s=%s;\n"):format(first_tmp, translate_expr(rhs_part))
                    for vi,vname in ipairs(vlist) do
                        vname = trim(vname); if #vname==0 then goto cont end
                        local rval = vi==1 and first_tmp
                            or ("(__retncount>%d?__retbuf[%d]:make_nil())"):format(vi-1,vi-1)
                        if lv then lv[vname]=true; code=code..("    Value %s=%s;\n"):format(vname,rval)
                        else gt[vname]=true; am[vname]=true; code=code..("    free_value(%s);\n    %s=%s;\n"):format(vname,vname,rval) end
                        ::cont::
                    end
                else
                    for vi,vname in ipairs(vlist) do
                        vname=trim(vname); if #vname==0 then goto cont end
                        local val = (vi==1 and rhs_part) and translate_expr(rhs_part) or "make_nil()"
                        if lv then lv[vname]=true; code=code..("    Value %s=%s;\n"):format(vname,val)
                        else gt[vname]=true; am[vname]=true; code=code..("    free_value(%s);\n    %s=%s;\n"):format(vname,vname,val) end
                        ::cont::
                    end
                end
                return code,1
            end
        end end

    -- local var = rhs
    local lname, rhs = s:match("^local%s+([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
    if lname and rhs then
        if lv then lv[lname]=true; return ("    Value %s=%s;\n"):format(lname,translate_expr(rhs)),1 end
        gt[lname]=true; am[lname]=true
        return ("    free_value(%s);\n    %s=%s;\n"):format(lname,lname,translate_expr(rhs)),1
    end
    local lname2 = s:match("^local%s+([A-Za-z_][A-Za-z0-9_]*)$")
    if lname2 then
        if lv then lv[lname2]=true; return ("    Value %s=make_nil();\n"):format(lname2),1 end
        gt[lname2]=true; am[lname2]=true; return "",1
    end

    local pargs = s:match("^print%s*%((.*)%)$")
    if pargs then return gen_print(pargs),1 end

    local ta = try_table_assign(s); if ta then return ta,1 end

    -- multi-var assignment
    do local mavar = s:match("^([A-Za-z_][A-Za-z0-9_]*%s*,.-[A-Za-z_][A-Za-z0-9_]*)%s*=%s*")
        if mavar then
            local marhs = s:match("^[A-Za-z_][A-Za-z0-9_]*%s*,.-[A-Za-z_][A-Za-z0-9_]*%s*=%s*(.+)$")
            if marhs then
                local vlist = split_args(mavar); local code = ""
                if is_call_expr(marhs) and not marhs:find(",") then
                    local first_tmp = newtmp()
                    code = code..("    Value %s=%s;\n"):format(first_tmp, translate_expr(marhs))
                    for vi,vn in ipairs(vlist) do
                        vn = trim(vn); if vn=="" then goto cont end
                        local rval = vi==1 and first_tmp
                            or ("(__retncount>%d?__retbuf[%d]:make_nil())"):format(vi-1,vi-1)
                        code = code..("    free_value(%s);\n    %s=%s;\n"):format(vn,vn,rval)
                        am[vn] = true
                        ::cont::
                    end
                else
                    local tmp2 = newtmp()
                    code = ("    Value %s=%s;\n"):format(tmp2, translate_expr(marhs))
                    local first_v = trim(vlist[1] or "")
                    if first_v ~= "" then
                        code=code..("    free_value(%s);\n    %s=%s;\n"):format(first_v,first_v,tmp2); am[first_v]=true
                    else code=code..("    free_value(%s);\n"):format(tmp2) end
                    for vi2=2,#vlist do
                        local vn2=trim(vlist[vi2])
                        if vn2~="" then
                            code=code..("    free_value(%s);\n    %s=make_nil();\n"):format(vn2,vn2); am[vn2]=true
                        end
                    end
                end
                return code,1
            end
        end end

    -- simple assignment
    local var, rhs2 = s:match("^([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
    if var and rhs2 then
        am[var] = true
        if lv and not lv[var] and not gt[var] then
            lv[var]=true; return ("    Value %s=%s;\n"):format(var,translate_expr(rhs2)),1
        end
        local tmp = newtmp()
        return ("    Value %s=%s;\n    free_value(%s);\n    %s=%s;\n"):format(tmp,translate_expr(rhs2),var,var,tmp),1
    end

    if s:match("^if%s") then return gen_if(s, ctx, idx, src) end

    do local fc,consumed = gen_for(s, ctx, idx, src); if fc then return fc,consumed end end

    -- bare call expression
    if s:match("%(") or s:match("%[") or s:match("%.") then
        local tmp = newtmp()
        return ("    Value %s=%s;\n    free_value(%s);\n"):format(tmp,translate_expr(s),tmp),1
    end

    return "    /* unsupported: "..s:gsub("/%*","/ *"):gsub("%*/","* /").." */\n",1
end

-- ---------------------------------------------------------------------------
-- Usage analysis
-- ---------------------------------------------------------------------------
local all_source = table.concat(lines,"\n")
local function src_uses(pat) return all_source:find(pat) ~= nil end

local use = {}
local U = {
    print="print%s*%(", value_len="#[%w_%(\"]", value_concat="%.%.",
    value_add="[%w_%)\"]%s*%+", value_sub="[%w_%)\"]%s*%-[^%-]",
    value_mul="%*", value_div="[^/]/[^/]", value_mod="[%w_%)\"]%s*%%[^%%]",
    value_pow="%^",
    value_eq="==", value_neq="~=", value_lt="[^<]<[^=<]", value_gt="[^>]>[^=>]",
    value_le="<=", value_ge=">=",
    value_and="[%)%w_\"]%s+and%s", value_or="[%)%w_\"]%s+or%s",
    value_not="[%(,%s]not%s", table_init="{", table_ops="%.[%a_][%w_]*",
    method_call=":[A-Za-z_]", assert="assert%s*%(", error="error%s*%(",
    use_ipairs="ipairs%s*%(", use_pairs="pairs%s*%(", use_arg="%barg%s*%[",
    use_string="string%s*%.", use_str_method=":[a-z]",
    use_tostring="tostring%s*%(", use_tonumber="tonumber%s*%(", use_type="type%s*%(",
    use_select="select%s*%(", use_vararg="%.",
}
for k,p in pairs(U) do use[k]=src_uses(p) end
use.use_vararg = src_uses("%.%.%.")
use.value_add  = use.value_add  or src_uses("%+%s*[%w_%(\"']")
use.value_lt   = use.value_lt   or src_uses("^<[^=]")
use.value_gt   = use.value_gt   or src_uses("^>[^=]")
use.value_and  = use.value_and  or src_uses("%sand%s+[%(]")
use.value_or   = use.value_or   or src_uses("%sor%s+[%(]")
use.value_not  = use.value_not  or src_uses("^not%s")
use.table_ops  = use.table_ops  or src_uses("%[")
if use.use_ipairs or use.use_pairs then use.table_ops=true; use.table_init=true end
use.use_arg = use.use_arg or src_uses("arg%s*%.")
if use.use_arg then use.table_ops=true end

local str_fns = {"find","match","gmatch","gsub","sub","len","format","rep","reverse","upper","lower","byte","char"}
local used_str = {}
for _,fn in ipairs(str_fns) do
    used_str[fn] = src_uses("string%s*%.%s*"..fn) or src_uses(":"..fn.."%s*%(")
end
use.string_lib = false
for _,fn in ipairs(str_fns) do if used_str[fn] then use.string_lib=true end end
if src_uses(":gmatch%s*%(") then use.string_lib=true; used_str.gmatch=true end
use.use_select = use.use_select or src_uses("select%s*%(")

local math_fns = {"abs","floor","ceil","sqrt","sin","cos","tan","asin","acos","atan","atan2",
    "exp","log","log10","sinh","cosh","tanh","deg","rad","pow","fmod","modf","frexp","ldexp","max","min","random","randomseed"}
local used_math = {}
for _,fn in ipairs(math_fns) do used_math[fn]=src_uses("math%s*%.%s*"..fn) end
local use_math_pi   = src_uses("math%s*%.%s*pi")
local use_math_huge = src_uses("math%s*%.%s*huge")

local os_fns = {"clock","time","difftime","date","exit","getenv","execute","remove","rename","tmpname","setlocale"}
local used_os = {}
for _,fn in ipairs(os_fns) do used_os[fn]=src_uses("os%s*%.%s*"..fn) end

local io_fns = {"write","read","lines","open","close","flush","stdin","stdout","stderr"}
local used_io = {}
for _,fn in ipairs(io_fns) do used_io[fn]=src_uses("io%s*%.%s*"..fn) end

if use.value_neq or use.value_le or use.value_ge then use.value_eq=true end
if use.value_le  or use.value_ge then use.value_lt=true end
if use.value_gt  then use.value_lt=true end

use.math_lib = use_math_pi or use_math_huge
for _,fn in ipairs(math_fns) do if used_math[fn] then use.math_lib=true end end
use.os_lib = false; for _,fn in ipairs(os_fns)  do if used_os[fn]   then use.os_lib=true  end end
use.io_lib = false; for _,fn in ipairs(io_fns)  do if used_io[fn]   then use.io_lib=true  end end
use.prng   = used_math.random or used_math.randomseed

use.numval = use.value_add or use.value_sub or use.value_mul or use.value_div
    or use.value_mod or use.value_pow or use.value_lt or use.value_gt or use.value_le or use.value_ge or use.value_concat
if use.math_lib then use.numval=true end
if used_os.difftime or used_os.exit or used_os.date then use.numval=true end
use.math_h  = use.math_lib or use.value_mod or use.value_pow or use.string_lib
use.time_h  = use.prng     or use.os_lib
if used_io.open    then use.file_methods=true; use.method_call=true end
if use.method_call then use.table_ops=true end
if use.use_str_method or use.string_lib then use.table_ops=true end
use.value_call = true

-- numeric for always needs numval for the float branch
use.numval = true

local has_tables = true

-- ---------------------------------------------------------------------------
-- Emit C
-- ---------------------------------------------------------------------------
local out = {}
local function w(s)   table.insert(out, s) end
local function wif(c,s) if c then w(s) end end

w("#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <stdint.h>\n#include <stdarg.h>")
wif(use.math_h,  "#include <math.h>")
wif(use.time_h,  "#include <time.h>")
wif(use.string_lib, "#include <ctype.h>")
if used_os.getenv or used_os.execute or used_os.remove or used_os.rename or used_os.tmpname or used_os.setlocale then
    w("#include <errno.h>\n#include <locale.h>") end
w("")

w([[/* Value type */
typedef enum{T_INT,T_DOUBLE,T_STRING,T_BOOL,T_NIL,T_TABLE,T_FUNC,T_FILE}Type;
typedef struct LuaStr{int refcount;uint32_t hash;char data[];}LuaStr;
struct Table;
typedef struct Value{Type t;union{int64_t i;double d;LuaStr*ls;struct Table*tbl;struct Value(*fn)(int,struct Value*);FILE*file;};}Value;
static LuaStr*luastr_new(const char*s,size_t len){LuaStr*ls=malloc(sizeof(LuaStr)+len+1);ls->refcount=1;ls->hash=0;if(s)memcpy(ls->data,s,len);ls->data[len]='\0';return ls;}
static inline void luastr_incref(LuaStr*ls){if(ls)ls->refcount++;}
static inline void luastr_decref(LuaStr*ls){if(ls&&--ls->refcount<=0)free(ls);}
static inline const char*luastr_cstr(const LuaStr*ls){return ls?ls->data:"";}
static uint32_t luastr_hash(LuaStr*ls){if(!ls)return 0;if(ls->hash)return ls->hash;uint32_t h=2166136261u;for(const char*p=ls->data;*p;p++){h^=(uint8_t)*p;h*=16777619u;}if(!h)h=1;ls->hash=h;return h;}]])

-- FIX 7: document retbuf non-reentrancy
w([[
/* NOTE: global return buffer - not reentrant / not thread-safe.
 * Nested calls that return multiple values will overwrite this buffer.
 * A full fix requires per-call-frame stacks (as Lua's stack-based VM provides). */
#define RETBUF_CAP 32
static Value __retbuf_storage[RETBUF_CAP];
static Value* __retbuf = __retbuf_storage;
static int    __retbuf_cap = RETBUF_CAP;
static int    __retncount = 0;
]])

if has_tables then w([[
typedef struct TableEntry{Value key;Value val;int used;}TableEntry;
/* FIX 6: cap is always a power of two (starts at TBL_INIT_CAP=8, only ever doubled).
 * array_len tracks the contiguous integer-key boundary 1..n for the # operator. */
typedef struct Table{TableEntry*entries;int cap;int len;int array_len;int refcount;}Table;
#define TBL_INIT_CAP 8
static uint32_t hash_value(Value k){switch(k.t){case T_INT:return(uint32_t)(k.i*2654435761ULL);case T_DOUBLE:{if(k.d==0.0)return 0;uint64_t u;memcpy(&u,&k.d,8);return(uint32_t)(u^(u>>32))*2654435761u;}case T_STRING:return luastr_hash(k.ls);case T_BOOL:return(uint32_t)k.i^0xdeadbeef;default:return 0;}}
static int keys_equal(Value a,Value b){if(a.t!=b.t){if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE)){double da=a.t==T_DOUBLE?a.d:(double)a.i,db=b.t==T_DOUBLE?b.d:(double)b.i;return da==db;}return 0;}switch(a.t){case T_INT:return a.i==b.i;case T_DOUBLE:return a.d==b.d;case T_BOOL:return a.i==b.i;case T_NIL:return 1;case T_STRING:return a.ls==b.ls||strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))==0;case T_TABLE:return a.tbl==b.tbl;default:return 0;}}]]) end

w([[
static void free_value(Value v);
static Value value_copy(Value v);
static int value_is_truthy(Value v);]])

-- FIX 3: runtime error helper - must appear before any function that uses it
w([[
/* ── Runtime error helpers (FIX 3) ── */
static void lua_runtime_error(const char*fmt,...){
    va_list ap;va_start(ap,fmt);
    fprintf(stderr,"runtime error: ");
    vfprintf(stderr,fmt,ap);
    fprintf(stderr,"\n");
    va_end(ap);
    abort();
}
/* FIX 7: mark that control never returns from lua_runtime_error */
#if defined(__GNUC__)||defined(__clang__)
#define LUA_UNREACHABLE() __builtin_unreachable()
#else
#define LUA_UNREACHABLE() do{}while(0)
#endif]])

if has_tables then w([[
static Table*table_new(void){Table*t=calloc(1,sizeof(Table));t->cap=TBL_INIT_CAP;t->entries=calloc(t->cap,sizeof(TableEntry));t->refcount=1;t->array_len=0;return t;}
static void table_free(Table*t){if(!t||--t->refcount>0)return;for(int i=0;i<t->cap;i++)if(t->entries[i].used){free_value(t->entries[i].key);free_value(t->entries[i].val);}free(t->entries);free(t);}
static void table_raw_set(Table*t,Value key,Value val);
static void table_resize(Table*t){
    /* FIX 5+6: cap is always power-of-two; move entries without double-free risk */
    int oc=t->cap;TableEntry*old=t->entries;
    t->cap*=2;t->entries=calloc(t->cap,sizeof(TableEntry));t->len=0;t->array_len=0;
    for(int i=0;i<oc;i++){
        if(!old[i].used)continue;
        /* ownership of key/val transfers to new slot; do not free_value old copies */
        table_raw_set(t,old[i].key,old[i].val);
        old[i].used=0; /* mark moved so table_free won't double-free */
    }
    free(old);
}
/* FIX 2+3: nil value = delete key; array_len shrinks if boundary key removed */
static void table_raw_delete(Table*t,Value key){
    /* Open-addressing deletion via tombstone-free backward shift (Robin Hood) */
    uint32_t h=hash_value(key);int mask=t->cap-1,idx=(int)(h&mask),chk=0;
    while(t->entries[idx].used&&chk<t->cap){
        if(keys_equal(t->entries[idx].key,key)){
            /* shrink array_len if we're removing the current boundary key */
            if(key.t==T_INT&&key.i==(int64_t)t->array_len){
                /* scan backward: new boundary = largest k <= array_len-1 present */
                t->array_len--;
                /* keep shrinking while the new boundary key is also absent */
                while(t->array_len>0){
                    int64_t ck=(int64_t)t->array_len;
                    uint32_t ch=(uint32_t)(ck*2654435761ULL);
                    int ci=(int)(ch&mask),cc=0;int found=0;
                    while(t->entries[ci].used&&cc<t->cap){
                        if(t->entries[ci].key.t==T_INT&&t->entries[ci].key.i==ck){found=1;break;}
                        ci=(ci+1)&mask;cc++;}
                    if(found)break;
                    t->array_len--;
                }
            }
            free_value(t->entries[idx].key);free_value(t->entries[idx].val);
            t->entries[idx].used=0;t->len--;
            /* backward-shift subsequent entries to fix probe chains */
            int prev=idx;
            idx=(idx+1)&mask;
            while(t->entries[idx].used){
                uint32_t nat=(int)(hash_value(t->entries[idx].key)&mask);
                /* move entry if it is displaced from its natural slot */
                int displaced=0;
                if(nat<=prev){displaced=(nat<=prev&&prev<idx);}
                else{displaced=(nat<=prev||prev<idx);}/* wrap case */
                if(displaced){
                    t->entries[prev]=t->entries[idx];
                    t->entries[idx].used=0;
                    prev=idx;}
                idx=(idx+1)&mask;
            }
            return;
        }
        idx=(idx+1)&mask;chk++;
    }
    free_value(key); /* key not found - nothing to delete */
}
static void table_raw_set(Table*t,Value key,Value val){
    /* FIX 3: nil value means delete */
    if(val.t==T_NIL){free_value(val);table_raw_delete(t,key);return;}
    if(t->len*2>=t->cap)table_resize(t);
    /* FIX 6: mask works because cap is always a power of two */
    uint32_t h=hash_value(key);int mask=t->cap-1,idx=(int)(h&mask);
    while(t->entries[idx].used){
        if(keys_equal(t->entries[idx].key,key)){
            free_value(t->entries[idx].key);free_value(t->entries[idx].val);
            t->entries[idx].key=key;t->entries[idx].val=val;
            return;}
        idx=(idx+1)&mask;}
    t->entries[idx].used=1;t->entries[idx].key=key;t->entries[idx].val=val;t->len++;
    /* FIX 1: update contiguous-integer-key boundary for # operator */
    if(key.t==T_INT&&key.i==(int64_t)(t->array_len+1)){
        t->array_len++;
        /* extend boundary if subsequent keys already exist */
        while(1){int64_t nk=(int64_t)(t->array_len+1);uint32_t nh=(uint32_t)(nk*2654435761ULL);int ni=(int)(nh&mask),chk=0;
            while(t->entries[ni].used&&chk<t->cap){
                if(t->entries[ni].key.t==T_INT&&t->entries[ni].key.i==nk){t->array_len++;goto next_key;}
                ni=(ni+1)&mask;chk++;}
            break;next_key:;}
    }
}
static void table_set(Value tbl,Value key,Value val){if(tbl.t!=T_TABLE||!tbl.tbl){lua_runtime_error("attempt to index a %s value",(tbl.t==T_NIL?"nil":tbl.t==T_BOOL?"boolean":tbl.t==T_INT||tbl.t==T_DOUBLE?"number":tbl.t==T_FUNC?"function":"?"));free_value(tbl);free_value(key);free_value(val);return;}table_raw_set(tbl.tbl,key,val);free_value(tbl);}
static Value table_get(Value tbl,Value key){
    /* FIX 3: index error on non-table */
    if(tbl.t!=T_TABLE||!tbl.tbl){lua_runtime_error("attempt to index a %s value",(tbl.t==T_NIL?"nil":tbl.t==T_BOOL?"boolean":tbl.t==T_INT||tbl.t==T_DOUBLE?"number":tbl.t==T_FUNC?"function":"?"));free_value(tbl);free_value(key);return(Value){.t=T_NIL};}
    Table*t=tbl.tbl;uint32_t h=hash_value(key);int mask=t->cap-1,idx=(int)(h&mask),chk=0;while(t->entries[idx].used&&chk<t->cap){if(keys_equal(t->entries[idx].key,key)){Value r=value_copy(t->entries[idx].val);free_value(tbl);free_value(key);return r;}idx=(idx+1)&mask;chk++;}free_value(tbl);free_value(key);return(Value){.t=T_NIL};}
static Value table_call(Value tbl,Value key,int nargs,...);]]) end

w([[
static inline Value make_int(int64_t x){Value v;v.t=T_INT;v.i=x;return v;}
static inline Value make_double(double x){Value v;v.t=T_DOUBLE;v.d=x;return v;}
static inline Value make_bool(int b){Value v;v.t=T_BOOL;v.i=b?1:0;return v;}
static inline Value make_nil(void){Value v;v.t=T_NIL;v.i=0;return v;}
static Value make_string(const char*s){Value v;v.t=T_STRING;v.ls=s?luastr_new(s,strlen(s)):NULL;return v;}
static Value make_string_n(const char*s,size_t n){Value v;v.t=T_STRING;v.ls=luastr_new(s,n);return v;}]])
if has_tables then
    w("static Value make_table(void){Value v;v.t=T_TABLE;v.tbl=table_new();return v;}")
    w("static Value make_func(Value(*fn)(int,Value*)){Value v;v.t=T_FUNC;v.fn=fn;return v;}") end
wif(use.io_lib,"static Value make_file(FILE*f){Value v;v.t=T_FILE;v.file=f;return v;}")
wif(use.table_init,[[
static Value table_init(int n,...){Value tbl=make_table();va_list ap;va_start(ap,n);for(int i=0;i<n;i++){Value k=va_arg(ap,Value),v=va_arg(ap,Value);table_raw_set(tbl.tbl,k,v);}va_end(ap);return tbl;}]])
w([[
static void free_value(Value v){if(v.t==T_STRING)luastr_decref(v.ls);]])
wif(has_tables,"    else if(v.t==T_TABLE)table_free(v.tbl);")
w([[}
static Value value_copy(Value v){if(v.t==T_STRING){luastr_incref(v.ls);return v;}]])
wif(has_tables,"    if(v.t==T_TABLE&&v.tbl){v.tbl->refcount++;return v;}")
w("    return v;\n}")
w("static int value_is_truthy(Value v){if(v.t==T_NIL)return 0;if(v.t==T_BOOL)return v.i!=0;return 1;}")

wif(use.use_select or use.use_vararg,[[
static Value lua_select_vararg(Value idx,int fixed,int nargs,Value*args){
    if(idx.t==T_STRING&&idx.ls&&idx.ls->data[0]=='#'&&idx.ls->data[1]=='\0'){free_value(idx);return make_int(nargs-fixed);}
    int64_t n=(idx.t==T_INT)?idx.i:(int64_t)idx.d; free_value(idx);
    if(n<0)n=(nargs-fixed)+n+1;
    int pos=fixed+(int)n-1;
    return(pos>=0&&pos<nargs)?value_copy(args[pos]):make_nil();
}]])

-- FIX 2+3: value_call aborts with descriptive error on non-function
w([[
static Value value_call(Value fn,int nargs,...){
    Value stack_args[16];Value*args=nargs>0?(nargs<=16?stack_args:malloc(nargs*sizeof(Value))):NULL;
    va_list ap;va_start(ap,nargs);for(int i=0;i<nargs;i++)args[i]=va_arg(ap,Value);va_end(ap);
    Value r;
    if(fn.t==T_FUNC&&fn.fn)r=fn.fn(nargs,args);
    else{
        for(int i=0;i<nargs;i++)free_value(args[i]);
        /* FIX 2+3: runtime error instead of silent nil */
        lua_runtime_error("attempt to call a %s value",
            fn.t==T_NIL?"nil":fn.t==T_BOOL?"boolean":
            fn.t==T_INT||fn.t==T_DOUBLE?"number":fn.t==T_STRING?"string":
            fn.t==T_TABLE?"table":"?");
        LUA_UNREACHABLE();r=make_nil();}
    free_value(fn);if(nargs>16&&args)free(args);return r;
}
static Value value_call_splice(Value fn,int extra_count,Value*extra_args){
    Value r;
    if(fn.t==T_FUNC&&fn.fn)r=fn.fn(extra_count,extra_args);
    else{
        for(int i=0;i<extra_count;i++)free_value(extra_args[i]);
        lua_runtime_error("attempt to call a %s value",
            fn.t==T_NIL?"nil":fn.t==T_BOOL?"boolean":
            fn.t==T_INT||fn.t==T_DOUBLE?"number":fn.t==T_STRING?"string":
            fn.t==T_TABLE?"table":"?");
        LUA_UNREACHABLE();r=make_nil();}
    free_value(fn);return r;
}]])

wif(has_tables,[[
static Value table_call(Value tbl,Value key,int nargs,...){
    Value fn=table_get(value_copy(tbl),value_copy(key));free_value(tbl);free_value(key);
    Value stack_args[16];Value*args=nargs>0?(nargs<=16?stack_args:malloc(nargs*sizeof(Value))):NULL;
    va_list ap;va_start(ap,nargs);for(int i=0;i<nargs;i++)args[i]=va_arg(ap,Value);va_end(ap);
    Value r;
    if(fn.t==T_FUNC&&fn.fn)r=fn.fn(nargs,args);
    else{
        for(int i=0;i<nargs;i++)free_value(args[i]);
        lua_runtime_error("attempt to call a %s value",
            fn.t==T_NIL?"nil":fn.t==T_BOOL?"boolean":
            fn.t==T_INT||fn.t==T_DOUBLE?"number":fn.t==T_STRING?"string":
            fn.t==T_TABLE?"table":"?");
        LUA_UNREACHABLE();r=make_nil();}
    free_value(fn);if(nargs>16&&args)free(args);return r;
}
static Value table_call_splice(Value tbl,Value key,int extra_count,Value*extra_args){
    Value fn=table_get(value_copy(tbl),value_copy(key));free_value(tbl);free_value(key);
    Value r;
    if(fn.t==T_FUNC&&fn.fn)r=fn.fn(extra_count,extra_args);
    else{
        for(int i=0;i<extra_count;i++)free_value(extra_args[i]);
        lua_runtime_error("attempt to call a %s value",
            fn.t==T_NIL?"nil":fn.t==T_BOOL?"boolean":
            fn.t==T_INT||fn.t==T_DOUBLE?"number":fn.t==T_STRING?"string":
            fn.t==T_TABLE?"table":"?");
        LUA_UNREACHABLE();r=make_nil();}
    free_value(fn);return r;
}]])

wif(use.method_call,[[
static Value value_method_call(Value self,const char*method,int nargs,...){
    Value fn=table_get(value_copy(self),make_string(method));
    int total=nargs+1;
    Value stack_args[17];Value*args=total<=17?stack_args:malloc(total*sizeof(Value));
    args[0]=self;
    va_list ap;va_start(ap,nargs);for(int i=0;i<nargs;i++)args[i+1]=va_arg(ap,Value);va_end(ap);
    Value r;
    if(fn.t==T_FUNC&&fn.fn)r=fn.fn(total,args);
    else{for(int i=0;i<total;i++)free_value(args[i]);lua_runtime_error("attempt to call method '%s' (a %s value)",method,fn.t==T_NIL?"nil":fn.t==T_TABLE?"table":"?");r=make_nil();}
    free_value(fn);if(total>17)free(args);return r;
}]])

wif(use.use_tostring or use.print,[[
static Value lua_tostring(Value v){
    char buf[64];
    switch(v.t){
        case T_STRING:return v;
        case T_INT:snprintf(buf,sizeof buf,"%lld",(long long)v.i);free_value(v);return make_string(buf);
        case T_DOUBLE:snprintf(buf,sizeof buf,"%g",v.d);free_value(v);return make_string(buf);
        case T_BOOL:{const char*s=v.i?"true":"false";free_value(v);return make_string(s);}
        case T_NIL:free_value(v);return make_string("nil");
        case T_TABLE:snprintf(buf,sizeof buf,"table:%p",(void*)v.tbl);free_value(v);return make_string(buf);
        case T_FUNC:snprintf(buf,sizeof buf,"function:%p",(void*)(size_t)v.fn);free_value(v);return make_string(buf);
        default:free_value(v);return make_string("?");
    }
}]])

wif(use.use_tonumber,[[
static Value lua_tonumber(Value v){
    if(v.t==T_INT||v.t==T_DOUBLE)return v;
    if(v.t==T_STRING&&v.ls){char*end;const char*s=v.ls->data;
        long long iv=strtoll(s,&end,0);if(*end=='\0'){free_value(v);return make_int(iv);}
        double dv=strtod(s,&end);if(*end=='\0'){free_value(v);return make_double(dv);}
    }
    free_value(v);return make_nil();
}]])

wif(use.use_type,[[
static Value lua_type(Value v){
    const char*s;
    switch(v.t){case T_INT:case T_DOUBLE:s="number";break;case T_STRING:s="string";break;
    case T_BOOL:s="boolean";break;case T_NIL:s="nil";break;case T_TABLE:s="table";break;
    case T_FUNC:s="function";break;case T_FILE:s="file";break;default:s="userdata";}
    free_value(v);return make_string(s);
}]])

wif(use.error or use.assert,[[
static Value lua_error(Value msg){const char*m=(msg.t==T_STRING)?luastr_cstr(msg.ls):"(error object)";fprintf(stderr,"error: %s\n",m);free_value(msg);abort();return make_nil();}]])
wif(use.assert,[[
static Value lua_assert(Value cond,Value msg){if(!value_is_truthy(cond)){const char*m=(msg.t==T_STRING)?luastr_cstr(msg.ls):"assertion failed!";fprintf(stderr,"assertion failed: %s\n",m);free_value(cond);free_value(msg);abort();}free_value(msg);return cond;}]])
wif(use.print,[[
static void print_values(int n,Value*args){
    size_t cap=256;char*buf=malloc(cap);if(!buf)return;
    size_t len=0;
    for(int i=0;i<n;i++){
        if(i>0){if(len+1>=cap){cap*=2;void*__rb=realloc(buf,cap);if(!__rb){free(buf);return;}buf=(char*)__rb;}buf[len++]='\t';}
        Value v=args[i];char tmp[64];const char*s=NULL;size_t slen=0;
        switch(v.t){case T_INT:slen=(size_t)snprintf(tmp,sizeof tmp,"%lld",(long long)v.i);s=tmp;break;case T_DOUBLE:slen=(size_t)snprintf(tmp,sizeof tmp,"%g",v.d);s=tmp;break;case T_STRING:s=luastr_cstr(v.ls);slen=strlen(s);break;case T_BOOL:s=v.i?"true":"false";slen=v.i?4u:5u;break;case T_NIL:s="nil";slen=3;break;case T_TABLE:slen=(size_t)snprintf(tmp,sizeof tmp,"table:%p",(void*)v.tbl);s=tmp;break;case T_FUNC:slen=(size_t)snprintf(tmp,sizeof tmp,"function:%p",(void*)(size_t)v.fn);s=tmp;break;case T_FILE:slen=(size_t)snprintf(tmp,sizeof tmp,"file:%p",(void*)v.file);s=tmp;break;default:s="";slen=0;break;}
        if(len+slen+1>=cap){while(len+slen+1>=cap)cap*=2;void*__rb=realloc(buf,cap);if(!__rb){free(buf);return;}buf=(char*)__rb;}
        if(slen>0)memcpy(buf+len,s,slen);len+=slen;}
    if(len+1>=cap){cap=len+1;void*__rb=realloc(buf,cap);if(!__rb){free(buf);return;}buf=(char*)__rb;}
    buf[len++]='\n';fwrite(buf,1,len,stdout);free(buf);
    for(int i=0;i<n;i++)free_value(args[i]);}]])

w("\n/* Operator helpers */")
-- FIX 1: use array_len for # on tables; FIX 6: error on non-string/non-table
wif(use.value_len,[[static Value value_len(Value v){
    if(v.t==T_STRING){int64_t l=v.ls?(int64_t)strlen(v.ls->data):0;free_value(v);return make_int(l);}
    if(v.t==T_TABLE&&v.tbl){int64_t l=(int64_t)v.tbl->array_len;free_value(v);return make_int(l);}
    lua_runtime_error("attempt to get length of a %s value",
        v.t==T_NIL?"nil":v.t==T_BOOL?"boolean":v.t==T_INT||v.t==T_DOUBLE?"number":
        v.t==T_FUNC?"function":"?");
    free_value(v);return make_int(0);}]])
-- FIX 13: value_concat errors on non-string/number types
wif(use.value_concat,[[
static Value value_concat(Value a,Value b){
    char abuf[64],bbuf[64];const char*as=NULL;const char*bs=NULL;
    if(a.t==T_STRING)as=luastr_cstr(a.ls);
    else if(a.t==T_INT){snprintf(abuf,sizeof abuf,"%lld",(long long)a.i);as=abuf;}
    else if(a.t==T_DOUBLE){snprintf(abuf,sizeof abuf,"%g",a.d);as=abuf;}
    else{lua_runtime_error("attempt to concatenate a %s value",
            a.t==T_NIL?"nil":a.t==T_BOOL?"boolean":a.t==T_TABLE?"table":
            a.t==T_FUNC?"function":"?");free_value(a);free_value(b);return make_string("");}
    if(b.t==T_STRING)bs=luastr_cstr(b.ls);
    else if(b.t==T_INT){snprintf(bbuf,sizeof bbuf,"%lld",(long long)b.i);bs=bbuf;}
    else if(b.t==T_DOUBLE){snprintf(bbuf,sizeof bbuf,"%g",b.d);bs=bbuf;}
    else{lua_runtime_error("attempt to concatenate a %s value",
            b.t==T_NIL?"nil":b.t==T_BOOL?"boolean":b.t==T_TABLE?"table":
            b.t==T_FUNC?"function":"?");free_value(a);free_value(b);return make_string("");}
    size_t la=as?strlen(as):0,lb=bs?strlen(bs):0;
    LuaStr*ls=luastr_new(NULL,la+lb);
    if(la>0&&as)memcpy(ls->data,as,la);
    if(lb>0&&bs)memcpy(ls->data+la,bs,lb);
    free_value(a);free_value(b);Value r;r.t=T_STRING;r.ls=ls;return r;}]])
-- numval always emitted (needed by float for-loop)
w("static double numval(Value v){return v.t==T_DOUBLE?v.d:(double)v.i;}")
-- FIX 3: arithmetic type errors
wif(use.value_add,[[static Value value_add(Value a,Value b){
    if((a.t!=T_INT&&a.t!=T_DOUBLE)||(b.t!=T_INT&&b.t!=T_DOUBLE)){
        lua_runtime_error("attempt to perform arithmetic on a %s value",
            (a.t!=T_INT&&a.t!=T_DOUBLE)?(a.t==T_NIL?"nil":a.t==T_STRING?"string":a.t==T_BOOL?"boolean":"?")
                                        :(b.t==T_NIL?"nil":b.t==T_STRING?"string":b.t==T_BOOL?"boolean":"?"));
        free_value(a);free_value(b);return make_nil();}
    Value r=(a.t==T_INT&&b.t==T_INT)?make_int(a.i+b.i):make_double(numval(a)+numval(b));free_value(a);free_value(b);return r;}]])
wif(use.value_sub,[[static Value value_sub(Value a,Value b){
    if((a.t!=T_INT&&a.t!=T_DOUBLE)||(b.t!=T_INT&&b.t!=T_DOUBLE)){
        lua_runtime_error("attempt to perform arithmetic on a %s value",
            (a.t!=T_INT&&a.t!=T_DOUBLE)?(a.t==T_NIL?"nil":a.t==T_STRING?"string":a.t==T_BOOL?"boolean":"?")
                                        :(b.t==T_NIL?"nil":b.t==T_STRING?"string":b.t==T_BOOL?"boolean":"?"));
        free_value(a);free_value(b);return make_nil();}
    Value r=(a.t==T_INT&&b.t==T_INT)?make_int(a.i-b.i):make_double(numval(a)-numval(b));free_value(a);free_value(b);return r;}]])
wif(use.value_mul,[[static Value value_mul(Value a,Value b){
    if((a.t!=T_INT&&a.t!=T_DOUBLE)||(b.t!=T_INT&&b.t!=T_DOUBLE)){
        lua_runtime_error("attempt to perform arithmetic on a %s value",
            (a.t!=T_INT&&a.t!=T_DOUBLE)?(a.t==T_NIL?"nil":a.t==T_STRING?"string":a.t==T_BOOL?"boolean":"?")
                                        :(b.t==T_NIL?"nil":b.t==T_STRING?"string":b.t==T_BOOL?"boolean":"?"));
        free_value(a);free_value(b);return make_nil();}
    Value r=(a.t==T_INT&&b.t==T_INT)?make_int(a.i*b.i):make_double(numval(a)*numval(b));free_value(a);free_value(b);return r;}]])
wif(use.value_div,[[static Value value_div(Value a,Value b){
    /* FIX 4: integer /0 is a runtime error; float /0 yields inf (IEEE, Lua compatible) */
    if(a.t==T_INT&&b.t==T_INT){
        if(b.i==0){free_value(a);free_value(b);lua_runtime_error("attempt to divide by zero");}
        /* / in Lua 5.1/5.2 produces a float even for integers */
        double r=(double)a.i/(double)b.i;free_value(a);free_value(b);return make_double(r);}
    double r=numval(a)/numval(b);free_value(a);free_value(b);return make_double(r);}]])
wif(use.value_mod,[[static Value value_mod(Value a,Value b){
    /* FIX 5: guard integer b==0 */
    if(a.t==T_INT&&b.t==T_INT){
        if(b.i==0){free_value(a);free_value(b);lua_runtime_error("attempt to perform 'n%%0'");}
        int64_t r=((a.i%b.i)+b.i)%b.i;free_value(a);free_value(b);return make_int(r);}
    double da=numval(a),db=numval(b);free_value(a);free_value(b);
    /* FIX 4: float %0 → NaN (Lua allows this; avoids platform SIGFPE) */
    if(db==0.0)return make_double(0.0/0.0);
    return make_double(da-floor(da/db)*db);}]])
wif(use.value_pow,"static Value value_pow(Value a,Value b){double r=pow(numval(a),numval(b));free_value(a);free_value(b);return make_double(r);}")
wif(use.value_eq,"static Value value_eq(Value a,Value b){int eq;if(a.t==T_NIL&&b.t==T_NIL)eq=1;else if(a.t==T_NIL||b.t==T_NIL)eq=0;else if(a.t==b.t){if(a.t==T_INT)eq=(a.i==b.i);else if(a.t==T_DOUBLE)eq=(a.d==b.d);else if(a.t==T_STRING)eq=(a.ls==b.ls||strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))==0);else if(a.t==T_BOOL)eq=(a.i==b.i);else if(a.t==T_TABLE)eq=(a.tbl==b.tbl);else eq=0;}else if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE))eq=(numval(a)==numval(b));else eq=0;free_value(a);free_value(b);return make_bool(eq);}")
wif(use.value_neq,"static Value value_neq(Value a,Value b){Value r=value_eq(a,b);int v=!value_is_truthy(r);free_value(r);return make_bool(v);}")
-- FIX 5: comparison operators error on incompatible type pairs (Lua semantics).
-- Emit a helper macro once so the type-name logic isn't repeated four times.
w([[
#define LUA_TYPENAME(v) ((v).t==T_NIL?"nil":(v).t==T_BOOL?"boolean":\
    (v).t==T_INT||(v).t==T_DOUBLE?"number":(v).t==T_STRING?"string":\
    (v).t==T_TABLE?"table":(v).t==T_FUNC?"function":"?")
]])
wif(use.value_lt,[[static Value value_lt(Value a,Value b){
    if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE)){int r=(numval(a)<numval(b));free_value(a);free_value(b);return make_bool(r);}
    if(a.t==T_STRING&&b.t==T_STRING){int r=(strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))<0);free_value(a);free_value(b);return make_bool(r);}
    lua_runtime_error("attempt to compare %s with %s",LUA_TYPENAME(a),LUA_TYPENAME(b));
    free_value(a);free_value(b);return make_bool(0);}]])
wif(use.value_gt,"static Value value_gt(Value a,Value b){return value_lt(b,a);}")
wif(use.value_le,[[static Value value_le(Value a,Value b){
    if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE)){int r=(numval(a)<=numval(b));free_value(a);free_value(b);return make_bool(r);}
    if(a.t==T_STRING&&b.t==T_STRING){int r=(strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))<=0);free_value(a);free_value(b);return make_bool(r);}
    lua_runtime_error("attempt to compare %s with %s",LUA_TYPENAME(a),LUA_TYPENAME(b));
    free_value(a);free_value(b);return make_bool(0);}]])
wif(use.value_ge,[[static Value value_ge(Value a,Value b){
    if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE)){int r=(numval(a)>=numval(b));free_value(a);free_value(b);return make_bool(r);}
    if(a.t==T_STRING&&b.t==T_STRING){int r=(strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))>=0);free_value(a);free_value(b);return make_bool(r);}
    lua_runtime_error("attempt to compare %s with %s",LUA_TYPENAME(a),LUA_TYPENAME(b));
    free_value(a);free_value(b);return make_bool(0);}]])
wif(use.value_and,"static Value value_and(Value a,Value b){if(!value_is_truthy(a)){free_value(b);return a;}free_value(a);return b;}")
wif(use.value_or,"static Value value_or(Value a,Value b){if(value_is_truthy(a)){free_value(b);return a;}free_value(a);return b;}")
wif(use.value_not,"static Value value_not(Value a){int r=!value_is_truthy(a);free_value(a);return make_bool(r);}")

-- ---------------------------------------------------------------------------
-- String library
-- ---------------------------------------------------------------------------
if use.string_lib then
w([==[
/* =====================================================================
   Lua pattern matching engine
   ===================================================================== */
typedef struct{
    const char*src_init,*src_end,*p_end;
    struct{const char*init;ptrdiff_t len;}capture[32];
    int level;
}MatchState;
#define CAP_UNFINISHED (-1)
#define CAP_POSITION   (-2)
#define L_ESC '%'

static int matchclass(int c,int cl){int res,lc=tolower(cl);switch(lc){case 'a':res=isalpha(c);break;case 'c':res=iscntrl(c);break;case 'd':res=isdigit(c);break;case 'g':res=isgraph(c);break;case 'l':res=islower(c);break;case 'p':res=ispunct(c);break;case 's':res=isspace(c);break;case 'u':res=isupper(c);break;case 'w':res=isalnum(c);break;case 'x':res=isxdigit(c);break;default:return cl==c;}return(islower(cl)?res:!res);}
static int singlematch(MatchState*ms,const char*s,const char*p){if(s>=ms->src_end)return 0;unsigned char c=(unsigned char)*s;switch(*p){case '.':return 1;case L_ESC:return matchclass(c,(unsigned char)*(p+1));case '[':return 0;default:return((unsigned char)*p==c);}}
static const char*match(MatchState*ms,const char*s,const char*p);
static const char*matchbalance(MatchState*ms,const char*s,const char*p){if(p>=ms->p_end-1)return NULL;if(*s!=*p)return NULL;int b=*p,e=*(p+1),cont=1;while(++s<ms->src_end){if(*s==e){if(--cont==0)return s+1;}else if(*s==b)cont++;}return NULL;}
static const char*max_expand(MatchState*ms,const char*s,const char*p,const char*ep){int i=0;while(singlematch(ms,s+i,p))i++;while(i>=0){const char*res=match(ms,s+i,ep);if(res)return res;i--;}return NULL;}
static const char*min_expand(MatchState*ms,const char*s,const char*p,const char*ep){for(;;){const char*res=match(ms,s,ep);if(res)return res;if(singlematch(ms,s,p))s++;else return NULL;}}
static int matchbracketclass(int c,const char*p,const char*ec){int sig=1;if(*(p+1)=='^'){sig=0;p++;}while(++p<ec){if(*p==L_ESC){p++;if(matchclass(c,(unsigned char)*p))return sig;}else if((*(p+1)=='-')&&(p+2<ec)){p+=2;if((unsigned char)*(p-2)<=(unsigned char)c&&c<=(unsigned char)*p)return sig;}else if((unsigned char)*p==c)return sig;}return !sig;}
static const char*classend(const char*p){switch(*p++){case'\0':return p-1;case L_ESC:return(*p=='\0'?p:p+1);case'[':{if(*p=='^')p++;do{if(*p=='\0')return p;if(*p++==L_ESC&&*p!='\0')p++;}while(*p!=']');return p+1;}default:return p;}}
static const char*match(MatchState*ms,const char*s,const char*p){
    if(p>=ms->p_end)return s;
    switch(*p){
        case'(':{const char*res;int l=ms->level;if(*(p+1)==')'){ms->capture[l].init=s;ms->capture[l].len=CAP_POSITION;ms->level=l+1;res=match(ms,s,p+2);if(!res)ms->level=l;}else{ms->capture[l].init=s;ms->capture[l].len=CAP_UNFINISHED;ms->level=l+1;res=match(ms,s,p+1);if(!res)ms->level=l;}return res;}
        case')':{int l=ms->level-1;while(l>=0&&ms->capture[l].len!=CAP_UNFINISHED)l--;if(l<0)return NULL;ms->capture[l].len=(ptrdiff_t)(s-ms->capture[l].init);const char*res=match(ms,s,p+1);if(!res)ms->capture[l].len=CAP_UNFINISHED;return res;}
        case'$':if(*(p+1)=='\0')return(s==ms->src_end?s:NULL);
        default:{const char*ep=classend(p);int m;if(*p=='[')m=matchbracketclass((unsigned char)*s,p,ep-1)&&s<ms->src_end;else m=singlematch(ms,s,p);switch(*ep){case'?':{const char*res;if(m&&(res=match(ms,s+1,ep+1)))return res;return match(ms,s,ep+1);}case'+':{return m?max_expand(ms,s+1,p,ep+1):NULL;}case'*':{return max_expand(ms,s,p,ep+1);}case'-':{return min_expand(ms,s,p,ep+1);}default:{if(!m)return NULL;s++;p=ep;return match(ms,s,p);}}}
        case'%':{switch(*(p+1)){case'b':{s=matchbalance(ms,s,p+2);if(!s)return NULL;p+=4;return match(ms,s,p);}default:{const char*ep=classend(p);int m;if(*p=='[')m=matchbracketclass((unsigned char)*s,p,ep-1)&&s<ms->src_end;else m=singlematch(ms,s,p);switch(*ep){case'?':{const char*res;if(m&&(res=match(ms,s+1,ep+1)))return res;return match(ms,s,ep+1);}case'+':{return m?max_expand(ms,s+1,p,ep+1):NULL;}case'*':{return max_expand(ms,s,p,ep+1);}case'-':{return min_expand(ms,s,p,ep+1);}default:{if(!m)return NULL;return match(ms,s+1,ep);}}}}}
    }
}
static int push_captures(MatchState*ms,const char*s,const char*e,int off){
    int nlevels=(ms->level==0&&s)?1:ms->level,count=0;
    for(int i=0;i<nlevels;i++){if(i+off>=__retbuf_cap)break;
        if(ms->level==0)__retbuf[off+i]=make_string_n(s,(size_t)(e-s));
        else if(ms->capture[i].len==CAP_POSITION)__retbuf[off+i]=make_int(ms->capture[i].init-ms->src_init+1);
        else __retbuf[off+i]=make_string_n(ms->capture[i].init,(size_t)ms->capture[i].len);
        count++;}
    return count;
}

/* FIX 8: safe realloc helpers used by string functions */
#define STR_FREE_RET(n,a,ret) do{for(int _i=0;_i<(n);_i++)free_value((a)[_i]);return(ret);}while(0)
/* BA/BAS macros save pointer before realloc to avoid leak on failure */
#define BA(c) do{if(buflen+1>=bufsz){bufsz*=2;void*__r=realloc(buf,bufsz);if(!__r){free(buf);buf=NULL;}else buf=(char*)__r;}if(buf)buf[buflen++]=(c);}while(0)
#define BAS(str,l2) do{size_t _l=(l2);while(buflen+_l+1>=bufsz){bufsz*=2;void*__r=realloc(buf,bufsz);if(!__r){free(buf);buf=NULL;break;}buf=(char*)__r;}if(buf){memcpy(buf+buflen,(str),_l);buflen+=_l;}}while(0)

static Value lua_string_len(int n,Value*a){if(n<1||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_int(0));int64_t l=a[0].ls?(int64_t)strlen(a[0].ls->data):0;STR_FREE_RET(n,a,make_int(l));}
static Value lua_string_sub(int n,Value*a){
    if(n<1||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_string(""));
    const char*s=luastr_cstr(a[0].ls);int64_t sl=(int64_t)strlen(s);
    int64_t i=n>1?(int64_t)numval(a[1]):1,j=n>2?(int64_t)numval(a[2]):sl;
    if(i<0)i=sl+i+1;if(j<0)j=sl+j+1;if(i<1)i=1;if(j>sl)j=sl;
    Value r=(i>j)?make_string(""):make_string_n(s+(i-1),(size_t)(j-i+1));
    STR_FREE_RET(n,a,r);
}
static Value lua_string_rep(int n,Value*a){
    if(n<2||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_string(""));
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);int64_t cnt=(int64_t)numval(a[1]);
    const char*sep=(n>2&&a[2].t==T_STRING)?luastr_cstr(a[2].ls):"";size_t sepl=strlen(sep);
    if(cnt<=0)STR_FREE_RET(n,a,make_string(""));
    size_t total=sl*cnt+sepl*(cnt>1?cnt-1:0);
    char*buf=(char*)malloc(total+1);
    if(!buf)STR_FREE_RET(n,a,make_string(""));  /* FIX 8 */
    size_t pos=0;
    for(int64_t k=0;k<cnt;k++){if(k>0&&sepl){memcpy(buf+pos,sep,sepl);pos+=sepl;}memcpy(buf+pos,s,sl);pos+=sl;}
    buf[total]='\0';Value r=make_string(buf);free(buf);STR_FREE_RET(n,a,r);
}
static Value lua_string_reverse(int n,Value*a){
    if(n<1||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_string(""));
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);char*buf=malloc(sl+1);
    if(!buf)STR_FREE_RET(n,a,make_string(""));
    for(size_t k=0;k<sl;k++)buf[k]=s[sl-1-k];buf[sl]='\0';
    Value r=make_string(buf);free(buf);STR_FREE_RET(n,a,r);
}
static Value lua_string_upper(int n,Value*a){
    if(n<1||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_string(""));
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);char*buf=malloc(sl+1);
    if(!buf)STR_FREE_RET(n,a,make_string(""));
    for(size_t k=0;k<sl;k++)buf[k]=(char)toupper((unsigned char)s[k]);buf[sl]='\0';
    Value r=make_string(buf);free(buf);STR_FREE_RET(n,a,r);
}
static Value lua_string_lower(int n,Value*a){
    if(n<1||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_string(""));
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);char*buf=malloc(sl+1);
    if(!buf)STR_FREE_RET(n,a,make_string(""));
    for(size_t k=0;k<sl;k++)buf[k]=(char)tolower((unsigned char)s[k]);buf[sl]='\0';
    Value r=make_string(buf);free(buf);STR_FREE_RET(n,a,r);
}
static Value lua_string_byte(int n,Value*a){
    if(n<1||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_nil());
    const char*s=luastr_cstr(a[0].ls);int64_t sl=(int64_t)strlen(s);
    int64_t i=n>1?(int64_t)numval(a[1]):1,j=n>2?(int64_t)numval(a[2]):i;
    if(i<0)i=sl+i+1;if(j<0)j=sl+j+1;if(i<1)i=1;if(j>sl)j=sl;
    for(int k=0;k<n;k++)free_value(a[k]);
    if(i>j)return make_nil();
    int64_t cnt=j-i+1;
    for(int ri=1;ri<__retncount&&ri<__retbuf_cap;ri++)free_value(__retbuf[ri]);
    __retncount=(int)cnt;
    for(int64_t k=0;k<cnt;k++)if(k<__retbuf_cap)__retbuf[k]=make_int((unsigned char)s[i-1+k]);
    return make_int((unsigned char)s[i-1]);
}
static Value lua_string_char(int n,Value*a){
    char*buf=malloc(n+1);
    if(!buf){for(int i=0;i<n;i++)free_value(a[i]);return make_string("");}
    for(int i=0;i<n;i++){buf[i]=(char)(int64_t)numval(a[i]);free_value(a[i]);}
    buf[n]='\0';Value r=make_string(buf);free(buf);return r;
}
static Value lua_string_find(int n,Value*a){
    if(n<2||a[0].t!=T_STRING||a[1].t!=T_STRING)STR_FREE_RET(n,a,make_nil());
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);
    const char*p=luastr_cstr(a[1].ls);
    int64_t init=n>2?(int64_t)numval(a[2]):1;int plain=n>3&&value_is_truthy(a[3]);
    if(init<0)init=(int64_t)sl+init+1;if(init<1)init=1;if(init>(int64_t)sl+1)init=(int64_t)sl+1;
    const char*s1=s+init-1;
    for(int i=0;i<n;i++)free_value(a[i]);
    if(plain){const char*found=strstr(s1,p);if(!found)return make_nil();
        int64_t st=(int64_t)(found-s)+1,en=st+(int64_t)strlen(p)-1;
        for(int ri=1;ri<__retncount&&ri<__retbuf_cap;ri++)free_value(__retbuf[ri]);
        __retncount=2;__retbuf[0]=make_int(st);__retbuf[1]=make_int(en);return make_int(st);}
    MatchState ms;ms.src_init=s;ms.src_end=s+sl;ms.p_end=p+strlen(p);
    int anchor=0;if(*p=='^'){anchor=1;p++;}
    const char*s2=s1;
    do{ms.level=0;const char*res=match(&ms,s2,p);
        if(res){int64_t st=(int64_t)(s2-s)+1,en=(int64_t)(res-s);
            for(int ri=1;ri<__retncount&&ri<__retbuf_cap;ri++)free_value(__retbuf[ri]);
            __retncount=2;__retbuf[0]=make_int(st);__retbuf[1]=make_int(en);return make_int(st);}
    }while(s2++<ms.src_end&&!anchor);
    return make_nil();
}
static Value lua_string_match(int n,Value*a){
    if(n<2||a[0].t!=T_STRING||a[1].t!=T_STRING)STR_FREE_RET(n,a,make_nil());
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);const char*p=luastr_cstr(a[1].ls);
    int64_t init=n>2?(int64_t)numval(a[2]):1;
    if(init<0)init=(int64_t)sl+init+1;if(init<1)init=1;if(init>(int64_t)sl+1)init=(int64_t)sl+1;
    const char*s1=s+init-1;
    for(int i=0;i<n;i++)free_value(a[i]);
    MatchState ms;ms.src_init=s;ms.src_end=s+sl;int anchor=0;
    if(*p=='^'){anchor=1;p++;}ms.p_end=p+strlen(p);
    const char*s2=s1;
    do{ms.level=0;const char*res=match(&ms,s2,p);
        if(res){for(int ri=0;ri<__retncount&&ri<__retbuf_cap;ri++)free_value(__retbuf[ri]);
            int nc=push_captures(&ms,s2,res,0);__retncount=nc;
            return nc>0?value_copy(__retbuf[0]):make_nil();}
    }while(s2++<ms.src_end&&!anchor);
    return make_nil();
}
static Value lua_string_gmatch(int n,Value*a){
    if(n<2||a[0].t!=T_STRING||a[1].t!=T_STRING)STR_FREE_RET(n,a,make_nil());
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);const char*p=luastr_cstr(a[1].ls);
    for(int i=0;i<n;i++)free_value(a[i]);
    Value tbl=make_table();int idx=1;
    MatchState ms;ms.src_init=s;ms.src_end=s+sl;ms.p_end=p+strlen(p);
    const char*src=s;
    while(src<=ms.src_end){
        ms.level=0;const char*e=match(&ms,src,p);
        if(e){
            if(ms.level>1){Value sub=make_table();for(int ci=0;ci<ms.level;ci++){Value cap;if(ms.capture[ci].len==CAP_POSITION)cap=make_int(ms.capture[ci].init-ms.src_init+1);else cap=make_string_n(ms.capture[ci].init,(size_t)ms.capture[ci].len);table_raw_set(sub.tbl,make_int(ci+1),cap);}table_raw_set(tbl.tbl,make_int(idx++),sub);}
            else if(ms.level==1){Value cap;if(ms.capture[0].len==CAP_POSITION)cap=make_int(ms.capture[0].init-ms.src_init+1);else cap=make_string_n(ms.capture[0].init,(size_t)ms.capture[0].len);table_raw_set(tbl.tbl,make_int(idx++),cap);}
            else{table_raw_set(tbl.tbl,make_int(idx++),make_string_n(src,(size_t)(e-src)));}
            if(e==src)src++;else src=e;
        }else src++;
    }
    return tbl;
}
static Value lua_string_gsub(int n,Value*a){
    if(n<3||a[0].t!=T_STRING||a[1].t!=T_STRING)STR_FREE_RET(n,a,make_string(""));
    const char*s=luastr_cstr(a[0].ls);size_t sl=strlen(s);const char*p=luastr_cstr(a[1].ls);
    int maxn=n>3?(int)numval(a[3]):-1;
    size_t bufsz=sl*2+64;char*buf=malloc(bufsz);size_t buflen=0;int count=0;
    if(!buf)STR_FREE_RET(n,a,make_string(""));
    MatchState ms;ms.src_init=s;ms.src_end=s+sl;ms.p_end=p+strlen(p);
    int anchor=(*p=='^');if(anchor)p++;ms.p_end=p+strlen(p);
    const char*src=s;
    while((maxn<0||count<maxn)&&src<=ms.src_end){
        ms.level=0;const char*e=match(&ms,src,p);
        if(e){count++;
            if(a[2].t==T_STRING){const char*repl=luastr_cstr(a[2].ls);while(*repl){if(*repl!='%'){BA(*repl++);}else{repl++;if(*repl>='0'&&*repl<='9'){int ci=*repl-'0';repl++;if(ci==0){BAS(src,(size_t)(e-src));}else if(ci<=ms.level&&ms.capture[ci-1].len>=0)BAS(ms.capture[ci-1].init,(size_t)ms.capture[ci-1].len);}else{BA(*repl++);}}}}
            else if(a[2].t==T_TABLE){Value key=ms.level>0&&ms.capture[0].len>=0?make_string_n(ms.capture[0].init,(size_t)ms.capture[0].len):make_string_n(src,(size_t)(e-src));Value val=table_get(value_copy(a[2]),key);if(value_is_truthy(val)){Value sv=lua_tostring(value_copy(val));BAS(luastr_cstr(sv.ls),strlen(luastr_cstr(sv.ls)));free_value(sv);}else{BAS(src,(size_t)(e-src));}free_value(val);}
            else if(a[2].t==T_FUNC){Value fargs[32];int nf=0;if(ms.level>0){for(int ci=0;ci<ms.level&&nf<32;ci++){if(ms.capture[ci].len==CAP_POSITION)fargs[nf++]=make_int(ms.capture[ci].init-ms.src_init+1);else fargs[nf++]=make_string_n(ms.capture[ci].init,(size_t)ms.capture[ci].len);}}else{fargs[nf++]=make_string_n(src,(size_t)(e-src));}Value rv=a[2].fn(nf,fargs);if(value_is_truthy(rv)){Value sv=lua_tostring(value_copy(rv));BAS(luastr_cstr(sv.ls),strlen(luastr_cstr(sv.ls)));free_value(sv);}else{BAS(src,(size_t)(e-src));}free_value(rv);}
            if(e==src)BA(*src++);else src=e;
        }else{BA(*src++);}
        if(anchor)break;
    }
    if(buf){while(src<ms.src_end)BA(*src++);buf[buflen]='\0';}
    int64_t cnt_val=count;
    for(int i=0;i<n;i++)free_value(a[i]);
    for(int ri=1;ri<__retncount&&ri<__retbuf_cap;ri++)free_value(__retbuf[ri]);
    __retncount=2;
    Value res_str=buf?make_string(buf):make_string("");
    free(buf);
    __retbuf[0]=res_str;__retbuf[1]=make_int(cnt_val);
    return value_copy(__retbuf[0]);
}
static Value lua_string_format(int n,Value*a){
    if(n<1||a[0].t!=T_STRING)STR_FREE_RET(n,a,make_string(""));
    const char*fmt=luastr_cstr(a[0].ls);size_t bufsz=256;char*buf=malloc(bufsz);
    if(!buf)STR_FREE_RET(n,a,make_string(""));
    size_t buflen=0;int argi=1;
    while(*fmt){
        if(*fmt!='%'){BA(*fmt++);continue;}fmt++;if(*fmt=='%'){BA('%');fmt++;continue;}
        char spec[64];int si=0;spec[si++]='%';
        while(*fmt&&strchr("-+ #0",*fmt))spec[si++]=*fmt++;
        while(*fmt&&isdigit(*fmt))spec[si++]=*fmt++;
        if(*fmt=='.'){spec[si++]=*fmt++;while(*fmt&&isdigit(*fmt))spec[si++]=*fmt++;}
        char conv=*fmt++;
        switch(conv){case'd':case'i':case'u':case'o':case'x':case'X':spec[si++]='l';spec[si++]='l';spec[si++]=conv;spec[si]='\0';break;default:spec[si++]=conv;spec[si]='\0';}
        char tmp[256];Value av=argi<n?value_copy(a[argi]):make_nil();argi++;
        switch(conv){
            case'd':case'i':snprintf(tmp,sizeof tmp,spec,(long long)(av.t==T_INT?av.i:(int64_t)av.d));BAS(tmp,strlen(tmp));break;
            case'u':snprintf(tmp,sizeof tmp,spec,(unsigned long long)(av.t==T_INT?(uint64_t)av.i:(uint64_t)(int64_t)av.d));BAS(tmp,strlen(tmp));break;
            case'o':case'x':case'X':snprintf(tmp,sizeof tmp,spec,(unsigned long long)(av.t==T_INT?(uint64_t)av.i:(uint64_t)(int64_t)av.d));BAS(tmp,strlen(tmp));break;
            case'f':case'e':case'E':case'g':case'G':snprintf(tmp,sizeof tmp,spec,numval(av));BAS(tmp,strlen(tmp));break;
            case'c':BA((char)(av.t==T_INT?av.i:(int64_t)av.d));break;
            case's':{const char*sv;char sb[64];if(av.t==T_STRING)sv=luastr_cstr(av.ls);else if(av.t==T_INT){snprintf(sb,sizeof sb,"%lld",(long long)av.i);sv=sb;}else if(av.t==T_DOUBLE){snprintf(sb,sizeof sb,"%g",av.d);sv=sb;}else sv="nil";snprintf(tmp,sizeof tmp,spec,sv);BAS(tmp,strlen(tmp));break;}
            case'q':{BA('"');const char*sv;if(av.t==T_STRING)sv=luastr_cstr(av.ls);else{char qb[64];if(av.t==T_INT)snprintf(qb,sizeof qb,"%lld",(long long)av.i);else if(av.t==T_DOUBLE)snprintf(qb,sizeof qb,"%g",av.d);else snprintf(qb,sizeof qb,"nil");sv=qb;}while(*sv){if(*sv=='"'||*sv=='\\'||*sv=='\n'){BA('\\');}BA(*sv++);}BA('"');break;}
            default:BA(conv);break;
        }
        free_value(av);
    }
    if(buf)buf[buflen]='\0';
    for(int i=0;i<n;i++)free_value(a[i]);
    Value r=buf?make_string(buf):make_string("");free(buf);return r;
}
#undef STR_FREE_RET
#undef BA
#undef BAS
static Value make_string_table(void){
    Value t=make_table();
    #define SS(name) table_raw_set(t.tbl,make_string(#name),make_func(lua_string_##name))
    SS(len);SS(sub);SS(rep);SS(reverse);SS(upper);SS(lower);SS(byte);SS(char);
    SS(find);SS(match);SS(gmatch);SS(gsub);SS(format);
    #undef SS
    return t;
}
]==])
end

-- Math library
if use.math_lib then
    w("\n/* math */")
    wif(use.prng,"static uint64_t prng_state=0;")
    w("#define M1(name,expr) static Value lua_math_##name(int n,Value*a){double x=numval(a[0]);free_value(a[0]);return make_double(expr);}")
    w("#define M2(name,expr) static Value lua_math_##name(int n,Value*a){double x=numval(a[0]),y=numval(a[1]);free_value(a[0]);free_value(a[1]);return make_double(expr);}")
    local m1={abs="fabs(x)",floor="floor(x)",ceil="ceil(x)",sqrt="sqrt(x)",sin="sin(x)",cos="cos(x)",tan="tan(x)",
        asin="asin(x)",acos="acos(x)",atan="atan(x)",exp="exp(x)",log="log(x)",log10="log10(x)",
        sinh="sinh(x)",cosh="cosh(x)",tanh="tanh(x)",deg="x*(180.0/3.14159265358979323846)",rad="x*(3.14159265358979323846/180.0)"}
    local m2={atan2="atan2(x,y)",pow="pow(x,y)",fmod="fmod(x,y)"}
    for _,fn in ipairs(math_fns) do if used_math[fn] then
        if     m1[fn] then w(("M1(%s,%s)"):format(fn,m1[fn]))
        elseif m2[fn] then w(("M2(%s,%s)"):format(fn,m2[fn]))
        elseif fn=="max" then w("static Value lua_math_max(int n,Value*a){double r=numval(a[0]);free_value(a[0]);for(int i=1;i<n;i++){double v=numval(a[i]);free_value(a[i]);if(v>r)r=v;}return make_double(r);}")
        elseif fn=="min" then w("static Value lua_math_min(int n,Value*a){double r=numval(a[0]);free_value(a[0]);for(int i=1;i<n;i++){double v=numval(a[i]);free_value(a[i]);if(v<r)r=v;}return make_double(r);}")
        elseif fn=="modf" then w("static Value lua_math_modf(int n,Value*a){double ip,x=numval(a[0]);free_value(a[0]);modf(x,&ip);return make_double(ip);}")
        elseif fn=="frexp" then w("static Value lua_math_frexp(int n,Value*a){int e;double x=numval(a[0]);free_value(a[0]);return make_double(frexp(x,&e));}")
        elseif fn=="ldexp" then w("static Value lua_math_ldexp(int n,Value*a){double x=numval(a[0]);int e=(int)numval(a[1]);free_value(a[0]);free_value(a[1]);return make_double(ldexp(x,e));}")
        elseif fn=="random" then w([[static Value lua_math_random(int n,Value*a){prng_state=prng_state*6364136223846793005ULL+1442695040888963407ULL;double d=(double)(prng_state>>11)/(double)(1ULL<<53);if(n==0)return make_double(d);if(n==1){double r1=numval(a[0]);free_value(a[0]);return make_int((int64_t)(d*r1)+1);}double r1=numval(a[0]),r2=numval(a[1]);free_value(a[0]);free_value(a[1]);return make_int((int64_t)(d*(r2-r1+1))+r1);}]])
        elseif fn=="randomseed" then w("static Value lua_math_randomseed(int n,Value*a){if(n>0){prng_state=(uint64_t)numval(a[0]);free_value(a[0]);}else prng_state=(uint64_t)time(NULL);return make_nil();}") end
    end end
    w("static Value make_math_table(void){Value t=make_table();")
    w("#define MS(n) table_raw_set(t.tbl,make_string(#n),make_func(lua_math_##n))")
    for _,fn in ipairs(math_fns) do wif(used_math[fn],"    MS("..fn..");") end
    w("#undef MS")
    wif(use_math_pi,'    table_raw_set(t.tbl,make_string("pi"),make_double(3.14159265358979323846));')
    wif(use_math_huge,'    table_raw_set(t.tbl,make_string("huge"),make_double(1e300*1e300));')
    w("    return t;\n}\n#undef M1\n#undef M2")
end

-- OS library
if use.os_lib then
    w("\n/* os */")
    wif(used_os.clock,"static Value lua_os_clock(int n,Value*a){(void)n;(void)a;return make_double((double)clock()/(double)CLOCKS_PER_SEC);}")
    wif(used_os.time,"static Value lua_os_time(int n,Value*a){(void)n;(void)a;return make_double((double)time(NULL));}")
    wif(used_os.difftime,"static Value lua_os_difftime(int n,Value*a){double t2=n>0?numval(a[0]):0,t1=n>1?numval(a[1]):0;if(n>0)free_value(a[0]);if(n>1)free_value(a[1]);return make_double(difftime((time_t)t2,(time_t)t1));}")
    wif(used_os.date,[[static Value lua_os_date(int n,Value*a){char fb[256];const char*fmt="%c";if(n>0&&a[0].t==T_STRING&&a[0].ls){strncpy(fb,a[0].ls->data,sizeof(fb)-1);fb[sizeof(fb)-1]='\0';fmt=fb;}if(n>0)free_value(a[0]);if(n>1)free_value(a[1]);time_t t=time(NULL);const char*s=fmt;int utc=(*s=='!');if(utc)s++;struct tm*stm=utc?gmtime(&t):localtime(&t);if(!stm)return make_nil();char buf[256];strftime(buf,sizeof buf,s,stm);return make_string(buf);}]])
    wif(used_os.exit,"static Value lua_os_exit(int n,Value*a){int status=EXIT_SUCCESS;if(n>0){if(a[0].t==T_BOOL)status=a[0].i?EXIT_SUCCESS:EXIT_FAILURE;else status=(int)numval(a[0]);free_value(a[0]);}exit(status);return make_nil();}")
    wif(used_os.getenv,"static Value lua_os_getenv(int n,Value*a){if(n<1||a[0].t!=T_STRING){if(n>0)free_value(a[0]);return make_nil();}const char*v=getenv(luastr_cstr(a[0].ls));free_value(a[0]);return v?make_string(v):make_nil();}")
    wif(used_os.execute,"static Value lua_os_execute(int n,Value*a){char*c=NULL;if(n>0&&a[0].t==T_STRING&&a[0].ls)c=strdup(a[0].ls->data);if(n>0)free_value(a[0]);int r=system(c);free(c);return make_int(r);}")
    wif(used_os.remove,"static Value lua_os_remove(int n,Value*a){if(n<1||a[0].t!=T_STRING){if(n>0)free_value(a[0]);return make_nil();}char*f=strdup(luastr_cstr(a[0].ls));free_value(a[0]);int ok=remove(f)==0;free(f);return ok?make_bool(1):make_string(strerror(errno));}")
    wif(used_os.rename,"static Value lua_os_rename(int n,Value*a){if(n<2||a[0].t!=T_STRING||a[1].t!=T_STRING){for(int i=0;i<n;i++)free_value(a[i]);return make_nil();}char*fr=strdup(luastr_cstr(a[0].ls)),*to=strdup(luastr_cstr(a[1].ls));free_value(a[0]);free_value(a[1]);int ok=rename(fr,to)==0;free(fr);free(to);return ok?make_bool(1):make_string(strerror(errno));}")
    wif(used_os.tmpname,[[static Value lua_os_tmpname(int n,Value*a){(void)n;(void)a;
#if defined(__unix__)||defined(__linux__)||defined(__APPLE__)
char buf[32];strcpy(buf,"/tmp/lua_XXXXXX");int fd=mkstemp(buf);if(fd!=-1)close(fd);return make_string(buf);
#else
char buf[L_tmpnam];if(tmpnam(buf)==NULL)return make_nil();return make_string(buf);
#endif
}]])
    wif(used_os.setlocale,"static Value lua_os_setlocale(int n,Value*a){const char*loc=n>0&&a[0].t==T_STRING?luastr_cstr(a[0].ls):NULL;const char*r=setlocale(LC_ALL,loc);if(n>0)free_value(a[0]);if(n>1)free_value(a[1]);return r?make_string(r):make_nil();}")
    w("static Value make_os_table(void){Value t=make_table();")
    w("#define OS(n) table_raw_set(t.tbl,make_string(#n),make_func(lua_os_##n))")
    for _,fn in ipairs(os_fns) do wif(used_os[fn],"    OS("..fn..");") end
    w("#undef OS\n    return t;\n}")
end

-- IO library
if use.io_lib then
    w("\n/* io */")
    w("#define READ_LINE(F,DEST,FAIL_EXPR) do{size_t cap=256,len=0;char*buf=malloc(cap);int c;while((c=fgetc(F))!=EOF&&c!='\\n'){if(len+1>=cap){cap*=2;void*__rb=realloc(buf,cap);if(!__rb){free(buf);FAIL_EXPR;}buf=(char*)__rb;}buf[len++]=(char)c;}if(c==EOF&&len==0){free(buf);FAIL_EXPR;}buf[len]='\\0';DEST=make_string(buf);free(buf);}while(0)")
    w("#define READ_ALL(F,DEST) do{size_t cap=256,len=0;char*buf=malloc(cap);int c;while((c=fgetc(F))!=EOF){if(len+1>=cap){cap*=2;void*__rb=realloc(buf,cap);if(!__rb){free(buf);DEST=make_string(\"\");break;}buf=(char*)__rb;}buf[len++]=(char)c;}buf[len]='\\0';DEST=make_string(buf);free(buf);}while(0)")
    w("#define IS_NUM_FMT(f) (strcmp(f,\"*n\")==0||strcmp(f,\"n\")==0||strcmp(f,\"*number\")==0||strcmp(f,\"number\")==0)")
    w("#define IS_ALL_FMT(f) (strcmp(f,\"*a\")==0||strcmp(f,\"a\")==0)")
    wif(used_io.write,[[static Value lua_io_write(int n,Value*a){for(int i=0;i<n;i++){switch(a[i].t){case T_STRING:fwrite(luastr_cstr(a[i].ls),1,strlen(luastr_cstr(a[i].ls)),stdout);break;case T_INT:fprintf(stdout,"%lld",(long long)a[i].i);break;case T_DOUBLE:fprintf(stdout,"%g",a[i].d);break;default:break;}free_value(a[i]);}fflush(stdout);return make_nil();}]])
    wif(used_io.read,[[static Value lua_io_read(int n,Value*a){const char*fmt="*l";if(n>0&&a[0].t==T_STRING&&a[0].ls)fmt=luastr_cstr(a[0].ls);Value r;if(IS_NUM_FMT(fmt)){double d;r=(scanf("%lf",&d)==1)?make_double(d):make_nil();}else if(IS_ALL_FMT(fmt)){READ_ALL(stdin,r);}else{READ_LINE(stdin,r,{if(n>0)free_value(a[0]);return make_nil();});}if(n>0)free_value(a[0]);return r;}]])
    if used_io.open then w([[
static Value lua_file_read(int n,Value*a);
static Value lua_file_write(int n,Value*a);
static Value lua_file_close(int n,Value*a);
static Value lua_file_lines(int n,Value*a);
static Value make_file_handle(FILE*f){Value t=make_table();table_raw_set(t.tbl,make_string("__file"),make_file(f));table_raw_set(t.tbl,make_string("read"),make_func(lua_file_read));table_raw_set(t.tbl,make_string("write"),make_func(lua_file_write));table_raw_set(t.tbl,make_string("close"),make_func(lua_file_close));table_raw_set(t.tbl,make_string("lines"),make_func(lua_file_lines));return t;}
static FILE*file_handle_get(Value self){if(self.t!=T_TABLE||!self.tbl)return NULL;Value fv=table_get(value_copy(self),make_string("__file"));FILE*f=fv.t==T_FILE?fv.file:NULL;free_value(fv);return f;}
static Value lua_io_open(int n,Value*a){if(n<1||a[0].t!=T_STRING){for(int i=0;i<n;i++)free_value(a[i]);return make_nil();}const char*path=luastr_cstr(a[0].ls);const char*mode=(n>1&&a[1].t==T_STRING)?luastr_cstr(a[1].ls):"r";FILE*f=fopen(path,mode);for(int i=0;i<n;i++)free_value(a[i]);return f?make_file_handle(f):make_nil();}
static Value lua_file_read(int n,Value*a){if(n<1)return make_nil();FILE*f=file_handle_get(a[0]);if(!f){for(int i=0;i<n;i++)free_value(a[i]);return make_nil();}const char*fmt="*l";if(n>1&&a[1].t==T_STRING&&a[1].ls)fmt=luastr_cstr(a[1].ls);Value r;if(IS_NUM_FMT(fmt)){double d;r=(fscanf(f,"%lf",&d)==1)?make_double(d):make_nil();}else if(IS_ALL_FMT(fmt)){READ_ALL(f,r);}else{READ_LINE(f,r,{for(int i=0;i<n;i++)free_value(a[i]);return make_nil();});}for(int i=0;i<n;i++)free_value(a[i]);return r;}
static Value lua_file_write(int n,Value*a){if(n<1)return make_nil();FILE*f=file_handle_get(a[0]);if(!f){for(int i=0;i<n;i++)free_value(a[i]);return make_nil();}for(int i=1;i<n;i++){switch(a[i].t){case T_STRING:fwrite(luastr_cstr(a[i].ls),1,strlen(luastr_cstr(a[i].ls)),f);break;case T_INT:fprintf(f,"%lld",(long long)a[i].i);break;case T_DOUBLE:fprintf(f,"%g",a[i].d);break;default:break;}}for(int i=0;i<n;i++)free_value(a[i]);return make_nil();}
static Value lua_file_close(int n,Value*a){if(n>0){FILE*f=file_handle_get(a[0]);if(f&&f!=stdout&&f!=stderr&&f!=stdin)fclose(f);for(int i=0;i<n;i++)free_value(a[i]);}return make_nil();}
static Value lua_file_lines(int n,Value*a){if(n<1)return make_nil();FILE*f=file_handle_get(a[0]);if(!f){for(int i=0;i<n;i++)free_value(a[i]);return make_nil();}Value tbl=make_table();int idx=1;while(1){Value line;READ_LINE(f,line,break);table_raw_set(tbl.tbl,make_int(idx++),line);}for(int i=0;i<n;i++)free_value(a[i]);return tbl;}]]) end
    wif(used_io.close,"static Value lua_io_close(int n,Value*a){if(n>0){FILE*f=file_handle_get(a[0]);if(f&&f!=stdout&&f!=stderr&&f!=stdin)fclose(f);for(int i=0;i<n;i++)free_value(a[i]);}return make_nil();}")
    wif(used_io.flush,"static Value lua_io_flush(int n,Value*a){fflush(stdout);for(int i=0;i<n;i++)free_value(a[i]);return make_nil();}")
    wif(used_io.lines,[[static Value lua_io_lines(int n,Value*a){FILE*f=stdin;int opened=0;if(n>0&&a[0].t==T_STRING&&a[0].ls){f=fopen(luastr_cstr(a[0].ls),"r");opened=1;}for(int i=0;i<n;i++)free_value(a[i]);if(!f)return make_nil();Value tbl=make_table();int idx=1;while(1){Value line;READ_LINE(f,line,break);table_raw_set(tbl.tbl,make_int(idx++),line);}if(opened)fclose(f);return tbl;}]])
    w("static Value make_io_table(void){Value t=make_table();")
    w("#define IO(n) table_raw_set(t.tbl,make_string(#n),make_func(lua_io_##n))")
    for _,fn in ipairs({"write","read","open","close","flush","lines"}) do wif(used_io[fn],"    IO("..fn..");") end
    w("#undef IO")
    wif(used_io.stdin,'    table_raw_set(t.tbl,make_string("stdin"),make_file(stdin));')
    wif(used_io.stdout,'    table_raw_set(t.tbl,make_string("stdout"),make_file(stdout));')
    wif(used_io.stderr,'    table_raw_set(t.tbl,make_string("stderr"),make_file(stderr));')
    w("    return t;\n}")
    w("#undef READ_LINE\n#undef READ_ALL\n#undef IS_NUM_FMT\n#undef IS_ALL_FMT")
end

-- Globals
w("\n/* globals */")
for name in pairs(globals) do w("static Value "..name..";") end
wif(use.math_lib,"static Value math;")
wif(use.os_lib,  "static Value os;")
wif(use.io_lib,  "static Value io;")
wif(use.string_lib,"static Value string;")
w("static Value arg;")
w("")

-- User-defined functions
for _,fn in ipairs(functions) do
    local fname = fn.name
    local args_str = trim(fn.args)
    local fixed_args = {}; local is_vararg = false
    if args_str ~= "" then
        for a in (args_str..","):gmatch("(.-),") do
            a = trim(a)
            if a == "..." then is_vararg = true
            elseif #a > 0 then table.insert(fixed_args, a) end
        end
    end

    local local_vars = {}
    w(("static Value %s(int __nargs,Value*__args){"):format(fname))
    for ai,a in ipairs(fixed_args) do
        w(("    Value %s=__nargs>%d?value_copy(__args[%d]):make_nil();"):format(a,ai-1,ai-1))
        local_vars[a] = true
    end

    local prev_fixed = current_fn_fixed_argc
    current_fn_fixed_argc = #fixed_args

    local ctx = {local_vars=local_vars, assigned={}, globals_tbl=globals}
    local bi = 1
    while bi <= #fn.body do local stmt,consumed = gen_stmt(fn.body,bi,ctx); w(stmt); bi=bi+consumed end
    -- FIX 2: only emit epilogue cleanup if we didn't already clean up at a return statement.
    -- (If the function has multiple exit paths, some via return and some falling off the end,
    --  the fallthrough path still needs cleanup.)
    if not ctx.returned then
        for v in pairs(local_vars) do w(("    free_value(%s);"):format(v)) end
    end
    w("    return make_nil();\n}\n")

    current_fn_fixed_argc = prev_fixed
end

-- main()
w("int main(int argc,char**argv){")
for name in pairs(globals) do w("    "..name.."=make_nil();") end
wif(use.math_lib,  "    math=make_math_table();")
wif(use.os_lib,    "    os=make_os_table();")
wif(use.io_lib,    "    io=make_io_table();")
wif(use.string_lib,"    string=make_string_table();")
w([[
    arg=make_table();
    for(int __ai=1;__ai<argc;__ai++){
        table_raw_set(arg.tbl,make_int(__ai),make_string(argv[__ai]));
    }
]])

local method_registry = {}
for _,fn in ipairs(functions) do
    local tp,mn = fn.name:match("^(.+)__([^_].*)$")
    if not tp then tp,mn = fn.name:match("^(.+)__(_+.*)$") end
    if tp and mn then
        if not method_registry[tp] then method_registry[tp]={} end
        table.insert(method_registry[tp], {meth=mn, fname=fn.name})
    end
end
w("")

local assigned_map = {}; local ti = 1
current_fn_fixed_argc = 0
local ctx_top = {local_vars=nil, assigned=assigned_map, globals_tbl=globals}
while ti <= #topstmts do
    local stmt,consumed = gen_stmt(topstmts, ti, ctx_top); w(stmt)
    local av = trim(topstmts[ti] or ""):match("^local%s+([A-Za-z_][A-Za-z0-9_]*)%s*=")
           or  trim(topstmts[ti] or ""):match("^([A-Za-z_][A-Za-z0-9_]*)%s*=")
    if av and method_registry[av] then
        for _,m in ipairs(method_registry[av]) do
            w(('    table_raw_set(%s.tbl,make_string("%s"),make_func(%s));'):format(av,m.meth,m.fname)) end
        method_registry[av] = nil
    end
    ti = ti+consumed
end
for tbl_name,methods in pairs(method_registry) do
    for _,m in ipairs(methods) do
        w(('    table_raw_set(%s.tbl,make_string("%s"),make_func(%s));'):format(tbl_name,m.meth,m.fname)) end
end

w("\n    /* cleanup globals */")
for name in pairs(globals) do w("    free_value("..name..");") end
wif(use.math_lib,  "    free_value(math);")
wif(use.os_lib,    "    free_value(os);")
wif(use.io_lib,    "    free_value(io);")
wif(use.string_lib,"    free_value(string);")
w("    free_value(arg);")
w("    return 0;\n}")

local f = assert(io.open(output_path,"w"))
f:write(table.concat(out,"\n"))
f:close()
print("Wrote "..output_path)
