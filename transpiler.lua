-- transpiler.lua  v7
-- made by macsipac, Apache 2.0 liscence
-- Lua -> C AOT transpiler
-- Usage: lua transpiler.lua input.lua  =>  output.c

local input_path  = arg[1] or "input.lua"
local output_path = "output.c"

local function trim(s) return (s or ""):match("^%s*(.-)%s*$") end
local LONG_STR_NL = "\1"

local function escape_c(s)
    return s:gsub("\\","\\\\"):gsub('"','\\"'):gsub("\1","\\n"):gsub("\n","\\n"):gsub("\r","\\r")
end
local function lua_str_inner(expr)
    local d,inner=expr:sub(1,1),expr:sub(2,-2)
    inner=inner:gsub("\1","\\n")
    if d=="'" then inner=inner:gsub("\\'","'"):gsub('"','\\"') end
    return inner
end
local function is_int(s)  return s:match("^%-?%d+$") end
local function is_flt(s)  return s:match("^%-?%d+%.%d+$") end
local function is_str(s)  return s:match('^".*"$') or s:match("^'.*'$") or s:match("^%[%[.-%]%]$") end
local function is_id(s)   return s:match("^[A-Za-z_][A-Za-z0-9_]*$") end

local function skip_str(e,i)
    local q=e:sub(i,i); i=i+1
    while i<=#e do
        local c=e:sub(i,i)
        if c=='\\' then i=i+2 elseif c==q then return i+1 else i=i+1 end
    end
    return i
end

-- scan expr tracking depth; call cb(i,ch) at depth==0, returns early if cb returns a value
local function depth_scan(e,cb)
    local d,i=0,1
    while i<=#e do
        local ch=e:sub(i,i)
        if ch=='"' or ch=="'" then i=skip_str(e,i)
        elseif ch=='('or ch=='['or ch=='{' then d=d+1;i=i+1
        elseif ch==')'or ch==']'or ch=='}' then d=d-1;i=i+1
        else
            if d==0 then local r1,r2=cb(i,ch); if r1 then return r1,r2 end end
            i=i+1
        end
    end
end

local function find_op(expr,ops)
    local len=#expr
    return depth_scan(expr,function(i,_)
        for _,op in ipairs(ops) do
            local ol=#op
            if i+ol-1<=len and expr:sub(i,i+ol-1)==op then
                local bef=expr:sub(math.max(1,i-1),i-1)
                local aft=expr:sub(i+ol,math.min(len,i+ol))
                if op:match("%a") then
                    if(bef==""or bef:match("%W"))and(aft==""or aft:match("%W"))then return i,op end
                else return i,op end
            end
        end
    end)
end

local function split_args(s)
    local args,cur={},""
    local d,i=0,1
    while i<=#s do
        local ch=s:sub(i,i)
        if ch=='"'or ch=="'" then
            local j=skip_str(s,i); cur=cur..s:sub(i,j-1); i=j
        elseif ch=='('or ch=='['or ch=='{' then d=d+1;cur=cur..ch;i=i+1
        elseif ch==')'or ch==']'or ch=='}' then d=d-1;cur=cur..ch;i=i+1
        elseif ch==','and d==0 then table.insert(args,trim(cur));cur="";i=i+1
        else cur=cur..ch;i=i+1 end
    end
    if trim(cur)~="" then table.insert(args,trim(cur)) end
    return args
end

-- scan right-to-left at depth 0 for last occurrence of chars
local function last_op_scan(expr,chars)
    local last_i,last_op
    local d,i=0,1
    while i<=#expr do
        local ch=expr:sub(i,i)
        if ch=='"'or ch=="'" then i=skip_str(expr,i)
        elseif ch=='('or ch=='['or ch=='{' then d=d+1;i=i+1
        elseif ch==')'or ch==']'or ch=='}' then d=d-1;i=i+1
        elseif d==0 then
            if chars[ch] then last_i=i;last_op=ch end
            i=i+1
        else i=i+1 end
    end
    return last_i,last_op
end

local function translate_expr(expr)
    expr=trim(expr)
    if expr=="" then return "make_int(0)" end
    if expr:sub(1,1)=='#' then return ("value_len(%s)"):format(translate_expr(expr:sub(2))) end
    if expr:match("^not%s+") then return ("value_not(%s)"):format(translate_expr(expr:match("^not%s+(.+)$"))) end
    if expr:sub(1,1)=='-'and is_int(expr:sub(2)) then return "make_int("..expr..")" end
    if expr:sub(1,1)=='-'and is_flt(expr:sub(2)) then return "make_double("..expr..")" end

    do local i=find_op(expr,{" or "})
        if i then return("value_or(%s,%s)"):format(translate_expr(trim(expr:sub(1,i-1))),translate_expr(trim(expr:sub(i+4)))) end end
    do local i=find_op(expr,{" and "})
        if i then return("value_and(%s,%s)"):format(translate_expr(trim(expr:sub(1,i-1))),translate_expr(trim(expr:sub(i+5)))) end end
    do local i,op=find_op(expr,{"==","~=","<=",">=","<",">"})
        if i then
            local fn=({["=="]="value_eq",["~="]="value_neq",["<="]="value_le",
                       [">="]="value_ge",["<"]="value_lt",[">"]="value_gt"})[op]
            return ("%s(%s,%s)"):format(fn,translate_expr(trim(expr:sub(1,i-1))),translate_expr(trim(expr:sub(i+#op))))
        end end
    do local i=find_op(expr,{".."})
        if i then return("value_concat(%s,%s)"):format(translate_expr(trim(expr:sub(1,i-1))),translate_expr(trim(expr:sub(i+2)))) end end

    -- additive (rightmost +/- at depth 0, left side must be non-empty)
    do
        local last_i,last_op
        local d,i=0,1
        while i<=#expr do
            local ch=expr:sub(i,i)
            if ch=='"'or ch=="'" then i=skip_str(expr,i)
            elseif ch=='('or ch=='['or ch=='{' then d=d+1;i=i+1
            elseif ch==')'or ch==']'or ch=='}' then d=d-1;i=i+1
            elseif d==0 and(ch=='+'or ch=='-')and trim(expr:sub(1,i-1))~="" then last_i=i;last_op=ch;i=i+1
            else i=i+1 end
        end
        if last_i then
            return(last_op=='+'and"value_add"or"value_sub").."("..translate_expr(trim(expr:sub(1,last_i-1)))..",\z
"..translate_expr(trim(expr:sub(last_i+1)))..")"
        end
    end

    do local li,lo=last_op_scan(expr,{["*"]=true,["/"]=true,["%"]=true})
        if li then
            return({["*"]="value_mul",["/"]="value_div",["%"]="value_mod"})[lo]
                .."("..translate_expr(trim(expr:sub(1,li-1)))..",\z
"..translate_expr(trim(expr:sub(li+1)))..")"
        end end

    if expr:match("^%[%[") then local s=expr:match("^%[%[(.-)%]%]$"); if s then return('make_string("%s")'):format(escape_c(s)) end end
    if is_str(expr)  then return('make_string("%s")'):format(lua_str_inner(expr)) end
    if is_int(expr)  then return "make_int("..expr..")" end
    if is_flt(expr)  then return "make_double("..expr..")" end
    if expr=="true"  then return "make_bool(1)" end
    if expr=="false" then return "make_bool(0)" end
    if expr=="nil"   then return "make_nil()" end

    if expr:sub(1,1)=='{' then
        local d,close=0,#expr
        for i2=1,#expr do local ch=expr:sub(i2,i2)
            if ch=='{' then d=d+1 elseif ch=='}' then d=d-1 end
            if d==0 then close=i2;break end end
        local inner=trim(expr:sub(2,close-1))
        if inner=="" then return "make_table()" end
        local parts,ai={},1
        for _,field in ipairs(split_args(inner)) do
            field=trim(field)
            local k,v=field:match("^([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
            if k and v then
                table.insert(parts,('make_string("%s")'):format(escape_c(k))); table.insert(parts,translate_expr(v))
            else
                local ke,ve=field:match("^%[(.+)%]%s*=%s*(.+)$")
                if ke and ve then table.insert(parts,translate_expr(ke)); table.insert(parts,translate_expr(ve))
                else table.insert(parts,"make_int("..ai..")"); table.insert(parts,translate_expr(field)); ai=ai+1 end
            end
        end
        return("table_init(%d,%s)"):format(#parts/2,table.concat(parts,","))
    end

    do local a=expr:match("^error%s*%((.*)%)$")
        if a then local args=split_args(a)
            return("lua_error(%s)"):format(args[1] and translate_expr(trim(args[1])) or 'make_string("error")') end end
    do local a=expr:match("^assert%s*%((.*)%)$")
        if a then local args=split_args(a)
            return("lua_assert(%s,%s)"):format(translate_expr(trim(args[1] or "")),
                args[2] and translate_expr(trim(args[2])) or 'make_string("assertion failed!")') end end

    -- method call obj:method(args)
    do local found; depth_scan(expr,function(i,ch)
        if ch==':' then
            local obj=trim(expr:sub(1,i-1)); local rest=trim(expr:sub(i+1))
            local meth,as=rest:match("^([A-Za-z_][A-Za-z0-9_]*)%s*%((.*)%)$")
            if meth then
                local args=split_args(as); local p={}
                for _,a in ipairs(args) do table.insert(p,translate_expr(trim(a))) end
                found=("value_method_call(%s,\"%s\",%d%s)"):format(
                    translate_expr(obj),meth,#args,#args>0 and ","..table.concat(p,",") or "")
                return true
            end
        end
    end); if found then return found end end

    -- suffix walker: call / index / dot
    do
        local ss,st
        -- manual walk tracking depth for suffix detection
        local d2,i=0,1
        while i<=#expr do
            local ch=expr:sub(i,i)
            if ch=='"'or ch=="'" then i=skip_str(expr,i)
            elseif ch=='('or ch=='['or ch=='{' then
                if d2==0 and i>1 then
                    if ch=='(' then ss=i;st='call' elseif ch=='[' then ss=i;st='index' end
                end
                d2=d2+1;i=i+1
            elseif ch==')'or ch==']'or ch=='}' then d2=d2-1;i=i+1
            elseif ch=='.'and d2==0 and i>1 then
                local rest=expr:sub(i+1); local key=rest:match("^([A-Za-z_][A-Za-z0-9_]*)")
                if key and rest:sub(#key+1,#key+1)~='(' then ss=i;st='dot' end
                i=i+1
            else i=i+1 end
        end

        if ss and st=='call' then
            local d3,cp=0,#expr
            for j=ss,#expr do local ch=expr:sub(j,j)
                if ch=='(' then d3=d3+1 elseif ch==')' then d3=d3-1 end
                if d3==0 then cp=j;break end end
            local fn_e=trim(expr:sub(1,ss-1))
            local as=trim(expr:sub(ss+1,cp-1))
            local args=as~="" and split_args(as) or {}
            local parts={}; for _,a in ipairs(args) do table.insert(parts,translate_expr(a)) end
            local sep=#parts>0 and ","..table.concat(parts,",") or ""
            local dobj,dkey=fn_e:match("^(.+)%.([A-Za-z_][A-Za-z0-9_]*)$")
            if dobj then return("table_call(%s,make_string(\"%s\"),%d%s)"):format(translate_expr(dobj),escape_c(dkey),#parts,sep) end
            if is_id(fn_e) then return fn_e.."("..table.concat(parts,",")..")" end
            return("value_call(%s,%d%s)"):format(translate_expr(fn_e),#parts,sep)
        elseif ss and st=='index' then
            local d3,cb=0,#expr
            for j=ss,#expr do local ch=expr:sub(j,j)
                if ch=='[' then d3=d3+1 elseif ch==']' then d3=d3-1 end
                if d3==0 then cb=j;break end end
            return("table_get(%s,%s)"):format(translate_expr(trim(expr:sub(1,ss-1))),translate_expr(trim(expr:sub(ss+1,cb-1))))
        elseif ss and st=='dot' then
            local te=trim(expr:sub(1,ss-1)); local key=expr:sub(ss+1):match("^([A-Za-z_][A-Za-z0-9_]*)")
            if key and te~="" then return('table_get(%s,make_string("%s"))'):format(translate_expr(te),escape_c(key)) end
        end
    end

    if is_id(expr) then return "value_copy("..expr..")" end
    do local inner=expr:match("^%((.+)%)$"); if inner then return translate_expr(inner) end end
    return expr
end

-- ---------------------------------------------------------------------------
-- Read + pre-process source
-- ---------------------------------------------------------------------------
local raw_src=assert(io.open(input_path)):read("*a")
raw_src=raw_src:gsub("%[%[(.-)%]%]",function(s)
    return '"'..s:gsub("\\","\\\\"):gsub('"','\\"'):gsub("\r\n",LONG_STR_NL):gsub("\n",LONG_STR_NL):gsub("\r",LONG_STR_NL)..'"'
end)
local raw_lines={}
for l in (raw_src.."\n"):gmatch("([^\n]*)\n") do table.insert(raw_lines,l) end

local function brace_depth(line)
    local depth,i,in_s,sq=0,1,false,nil
    while i<=#line do
        local ch=line:sub(i,i)
        if in_s then
            if ch=='\\' then i=i+2 elseif ch==sq then in_s=false;i=i+1 else i=i+1 end
        else
            if ch=='"'or ch=="'" then in_s=true;sq=ch;i=i+1
            elseif ch=='{' then depth=depth+1;i=i+1
            elseif ch=='}' then depth=depth-1;i=i+1
            elseif ch=='-'and line:sub(i,i+1)=='--' then break
            else i=i+1 end
        end
    end
    return depth
end

local lines={}
do local i=1
    while i<=#raw_lines do
        local combined=raw_lines[i]; local depth=brace_depth(combined)
        while depth>0 and i<#raw_lines do
            i=i+1; combined=combined.." "..trim(raw_lines[i]); depth=depth+brace_depth(raw_lines[i])
        end
        table.insert(lines,combined); i=i+1
    end
end

-- ---------------------------------------------------------------------------
-- Parse top-level: split functions vs statements
-- ---------------------------------------------------------------------------
local functions,topstmts={},{}

local function opens_block(ts)
    return ts:match("^if%s")or ts:match("^for%s")or ts:match("^while%s")
        or ts:match("^function%s")or ts:match("^local%s+function%s")
        or ts=="do"or ts:match("^do%s")or ts:match("^repeat$")or ts:match("^repeat%s")
end

local i,n=1,#lines
while i<=n do
    local line=lines[i]; local s=trim(line)
    if s==""or s:match("^%-%-") then i=i+1
    elseif s:match("^function%s")or s:match("^local%s+function%s") then
        local name,args=s:match("^%s*function%s+([A-Za-z_][A-Za-z0-9_]*)%s*%((.-)%)")
        if not name then name,args=s:match("^%s*local%s+function%s+([A-Za-z_][A-Za-z0-9_]*)%s*%((.-)%)") end
        if not name then
            local t2,m2,ma=s:match("^%s*function%s+([A-Za-z_][A-Za-z0-9_]*)[.:]([A-Za-z_][A-Za-z0-9_]*)%s*%((.-)%)")
            if t2 then name=t2.."__"..m2;args=ma end
        end
        args=trim(args or "")
        local body={};i=i+1;local depth=1
        while i<=n do
            local l=lines[i];local ts2=trim(l)
            if opens_block(ts2) then depth=depth+1 end
            if ts2=="end" then depth=depth-1;if depth==0 then break end end
            table.insert(body,l);i=i+1
        end
        functions[#functions+1]={name=name,args=args,body=body};i=i+1
    else table.insert(topstmts,line);i=i+1 end
end

local globals,builtin_globals={},{math=true,os=true,io=true}
for _,line in ipairs(topstmts) do
    local s=trim(line)
    local v=s:match("^local%s+([A-Za-z_][A-Za-z0-9_]*)")or s:match("^([A-Za-z_][A-Za-z0-9_]*)%s*=")
    if v and not builtin_globals[v] then globals[v]=true end
end

local tmp_counter=0
local function newtmp() tmp_counter=tmp_counter+1; return "__tmp"..tmp_counter end

local function collect_block(src,si)
    local body={};local depth=1;local j=si
    while j<=#src do
        local L=trim(src[j])
        if opens_block(L) then depth=depth+1 end
        if L=="end" then depth=depth-1;if depth==0 then return body,(j-si+1) end end
        table.insert(body,src[j]);j=j+1
    end
    return body,(j-si)
end

-- ---------------------------------------------------------------------------
-- Shared statement generation
-- ctx = { is_top=bool, local_vars=table|nil, assigned=table, globals=table, stmts=table,
--         loop_vars=table (stack of {var,...} to free on return inside loops) }
-- ---------------------------------------------------------------------------
local gen_stmt  -- forward decl

-- Emit free_value calls for all locals currently in scope (for return paths)
local function emit_scope_cleanup(ctx)
    local code=""
    if ctx.local_vars then
        for v,_ in pairs(ctx.local_vars) do
            code=code..("    free_value(%s);\n"):format(v)
        end
    end
    return code
end

local function gen_print(pargs)
    local args=split_args(pargs); local nn=#args; local arr=newtmp()
    local code=("    Value %s[%d];\n"):format(arr,math.max(nn,1))
    for ii,a in ipairs(args) do code=code..("    %s[%d]=%s;\n"):format(arr,ii-1,translate_expr(trim(a))) end
    return code..("    print_values(%d,%s);\n"):format(nn,arr)
end

local function gen_assert_stmt(s)
    local args=split_args(s:match("^assert%s*%((.*)%)$"))
    local ce=translate_expr(trim(args[1]or""))
    local me=args[2] and translate_expr(trim(args[2])) or 'make_string("assertion failed!")'
    local tmp=newtmp()
    return("    Value %s=lua_assert(%s,%s);\n    free_value(%s);\n"):format(tmp,ce,me,tmp)
end

local function gen_if(s,ctx,idx,src)
    -- inline single-line if?
    local function find_then(str)
        local then_pos
        local d2,i2=0,1
        while i2<=#str do
            local ch=str:sub(i2,i2)
            if ch=='"'or ch=="'" then i2=skip_str(str,i2)
            elseif ch=='('or ch=='['or ch=='{' then d2=d2+1;i2=i2+1
            elseif ch==')'or ch==']'or ch=='}' then d2=d2-1;i2=i2+1
            elseif d2==0 and str:sub(i2,i2+4)==" then" then
                local af=str:sub(i2+5,i2+5)
                if af==""or af==" "or af=="\t" then then_pos=i2;break end
                i2=i2+1
            else i2=i2+1 end
        end
        return then_pos
    end

    local inline_result
    if s:match("%send$") or s=="end" then
        local tp=find_then(s)
        if tp then
            local cond=trim(s:sub(4,tp-1)); local rest=trim(s:sub(tp+5))
            if rest:match("end$") then
                rest=trim(rest:sub(1,-4))
                local ep; do local d3,i3=0,1; while i3<=#rest do
                    local ch=rest:sub(i3,i3)
                    if ch=='"'or ch=="'" then i3=skip_str(rest,i3)
                    elseif ch=='('or ch=='['or ch=='{' then d3=d3+1;i3=i3+1
                    elseif ch==')'or ch==']'or ch=='}' then d3=d3-1;i3=i3+1
                    elseif d3==0 and rest:sub(i3,i3+5)==" else " then ep=i3;break
                    else i3=i3+1 end
                end end
                local function gs2(st)
                    local code=""
                    for _,st2 in ipairs(st) do if trim(st2)~="" then
                        local r,_=gen_stmt({st2},1,ctx); code=code..r end end
                    return code
                end
                local tmp=newtmp();local cv=newtmp()
                local code=("    Value %s=%s;\n    int %s=value_is_truthy(%s);\n    free_value(%s);\n    if(%s){\n"):format(
                    tmp,translate_expr(cond),cv,tmp,tmp,cv)
                if ep then
                    code=code..gs2({trim(rest:sub(1,ep-1))}).."    }else{\n"..gs2({trim(rest:sub(ep+6))}).."    }\n"
                else code=code..gs2({rest}).."    }\n" end
                inline_result=code
            end
        end
    end
    if inline_result then return inline_result,1 end

    local clauses={}
    local cond=trim((s:match("^if%s+(.+)%s+then$")or s:match("^if%s+(.+)$")or""):gsub("%s+then$",""))
    clauses[1]={kind="if",cond=cond,body={}}
    local depth=1;local j=idx+1
    while j<=#src do
        local L=trim(src[j])
        if opens_block(L) then depth=depth+1;table.insert(clauses[#clauses].body,src[j]);j=j+1
        elseif depth>1 then
            if L=="end" then depth=depth-1 end
            table.insert(clauses[#clauses].body,src[j]);j=j+1
        else
            if L:match("^elseif%s") then
                local c=trim((L:match("^elseif%s+(.+)%s+then$")or L:match("^elseif%s+(.+)$")or""):gsub("%s+then$",""))
                clauses[#clauses+1]={kind="elseif",cond=c,body={}};j=j+1
            elseif L=="else"or L:match("^else%s*$") then clauses[#clauses+1]={kind="else",body={}};j=j+1
            elseif L=="end" then j=j+1;break
            else table.insert(clauses[#clauses].body,src[j]);j=j+1 end
        end
    end
    local function gen_clauses(cls,ci)
        if ci>#cls then return "" end; local cl=cls[ci]
        local function gen_body(b)
            local bc="";local bi=1
            while bi<=#b do local st,c2=gen_stmt(b,bi,ctx);bc=bc..st;bi=bi+c2 end
            return bc
        end
        if cl.kind=="if"or cl.kind=="elseif" then
            local tmp=newtmp();local cv=newtmp()
            local code=("    Value %s=%s;\n    int %s=value_is_truthy(%s);\n    free_value(%s);\n    if(%s){\n"):format(
                tmp,translate_expr(cl.cond),cv,tmp,tmp,cv)
            code=code..gen_body(cl.body)
            if ci<#cls then return code.."    }else{\n"..gen_clauses(cls,ci+1).."    }\n"
            else return code.."    }\n" end
        else return gen_body(cl.body) end
    end
    return gen_clauses(clauses,1),(j-idx)
end

local function gen_for(s,ctx,idx,src)
    local var,se,le,ste=s:match("^for%s+([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.-)%s*,%s*(.-)%s*,%s*(.-)%s+do$")
    if not var then var,se,le=s:match("^for%s+([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.-)%s*,%s*(.-)%s+do$") end
    if not var then return nil end
    local for_body,consumed=collect_block(src,idx+1)
    local sv,lv,stv=newtmp(),newtmp(),newtmp()
    local code=("    Value %s=%s;\n    Value %s=%s;\n    Value %s=%s;\n"):format(
        sv,translate_expr(se),lv,translate_expr(le),stv,ste and translate_expr(ste) or "make_int(1)")
    code=code..("    for(int64_t __i_%s=%s.i;(%s.i>=0?__i_%s<=%s.i:__i_%s>=%s.i);__i_%s+=%s.i){\n"):format(
        var,sv,stv,var,lv,var,lv,var,stv)
    code=code..("        Value %s=make_int(__i_%s);\n"):format(var,var)

    -- snapshot locals so inner-loop locals get freed
    local saved_lv={}
    if ctx.local_vars then for k,v in pairs(ctx.local_vars) do saved_lv[k]=v end end
    local saved_am={}; for k,v in pairs(ctx.assigned) do saved_am[k]=v end

    -- Create a child context that tracks its own new locals, but shares the same local_vars table
    -- so that return statements inside the loop can emit cleanup for loop-body locals.
    -- We track which vars are new inside the loop so we can free them at loop bottom.
    local vars_before={}
    if ctx.local_vars then for k,_ in pairs(ctx.local_vars) do vars_before[k]=true end end

    if ctx.local_vars then ctx.local_vars[var]=true end
    local loop_ctx=ctx
    -- push loop_var onto ctx so return-inside-loop knows to free it
    local old_loop_vars=ctx.loop_vars or {}
    ctx.loop_vars={var}
    setmetatable(ctx.loop_vars,{__index=old_loop_vars})

    local bi=1
    while bi<=#for_body do local st,c2=gen_stmt(for_body,bi,loop_ctx);code=code..st;bi=bi+c2 end

    -- Free any locals declared inside the loop body (but not the loop var itself yet)
    if ctx.local_vars then
        for v,_ in pairs(ctx.local_vars) do
            if not vars_before[v] and v~=var then
                code=code..("        free_value(%s);\n"):format(v)
            end
        end
        ctx.local_vars=saved_lv
        -- Restore the loop var slot (it was in saved_lv if it was declared before the loop,
        -- but as a for-loop var it's re-created each iteration)
        if ctx.local_vars then ctx.local_vars[var]=nil end
    end

    ctx.assigned=saved_am
    ctx.loop_vars=old_loop_vars

    return code..("        free_value(%s);\n    }\n"):format(var)
        ..("    free_value(%s);free_value(%s);free_value(%s);\n"):format(sv,lv,stv), 1+consumed
end

local function try_table_assign(s)
    local tbl,key,rhs=s:match("^([A-Za-z_][A-Za-z0-9_]*)%.([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
    if tbl then return("    table_set(value_copy(%s),make_string(\"%s\"),%s);\n"):format(tbl,escape_c(key),translate_expr(rhs)) end
    local t2,k2,r2=s:match("^([A-Za-z_][A-Za-z0-9_]*)%[(.+)%]%s*=%s*(.+)$")
    if t2 then return("    table_set(value_copy(%s),%s,%s);\n"):format(t2,translate_expr(k2),translate_expr(r2)) end
end

-- ctx fields: is_top, local_vars (nil if top), assigned, globals_tbl
gen_stmt=function(src,idx,ctx)
    local s=trim(src[idx]or""); if s=="" then return "",1 end
    local lv=ctx.local_vars; local am=ctx.assigned; local gt=ctx.globals_tbl

    -- return
    if s=="return" then
        local cleanup=emit_scope_cleanup(ctx)
        if lv then
            return cleanup.."    return make_nil();\n",1
        end
        return cleanup.."    return make_nil();\n",1
    end
    local ret=s:match("^return%s+(.+)$")
    if ret then
        local cleanup=emit_scope_cleanup(ctx)
        if lv then
            local tmp=newtmp()
            -- Evaluate the return expression BEFORE freeing locals
            local code=("    Value %s=%s;\n"):format(tmp,translate_expr(ret))
            code=code..cleanup
            return code..("    return %s;\n"):format(tmp),1
        end
        return cleanup.."    return "..translate_expr(ret)..";\n",1
    end

    -- assert statement
    if s:match("^assert%s*%(") then return gen_assert_stmt(s),1 end

    -- local var decl
    local lname,rhs=s:match("^local%s+([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
    if lname and rhs then
        if lv then lv[lname]=true; return("    Value %s=%s;\n"):format(lname,translate_expr(rhs)),1 end
        gt[lname]=true;am[lname]=true
        return("    free_value(%s);\n    %s=%s;\n"):format(lname,lname,translate_expr(rhs)),1
    end
    local lname2=s:match("^local%s+([A-Za-z_][A-Za-z0-9_]*)$")
    if lname2 then
        if lv then lv[lname2]=true; return("    Value %s=make_nil();\n"):format(lname2),1 end
        gt[lname2]=true;am[lname2]=true;return "",1
    end

    -- print
    local pargs=s:match("^print%s*%((.*)%)$")
    if pargs then return gen_print(pargs),1 end

    -- table assign
    local ta=try_table_assign(s); if ta then return ta,1 end

    -- assignment
    local var,rhs2=s:match("^([A-Za-z_][A-Za-z0-9_]*)%s*=%s*(.+)$")
    if var and rhs2 then
        am[var]=true
        if lv and not lv[var] and not gt[var] then
            lv[var]=true; return("    Value %s=%s;\n"):format(var,translate_expr(rhs2)),1
        end
        local tmp=newtmp()
        return("    Value %s=%s;\n    free_value(%s);\n    %s=%s;\n"):format(tmp,translate_expr(rhs2),var,var,tmp),1
    end

    -- if
    if s:match("^if%s") then return gen_if(s,ctx,idx,src) end

    -- for
    do local fc,consumed=gen_for(s,ctx,idx,src); if fc then return fc,consumed end end

    -- expression statement (call etc)
    if s:match("%(")or s:match("%[")or s:match("%.") then
        local tmp=newtmp()
        return("    Value %s=%s;\n    free_value(%s);\n"):format(tmp,translate_expr(s),tmp),1
    end

    return "    /* unsupported: "..s.." */\n",1
end

-- ---------------------------------------------------------------------------
-- Usage analysis
-- ---------------------------------------------------------------------------
local all_source=table.concat(lines,"\n")
local function src_uses(pat) return all_source:find(pat)~=nil end

local use={}
local U={
    print="print%s*%(",value_len="#[%w_%(\"]",value_concat="%.%.",
    value_add="[%w_%)\"]%s*%+",value_sub="[%w_%)\"]%s*%-[^%-]",
    value_mul="%*",value_div="[^/]/[^/]",value_mod="[%w_%)\"]%s*%%[^%%]",
    value_eq="==",value_neq="~=",value_lt="[^<]<[^=<]",value_gt="[^>]>[^=>]",
    value_le="<=",value_ge=">=",
    value_and="[%)%w_\"]%s+and%s",value_or="[%)%w_\"]%s+or%s",
    value_not="[%(,%s]not%s",table_init="{",table_ops="%.[%a_][%w_]*",
    method_call=":[A-Za-z_]",assert="assert%s*%(",error="error%s*%(",
}
for k,p in pairs(U) do use[k]=src_uses(p) end
use.value_add=use.value_add or src_uses("%+%s*[%w_%(\"']")
use.value_lt=use.value_lt or src_uses("^<[^=]")
use.value_gt=use.value_gt or src_uses("^>[^=]")
use.value_and=use.value_and or src_uses("%sand%s+[%(]")
use.value_or=use.value_or or src_uses("%sor%s+[%(]")
use.value_not=use.value_not or src_uses("^not%s")
use.table_ops=use.table_ops or src_uses("%[")

local math_fns={"abs","floor","ceil","sqrt","sin","cos","tan","asin","acos","atan","atan2",
    "exp","log","log10","sinh","cosh","tanh","deg","rad","pow","fmod","modf","frexp","ldexp","max","min","random","randomseed"}
local used_math={}
for _,fn in ipairs(math_fns) do used_math[fn]=src_uses("math%s*%.%s*"..fn) end
local use_math_pi=src_uses("math%s*%.%s*pi"); local use_math_huge=src_uses("math%s*%.%s*huge")

local os_fns={"clock","time","difftime","date","exit","getenv","execute","remove","rename","tmpname","setlocale"}
local used_os={}
for _,fn in ipairs(os_fns) do used_os[fn]=src_uses("os%s*%.%s*"..fn) end

local io_fns={"write","read","lines","open","close","flush","stdin","stdout","stderr"}
local used_io={}
for _,fn in ipairs(io_fns) do used_io[fn]=src_uses("io%s*%.%s*"..fn) end

if use.value_neq or use.value_le or use.value_ge then use.value_eq=true end
if use.value_le or use.value_ge then use.value_lt=true end
if use.value_gt then use.value_lt=true end

use.math_lib=use_math_pi or use_math_huge
for _,fn in ipairs(math_fns) do if used_math[fn] then use.math_lib=true end end
use.os_lib=false; for _,fn in ipairs(os_fns) do if used_os[fn] then use.os_lib=true end end
use.io_lib=false; for _,fn in ipairs(io_fns) do if used_io[fn] then use.io_lib=true end end
use.prng=used_math.random or used_math.randomseed

use.numval=use.value_add or use.value_sub or use.value_mul or use.value_div
    or use.value_mod or use.value_lt or use.value_gt or use.value_le or use.value_ge or use.value_concat
if use.math_lib then use.numval=true end
if used_os.difftime or used_os.exit or used_os.date then use.numval=true end
use.math_h=use.math_lib or use.value_mod
use.time_h=use.prng or use.os_lib
if used_io.open then use.file_methods=true;use.method_call=true end
if use.method_call then use.table_ops=true end
use.value_call=use.table_ops

local has_tables=use.table_ops or use.table_init or use.math_lib or use.os_lib or use.io_lib

-- ---------------------------------------------------------------------------
-- Emit C
-- ---------------------------------------------------------------------------
local out={}
local function w(s) table.insert(out,s) end
local function wif(c,s) if c then w(s) end end

w("#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <stdint.h>\n#include <stdarg.h>")
wif(use.math_h,"#include <math.h>")
wif(use.time_h,"#include <time.h>")
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

if has_tables then w([[
typedef struct TableEntry{Value key;Value val;int used;}TableEntry;
typedef struct Table{TableEntry*entries;int cap;int len;int refcount;}Table;
#define TBL_INIT_CAP 8
static uint32_t hash_value(Value k){switch(k.t){case T_INT:return(uint32_t)(k.i*2654435761ULL);case T_DOUBLE:{if(k.d==0.0)return 0;uint64_t u;memcpy(&u,&k.d,8);return(uint32_t)(u^(u>>32))*2654435761u;}case T_STRING:return luastr_hash(k.ls);case T_BOOL:return(uint32_t)k.i^0xdeadbeef;default:return 0;}}
static int keys_equal(Value a,Value b){if(a.t!=b.t){if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE)){double da=a.t==T_DOUBLE?a.d:(double)a.i,db=b.t==T_DOUBLE?b.d:(double)b.i;return da==db;}return 0;}switch(a.t){case T_INT:return a.i==b.i;case T_DOUBLE:return a.d==b.d;case T_BOOL:return a.i==b.i;case T_NIL:return 1;case T_STRING:return a.ls==b.ls||strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))==0;case T_TABLE:return a.tbl==b.tbl;default:return 0;}}]]) end

w([[
static void free_value(Value v);
static Value value_copy(Value v);
static int value_is_truthy(Value v);]])

if has_tables then w([[
static Table*table_new(void){Table*t=calloc(1,sizeof(Table));t->cap=TBL_INIT_CAP;t->entries=calloc(t->cap,sizeof(TableEntry));t->refcount=1;return t;}
static void table_free(Table*t){if(!t||--t->refcount>0)return;for(int i=0;i<t->cap;i++)if(t->entries[i].used){free_value(t->entries[i].key);free_value(t->entries[i].val);}free(t->entries);free(t);}
static void table_raw_set(Table*t,Value key,Value val);
static void table_resize(Table*t){int oc=t->cap;TableEntry*old=t->entries;t->cap*=2;t->entries=calloc(t->cap,sizeof(TableEntry));t->len=0;for(int i=0;i<oc;i++)if(old[i].used)table_raw_set(t,old[i].key,old[i].val);free(old);}
static void table_raw_set(Table*t,Value key,Value val){if(t->len*2>=t->cap)table_resize(t);uint32_t h=hash_value(key);int mask=t->cap-1,idx=(int)(h&mask);while(t->entries[idx].used){if(keys_equal(t->entries[idx].key,key)){free_value(t->entries[idx].key);free_value(t->entries[idx].val);t->entries[idx].key=key;t->entries[idx].val=val;return;}idx=(idx+1)&mask;}t->entries[idx].used=1;t->entries[idx].key=key;t->entries[idx].val=val;t->len++;}
static void table_set(Value tbl,Value key,Value val){if(tbl.t!=T_TABLE||!tbl.tbl){free_value(tbl);free_value(key);free_value(val);return;}table_raw_set(tbl.tbl,key,val);free_value(tbl);}
static Value table_get(Value tbl,Value key){if(tbl.t!=T_TABLE||!tbl.tbl){free_value(tbl);free_value(key);return(Value){.t=T_NIL};}Table*t=tbl.tbl;uint32_t h=hash_value(key);int mask=t->cap-1,idx=(int)(h&mask),chk=0;while(t->entries[idx].used&&chk<t->cap){if(keys_equal(t->entries[idx].key,key)){Value r=value_copy(t->entries[idx].val);free_value(tbl);free_value(key);return r;}idx=(idx+1)&mask;chk++;}free_value(tbl);free_value(key);return(Value){.t=T_NIL};}
static Value table_call(Value tbl,Value key,int nargs,...);]]) end

w([[
static inline Value make_int(int64_t x){Value v;v.t=T_INT;v.i=x;return v;}
static inline Value make_double(double x){Value v;v.t=T_DOUBLE;v.d=x;return v;}
static inline Value make_bool(int b){Value v;v.t=T_BOOL;v.i=b?1:0;return v;}
static inline Value make_nil(void){Value v;v.t=T_NIL;v.i=0;return v;}
static Value make_string(const char*s){Value v;v.t=T_STRING;v.ls=s?luastr_new(s,strlen(s)):NULL;return v;}]])
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

wif(use.error or use.assert,[[
static Value lua_error(Value msg){const char*m=(msg.t==T_STRING)?luastr_cstr(msg.ls):"(error object)";fprintf(stderr,"error: %s\n",m);free_value(msg);abort();return make_nil();}]])
wif(use.assert,[[
static Value lua_assert(Value cond,Value msg){if(!value_is_truthy(cond)){const char*m=(msg.t==T_STRING)?luastr_cstr(msg.ls):"assertion failed!";fprintf(stderr,"assertion failed: %s\n",m);free_value(cond);free_value(msg);abort();}free_value(msg);return cond;}]])
wif(use.print,[[
static void print_values(int n,Value*args){size_t cap=256;char*buf=malloc(cap);if(!buf)return;size_t len=0;for(int i=0;i<n;i++){if(i>0){if(len+1>=cap){cap*=2;buf=realloc(buf,cap);if(!buf)return;}buf[len++]='\t';}Value v=args[i];char tmp[64];const char*s=NULL;size_t slen=0;switch(v.t){case T_INT:slen=(size_t)snprintf(tmp,sizeof tmp,"%lld",(long long)v.i);s=tmp;break;case T_DOUBLE:slen=(size_t)snprintf(tmp,sizeof tmp,"%g",v.d);s=tmp;break;case T_STRING:s=luastr_cstr(v.ls);slen=strlen(s);break;case T_BOOL:s=v.i?"true":"false";slen=v.i?4u:5u;break;case T_NIL:s="nil";slen=3;break;case T_TABLE:slen=(size_t)snprintf(tmp,sizeof tmp,"table:%p",(void*)v.tbl);s=tmp;break;case T_FUNC:slen=(size_t)snprintf(tmp,sizeof tmp,"function:%p",(void*)(size_t)v.fn);s=tmp;break;case T_FILE:slen=(size_t)snprintf(tmp,sizeof tmp,"file:%p",(void*)v.file);s=tmp;break;default:s="";slen=0;break;}if(len+slen+1>=cap){while(len+slen+1>=cap)cap*=2;buf=realloc(buf,cap);if(!buf)return;}if(slen>0)memcpy(buf+len,s,slen);len+=slen;}if(len+1>=cap){cap=len+1;buf=realloc(buf,cap);if(!buf)return;}buf[len++]='\n';fwrite(buf,1,len,stdout);free(buf);for(int i=0;i<n;i++)free_value(args[i]);}]])

if has_tables then w([[
static Value table_call(Value tbl,Value key,int nargs,...){Value fn=table_get(value_copy(tbl),value_copy(key));free_value(tbl);free_value(key);Value stack_args[8];Value*args=nargs>0?(nargs<=8?stack_args:malloc(nargs*sizeof(Value))):NULL;va_list ap;va_start(ap,nargs);for(int i=0;i<nargs;i++)args[i]=va_arg(ap,Value);va_end(ap);Value r;if(fn.t==T_FUNC&&fn.fn){r=fn.fn(nargs,args);}else{for(int i=0;i<nargs;i++)free_value(args[i]);r=make_nil();}free_value(fn);if(nargs>8&&args)free(args);return r;}]]) end
wif(use.value_call,[[
static Value value_call(Value fn,int nargs,...){Value stack_args[8];Value*args=nargs>0?(nargs<=8?stack_args:malloc(nargs*sizeof(Value))):NULL;va_list ap;va_start(ap,nargs);for(int i=0;i<nargs;i++)args[i]=va_arg(ap,Value);va_end(ap);Value r;if(fn.t==T_FUNC&&fn.fn){r=fn.fn(nargs,args);}else{for(int i=0;i<nargs;i++)free_value(args[i]);r=make_nil();}free_value(fn);if(nargs>8&&args)free(args);return r;}]])
-- FIX: value_method_call was malloc'ing args but never freeing the buffer on error path,
-- and always leaked the malloc'd array (used free(args) but only after fn call, not on
-- non-func path). Fixed: always free(args) at end, use stack buffer for small arg counts.
wif(use.method_call,[[
static Value value_method_call(Value self,const char*method,int nargs,...){Value key=make_string(method);Value fn=table_get(value_copy(self),key);int total=nargs+1;Value stack_args[9];Value*args=total<=9?stack_args:malloc(total*sizeof(Value));args[0]=self;va_list ap;va_start(ap,nargs);for(int i=0;i<nargs;i++)args[i+1]=va_arg(ap,Value);va_end(ap);Value r;if(fn.t==T_FUNC&&fn.fn){r=fn.fn(total,args);}else{for(int i=0;i<total;i++)free_value(args[i]);r=make_nil();}free_value(fn);if(total>9)free(args);return r;}]])

w("\n/* Operator helpers */")
wif(use.value_len,"static Value value_len(Value v){Value r;if(v.t==T_STRING)r=make_int(v.ls?(int64_t)strlen(v.ls->data):0);else if(v.t==T_TABLE&&v.tbl)r=make_int(v.tbl->len);else r=make_int(0);free_value(v);return r;}")
-- FIX: value_concat - guard against NULL as/bs to avoid writing nothing but still allocating
wif(use.value_concat,[[
static Value value_concat(Value a,Value b){char abuf[64],bbuf[64];const char*as=NULL;const char*bs=NULL;if(a.t==T_STRING)as=luastr_cstr(a.ls);else if(a.t==T_INT){snprintf(abuf,sizeof abuf,"%lld",(long long)a.i);as=abuf;}else if(a.t==T_DOUBLE){snprintf(abuf,sizeof abuf,"%g",a.d);as=abuf;}if(b.t==T_STRING)bs=luastr_cstr(b.ls);else if(b.t==T_INT){snprintf(bbuf,sizeof bbuf,"%lld",(long long)b.i);bs=bbuf;}else if(b.t==T_DOUBLE){snprintf(bbuf,sizeof bbuf,"%g",b.d);bs=bbuf;}size_t la=as?strlen(as):0,lb=bs?strlen(bs):0;LuaStr*ls=luastr_new(NULL,la+lb);if(la>0&&as)memcpy(ls->data,as,la);if(lb>0&&bs)memcpy(ls->data+la,bs,lb);free_value(a);free_value(b);Value r;r.t=T_STRING;r.ls=ls;return r;}]])
wif(use.numval,"static double numval(Value v){return v.t==T_DOUBLE?v.d:(double)v.i;}")
wif(use.value_add,"static Value value_add(Value a,Value b){Value r=(a.t==T_INT&&b.t==T_INT)?make_int(a.i+b.i):make_double(numval(a)+numval(b));free_value(a);free_value(b);return r;}")
wif(use.value_sub,"static Value value_sub(Value a,Value b){Value r=(a.t==T_INT&&b.t==T_INT)?make_int(a.i-b.i):make_double(numval(a)-numval(b));free_value(a);free_value(b);return r;}")
wif(use.value_mul,"static Value value_mul(Value a,Value b){Value r=(a.t==T_INT&&b.t==T_INT)?make_int(a.i*b.i):make_double(numval(a)*numval(b));free_value(a);free_value(b);return r;}")
wif(use.value_div,"static Value value_div(Value a,Value b){double r=numval(a)/numval(b);free_value(a);free_value(b);return make_double(r);}")
wif(use.value_mod,"static Value value_mod(Value a,Value b){Value r;double da=numval(a),db=numval(b);if(a.t==T_INT&&b.t==T_INT&&b.i!=0)r=make_int(((a.i%b.i)+b.i)%b.i);else r=make_double(da-floor(da/db)*db);free_value(a);free_value(b);return r;}")
wif(use.value_eq,"static Value value_eq(Value a,Value b){int eq;if(a.t==T_NIL&&b.t==T_NIL)eq=1;else if(a.t==T_NIL||b.t==T_NIL)eq=0;else if(a.t==b.t){if(a.t==T_INT)eq=(a.i==b.i);else if(a.t==T_DOUBLE)eq=(a.d==b.d);else if(a.t==T_STRING)eq=(a.ls==b.ls||strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))==0);else if(a.t==T_BOOL)eq=(a.i==b.i);else if(a.t==T_TABLE)eq=(a.tbl==b.tbl);else eq=0;}else if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE))eq=(numval(a)==numval(b));else eq=0;free_value(a);free_value(b);return make_bool(eq);}")
wif(use.value_neq,"static Value value_neq(Value a,Value b){Value r=value_eq(a,b);int v=!value_is_truthy(r);free_value(r);return make_bool(v);}")
wif(use.value_lt,"static Value value_lt(Value a,Value b){int lt;if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE))lt=(numval(a)<numval(b));else if(a.t==T_STRING&&b.t==T_STRING)lt=(strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))<0);else lt=0;free_value(a);free_value(b);return make_bool(lt);}")
wif(use.value_gt,"static Value value_gt(Value a,Value b){return value_lt(b,a);}")
-- FIX: value_le - old version made a2/b2 copies then passed originals to value_lt which freed them,
-- then if not lt, called value_eq(a2,b2) which freed the copies. That is correct but convoluted.
-- Simpler and cleaner: use value_lt then value_eq on fresh copies, no manual copy juggling.
wif(use.value_le,[[
static Value value_le(Value a,Value b){int lt;if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE))lt=(numval(a)<=numval(b));else if(a.t==T_STRING&&b.t==T_STRING)lt=(strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))<=0);else lt=0;free_value(a);free_value(b);return make_bool(lt);}]])
wif(use.value_ge,[[
static Value value_ge(Value a,Value b){int ge;if((a.t==T_INT||a.t==T_DOUBLE)&&(b.t==T_INT||b.t==T_DOUBLE))ge=(numval(a)>=numval(b));else if(a.t==T_STRING&&b.t==T_STRING)ge=(strcmp(luastr_cstr(a.ls),luastr_cstr(b.ls))>=0);else ge=0;free_value(a);free_value(b);return make_bool(ge);}]])
-- FIX: value_and/value_or - old version freed both args but returned a plain bool, which is wrong
-- for Lua semantics (Lua 'and'/'or' return one of the operands, not a bool). However since we
-- eagerly evaluate both sides before calling, we can't truly short-circuit. We fix the semantics:
-- 'and' returns the first falsy value, or the last value if all truthy.
-- 'or'  returns the first truthy value, or the last value if all falsy.
-- This also eliminates the leak where the returned operand was being freed before return.
wif(use.value_and,[[
static Value value_and(Value a,Value b){if(!value_is_truthy(a)){free_value(b);return a;}free_value(a);return b;}]])
wif(use.value_or,[[
static Value value_or(Value a,Value b){if(value_is_truthy(a)){free_value(b);return a;}free_value(a);return b;}]])
wif(use.value_not,"static Value value_not(Value a){int r=!value_is_truthy(a);free_value(a);return make_bool(r);}")

-- Math library
if use.math_lib then
    w("\n/* math */")
    wif(use.prng,"static uint64_t prng_state=0;")
    w("#define M1(name,expr) static Value lua_math_##name(int n,Value*a){double x=numval(a[0]);free_value(a[0]);return make_double(expr);}");
    w("#define M2(name,expr) static Value lua_math_##name(int n,Value*a){double x=numval(a[0]),y=numval(a[1]);free_value(a[0]);free_value(a[1]);return make_double(expr);}")
    local m1={abs="fabs(x)",floor="floor(x)",ceil="ceil(x)",sqrt="sqrt(x)",sin="sin(x)",cos="cos(x)",tan="tan(x)",
        asin="asin(x)",acos="acos(x)",atan="atan(x)",exp="exp(x)",log="log(x)",log10="log10(x)",
        sinh="sinh(x)",cosh="cosh(x)",tanh="tanh(x)",deg="x*(180.0/3.14159265358979323846)",rad="x*(3.14159265358979323846/180.0)"}
    local m2={atan2="atan2(x,y)",pow="pow(x,y)",fmod="fmod(x,y)"}
    for _,fn in ipairs(math_fns) do if used_math[fn] then
        if m1[fn] then w(("M1(%s,%s)"):format(fn,m1[fn]))
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
    -- shared read-line helper macro
    w("#define READ_LINE(F,DEST,FAIL_EXPR) do{size_t cap=256,len=0;char*buf=malloc(cap);int c;while((c=fgetc(F))!=EOF&&c!='\\n'){if(len+1>=cap){cap*=2;buf=realloc(buf,cap);}buf[len++]=(char)c;}if(c==EOF&&len==0){free(buf);FAIL_EXPR;}buf[len]='\\0';DEST=make_string(buf);free(buf);}while(0)")
    w("#define READ_ALL(F,DEST) do{size_t cap=256,len=0;char*buf=malloc(cap);int c;while((c=fgetc(F))!=EOF){if(len+1>=cap){cap*=2;buf=realloc(buf,cap);}buf[len++]=(char)c;}buf[len]='\\0';DEST=make_string(buf);free(buf);}while(0)")
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
for name,_ in pairs(globals) do w("static Value "..name..";") end
wif(use.math_lib,"static Value math;")
wif(use.os_lib,"static Value os;")
wif(use.io_lib,"static Value io;")
w("")

-- User-defined functions
for _,fn in ipairs(functions) do
    local fname=fn.name; local args=trim(fn.args)
    local local_vars={}
    local tp,mn=fname:match("^(.+)__([^_].*)$")
    if not tp then tp,mn=fname:match("^(.+)__(_+.*)$") end
    if tp and mn then
        w(("static Value %s(int __nargs,Value*__args){"):format(fname))
        local ai=0
        for a in (args..","):gmatch("(.-),") do a=trim(a); if #a>0 then
            w(("    Value %s=__nargs>%d?value_copy(__args[%d]):make_nil();"):format(a,ai,ai))
            local_vars[a]=true; ai=ai+1 end end
    else
        local arglist={}
        for a in (args..","):gmatch("(.-),") do a=trim(a); if #a>0 then
            table.insert(arglist,"Value "..a); local_vars[a]=true end end
        w(("Value %s(%s){"):format(fname,table.concat(arglist,",")))
    end
    local ctx={local_vars=local_vars,assigned={},globals_tbl=globals}
    local bi=1
    while bi<=#fn.body do local stmt,consumed=gen_stmt(fn.body,bi,ctx);w(stmt);bi=bi+consumed end
    -- Only free locals that weren't freed by a return statement
    -- (emit_scope_cleanup handles locals on return paths; here we handle fall-through)
    for v,_ in pairs(local_vars) do w(("    free_value(%s);"):format(v)) end
    w("    return make_nil();\n}\n")
end

-- main()
w("int main(void){")
for name,_ in pairs(globals) do w("    "..name.."=make_nil();") end
wif(use.math_lib,"    math=make_math_table();")
wif(use.os_lib,"    os=make_os_table();")
wif(use.io_lib,"    io=make_io_table();")

local method_registry={}
for _,fn in ipairs(functions) do
    local tp,mn=fn.name:match("^(.+)__([^_].*)$")
    if not tp then tp,mn=fn.name:match("^(.+)__(_+.*)$") end
    if tp and mn then
        if not method_registry[tp] then method_registry[tp]={} end
        table.insert(method_registry[tp],{meth=mn,fname=fn.name})
    end
end
w("")

local assigned_map={}; local ti=1
local ctx_top={local_vars=nil,assigned=assigned_map,globals_tbl=globals}
while ti<=#topstmts do
    local stmt,consumed=gen_stmt(topstmts,ti,ctx_top); w(stmt)
    local av=trim(topstmts[ti]or""):match("^([A-Za-z_][A-Za-z0-9_]*)%s*=")
    if av and method_registry[av] then
        for _,m in ipairs(method_registry[av]) do
            w(('    table_raw_set(%s.tbl,make_string("%s"),make_func(%s));'):format(av,m.meth,m.fname)) end
        method_registry[av]=nil
    end
    ti=ti+consumed
end
for tbl_name,methods in pairs(method_registry) do
    for _,m in ipairs(methods) do
        w(('    table_raw_set(%s.tbl,make_string("%s"),make_func(%s));'):format(tbl_name,m.meth,m.fname)) end
end

w("\n    /* cleanup */")
for name,_ in pairs(globals) do w("    free_value("..name..");") end
wif(use.math_lib,"    free_value(math);")
wif(use.os_lib,"    free_value(os);")
wif(use.io_lib,"    free_value(io);")
w("    return 0;\n}")

local f=assert(io.open(output_path,"w"))
f:write(table.concat(out,"\n"))
f:close()
print("Wrote "..output_path)


