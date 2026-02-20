# LuaToC
Made by macsipac, a Lua to C transpiler.  
Please report all issues in well, the github issues tab!  
(this is a re-implementation of lua! not all lua code is guaranteed to work with this)  
How to use:  
1. If you did not already, install lua (luajit works best!)  
2. Download the transpiler.lua file  
3. Make a lua script. This will be turned into C  
4. Run lua transpiler.lua [your .lua script path, by default ./input.lua]  
5. Output.c will be generated, if nothing went wrong it should be able to be compiled!  
Heres a MinGW64 command to compile output.c with max optimization:  
gcc -O3 -march=native -flto -o output output.c  
