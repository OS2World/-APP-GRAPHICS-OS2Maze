set include=d:\user\msc\include
set lib=d:\user\msc\lib
set tmp=d:\user\msc\work
cl /AL /W3 /Gt /Zp /Lp -c os2maze.c
link /STACK:8000 os2maze.obj,os2maze.exe,,c:\os2\doscalls.lib,os2maze.def
