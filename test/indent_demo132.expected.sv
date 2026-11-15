int reimport_function; function void foo();
  x = 1;
endfunction
y = 2;
myimport = 1; function void foo2();
  x = 1;
endfunction
y = 2;
imported = 1; task run();
  x = 1;
endtask
y = 2;
myexport = 1; function void foo3();
  x = 1;
endfunction
y = 2;
importer = 1; function void foo4();
  x = 1;
endfunction
y = 2;
reimport = 1; function void foo5();
  x = 1;
endfunction
y = 2;
