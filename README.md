An example from this slide  
https://www.slideshare.net/sakai/how-a-cdcl-sat-solver-works  

in.txt
```
p cnf 9 7  
-1 -4 5 0  
-4 6 0  
-5 -6 7 0  
-7 8 0  
-2 -7 9 0  
-8 -9 0  
-8 9 0  
```
terminal

```
$ make sat
$ ./sat
1
[1, 2, 3, -4, 5, -6, -7, -8, 9]
```

