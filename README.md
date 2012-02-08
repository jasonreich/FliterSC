F-liter Supercompiler
=====================

A reimplementation of the Bollingbroke & Peyton-Jones (2010) compiler
for the F-liter language in an attempt to understand it
better. Currently packaged as a library and as is. 

Try;
```
$ ghci Supercompiler
λ> example'

f0 x = let y = f2
       in
          let z = f1 y x
          in f1 y z
f1 x y = case y of
           Nil  -> Nil
           Cons z p -> let
                           q = x z
                           r = f1 x p
                       in Cons q r
f2 x = let y = 1
       in x + y

λ> sc example' (lam "xs" $ fun 0 @: "xs") 0
...
```

It will supercompiler the function `f0` of program `example'` with an
unknown input. 
