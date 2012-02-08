F-liter Supercompiler
=====================

A reimplementation of the Bollingbroke & Peyton-Jones (2010) compiler
for the F-liter language in an attempt to understand it
better. Currently packaged as a library and as is. 

Try;
<pre>
$ ghci Supercompiler
λ> ex_mapmap
f0  = let x = Nil
      in f1 x
f1 x = let y = f3
       in
          let z = f2 y x
          in f2 y z
f2 x y = case y of
           Nil  -> Nil
           Cons z p -> let
                           q = x z
                           r = f2 x p
                       in Cons q r
f3 x = let y = 1
       in x + y
λ> sc ex_mapmap (lam "xs" $ fun 1 @: "xs") 1
...
</pre>

It will supercompiler the function `f0` of program `ex_mapmap` with an
unknown input. 
