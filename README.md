F-liter Supercompiler
=====================

*Debug variant.*

A reimplementation of the Bollingbroke & Peyton-Jones (2010) compiler
for the F-liter language in an attempt to understand it
better. Currently packaged as a library and as is. 

Try;
<pre>
$ ghci Supercompiler
λ> ex_mapmap
main  = let x = Nil
        in sc x
sc x = let y = inc
       in
          let z = map y x
          in map y z
map x y = case y of
            Nil  -> Nil
            Cons z p -> let
                            q = x z
                            r = map x p
                        in Cons q r
inc x = let y = 1
        in x + y
λ> sc_wrapper ex_mapmap ("sc", lam "xs" $ fun "sc" @: "xs")
...
</pre>

It will supercompile the function `sc` of program `ex_mapmap` with an
unknown input. 


Extra debug features
--------------------

To aid debugging, the `Debug.RocketFuel` library prematurely
terminates supercompilation when a predetermined "fuel" supply
is depleted. This a very unsafe implementation of the concept
introduced in Whalley's (1994) *Automatic isolation of compiler
errors.*

By default, the fuel tank is infinite (i.e. `Nothing`).

*  `fuelTank` is a global variable.
*  `disableTank` creates infinite fuel.
*  `fillTank n` creates a finite pool of `n` units of fuel.
*  `consumeFuel empty full` will consume 1 unit of fuel. If the tank
   is depleted, it returns `empty`, otherwise `full`.
*  `readTank` returns the fuel tank value.
