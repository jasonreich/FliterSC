{

main = let {x = 4} in fib x;
  
fib n = let { one = 1; two = 2 } in (case (n <= one) of {
          True  -> 1;
          False -> let { nm1 = n - one; nm2 = n - two } 
                   in (let { fibnm1 = fib nm1; fibnm2 = fib nm2 } 
                       in fibnm1 + fibnm2)
        })

}
