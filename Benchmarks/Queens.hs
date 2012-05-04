{
and x y = case x of {
  False -> False;
  True  -> y };

map f v0 = case v0 of {
  Nil       -> Nil;
  Cons x xs -> Cons (f x) (map f xs) };

append v0 ys = case v0 of {
  Nil       -> ys;
  Cons x xs -> Cons x (append xs ys) };

concatMap f v0 = case v0 of {
  Nil       -> Nil;
  Cons x xs -> append (f x) (concatMap f xs) };

length xs = lengthAcc 0 xs;

lengthAcc acc v0 = case v0 of {
  Nil       -> acc;
  Cons x xs -> let { one = 1 } in lengthAcc (one + acc) xs };

gen nq n = let {zero = 0; one = 1} in
  case (n == zero) of {
    True -> Cons Nil Nil;
    False -> concatMap (gen1 nq) (gen nq (n - one))
  };

gen1 nq b = concatMap (gen2 b) (toOne nq);

gen2 b q = case safe q 1 b of {
             True -> Cons (Cons q b) Nil;
             False -> Nil
           };

safe x d v0 = let {one = 1} in case v0 of {
  Nil -> True;
  Cons q l ->
    let {qpd = (q + d); qmd = (q - d) } in
  and (x /= q) (
  and (x /= qpd) (
  and (x /= qmd) (
  safe x (d + one) l))) };

toOne n = let {one = 1} in (case (n == one) of {
            True -> Cons 1 Nil;
            False -> Cons n (toOne (n - one))
          });
  
nsoln nq = length (gen nq nq);

main = nsoln 5

}
