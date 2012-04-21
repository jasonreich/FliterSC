{
and x y = case x of
  { False -> False
  ; True  -> y };
  
head xs = case xs of
  { Cons y ys -> y };

map f xs = case xs of
  { Nil -> Nil
  ; Cons y ys -> Cons (f y) (map f ys) };

append xs zs = case xs of
  { Nil -> zs
  ; Cons y ys -> Cons y (append ys zs) };

concatMap f xs = case xs of
  { Nil -> Nil
  ; Cons y ys -> append (f y) (concatMap f ys) };

filter p xs = case xs of
  { Nil -> Nil
  ; Cons y ys -> case p y of
                 { True -> Cons y (filter p ys) 
                 ; False -> filter p ys } };
  
place x xs = case xs of
  { Nil -> Cons (Cons x Nil) Nil
  ; Cons y ys -> Cons (Cons x (Cons y ys)) (map (Cons y) (place x ys)) };


perm ys = case ys of
  { Nil -> Cons Nil Nil
  ; Cons x xs -> concatMap (place x) (perm xs) };

permSort xs = head (filter ord (perm xs));

ord xs = case xs of
 { Nil -> True
 ; Cons x ys -> case ys of 
     { Nil -> True
     ; Cons y zs -> and (x <= y) (ord (Cons y zs)) } };

main = head (permSort (Cons 10 (Cons 5 (Cons 8 (Cons 7 Nil)))))

}
