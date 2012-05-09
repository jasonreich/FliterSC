> {-# LANGUAGE OverloadedStrings, FlexibleInstances, TypeSynonymInstances #-}
> module Fliter.EDSL where
> 
> import Fliter.Pretty
> import Fliter.Syntax
> 
> import Data.Char
> import GHC.Exts( IsString(..) )
> 
> tag  = (:>) ()
> 
> mkApp x [] = x
> mkApp x ys = tag $ x :@ ys
> mkLet [] y = y
> mkLet xs y = tag $ Let xs y
               
> var  = tag . Var . Fre
> fun  = tag . flip Fun []
> con  = tag . flip Con []
> pVa  = tag . PVa
> (+$) v w = tag $ POp Pl (Fre v) (Fre w)
> (-$) v w = tag $ POp Mi (Fre v) (Fre w)
> (==$) v w = tag $ POp Eq (Fre v) (Fre w)
> (<=$) v w = tag $ POp Le (Fre v) (Fre w)
> (/=$) v w = tag $ POp Ne (Fre v) (Fre w)
> seqq v w = tag $ POp Seq (Fre v) (Fre w)
> x @: vs = tag $ x :@ map Fre (words vs)
> letIn bs x = tag $ Let (map snd bs) (open (map fst bs) x)
> (=:) = (,)
> caseOf x as = tag $ Case x as
> (-->) p y = (c, length vs) :-> open vs y
>   where (c:vs) = words p
> lam p x = Lam (length vs) (open vs x)
>   where vs = words p        
> func p x = (f, Lam (length vs) (open vs x))
>   where (f:vs) = words p
> 
> infix 8 =:
> infix 8 -->
>   
> instance IsString (Expr () String) where
>   fromString xs@(x:_) | isLower x = var xs
>                       | otherwise = con xs
> 
> example = Prog
>  [ func "main" $ letIn ["inc'" =: fun "inc", "xs" =: "Nil"]
>               $ letIn ["xs'" =: fun "map" @: "inc' xs"]
>                 $ fun "map" @: "inc' xs'"
>  , func "map f x" $ caseOf "x"
>      [ "Nil"       --> "Nil" 
>      , "Cons x xs" --> letIn [ "x'"  =:  "f" @: "x"
>                              , "xs'" =: fun "map" @: "f xs" ]
>                        ("Cons" @: "x' xs'") ]
>  , func "inc m" $ letIn [ "one" =: pVa 1 ] $ "m" +$ "one" ]
>  
> 
> isFre (_ :> (Var (Fre v))) = True
> isFre _ = False
>
> app x ys = mkLet non_vs $ mkApp x ys'
>  where non_vs = [ y | y <- ys, not (isFre y) ]
>        ys' = aux 0 ys
>        aux i [] = []
>        aux i (_ :> Var (Fre v):ys) = Fre v : aux i ys
>        aux i (_:ys) = Bnd i : aux (i + 1) ys

> example' = Prog
>  [ func "main" $ letIn ["inc'" =: fun "inc", "xs" =: "Nil"]
>               $ letIn ["xs'" =: fun "map" @: "inc' xs"]
>                 $ fun "map" @: "inc' xs'"
>  , func "map f x" $ caseOf "x"
>      [ "Nil"       --> "Nil" 
>      , "Cons x xs" --> ("Cons" `app` ["f" @: "x", fun "map" @: "f xs"] ) ]
>  , func "inc m" $ letIn [ "one" =: pVa 1 ] $ "m" +$ "one" ]