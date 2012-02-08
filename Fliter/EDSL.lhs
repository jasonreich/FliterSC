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
> letIn bs x = tag $ Let (map snd bs) (abstract' (map fst bs) x)
> (=:) = (,)
> caseOf x as = tag $ Case x as
> (-->) p y = (c, length vs) :-> abstract' vs y
>   where (c:vs) = words p
> lam p x = Lam (length vs) (abstract' vs x)
>   where vs = words p                   
> 
> infix 8 =:
> infix 8 -->
>   
> instance IsString (Expr () String) where
>   fromString xs@(x:_) | isLower x = var xs
>                       | otherwise = con xs
> 
> example = Prog
>  [ lam "" $ letIn ["inc" =: fun 2, "xs" =: "Nil"]
>               $ letIn ["xs'" =: fun 1 @: "inc xs"]
>                 $ fun 1 @: "inc xs'"
>  , lam "f x" $ caseOf "x"
>      [ "Nil"       --> "Nil" 
>      , "Cons x xs" --> letIn [ "x'"  =:  "f" @: "x"
>                              , "xs'" =: fun 1 @: "f xs" ]
>                        ("Cons" @: "x' xs'") ]
>  , lam "m" $ letIn [ "one" =: pVa 1 ] $ "m" +$ "one" ]
>  
> 
