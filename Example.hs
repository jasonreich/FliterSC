{-# LANGUAGE OverloadedStrings #-}
module Example where

import Fliter.EDSL
import Fliter.Syntax

ex_mapmap = Prog
  [ lam "" $ letIn ["input" =: con "Nil"] (fun 1 @: "input")
  , lam "xs" $ letIn ["inc" =: fun 3]
               $ letIn ["xs'" =: fun 2 @: "inc xs"]
                 $ fun 2 @: "inc xs'"
  , lam "f x" $ caseOf "x"
      [ "Nil"       --> "Nil" 
      , "Cons x xs" --> letIn [ "x'"  =:  "f" @: "x"
                              , "xs'" =: fun 2 @: "f xs" ]
                        ("Cons" @: "x' xs'") ]
  , lam "m" $ letIn [ "one" =: pVa 1 ] $ "m" +$ "one" ]