{-# LANGUAGE OverloadedStrings #-}
module Example where

import Fliter.EDSL
import Fliter.Syntax

ex_mapmap = Prog
  [ func "main" $ letIn ["input" =: con "Nil"] (fun "sc" @: "input")
  , func "sc xs" $ letIn ["inc'" =: fun "inc"]
               $ letIn ["xs'" =: fun "map" @: "inc' xs"]
                 $ fun "map" @: "inc' xs'"
  , func "map f x" $ caseOf "x"
      [ "Nil"       --> "Nil" 
      , "Cons x xs" --> letIn [ "x'"  =:  "f" @: "x"
                              , "xs'" =: fun "map" @: "f xs" ]
                        ("Cons" @: "x' xs'") ]
  , func "inc m" $ letIn [ "one" =: pVa 1 ] $ "m" +$ "one" ]