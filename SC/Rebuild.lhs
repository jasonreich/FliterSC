> module SC.Rebuild where
> 
> import Control.Arrow (first)
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> 
> import Fliter.Semantics
> import Fliter.Syntax
> 
> splitFree :: [HP] -> [(HP, Expr () HP)] -> ([(HP, Expr () HP)], [(HP, Expr () HP)])
> splitFree vs [] = ([], [])
> splitFree vs ((v,x):xs) 
>   | any (`Set.member` freeVars x) vs = ([], (v,x):xs)
>   | otherwise = first ((v,x):) $ splitFree (v:vs) xs
> 
> mkLet [] y = y
> mkLet xs y = () :> Let xs y
> 
> rebuildHeap :: Heap () -> Expr () HP -> Expr () HP
> rebuildHeap h fcs = rb [ (v, x) | (v, Just x) <- Map.toAscList h 
>                                 , v `Set.member` acc ] [] fcs
>   where acc = accessible h fcs
>         rb :: [(HP, Expr () HP)] -> [HP] -> Expr () HP -> Expr () HP
>         rb [] rho y = abstract' rho y
>         rb h  rho y = mkLet (map (abstract' rho) ls) (rb xs (vs ++ rho) y)
>           where (bs, xs) = splitFree [] h
>                 free = Set.unions $ map freeVars (y:map snd xs)
>                 (vs, ls) = unzip $ filter ((`Set.member` free) . fst) bs
> 
> rebuildStack :: State () -> Expr () HP
> rebuildStack s = case stack s of
>   [] -> rebuildHeap (heap s) (focus s)
>   (Upd v : stk) -> rebuildStack $ S { heap = Map.insert v (Just $ focus s) (heap s)
>                                     , focus = () :> Var (Fre v), stack = stk }
>   (App vs : stk) -> rebuildStack $ s { focus = () :> (focus s :@ map Fre vs), stack = stk }
>   (Cas as : stk) -> rebuildStack $ s { focus = () :> Case (focus s) as, stack = stk }
>   (PrL o w : stk) -> rebuildStack $ s { focus = () :> Let [focus s] (() :> POp o (Bnd 0) (Fre w)), stack = stk }
>   (PrR o m : stk) -> rebuildStack $ s { focus = () :> Let [() :> PVa m, focus s] (() :> POp o (Bnd 0) (Bnd 1)), stack = stk }
