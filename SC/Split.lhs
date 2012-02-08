FliterSC: Splitter
==================

> {-# LANGUAGE TupleSections, ParallelListComp #-}
> module SC.Split where

The splitter takes a state and returns a list of further states to
supercompile and a function to reconstruct an equivalent expression
based on the result of those supercompilations.

Imports
-------

Nothing too tricky here. See the root `Supercompilation` module
for more info about any of these.

> import Control.Arrow (first)
> import Control.Monad
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> 
> import Fliter.Semantics
> import Fliter.Syntax

Brackets
--------

The bracket notation is used by Bollingbroke (2010) and Mitchell 
(2009). If states have the form `⟨ HEAP , FOCUS , STACK ⟩` then a
Bracket, `⟦ f ⟨Γ₀ , X₀ , S₀⟩ ⟨Γ₁ , X₁ , S₁⟩ ⟧` represents two states 
(holes) to be further supercompiled and a context that would apply `f`
to the results of those supercompilations.

> data Bracket t = B { holes   :: [State t]
>                    , context :: [Expr () HP] -> Expr () HP }
> 
> instance Show (Bracket t) where
>   show (B hls ctx) = "B\n" ++ unlines (map show hls) ++
>                      show (ctx [ undefined :> 
>                                  Con ("<" ++ show i ++ ">") []
>                                | i <- [0..]])

Utility functions
-----------------

Make a new let only if we're binding to something.

> mkLet [] y = y
> mkLet xs y = () :> Let xs y

Rebuilding
----------

> rebuildHeap :: Heap () -> Expr () HP -> Expr () HP
> rebuildHeap h fcs = rb [ (v, x) | (v, Just x) <- Map.toAscList h 
>                                 , v `Set.member` acc ] [] fcs
>   where acc = accessible h fcs
>         rb :: [(HP, Expr () HP)] -> [HP] -> Expr () HP -> Expr () HP
>         rb [] rho y = abstract' rho y
>         rb h  rho y = mkLet (map (abstract' rho) ls) (rb xs (vs ++ rho) y)
>           where (bs, xs) = spanHeap [] h
>                 free = Set.unions $ map freeVars (y:map snd xs)
>                 (vs, ls) = unzip $ filter ((`Set.member` free) . fst) bs

Split an ordered heap such that none of the bindings on the left refer
to each other.

> spanHeap :: [HP] -> [(HP, Expr () HP)] 
>           -> ([(HP, Expr () HP)], [(HP, Expr () HP)])
> spanHeap vs [] = ([], [])
> spanHeap vs ((v,x):xs) 
>   | any (`Set.member` freeVars x) vs = ([], (v,x):xs)
>   | otherwise = first ((v,x):) $ spanHeap (v:vs) xs

Splitting
---------

> splitApp :: State t -> Bracket t
> splitApp s = case focus s of
>   t :> Var (Fre v)    -> splitStack [v] s
>   t :> Fun f vs@(_:_) -> splitStack [] $ s { focus = t :> Fun f []
>                                            , stack = App vs : stack s }
>   t :> Con c vs@(_:_) -> splitStack [] $ s { focus = t :> Con c []
>                                            , stack = App vs : stack s  }
>   t :> POp _ v w      -> badSplitApp [x | Fre x <- [v,w]] (heap s)
>                          $ splitStack [] $ wipe [x | Fre x <- [v,w]] s
>   _                   -> splitStack [] s
> 
> 
> wipe :: [HP] -> State t -> State t
> wipe vs s = s { heap = inserts (heap s) (map (, Nothing) vs) }
> 
> splitStack :: [HP] -> State t -> Bracket t
> splitStack vs s = case stack s of
>   []              -> B [] $ \_ -> rebuildHeap (heap s') (focus s')
>     where s' = deTagSt s
>   (Upd v  : stk)  -> splitStack (v:vs) $ s { stack = stk }
>   -- Drive on the vs too
>   (App vs : stk)  -> badSplitApp vs (heap s) $ splitStack []
>                      $ wipe vs $ s { focus = t :> (focus s :@ map Fre vs) 
>                                    , stack = stk }
>   (Cas as : stk)  -> splitAlts vs (heap s) (focus s) stk as
>   -- Drive on the w too
>   (PrL o w : stk) -> badSplitApp [w] (heap s)
>                      $ splitStack [] $ wipe [w] $
>                      s { focus = t :> Let [focus s] (t :> POp o (Bnd 0) (Fre w)), stack = stk }
>   (PrR o m : stk) -> splitStack [] $
>                      s { focus = t :> Let [t :> PVa m, focus s] 
>                                        (t :> POp o (Bnd 0) (Bnd 1))
>                        , stack = stk }
>   where t = getTag $ focus s
> 
> splitAlts :: [HP] -> Heap t -> Expr t HP -> Stack t -> [Alte t HP] -> Bracket t
> splitAlts vs h fcs stk as = B hls ctx
>   where nxthps = (nextHPs . nextKey) h
>         hls = [ gc $ S (inserts h $ map (, Nothing) ws ++ map (, Just x) vs)
>                        (instantiate' ws y) stk
>               | ((c, nows) :-> y) <- as 
>               , let ws = take nows nxthps 
>               , let x = getTag fcs :> Con c ws ]
>         ctx ys = rebuildHeap (deTagH h) $ () :>
>                  Case (deTag fcs) [ ((c, nows) :-> abstract' ws y)
>                                   | ((c, nows) :-> _) <- as 
>                                   , let ws = take nows nxthps 
>                                   | y <- ys ]
> 
> badisWHNF (_ :> PVa _) = True
> badisWHNF (_ :> Con _ _) = True
> badisWHNF _ = False
> 
> badSplitApp :: [HP] -> Heap t -> Bracket t -> Bracket t
> badSplitApp vs h br = B hls ctx
>   where (vs', sts) = unzip [ (v, S h fcs [])
>                            | v <- vs, Just fcs <- [ join (Map.lookup v h) ] 
>                            {- not (badisWHNF fcs) -} ]
>         hls = sts ++ holes br
>         ctx es = mkLet xs (abstract' vs' $ context br ys)
>           where (xs, ys) = splitAt (length sts) es
> 
> {-
> If there are any non-linear variables or non-value, abstract them.
> i.e. Remove them from the heaps of holes and evaluate independently.
> When reconstructing, let-bind and reinject.
> -}
> abstractNonlinear :: State t -> (Expr () HP -> Expr () HP)
>                   -> Bracket t -> Bracket t
> abstractNonlinear hl ctx br = B hls' ctx'
>   where vs = heap hl `Map.intersection`
>              (Map.unions $ map heap $ holes br)
>         wipe s = s { heap = inserts (heap s) $ map (, Nothing) (Map.keys vs) }
>         hls' = map wipe $ hl : holes br
>         ctx' = undefined
>         
> sharedStruct :: Heap t -> Heap t -> Set HP
> sharedStruct x y = undefined
>   where xs = Map.map (maybe Set.empty $ accessible x) x
>         ys = Map.map (maybe Set.empty $ accessible y) y
>         vs = xs `Map.intersection` ys