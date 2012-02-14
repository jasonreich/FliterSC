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
> import Data.Maybe
> import Data.Set (Set)
> import qualified Data.Set as Set

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

> instance Show (Bracket t) where
>   show (B hls ctx) = "B\n" ++ unlines (map show hls) ++
>                      show (ctx [ undefined :> 
>                                  Con ("<" ++ show i ++ ">") []
>                                | i <- [0..]])

Utility functions
-----------------

Compress lets where the new binding is not free in the others.

> mkLet (v, x) (() :> Let xs y) 
>   | v `Set.notMember` (Set.unions $ map freeVars xs)
>   = () :> Let (xs ++ [x]) (fmap (abstract rho) y)
>   where rho v' | v == v'   = Bnd $ length xs
>                | otherwise = Fre v'
> mkLet (v, x) y = () :> Let [x] (open [v] y)

> wipe :: HP -> State t -> State t
> wipe v s = s { heap = Map.insert v Nothing (heap s) }

Splitting
---------

Given a state, produce a bracket of constituent computations. These
could be;

*   Unevaluated case alternatives due to an unknown case subject.
*   Unevaluated application parameters that due to an unknown
    function/constructor.
                  
In the case of the latter, one must be careful not to lose sharing of
heap.

TODO: Any shared heap must be abstracted and supercompiled separately.

> split :: State t -> Bracket t
> split s = splitHeap (heap s) . splitFocus $ s

Split focus
-----------

`splitFocus` starts the process by normalising applied variables and
capturing any variables which share values with the case subject.

> splitFocus :: State t -> ([HP], Bracket t)
> splitFocus (S h x@(_ :> Var (Fre v)) stk)
>   = splitStack [v] stk x h
> splitFocus (S h (t :> Con c vs@(_:_)) stk)
>   = splitStack [] (App vs : stk) (t :> Con c []) h
> splitFocus (S h (t :> Fun f vs@(_:_)) stk)
>   = splitStack [] (App vs : stk) (t :> Fun f []) h
> splitFocus (S h x@(_ :> POp _ (Fre v) (Fre w)) stk) 
>   = first ((++) [v,w]) $ splitStack [] stk x h
> splitFocus (S h x stk) = splitStack [] stk x h

Split stack
-----------

`splitStack` peels off each stack element and produces; 

*  a list of variables that have been applied
*  a bracket equivalent to the state but having extracted states
   equivalent to nearest case-alternatives.

A list of variables where the current focus would be stored is 
accumulated to inject case analysis assumptions.

> splitStack :: [HP] -> Stack t -> Expr t HP -> Heap t
>            -> ([HP], Bracket t)
  
If the stack is empty, produce no further states and reconstruct
an equivalent expression by turning heap entries into let-bindings.
  
> splitStack upds [] x h
>   = ([], B [] $ const $ deTag x)

If there was an update, this focus must have been stored there.
Keep a note of that and continue down the stack.

> splitStack upds (Upd v : stk) x h
>   = splitStack (v:upds) stk x h

On a case frame, split down case alternatives.

> splitStack upds (Cas as : stk) x h
>   = (apps, B hls' ctx')
>   where (apps, B hls ctx) = splitStack [] [] x h
>         nxthps = (nextHPs . nextKey) h
>         s_as = [ gc $ S h' (close vs y) stk
>                | ((c, novs) :-> y) <- as
>                , let vs = take novs nxthps
>                , let x' = getTag y :> Con c vs
>                , let h' = inserts h $ map (, Nothing) vs
>                                    ++ map (, Just x') apps ]
>         hls' = hls ++ s_as
>         ctx' es = let (xs, ys) = splitAt (length hls) es
>                   in () :> Case (ctx xs) 
>                            [ p :-> open vs y
>                            | (p@(_, novs) :-> _) <- as
>                            , let vs = take novs nxthps
>                            | y <- ys ]

If there was an application, reapply and store the list of applied
bindings. Continue down stack.

> splitStack upds (App vs : stk) x h
>   = (vs ++ apps, B hls $ \es -> () :> ctx es :@ map Fre vs)
>   where (apps, B hls ctx) = splitStack [] stk x h

On a left-half primitive application, do equivalent to the above but
bind the focus for application. Continue down stack.

> splitStack upds (PrL o w : stk) x h
>   = (w : apps, B hls $ \es -> () :> Let [ctx es] 
>                               (() :> POp o (Bnd 0) (Fre w)))
>   where (apps, B hls ctx) = splitStack [] stk x h

On a right-half primitive application, reconstruct sensibly and
continue down stack.

> splitStack upds (PrR o m : stk) x h
>   = (apps, B hls $ \es -> () :> Let [() :> PVa m, ctx es] 
>                           (() :> POp o (Bnd 0) (Bnd 1)))
>   where (apps, B hls ctx) = splitStack [] stk x h

Split heap
----------

Given a list of applied bindings and a bracket, we want to;

*  Drive on these applied bindings, (add holes to bracket), preventing
   loss of sharing by;
   *  Removing this bindings from the heaps of existing states.
   *  And recursively doing the same for any bindings shared between
      across these or between existing states.
*  Reconstruct equivelent let-expressions representing these heap
   entries.

e.g.

  let x = foo in (let y = bar x in Pair x y)
    ==>
  ⟦ let x = ⟨ , foo,  ⟩ in (let y = ⟨ x->*, bar x,  ⟩ in Pair x y) ⟧

> splitHeap :: Heap t -> ([HP], Bracket t) -> Bracket t
> splitHeap h (apps, br) = foldr sh br (Set.toAscList vs)
>   where acc0 = Set.unions $ map accessibleSt $ holes br
>         vs0 = Set.fromList apps 
>         vs = Set.union vs0 $ acc0 `Set.intersection` accessible h vs0
>         sh v br@(B hls ctx) = fromMaybe br $ do
>           fcs <- join $ Map.lookup v h
>           let s = gc $ S h fcs []
>           let hls' = s : fmap (wipe v) hls
>           let ctx' (x : ys) = let y = ctx ys
>                               in if v `Set.member` freeVars y
>                                 then mkLet (v, x) y
>                                 else y
>           return $ B hls' ctx'