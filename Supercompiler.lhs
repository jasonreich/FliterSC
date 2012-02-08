F-liter Supercompiler
=====================

> module Supercompiler where

This literate program describes a supercompiler for the 
[F-liter][fliter] language. The design of the supercompiler is based
on that of [Bollingbroke & Peyton-Jones (2010)][bol2010].

The supercompiler is currently presented as a library with an
embedding of F-liter for inputting programs.

Imports
-------

We use `State` the structures to encaptulate shared information about
a supercompilation.

> import Control.Monad.State.Strict hiding (State)
> import qualified Control.Monad.State.Strict as St

`Map`s are used to represent `Heap`s in evaluation, mappings residual
function names to free variable listings and final definitions, 
and summaries of states for termination. `Set`s are used to describe
free variables and used function names.

> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe
> import Data.Set (Set)
> import qualified Data.Set as Set

We import syntax, syntax manpulation and small-step semantics for
F-liter.

> import Fliter.Miniplate (extract)
> import Fliter.Semantics
> import Fliter.Syntax

And modules containing other supercompilation machinary for state
equivalence, state splitting and reconstruction, and termination
conditions based on finite mappings.

> import SC.Matching
> import SC.Split
> import SC.Termination

These expose an embedding of F-liter for inputting programs and an
example program described in this way.

> import Example
> import Fliter.EDSL


Global supercompilation state
-----------------------------

A data structure contains relevant information for supercompilation.

*  An index of the current residual function.
*  A function of residual indexes to named free variables.
*  A mapping of indexes and states associated with them. 
*  A mapping of final residual definitions.

> data ScpState = ScpState { scThisPromise :: Ix
>                          , scFreeVars    :: Map Ix [HP]
>                          , scPromises    :: [(Ix, State ())]
>                          , scDefinition  :: Map Ix (Func () HP) }
>                 deriving Show
>
> initScp = ScpState 0 Map.empty [] Map.empty

A monad is used to pass this state around.

> type ScpM     = St.State ScpState

This indicates a new residual function has begun.

> scInc :: ScpM ()
> scInc = get >>= \s -> put (s { scThisPromise = scThisPromise s + 1 })

Store these free variables if there is nothing else in there. Return
the canonical free variables for this resudual index.

> scPerhapsFreevars :: Ix -> [HP] -> ScpM [HP]
> scPerhapsFreevars i fvs = do
>   scpSt <- get
>   let m = Map.insertWith (flip const) i fvs (scFreeVars scpSt)
>   put $ scpSt { scFreeVars = m }
>   return (m Map.! i)

Store this mapping of state to index.

> scAddPromise :: State () -> ScpM ()
> scAddPromise s = do
>   scpSt <- get
>   let i = scThisPromise scpSt
>   put $ scpSt { scPromises = (i, s) : scPromises scpSt }

Make an effect but return the input.

> bypass :: Monad m => m () -> a -> m a
> bypass cont x = cont >> return x

The supercompiler
-----------------

The supercompiler process;

1.  Take a program, `p`, an anonymous function `f@(Lam novs x)` and an
    initial name for the residual function.
2.  Tag each AST element of `p` and `f` with an integer. The set of
    tags used should be finite as the trees will be finite.
3.  Create a state, `s0` corresponding to `x` where the unbound 
    variables are empty heap positions.
4.  `drive` on this state (see driving section).
5.  Reconstruct a program using the residual definitions.

> sc :: Prog t a -> Func t' a' -> Int -> Prog () HP
> sc p (Lam novs x) f0 = p'
>   where p0 = intTagProg $ unsafeEraseProg $ p
>         Prog fs = deTagProg $ unsafeEraseProg $ p
>         vs = map HP [0 .. novs - 1]
>         s0 = S (Map.fromList [ (v, Nothing) | v <- vs ])
>                (instantiate' vs $ unsafeEraseExpr $ intTag x) []
>         scp = execState (drive [] p0 s0) 
>               (initScp { scThisPromise = f0 })
>         p' = Prog (take f0 fs ++ Map.elems (scDefinition scp))

Driving
-------
                  
Driving is the process normalising a term until it is in WHNF, is
stuck on an unknown variable or it fails some termination condition
to prevent infinite recursion.

This logic is actually contained in `drive'` but it is memoised to
fold back on any previously seen states.

When driving terminates, the result is `tie`d.

> drive :: History -> Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> drive hist p s = memo (drive' hist p) s
> 
> drive' :: History -> Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> drive' hist p s = case normalise p s of
>   Cont s' -> case terminate hist (summarise s) of
>     Stop           -> tie p s'
>     Continue hist' -> drive hist' p s'
>   Halt s' -> tie p s'
>   Crash   -> tie p s

In this case, we terminate when the bag of tags contained in a state
grows. We `summarise` a state into a bag of tags.

> summarise :: State Nat -> TagBag
> summarise s = Map.unionsWith (+) $ 
>               exTag (focus s) : (map (fmap (* 3) . exTag) . 
>                                  catMaybes . Map.elems . heap) s

Memoiser
--------

The `memo`iser checks to see if we've done this work before. If we
have, we fold back on that definition.

TODO: Consider if we should be doing instances or exact matches of
states. If it is instances, probably should drive on arguments.

> memo :: (State Nat -> ScpM (Expr () HP)) 
>      -> State Nat -> ScpM (Expr () HP)
> memo cont s = do
>   scpSt <- get
>   let s_dt = deTagSt s
>   let matches = [ (i, mapping)
>                 | (i, s') <- scPromises scpSt 
>                 , Just mapping <- [s_dt `instanceOf` s'] ]
>   scAddPromise s_dt 
>   case matches of
>     []             -> cont s
>     (i, mapping):_ -> do
>       fvs <- scPerhapsFreevars i $ map snd mapping
>       return $ () :> (Fun i (mkArgs fvs mapping))

> mkArgs :: [HP] -> [(HP, HP)] -> [HP]
> mkArgs xs ys = [ fst $ head $ filter ((== x) . snd) ys | x <- xs ]

Tying
-----

When driving terminates, split off case alternatives and applicants
for further driving, then reconstruct the expression and store.

If it's simple and non-recursive, just return the residual expression.
Otherwise, return a pointer to it.

> tie :: Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> tie p s = do
>   let B hls ctx = splitApp s
>   i <- fmap scThisPromise get
>   fvs <- scPerhapsFreevars i $ freeVarsSt s
>   rhs <- fmap ctx $ mapM (bypass scInc >=> drive [] p . gc) hls
>   let defn = Lam (length fvs) (abstract' fvs rhs)
>   scpSt <- get
>   put $ scpSt { scDefinition = Map.insert i defn (scDefinition scpSt) }
>   return $ if i `Set.member` funRefs rhs
>              then () :> Fun i fvs
>              else rhs

[fliter]:  https://github.com/jasonreich/FliterSemantics
[bol2010]: http://dx.doi.org/10.1145/1863523.1863540