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
> import qualified Data.Set as Set

We import syntax, syntax manpulation and small-step semantics for
F-liter.

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
> import Fliter.Parser (parseProg)

Debugging stuff

> import Debug.RocketFuel
> import Debug.Trace

> traceM :: Monad m => String -> m ()
> -- traceM = flip trace $ return ()
> traceM = const $ return ()

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
> scInc = get >>= \s -> put (s { scThisPromise = scThisPromise s + 1 }) >> traceM ('h' : (show $ scThisPromise s + 1) ++ ":")

Store these free variables if there is nothing else in there. Return
the canonical free variables for this resudual index.

> scPerhapsFreevars :: Ix -> [HP] -> ScpM [HP]
> scPerhapsFreevars i fvs = do
>   scpSt <- get
>   let m = Map.insertWith (flip const) i fvs (scFreeVars scpSt)
>   put $ scpSt { scFreeVars = m }
>   return (m Map.! i)

Alternative encoding

> scRecordFreevars :: State a -> ScpM (State a)
> scRecordFreevars s = do
>   scpSt <- get
>   let vs = accessibleSt s `Set.intersection` Set.fromList (unknownVarsSt s)
>   let m = Map.insert (scThisPromise scpSt) (Set.toList vs) (scFreeVars scpSt)
>   put $ scpSt { scFreeVars = m }
>   return s

Store this mapping of state to index.

> scAddPromise :: State () -> ScpM ()
> scAddPromise s = do
>   scpSt <- get
>   let i = scThisPromise scpSt
>   put $ scpSt { scPromises = scPromises scpSt ++ [(i, s)] }

> scAddDefinition :: Ix -> [HP] -> Expr () HP -> ScpM ()
> scAddDefinition f vs x = do
>   scpSt <- get
>   put $ scpSt { scDefinition = Map.insert f 
>                                (Lam (length vs) (open vs x)) 
>                                (scDefinition scpSt) }

Make an effect but return the input.

> bypass :: Monad m => m () -> a -> m a
> bypass cont x = cont >> return x

The supercompiler
-----------------

The supercompiler process;

1.  Take a program, `p` and a named function `(fid, Lam novs x)`.
2.  Tag each AST element of `p` and `x` with an integer. The set of
    tags used should be finite as the trees will be finite.
3.  Create a state, `s0` corresponding to `x` where the unbound 
    variables are empty heap positions.
4.  `drive` on this state (see driving section).
5.  Reconstruct a program using the residual definitions.

> sc :: Prog t HP -> (Id, Func t' HP) -> Prog () HP
> sc p (fid, Lam novs x) = p'
>   where p0 = intTagProg $ p
>         Prog fs = deTagProg $ p
>         vs = map HP [0 .. novs - 1]
>         s0 = S (Map.fromList [ (v, Nothing) | v <- vs ])
>                (close vs $ intTag x) []
>         (x', scp) = runState (drive [] p0 s0) initScp
>         p' = Prog $ Map.toList $
>              Map.mapKeysMonotonic toFunId (scDefinition scp)
>              `inserts` ((fid, Lam novs $ open vs $ x') : fs)

> sc_wrapper p (fid, body) 
>   = sc (unsafeEraseProg p) (fid, unsafeEraseFunc body)

Driving
-------
                  
Driving is the process normalising a term until it is in WHNF, is
stuck on an unknown variable or it fails some termination condition
to prevent infinite recursion.

This logic is actually contained in `drive'` but it is memoised to
fold back on any previously seen states.

When driving terminates, the result is `tie`d.

> drive :: History -> Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> drive hist p s = return (() :> Con "<BINGO>" []) `consumeFuel` memo (drive' hist p) s
> 
> drive' :: History -> Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> drive' hist p s = traceM (show s) >> case normalise p s of
>   Cont s' -> case terminate hist (summarise s') of
>     Stop           -> traceM (show s') >> traceM "Stop" >> tie p s'
>     Continue hist' -> drive hist' p s'
>   Halt s' -> traceM (show s') >> traceM "Halt" >> tie p s'
>   Crash   -> traceM (show s) >> traceM "Crash" >> tie p s

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

> memo :: (State Nat -> ScpM (Expr () HP)) 
>      -> State Nat -> ScpM (Expr () HP)
> memo cont s = do
>   scpSt <- get
>   let s_dt = deTagSt s
>   let matches = [ (i_prev, swap prevToCur, s')
>                 | (i_prev, s') <- scPromises scpSt
>                 , Just prevToCur <- [s_dt `equivalent` s'] ]
>   case matches of
>     []                  -> scAddPromise s_dt >> cont s
>     (i_prev, prevToCur, s'):_ -> do
>       traceM $ "Tied:"
>       traceM $ show s
>       traceM $ show s'
>       fvs_prev <- scPerhapsFreevars i_prev $ map fst prevToCur
>       let x_cur = wrapNull
>                   (() :> Fun (toFunId i_prev) (mkArgs prevToCur fvs_prev))
>       let i_cur = scThisPromise scpSt
>       fvs_cur <- scPerhapsFreevars i_cur $ map snd prevToCur
>       scAddDefinition i_cur fvs_cur x_cur
>       return $ x_cur

Produce arguments for given mappings and bindings.

> mkArgs :: [(HP, HP)] -> [HP] -> [HP]
> mkArgs prevToCur vs = [ fromMaybe (HP (-1)) (lookup v prevToCur)
>                       | v <- vs ]

> swap xs = [ (x, y) | (y, x) <- xs ]

> wrapNull x | noMissing = x
>            | otherwise = () :> Let [() :> Con "Null" []] (open [HP $ (-1)] x)
>  where noMissing = HP (-1) `Set.notMember` freeVars x

> toFunId :: Ix -> Id
> toFunId = ('h':) . show

Tying
-----

When driving terminates, split off case alternatives and applicants
for further driving, then reconstruct the expression and store.

If it's simple and non-recursive, just return the residual expression.
Otherwise, return a pointer to it.

> tie :: Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> tie p s = do
>   let br@(B hls ctx) = split s
>   i <- fmap scThisPromise get
>   fvs <- scPerhapsFreevars i $ unknownVarsSt s
>   rhs <- fmap ctx $ mapM (bypass scInc >=> drive [] p) hls
>   scAddDefinition i fvs rhs
>   return $ if True -- toFunId i `Set.member` funRefs rhs
>              then () :> Fun (toFunId i) fvs
>              else rhs

[fliter]:  https://github.com/jasonreich/FliterSemantics
[bol2010]: http://dx.doi.org/10.1145/1863523.1863540