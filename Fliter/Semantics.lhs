FliterSC: Semantics
===================

This module defines an abstract machine for evaluating f-liter
programs.

> {-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving #-}
> module Fliter.Semantics where

Imports
-------

> import Control.Arrow (first, second, (***))
> import Control.Monad
> import Data.List
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe (listToMaybe, isNothing, fromJust)
> import Data.Set (Set)
> import qualified Data.Set as Set

> import Fliter.FixSet
> import Fliter.Pretty
> import Fliter.Syntax

Utility functions 
-----------------

Insert multiple key/value pairs.

> inserts :: Ord k => Map k v -> [(k, v)] -> Map k v
> inserts = foldr (uncurry $ Map.insert)

Abstract machine state
----------------------

Heap pointers are tagged integers.

> newtype HP = HP { unHP :: Int }
>            deriving (Eq, Ord, Enum)
>                     
> instance Show HP where show = show . unHP

Generate the succeeding heap pointers 

> nextHPs :: HP -> [HP]
> nextHPs (HP i) = map HP [i..]

A heap is a mapping of heap pointers to closed terms. An extra layer
of maybe is included for unknown terms.

> type Heap t = Map HP (Maybe (Expr t HP))

Find the next available HP pointer.

> nextKey :: Map HP v -> HP
> nextKey m | Map.null m = HP 0
>           | otherwise  = HP . (+) 1 . unHP . fst $ Map.findMax m

Stack elements indicate; application, updating, case distinction,
left-hand primitive operation, right-hand primitive operation.

> data StackElem t = App [HP] | Upd HP | Cas [Alte t HP] 
>                  | PrL Op HP | PrR Op Int
>                deriving Show

Stacks are lists of stack elements.

> type Stack t = [StackElem t]

A state is a triple consisting of a heap, focus open expression and a
stack.

> data State t = S
>   { heap  :: Heap t
>   , focus :: (Expr t HP)
>   , stack :: Stack t }
>   deriving Show

> initState :: State ()
> initState = S Map.empty (() :> Fun "main" []) []

Execution monad
---------------

Execution monad represents partial and incomplete computations.

> data Exec h s = Cont s
>               | Halt h
>               | Crash
>               deriving (Functor, Show)

> instance Monad (Exec h) where
>   return       = Cont
>   Cont x >>= f = f x
>   _      >>= _ = Crash
>   fail _       = Crash

Translation from maybe to execution.

> toExec = maybe Crash Cont

Execution steps
---------------

Single step execution of a state in a program context.

> step :: Prog t HP -> State t -> Exec (State t) (State t)
> step (Prog fs) s = case (getRhs . focus) s of
>   Var (Bnd _) -> error "Unbound variable!"
>   Var (Fre v) -> do
>     fcs <- toExec $ join $ Map.lookup v (heap s)
>     return $ s { focus = fcs, stack = Upd v : stack s }
>   Fun f vs    -> do
>     let len_vs = length vs
>     Lam novs x <- toExec $ f `lookup` fs
>     if novs <= len_vs
>       then let (args, apps) = splitAt novs vs
>            in  return $ s { focus = close args x
>                           , stack = addApps apps (stack s) }
>       else stepWHNF s
>   Con _ _     -> stepWHNF s
>   PVa _       -> stepWHNF s
>   POp o (Fre v) (Fre w) -> do
>     fcs <- maybe Crash Cont $ join $ Map.lookup v (heap s)
>     return $ s { focus = fcs, stack = Upd v : PrL o w : stack s }
>   POp o _ _   -> error "Unbound variable!"
>   x :@ []     -> do
>     return $ s { focus = x }
>   x :@ vs     -> do
>     let vs' = [ v | Fre v <- vs ]
>     return $ s { focus = x, stack = App vs' : stack s }
>   Let xs y    -> do
>     let len_xs = length xs 
>     let bs = zip (nextHPs $ nextKey $ heap s) xs
>     let heap' = inserts (heap s) $ map (second Just) bs
>     let y' = close (map fst bs) y
>     return $ S heap' y' (stack s)
>   Case x as   -> do
>     return $ s { focus = x, stack = Cas as : stack s }

Useful for filtering empty applications.

> addApps :: [HP] -> Stack t -> Stack t
> addApps [] = id
> addApps xs = (App xs:)

If the focus was in WHNF, proceed with updating/primitive evaluation/
case distinctions.

> stepWHNF :: State t -> Exec (State t) (State t)
> stepWHNF s = case (stack s, focus s) of
>   ([], _) -> Halt s
>   (Upd v : stk, t :> x) -> do
>     return $ s { heap = Map.insert v (Just $ t :> x) (heap s), stack = stk }
>   (App ws : stk, t :> Fun f vs) -> do
>     return $ s { focus = t :> Fun f (vs ++ ws), stack = stk }
>   (App ws : stk, t :> Con c vs) -> do
>     return $ s { focus = t :> Con c (vs ++ ws), stack = stk }
>   (Cas as : stk, _ :> Con c vs) -> do
>     y <- toExec $ listToMaybe [ y | ((c', novs) :-> y) <- as
>                                   , c == c', novs == length vs ]
>     return $ s { focus = close vs y, stack = stk }
>   (PrL o w : stk, _ :> PVa m) -> do
>     fcs <- toExec $ join $ Map.lookup w (heap s)
>     return $ s { focus = fcs, stack = Upd w : PrR o m : stk }
>   (PrR o m : stk, t :> PVa n) -> do
>     return $ s { focus = t :> eval o m n, stack = stk }
>   _ -> Crash

Production of expressions resulting from primitive operations.

> eval :: Op -> Int -> Int -> Expr' t free
> eval Pl  m n = PVa (m + n)
> eval Mi  m n = PVa (m - n)
> eval Eq  m n = Con (show $ m == n) []
> eval Ne  m n = Con (show $ m /= n) []
> eval Le  m n = Con (show $ m <= n) []
> eval Seq _ n = PVa n


Full execution
--------------

> exec :: Prog t HP -> State t -> Maybe (State t)
> exec p s = case step p s of
>   Crash   -> Nothing
>   Halt s' -> Just s'
>   Cont s' -> exec p s'

Partial execution
-----------------

> execFor :: Int -> Prog t HP -> State t -> (Int, Exec (Expr () ()) (Expr () ()))
> execFor 0 p s = (0, Cont $ deTag $ fmap (fmap $ const ()) $ focus s)
> execFor n p s = case step p s of
>   Crash   -> (0, Crash)
>   Halt s' -> (0, Halt $ deTag $ fmap (fmap $ const ()) $ focus s')
>   Cont s' -> first (+1) $ execFor (n - 1) p s'

Strong normalisation
--------------------

Reduce the program until a saturated function application is reached,
the program has halted or the program is about to crash due to unknown
input.

> normalise :: Prog t HP -> State t -> Exec (State t) (State t)
> normalise p s = case step p s of
>   Crash   -> Crash
>   Halt s' -> Halt s'
>   Cont s' | isPause p s' -> Cont s'
>           | isUnknown s' -> Halt s'
>           | otherwise    -> normalise p s'

Saturated function application.

> isPause :: Prog t HP -> State t -> Bool
> isPause (Prog fs) s = case getRhs $ focus s of
>   Fun f vs  -> maybe False id $ do
>     let len_vs = length vs
>     Lam novs x <- f `lookup` fs
>     return $ novs <= len_vs
>   _         -> False

Unknown variable or primitive.

> isUnknown :: State t -> Bool
> isUnknown s = case getRhs $ focus s of
>   Var (Fre v)      -> isNothing . join $ v `Map.lookup` heap s
>   POp _ _ _        -> True
>   _                -> False

State utility functions
-----------------------

Free variables in a stack element.

> freeVarsSE :: StackElem t -> Set HP
> freeVarsSE (App vs)  = Set.fromList vs
> freeVarsSE (Cas as)  = Set.unions [ freeVars y | (_ :-> y) <- as ]
> freeVarsSE (PrL o w) = Set.singleton w
> freeVarsSE _         = Set.empty

Free variables in a stack.

> freeVarsStk :: Stack t -> Set HP
> freeVarsStk = Set.unions . map freeVarsSE

Unknown variables in a state, ~ free variables.

> unknownVarsSt :: State t -> [HP]
> unknownVarsSt = Map.keys . Map.filter isNothing . heap

All heap pointers accessible from these.

> accessible :: Heap t -> Set HP -> Set HP
> accessible h = fixSet $ maybe Set.empty freeVars . 
>                         join . (`Map.lookup` h)

All heap pointers accessible in this state.

> accessibleSt :: State t -> Set HP
> accessibleSt s = accessible (heap s) vs0
>   where vs0 = freeVars (focus s) `Set.union` freeVarsStk (stack s)

Remove all inaccessible heap pointers.

> gc :: State t -> State t
> gc s = s { heap = heap' }
>   where heap' = Map.filterWithKey (const . (`Set.member` vs)) (heap s)
>         vs = accessibleSt s

State/tag utilities
-------------------

Detag a stack element.

> deTagSE (App vs)  = App vs
> deTagSE (Upd v)   = Upd v
> deTagSE (Cas as)  = Cas [ (p :-> deTag y) | (p :-> y) <- as ]
> deTagSE (PrL o w) = PrL o w
> deTagSE (PrR o m) = PrR o m

Detag a heap.

> deTagH = Map.map (fmap deTag)

Detag a state.

> deTagSt :: State t -> State ()
> deTagSt (S h fcs stk) = S (deTagH h) 
>                           (deTag fcs) 
>                           (map deTagSE stk)

Reverse execution
-----------------

Back-step

> backstep :: State () -> Either (Heap (), Expr () HP) (State ())
> backstep st | (null.stack) st = Left (heap st, focus st)
>             | otherwise = case (head.stack) st of
>  App vs  -> Right $ st { stack = (tail.stack) st
>                        , focus = () :> (focus st :@ map Fre vs) }
>  Upd v   -> Right $ st { stack = (tail.stack) st
>                        , heap = Map.insert v (Just $ focus st) (heap st) }
>  Cas as  -> Right $ st { stack = (tail.stack) st
>                        , focus = () :> Case (focus st) as }
>  PrL o v -> Right $ st { stack = (tail.stack) st
>                        , focus = () :> Let [focus st] 
>                                    (() :> POp o (Fre v) (Bnd 0)) }
>  PrR o m -> Right $ st { stack = (tail.stack) st
>                        , focus = () :> Let [() :> PVa m, focus st] 
>                                     (() :> POp o (Bnd 0) (Bnd 1)) }

> -- backstepHeap :: (Heap (), Expr () HP) -> Func () HP
> backstepHeap (h, y) = {- Lam (length free) $ open free -} result
>   where (free, bound) = (map fst) *** (map $ second fromJust)
>                       $ partition (isNothing . snd) $ Map.assocs h
>         result = foldr (\(v, x) y -> () :> Let [x] (open [v] y)) y bound

> reconstruct = either backstepHeap reconstruct . backstep