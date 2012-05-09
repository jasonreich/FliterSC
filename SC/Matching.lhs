FliterSC: Matching
==================

This module focuses on showing two states are equivalent.

> module SC.Matching where

Imports
-------

Nothing too complicated here.

> import Control.Applicative
> import Data.List
> import Data.Monoid
> import Control.Monad
> import Control.Monad.State hiding (State)
> import qualified Data.Map as Map
> 
> import Fliter.Miniplate
> import Fliter.Semantics
> import Fliter.Syntax

Utility functions
-----------------

This function is similar to `freeVars` except it returns a full
list, in depth-first order, of heap pointers in an expression.

> heapPointers :: Expr t a -> [a]
> heapPointers = fv . getRhs
>   where fv (Var (Fre x)) = [x]
>         fv (Con _ vs)    = vs
>         fv (Fun _ vs)    = vs
>         fv (POp _ v w)   = [ x | Fre x <- [v, w] ]
>         fv (x :@ vs)     = heapPointers x ++ [ v | Fre v <- vs ]
>         fv x             = extract fv x


Matching components
-------------------

Two expressions are equivelent up to variable names if they are
syntactically equivalent when heap pointers are erased. If equivalent,
returns the list of variable pairs.

> matchExpr :: Expr () a -> Expr () b -> Maybe [(a, b)]
> matchExpr x y = do
>   guard $ eraseFreeExpr x == eraseFreeExpr y
>   return $ zip (heapPointers x) (heapPointers y)

Two stack elements are equivelent up to variable names if they are
syntactically equivalent when heap pointers are erased. If equivalent,
returns the list of variable pairs.

> matchStkElm :: StackElem () -> StackElem () -> Maybe [(HP, HP)]
> matchStkElm (Upd hp_x)    (Upd hp_y)  = do
>   return [(hp_x, hp_y)]
> matchStkElm (App hps_x)   (App hps_y) = do
>   guard $ length hps_x == length hps_y
>   return (zip hps_x hps_y)
> matchStkElm (Cas as_x)    (Cas as_y)  = do 
>   let mkCase as = () :> Case (() :> Con "NULL" []) as
>   matchExpr (mkCase as_x) (mkCase as_y)
> matchStkElm (PrL o_x w_x) (PrL o_y w_y) = do
>   guard $ o_x == o_y
>   return [(w_x, w_y)]
> matchStkElm (PrR o_x m_x) (PrR o_y m_y) = do
>   guard $ o_x == o_y && m_x == m_y
>   return []
> matchStkElm _ _ = Nothing

Two stacks are the same if all their elements are the same.

> matchStk :: Stack () -> Stack () -> Maybe [(HP, HP)]
> matchStk xs ys = do
>   guard $ length xs == length ys
>   concat <$> zipWithM matchStkElm xs ys

Matching states
---------------

A state, s, is an instance of another state, t, if;

*  Their focuses are equivalent up to variables, and,
*  Their stacks are equivalent up to variables, and,
*  For all variable pairs referenced, all heap entries are equivalent
   or the heap entry in t is free and consistent.
  
Returns the list of s heap pointers mapped to free t heap pointers.

> instantiatesTo :: State () -> State () -> Maybe ([(HP, HP)], [HP])
> instantiatesTo x y = do
>     initMatch <- (++) <$> matchExpr (focus x) (focus y)
>                       <*> matchStk  (stack x) (stack y)
>     evalStateT (mconcat <$> mapM matchPtr initMatch) []
>   where matchPtr :: (HP, HP) -> StateT [(HP, HP)] Maybe ([(HP, HP)], [HP])
>         matchPtr (v, w) = do
>           assumptions <- get
>           let assoc_v = filter ((==) v . fst) $ assumptions
>           guard $ all ((==) w . snd) $ assoc_v
>           let assoc_w = filter ((==) w . snd) $ assumptions
>           guard $ all ((==) v . fst) $ assoc_w
>           if (not.null) assoc_v
>              then return ([], [])
>              else do modify $ nub . ((v,w) :)
>                      case ( join $ Map.lookup v (heap x)
>                           , join $ Map.lookup w (heap y)) of
>                        (Nothing, _)       -> return ([(v, w)], [w])
>                        (Just i,  Just j)  -> lift (matchExpr i j) >>=
>                                              fmap mconcat . mapM matchPtr
>                        (_,       _)       -> mzero

> equivalent :: State () -> State () -> Maybe [(HP, HP)]
> equivalent x y = do
>     initMatch <- (++) <$> matchExpr (focus x) (focus y)
>                       <*> matchStk  (stack x) (stack y)                 
>     evalStateT (concat <$> mapM matchPtr initMatch) []
>   where matchPtr :: (HP, HP) -> StateT [(HP, HP)] Maybe [(HP, HP)]
>         matchPtr (v, w) = do
>           assumptions <- get
>           let assoc_v = filter ((==) v . fst) $ assumptions
>           guard $ all ((==) w . snd) $ assoc_v
>           let assoc_w = filter ((==) w . snd) $ assumptions
>           guard $ all ((==) v . fst) $ assoc_w
>           if (not.null) assoc_v
>              then return []
>              else do modify $ nub . ((v,w) :)
>                      case ( join $ Map.lookup v (heap x)
>                           , join $ Map.lookup w (heap y)) of
>                        (Nothing, Nothing) -> return [(v, w)]
>                        (Just i,  Just j)  -> lift (matchExpr i j) >>=
>                                              fmap concat . mapM matchPtr
>                        (_,       _)       -> mzero