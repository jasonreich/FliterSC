FliterSC: Matching
==================

This module focuses on showing two states are equivalent.

> module SC.Matching where

Imports
------

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State hiding (State)
> import qualified Data.Map as Map
> 
> import Fliter.Miniplate
> import Fliter.Semantics
> import Fliter.Syntax
> 
> heapPointers :: Expr t a -> [a]
> heapPointers = fv . getRhs
>   where fv (Var (Fre x)) = [x]
>         fv (Con _ vs)    = vs
>         fv (Fun _ vs)    = vs
>         fv (POp _ v w)   = [ x | Fre x <- [v, w] ]
>         fv (x :@ vs)     = heapPointers x ++ [ v | Fre v <- vs ]
>         fv x             = extract fv x
> 
> matchExpr :: Expr () a -> Expr () b -> Maybe [(a, b)]
> matchExpr x y = do
>   guard $ fmap (fmap (const ())) x == fmap (fmap (const ())) y
>   return $ zip (heapPointers x) (heapPointers y)
> 
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
> 
> matchStk :: Stack () -> Stack () -> Maybe [(HP, HP)]
> matchStk xs ys = do
>   guard $ length xs == length ys
>   concat <$> zipWithM matchStkElm xs ys
> 
> instanceOf :: State () -> State () -> Maybe [(HP, HP)]
> instanceOf x y = do
>   initMatch <- (++) <$> matchExpr (focus x) (focus y)
>                     <*> matchStk  (stack x) (stack y)
>   let matchPtr (v, w) = do
>         assumed <- (Map.lookup w >=> return . (== v)) <$> get
>         case assumed of
>           Just False -> mzero
>           Just True  -> return []
>           Nothing    -> do
>             modify $ Map.insert w v
>             case (join $ Map.lookup v (heap x), join $ Map.lookup w (heap y)) of
>               (Nothing, Just _)  -> mzero
>               (Just i,  Just j)  -> lift (matchExpr i j) >>= fmap concat . mapM matchPtr
>               (_,       Nothing) -> return [(v, w)]
>   evalStateT (concat <$> mapM matchPtr initMatch) Map.empty