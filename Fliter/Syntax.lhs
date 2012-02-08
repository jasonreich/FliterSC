> {-# LANGUAGE ParallelListComp, DeriveFunctor, TypeOperators #-}
> module Fliter.Syntax where
> 
> import Control.Applicative
> import Control.Monad.Identity
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Function
> import Data.List
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> 
> import Fliter.Miniplate
> 
> -- Tagging
> infixl 8 :>
> data t :> a = t :> a
>             deriving Functor
> getTag (t :> _) = t
> getRhs (_ :> x) = x
> unzipTag = unzip . map (\ (t :> x) -> (t, x))
> 
> instance Eq a => Eq (t :> a) where
>   (==) = (==) `on` getRhs
> 
> instance Show a => Show (t :> a) where
>   show = show . getRhs
> 
> -- Basic abstract syntax tree
> type Id = String
> type Ix = Int
> 
> data V free = Fre free
>             | Bnd Ix
>             deriving (Show, Eq, Functor)
>                      
> bmap :: (Int -> Int) -> V free -> V free
> bmap f (Fre x) = Fre x
> bmap f (Bnd i) = Bnd (f i)
> 
> data Op = Pl | Mi | Eq | Ne | Le | Seq
>         deriving (Show, Eq)
> 
> type Expr t free = t :> Expr' t free 
> data Expr' t free = Var (V free)
>                   | Fun Ix [free]
>                   | Con Id [free]
>                   | PVa Int
>                   | POp Op (V free) (V free)
>                   | Expr t free :@ [V free]
>                   | Let [Expr t free] (Expr t free)
>                   | Case (Expr t free) [Alte t free]
>                   deriving (Eq, Functor)
> 
> data Alte t free = (Id, Ix) :-> Expr t free
>                  deriving (Eq, Functor)
>                         
> data Func t free = Lam Ix (Expr t free)
>                  deriving (Eq, Functor)
> 
> newtype Prog t free = Prog [Func t free]
>                     deriving (Eq, Functor)
> 
> isWHNF :: Prog t free -> Expr t free -> Bool
> isWHNF (Prog fs) (_ :> Con _ _)  = True
> isWHNF (Prog fs) (_ :> Fun f vs) = case drop f fs of
>   [] -> True
>   (Lam novs _:_) -> length vs < novs
> isWHNF (Prog fs) (_ :> PVa _)    = True
> isWHNF _         _               = False
> 
> -- Tree traversals
> tB :: [Expr t free] -> ([Expr t free] -> Expr' t free) -> Bracket (Expr' t free)
> tB hls ctx = B xs (ctx . zipWith (:>) ts)
>   where (ts, xs) = unzipTag hls
> 
> instance Uniplate (Expr' t free) where
>   uniplate (x :@ vs)   = tB [x] $ \[x] -> x :@ vs
>   uniplate (Let xs y)  = tB (y:xs) $ \(y:xs) -> Let xs y
>   uniplate (Case x as) = tB (x : [ y | _ :-> y <- as ]) 
>                          $ \(x:ys) -> Case x [ p :-> y 
>                                              | p :-> _ <- as 
>                                              | y <- ys ]
>   uniplate x = tB [] $ \[] -> x
> 
> -- Close terms
> 
> safeFree :: (Ix -> V free) -> (V free -> V free)
> safeFree rho (Fre x) = Fre x
> safeFree rho (Bnd v) = rho v
> 
> shift i rho = bmap (+ i) . rho . (+ (- i))
> 
> instantiate :: (Ix -> V free) -> Expr' t free -> Expr' t free
> instantiate rho (Var v)     = Var (safeFree rho v)
> instantiate rho (POp o v w) = POp o (safeFree rho v) (safeFree rho w)
> instantiate rho (x :@ vs)   = fmap (instantiate rho) x :@ 
>                               map (safeFree rho) vs
> instantiate rho (Let xs y)  = Let (map (fmap $ instantiate rho) xs)
>                                   (fmap (instantiate (shift (length xs) rho)) y)
> instantiate rho (Case x as) = Case (fmap (instantiate rho) x)
>                               [ (c, vs) :-> fmap (instantiate (shift vs rho)) y 
>                               | ((c, vs) :-> y) <- as ]
> instantiate _   x           = x
> 
> instantiate' xs = fmap $ instantiate rho
>   where len_xs = length xs
>         rho i | i < 0      = Bnd $ i
>               | i < len_xs = Fre $ xs !! i
>               | otherwise  = Bnd $ i - len_xs
> 
> -- Open terms
> safeBind :: (a -> V b) -> (V a -> V b)
> safeBind rho (Fre x) = rho x
> safeBind rho (Bnd v) = Bnd v
> 
> abstract :: (a -> V b) -> Expr' () a -> Expr' () b
> abstract rho (Var v)     = Var (safeBind rho v)
> abstract rho (Fun f vs)  = (() :> Fun f []) :@ map rho vs
> abstract rho (Con c vs)  = (() :> Con c []) :@ map rho vs
> abstract rho (PVa n)     = PVa n
> abstract rho (POp o v w) = POp o (safeBind rho v) (safeBind rho w)
> abstract rho (x :@ vs)   = fmap (abstract rho) x :@ map (safeBind rho) vs
> abstract rho (Let xs y)  = Let (map (fmap $ abstract rho) xs)
>                            (fmap (abstract (bmap (+ length xs) . rho)) y)
> abstract rho (Case x as) = Case (fmap (abstract rho) x)
>                            [ (c, vs) :-> fmap (abstract (bmap (+ vs) . rho)) y 
>                            | ((c, vs) :-> y) <- as ]
> 
> abstract' xs = fmap $ abstract rho
>   where rho x = maybe (Fre x) Bnd $ elemIndex x xs
>         
> freeVars :: Ord a => Expr t a -> Set a
> freeVars = fv . getRhs
>   where fv (Var (Fre x)) = Set.singleton x
>         fv (Con _ vs)    = Set.fromList vs
>         fv (Fun _ vs)    = Set.fromList vs
>         fv (POp _ v w)   = Set.fromList [ x | Fre x <- [v, w] ]
>         fv (x :@ vs)     = freeVars x `Set.union` Set.fromList [ v | Fre v <- vs ]
>         fv x             = extract fv x
> 
> reTag :: (Applicative m, Monad m) => (t -> m t') -> Expr t a -> m (Expr t' a)
> reTag f (t :> x) = (:>) <$> f t <*> rt x
>   where rt (Var v)     = pure $ Var v
>         rt (Fun f vs)  = pure $ Fun f vs
>         rt (Con f vs)  = pure $ Con f vs
>         rt (PVa m)     = pure $ PVa m
>         rt (POp o v w) = pure $ POp o v w
>         rt (x :@ vs)   = (:@ vs) <$> reTag f x
>         rt (Let xs y)  = Let <$> mapM (reTag f) xs <*> reTag f y
>         rt (Case x as) = Case <$> reTag f x <*> sequence [ (:->) p <$> reTag f y | (p :-> y) <- as ]
> 
> deTag :: Expr t a -> Expr () a
> deTag = runIdentity . reTag (const $ pure ())
> 
> deTagProg :: Prog t a -> Prog () a
> deTagProg (Prog p) = Prog (evalState (sequence [ Lam vs <$> reTag (const $ pure ()) rhs | Lam vs rhs <- p ]) 0)
> 
> intTag :: Expr t a -> Expr Int a
> intTag = flip evalState 0 . reTag (const $ get >>= \i -> modify (+1) >> return i)
> 
> intTagProg :: Prog t a -> Prog Int a
> intTagProg (Prog p) = Prog (evalState (sequence [ Lam vs <$> reTag (const $ get >>= \i -> modify (+1) >> return i) rhs | Lam vs rhs <- p ]) 0)
> 
> exTag :: Ord a => Expr a b -> Map a Int
> exTag x = foldr (flip (Map.insertWith (+)) 0) Map.empty $ execWriter (reTag (\t -> tell (t:)) x) []

> funRefs :: Expr () a -> Set Ix
> funRefs = fr . getRhs
>   where fr (Fun f _) = Set.singleton f
>         fr x = extract fr x

> unsafeEraseExpr :: Expr t a -> Expr t b
> unsafeEraseExpr = fmap (fmap (error "There should have been no free variables"))

> unsafeEraseProg :: Prog t a -> Prog t b
> unsafeEraseProg = fmap (error "There should have been no free variables")