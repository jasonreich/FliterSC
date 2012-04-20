FliterSC: Syntax
================

This module defines that AST for f-liter and contains some basic
operations.

We use a locally nameless approach similar to McBride and McKinna
(2004), but where free variable are polymorphic rather than strings.

> {-# LANGUAGE ParallelListComp, DeriveFunctor, TypeOperators #-}
> module Fliter.Syntax where

Imports
-------

> import Control.Applicative
> import Control.Arrow (second)
> import Control.Monad.Identity
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Function
> import Data.List
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe (isJust, fromJust, fromMaybe)
> import Data.Set (Set)
> import qualified Data.Set as Set

> import Fliter.FixSet
> import Fliter.Miniplate

Tagging
-------

For the purposes of supercompilation termination, the expressions of
the AST are tagged. To prevent the tampering of these tags, it
is kept polymorphic.

> infixl 8 :>
> data t :> a = (:>) { getTag :: t, getRhs :: a } 
>             deriving Functor

Equivalence is defined up to tags.

> instance Eq a => Eq (t :> a) where
>   (==) = (==) `on` getRhs

When we show expressions, we ignore the tag.

> instance Show a => Show (t :> a) where
>   show = show . getRhs

> unzipTag = unzip . map (\ (t :> x) -> (t, x))

Abstract syntax tree
--------------------

Constructor identifiers are strings. Function and variable identifiers
are positional indexes.

> type Id = String
> type Ix = Int

We use an approach similar to that of "I am not a number, I am a free
variable." Bound variables are de Bruijn indicies and free variables
can be anything!

> data V free = Fre free
>             | Bnd Ix
>             deriving (Show, Eq, Functor)

For changing bound variables.
       
> bmap :: (Int -> Int) -> V free -> V free
> bmap f (Fre x) = Fre x
> bmap f (Bnd i) = Bnd (f i)

Primitive operators are as follows.

> data Op = Pl | Mi | Eq | Ne | Le | Seq
>         deriving (Show, Eq)

Expressions are defined using a mutually recursive datastructure to
capture the tagged nature. Let-expressions are ambiguous at this
stage but we shall state now that they will be *non-recursive*.

> type Expr t free = t :> Expr' t free 
> data Expr' t free = Var (V free)  -- Variables
>                   | Fun Id [free] -- (Applied) functions
>                   | Con Id [free] -- (Applied) constructors
>                   | PVa Int       -- Primitive integers
>                   | POp Op (V free) (V free) -- Primitive operators
>                   | Expr t free :@ [V free]  -- Application
>                   | Let [Expr t free] (Expr t free)  -- Non-rec let
>                   | Case (Expr t free) [Alte t free] -- Case dist.
>                   deriving (Eq, Functor)

Alternatives are mappings of constructor names and arities to
expressions.

> data Alte t free = (Id, Ix) :-> Expr t free
>                  deriving (Eq, Functor)

Functions are expressions with a specified number of bound variables.
              
> data Func t free = Lam Ix (Expr t free)
>                  deriving (Eq, Functor)

Programs are a list of functions.

> newtype Prog t free = Prog [(Id, Func t free)]
>                     deriving (Eq, Functor)

Close expressions
-----------------

Given an expressions bound at this point with $n$ variables, replace
them with free terms $xs = x_1 x_2 ... x_n$.

> close :: [free] -> Expr t free -> Expr t free
> close xs = fmap $ instantiate rho
>   where len_xs = length xs
>         rho i | i < 0      = Bnd $ i
>               | i < len_xs = Fre $ xs !! i
>               | otherwise  = Bnd $ i - len_xs

This uses the more generic.

> instantiate :: (Ix -> V free) -> Expr' t free -> Expr' t free
> instantiate rho (Var v)     = Var (safeFree rho v)
> instantiate rho (POp o v w) = POp o (safeFree rho v) (safeFree rho w)
> instantiate rho (x :@ vs)   = fmap (instantiate rho) x :@ 
>                               map (safeFree rho) vs
> instantiate rho (Let xs y)  = Let xs' y'
>   where xs' = map (fmap $ instantiate rho) xs
>         y'  = fmap (instantiate (shift (length xs) rho)) y
> instantiate rho (Case x as) = Case x' as' 
>   where x'  = fmap (instantiate rho) x
>         as' = [ (c, vs) :-> fmap (instantiate (shift vs rho)) y 
>               | ((c, vs) :-> y) <- as ]
> instantiate _   x           = x

> safeFree :: (Ix -> V free) -> (V free -> V free)
> safeFree rho (Fre x) = Fre x
> safeFree rho (Bnd v) = rho v

> shift i rho = bmap (+ i) . rho . (+ (- i))

Open expressions
-----------------

Given an expressions bound at this point with free variables, replace
them with bound references.

> open :: Eq free => [free] -> Expr () free -> Expr () free
> open xs = fmap $ abstract rho
>   where rho x = maybe (Fre x) Bnd $ elemIndex x xs

This uses the more generic.

> abstract :: (a -> V b) -> Expr' () a -> Expr' () b
> abstract rho (Var v)     = Var (safeBind rho v)
> abstract rho (Fun f vs)  = (() :> Fun f []) :@ map rho vs
> abstract rho (Con c vs)  = (() :> Con c []) :@ map rho vs
> abstract rho (PVa n)     = PVa n
> abstract rho (POp o v w) = POp o (safeBind rho v) (safeBind rho w)
> abstract rho (x :@ vs)   = fmap (abstract rho) x :@ 
>                            map (safeBind rho) vs
> abstract rho (Let xs y)  = Let (map (fmap $ abstract rho) xs) y'
>   where y' = fmap (abstract (bmap (+ length xs) . rho)) y
> abstract rho (Case x as) = Case (fmap (abstract rho) x) as'
>   where as' = [ (c, vs) :-> fmap (abstract (bmap (+ vs) . rho)) y 
>               | ((c, vs) :-> y) <- as ]
          
> safeBind :: (a -> V b) -> (V a -> V b)
> safeBind rho (Fre x) = rho x
> safeBind rho (Bnd v) = Bnd v



Tree traversal
--------------

A simple uniplate-like library (miniplate) provides some generic
traversal operations.

TODO: Perhaps remove. Doesn't save that much.

A smart constructor that is like a miniplate bracket but preserves
tags.

> tB :: [Expr t free] -> ([Expr t free] -> Expr' t free) 
>    -> Bracket (Expr' t free)
> tB hls ctx = B xs (ctx . zipWith (:>) ts)
>   where (ts, xs) = unzipTag hls

Uniplate/miniplate instance.

> instance Uniplate (Expr' t free) where
>   uniplate (x :@ vs)   = tB [x] $ \[x] -> x :@ vs
>   uniplate (Let xs y)  = tB (y:xs) $ \(y:xs) -> Let xs y
>   uniplate (Case x as) = tB (x : [ y | _ :-> y <- as ]) 
>                          $ \(x:ys) -> Case x [ p :-> y 
>                                              | p :-> _ <- as 
>                                              | y <- ys ]
>   uniplate x = tB [] $ \[] -> x
 
Expression utilities
--------------------

Is an expression in WHNF.

> isWHNF :: Prog t free -> Expr t free -> Bool
> isWHNF (Prog fs) (_ :> Con _ _)  = True
> isWHNF (Prog fs) (_ :> Fun f vs) = case lookup f fs of
>   Nothing -> True
>   Just (Lam novs _) -> length vs < novs
> isWHNF (Prog fs) (_ :> PVa _)    = True
> isWHNF _         _               = False

The set of free variables in an expression.

> freeVars :: Ord a => Expr t a -> Set a
> freeVars = fv . getRhs
>   where fv (Var (Fre x)) = Set.singleton x
>         fv (Con _ vs)    = Set.fromList vs
>         fv (Fun _ vs)    = Set.fromList vs
>         fv (POp _ v w)   = Set.fromList [ x | Fre x <- [v, w] ]
>         fv (x :@ vs)     = freeVars x `Set.union` 
>                            Set.fromList [ v | Fre v <- vs ]
>         fv x             = extract fv x

The set of references to functions.

> funRefs :: Expr t a -> Set Id
> funRefs = fr . getRhs
>   where fr (Fun f _) = Set.singleton f
>         fr x = extract fr x

> funRefsProg :: Prog t a -> Set Id
> funRefsProg (Prog fs) = fixSet aux (Set.singleton "main")
>   where aux f = maybe Set.empty (\(Lam _ x) -> funRefs x) (lookup f fs)
          
> onlyReachable :: Prog t a -> Prog t a
> onlyReachable p@(Prog fs) = Prog $ filter ((`Set.member` funRefsProg p) . fst) fs

Assume the expression is closed when changing type.

> unsafeEraseExpr :: Expr t a -> Expr t b
> unsafeEraseExpr = fmap (fmap (error "Expecting no free variables!"))

> unsafeEraseFunc :: Func t a -> Func t b
> unsafeEraseFunc = fmap (error "Expecting no free variables!")

> unsafeEraseProg :: Prog t a -> Prog t b
> unsafeEraseProg = fmap (error "Expecting no free variables!")

> eraseFreeExpr :: Expr t a -> Expr t ()
> eraseFreeExpr = fmap $ fmap $ const ()

> eraseFreeProg :: Prog t a -> Prog t ()
> eraseFreeProg = fmap $ const ()

Tag utilities
-------------

Retag an expression or program using a monadic function on the
existing tag.
 
> reTag :: (Applicative m, Monad m) => (t -> m t') -> Expr t a 
>       -> m (Expr t' a)
> reTag f (t :> x) = (:>) <$> f t <*> rt x
>   where rt (Var v)     = pure $ Var v
>         rt (Fun f vs)  = pure $ Fun f vs
>         rt (Con f vs)  = pure $ Con f vs
>         rt (PVa m)     = pure $ PVa m
>         rt (POp o v w) = pure $ POp o v w
>         rt (x :@ vs)   = (:@ vs) <$> reTag f x
>         rt (Let xs y)  = Let <$> mapM (reTag f) xs <*> reTag f y
>         rt (Case x as) = Case <$> reTag f x <*> 
>                          sequence [ (:->) p <$> reTag f y 
>                                   | (p :-> y) <- as ]

> reTagProg :: (Applicative m, Monad m) => (t -> m t') -> Prog t a
>           -> m (Prog t' a)
> reTagProg f (Prog p) = fmap Prog $ sequence $
>                      [ (,) fid . Lam vs <$> reTag f rhs 
>                      | (fid, Lam vs rhs) <- p ]

Replace tags with unit.
 
> deTag :: Expr t a -> Expr () a
> deTag = runIdentity . reTag dT

> deTagProg :: Prog t a -> Prog () a
> deTagProg p = runIdentity (reTagProg dT p)

> dT = const $ pure ()

Replace tags with unique integer.

> intTag :: Expr t a -> Expr Int a
> intTag = flip evalState 0 . reTag iT

> intTagProg :: Prog t a -> Prog Int a
> intTagProg p = evalState (reTagProg iT p) 0

> iT = const $ get >>= \i -> modify (+1) >> return i

Extract a dictionary counting each tag.

> exTag :: Ord a => Expr a b -> Map a Int
> exTag x = foldr (flip (Map.insertWith (+)) 0) Map.empty 
>           $ execWriter (reTag (\t -> tell (t:)) x) []

Simple inline
-------------

Inline any root applications to functions.

> simpleInline :: Eq a => Prog t a -> Prog t a
> simpleInline (Prog fs) = Prog $ map (second aux) fs
>   where aux l@(Lam ar (_ :> ((_ :> Fun f []) :@ args))) = fromMaybe l $ do
>           Lam ar' body' <- f `lookup` fs
>           guard (args == [ Bnd v | v <- [0..ar' - 1] ])
>           return $ Lam ar body'
>         aux l = l

Inlining
--------

Inline non-recursive functions.

> nonRecInline :: Prog t a -> Prog t a
> nonRecInline (Prog fs) = Prog [ (f, Lam ar $ aux (Set.singleton f) `fmap` x)
>                               | (f, Lam ar x) <- fs ]
>   where
>     aux seen ((_ :> Fun f []) :@ vs) 
>       | isJust body = aux (Set.insert f seen) (fromJust body)
>       where mkApp x [] = getRhs x
>             mkApp x ys = x :@ ys
>             body = do guard $ f `Set.notMember` seen
>                       Lam ar rhs <- f `lookup` fs
>                       guard $ ar <= length vs
>                       let (applied, surplus) = splitAt ar vs
>                       let rho i | i < 0     = Bnd i
>                                 | i < ar    = applied !! i
>                                 | otherwise = error "nonRecInline: Beyond binding!"
>                       return $ mkApp (instantiate rho `fmap` rhs) surplus
>     aux seen ((_ :> x :@ vs) :@ ws)  = aux seen (x :@ (vs ++ ws))
>     aux seen x = descend (aux seen) x