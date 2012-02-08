> {-# LANGUAGE DeriveFunctor #-}
> module Fliter.Semantics where
> 
> import Prelude hiding ((!!))
> import Control.Arrow (second)
> import Control.Monad
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe (listToMaybe, isJust, isNothing)
> import Data.Set (Set)
> import qualified Data.Set as Set
> 
> import Fliter.FixSet
> import Fliter.Pretty
> import Fliter.Syntax
> 
> (!!) :: [a] -> Int -> Maybe a
> []     !! _ = Nothing
> (x:_)  !! 0 = Just x
> (_:xs) !! n = xs !! (n - 1)
> 
> nextKey :: Map HP v -> HP
> nextKey m | Map.null m = HP 0
>           | otherwise  = HP . (+) 1 . unHP . fst $ Map.findMax m
> 
> inserts :: Map HP v -> [(HP, v)] -> Map HP v
> inserts = foldr (uncurry $ Map.insert)
> 
> -- Descriptions of state
> newtype HP = HP { unHP :: Int }
>            deriving (Eq, Ord)
>                     
> instance Show HP where show = show . unHP
> 
> nextHPs :: HP -> [HP]
> nextHPs (HP i) = map HP [i..]
> 
> type Heap t = Map HP (Maybe (Expr t HP))
> data StackElem t = App [HP] | Upd HP | Cas [Alte t HP] 
>                  | PrL Op HP | PrR Op Int
>                deriving Show
> type Stack t = [StackElem t]
> 
> data State t = S
>   { heap  :: Heap t
>   , focus :: (Expr t HP)
>   , stack :: Stack t }
>   deriving Show
>   
> initState = S Map.empty (0 :> Fun 0 []) []
> 
> -- Small-step semantics
> data Exec h s = Cont s
>               | Halt h
>               | Crash
>               deriving (Functor, Show)
> 
> instance Monad (Exec h) where
>   return       = Cont
>   Cont x >>= f = f x
>   _      >>= _ = Crash
>   fail _       = Crash
> 
> toExec = maybe Crash Cont
> 
> addApps :: [HP] -> Stack t -> Stack t
> addApps [] = id
> addApps xs = (App xs:)
> 
> step :: Prog t HP -> State t -> Exec (State t) (State t)
> step (Prog fs) s = case (getRhs . focus) s of
>   Var (Bnd _) -> error "Unbound variable!"
>   Var (Fre v) -> do
>     fcs <- toExec $ join $ Map.lookup v (heap s)
>     return $ s { focus = fcs, stack = Upd v : stack s }
>   Fun f vs    -> do
>     let len_vs = length vs
>     Lam novs x <- toExec $ fs !! f
>     if novs <= len_vs
>       then let (args, apps) = splitAt novs vs
>            in  return $ s { focus = instantiate' args x
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
>     let y' = instantiate' (map fst bs) y
>     return $ S heap' y' (stack s)
>   Case x as   -> do
>     return $ s { focus = x, stack = Cas as : stack s }
>     
> eval :: Op -> Int -> Int -> Expr' t free
> eval Pl  m n = PVa (m + n)
> eval Mi  m n = PVa (m - n)
> eval Eq  m n = Con (show $ m == n) []
> eval Ne  m n = Con (show $ m /= n) []
> eval Le  m n = Con (show $ m <= n) []
> eval Seq _ n = PVa n
> 
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
>     return $ s { focus = instantiate' vs y, stack = stk }
>   (PrL o w : stk, _ :> PVa m) -> do
>     fcs <- toExec $ join $ Map.lookup w (heap s)
>     return $ s { focus = fcs, stack = Upd w : PrR o m : stk }
>   (PrR o m : stk, t :> PVa n) -> do
>     return $ s { focus = t :> eval o m n, stack = stk }
>   _ -> Crash
> 
> exec :: Prog t HP -> State t -> Exec (State t) (State t)
> exec p s = case step p s of
>   Crash   -> Crash
>   Halt s' -> Halt s'
>   Cont s' -> exec p s'
> 
> isPause :: Prog t HP -> State t -> Bool
> isPause (Prog fs) s = case getRhs $ focus s of
>   Fun f vs  -> maybe False id $ do
>     let len_vs = length vs
>     Lam novs x <- fs !! f
>     return $ novs <= len_vs
>   _         -> False
>   
> isUnknown :: State t -> Bool
> isUnknown s = case getRhs $ focus s of
>   Var (Fre v)      -> isNothing . join $ v `Map.lookup` heap s
>   POp _ (Fre v) _  -> isNothing . join $ v `Map.lookup` heap s
>   _                -> case stack s of
>     PrL _ w : _    -> isNothing . join $ w `Map.lookup` heap s
>     _              -> False
>     
> 
> -- Evaluate without beta-reduction
> normalise :: Prog t HP -> State t -> Exec (State t) (State t)
> normalise p s = case step p s of
>   Crash   -> Crash
>   Halt s' -> Halt s'
>   Cont s' | isPause p s' -> Cont s'
>           | isUnknown s' -> Halt s'
>           | otherwise    -> normalise p s'
> 
> freeVarsSE :: StackElem t -> Set HP
> freeVarsSE (App vs)  = Set.fromList vs
> freeVarsSE (Cas as)  = Set.unions [ freeVars y | (_ :-> y) <- as ]
> freeVarsSE (PrL o w) = Set.singleton w
> freeVarsSE _         = Set.empty
> 
> freeVarsStk :: Stack t -> Set HP
> freeVarsStk = Set.unions . map freeVarsSE
> 
> accessible :: Heap t -> Expr t HP -> Set HP
> accessible h x = fixSet (maybe Set.empty freeVars . join . (`Map.lookup` h)) vs0
>   where vs0 = freeVars x
> 
> accessibleSt :: State t -> Set HP
> accessibleSt s = fixSet (maybe Set.empty freeVars . join . (`Map.lookup` heap s)) vs0
>   where vs0 = freeVars (focus s) `Set.union` freeVarsStk (stack s)
> 
> gc :: State t -> State t
> gc s = s { heap = heap' }
>   where heap' = Map.filterWithKey (const . (`Set.member` vs)) (heap s)
>         vs = accessibleSt s
>         
> deTagSE (App vs)  = App vs
> deTagSE (Upd v)   = Upd v
> deTagSE (Cas as)  = Cas [ (p :-> deTag y) | (p :-> y) <- as ]
> deTagSE (PrL o w) = PrL o w
> deTagSE (PrR o m) = PrR o m
> 
> deTagH = Map.map (fmap deTag)
> 
> deTagSt :: State t -> State ()
> deTagSt (S h fcs stk) = S (deTagH h) 
>                           (deTag fcs) 
>                           (map deTagSE stk)