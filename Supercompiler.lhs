> {-# LANGUAGE OverloadedStrings #-}
> module Supercompiler where
> 
> import Control.Arrow
> import Control.Applicative
> import Control.Monad.State.Strict hiding (State)
> import qualified Control.Monad.State.Strict as St
> import Data.Function
> import Data.List
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe
> import Data.Set (Set)
> import qualified Data.Set as Set
> 
> import Fliter.EDSL
> import Fliter.Miniplate (extract)
> import Fliter.Semantics
> import Fliter.Syntax
> import SC.Matching
> import SC.Split
> import SC.Termination
> 
> import Debug.Trace
> traceM str = trace str $ return ()
> 
> {- Utility structures -}
> data ScpState = ScpState { scThisPromise :: Ix
>                          , scFreeVars    :: Map Ix [HP]
>                          , scPromises    :: [(Ix, State ())]
>                          , scDefinition  :: Map Ix (Func () HP) }
>                 deriving Show
> type ScpM     = St.State ScpState
> 
> initScp = ScpState 0 Map.empty [] Map.empty
> 
> scInc :: ScpM ()
> scInc = get >>= \s -> put (s { scThisPromise = scThisPromise s + 1 }) >> traceM (show $ scThisPromise s + 1) 
> 
> scPerhapsFreevars :: Ix -> [HP] -> ScpM [HP]
> scPerhapsFreevars i fvs = do
>   scpSt <- get
>   let m = Map.insertWith (flip const) i fvs (scFreeVars scpSt)
>   put $ scpSt { scFreeVars = m }
>   return (m Map.! i)
> 
> scAddPromise :: State () -> ScpM ()
> scAddPromise s = do
>   scpSt <- get
>   let i = scThisPromise scpSt
>   put $ scpSt { scPromises = (i, s) : scPromises scpSt }
>   
> freeVarsSt :: State t -> [HP]
> freeVarsSt = Map.keys . Map.filter isNothing . heap
>   
> bypass :: Monad m => m () -> a -> m a
> bypass cont x = cont >> return x
> 
> funRefs :: Expr () a -> Set Ix
> funRefs = fr . getRhs
>   where fr (Fun f _) = Set.singleton f
>         fr x = extract fr x
> 
> {- Supercompiler -}
> sc :: Prog t a -> Func t' a' -> Int -> Prog () HP
> sc p (Lam novs x) f0 = Prog (take f0 fs ++ Map.elems (scDefinition scp))
>   where p' = intTagProg $ fmap undefined $ p
>         Prog fs = deTagProg $ fmap undefined $ p
>         vs = map HP [0 .. novs - 1]
>         s' = S (Map.fromList [ (v, Nothing) | v <- vs ])
>                (instantiate' vs $ fmap (fmap undefined) $ intTag x) []
>         scp = execState (drive [] p' s') (initScp { scThisPromise = f0 })
> 
> drive :: History -> Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> drive hist p s = memo (drive' hist p) s
> 
> drive' :: History -> Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> drive' hist p s = case normalise p s of
>   Cont s' -> case terminate hist (summarise s) of
>     Stop           -> traceM "term" >> tie p s'
>     Continue hist' -> traceM "cont" >> drive hist' p s'
>   Halt s' -> traceM "halt" >> tie p s'
>   Crash   -> traceM "crash" >> tie p s
> 
> tie :: Prog Nat HP -> State Nat -> ScpM (Expr () HP)
> tie p s = do
>   let B hls ctx = splitApp s
>   i <- scThisPromise <$> get
>   fvs <- scPerhapsFreevars i $ freeVarsSt s
>   rhs <- ctx <$> mapM (bypass scInc >=> drive [] p . gc) hls
>   let defn = Lam (length fvs) (abstract' fvs rhs)
>   scpSt <- get
>   put $ scpSt { scDefinition = Map.insert i defn (scDefinition scpSt) }
>   return $ if i `Set.member` funRefs rhs
>              then () :> Fun i fvs
>              else rhs
> 
> summarise :: State Nat -> TagBag
> summarise s = Map.unionsWith (+) $ exTag (focus s) : (map (fmap (* 3) . exTag) . catMaybes . Map.elems . heap) s
> 
> mkArgs :: [HP] -> [(HP, HP)] -> [HP]
> mkArgs xs ys = [ fst $ head $ filter ((== x) . snd) ys | x <- xs ]
> 
> memo :: (State Nat -> ScpM (Expr () HP)) -> State Nat -> ScpM (Expr () HP)
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
> 
> -- Testing area
> 
> example' = intTagProg $ fmap undefined $ Prog
>  [ lam "xs" $ letIn ["inc" =: fun 2]
>               $ letIn ["xs'" =: fun 1 @: "inc xs"]
>                 $ fun 1 @: "inc xs'"
>  , lam "f x" $ caseOf "x"
>      [ "Nil"       --> "Nil" 
>      , "Cons x xs" --> letIn [ "x'"  =:  "f" @: "x"
>                              , "xs'" =: fun 1 @: "f xs" ]
>                        ("Cons" @: "x' xs'") ]
>  , lam "m" $ letIn [ "one" =: pVa 1 ] $ "m" +$ "one" ]
>  
> initState' = S (Map.singleton (HP 0) Nothing) (((-1) :: Nat) :> Fun 0 [HP 0]) []
> 
> run = print (Prog $ Map.elems $ scDefinition $ execState (drive [] example' initState') initScp)