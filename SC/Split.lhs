> {-# LANGUAGE TupleSections, ParallelListComp #-}
> module SC.Split where
> 
> import Control.Applicative
> import Control.Monad
> import qualified Data.Map as Map
> import Data.Maybe
> import Data.Set (Set)
> import qualified Data.Set as Set
> 
> import Fliter.Semantics
> import Fliter.Syntax
> import SC.Rebuild
> 
> import Debug.Trace
> 
> data Bracket t = B { holes   :: [State t]
>                    , context :: [Expr () HP] -> Expr () HP }
> 
> instance Show (Bracket t) where
>   show (B hls ctx) = "B\n" ++ unlines (map show hls) ++
>                      show (ctx [ undefined :> Con ("<" ++ show i ++ ">") []
>                                | i <- [0..]])
> 
> splitApp :: State t -> Bracket t
> splitApp s = case focus s of
>   t :> Var (Fre v)    -> splitStack [v] s
>   t :> Fun f vs@(_:_) -> splitStack [] $ s { focus = t :> Fun f []
>                                            , stack = App vs : stack s }
>   t :> Con c vs@(_:_) -> splitStack [] $ s { focus = t :> Con c []
>                                            , stack = App vs : stack s  }
>   t :> POp _ v w      -> badSplitApp [x | Fre x <- [v,w]] (heap s)
>                          $ splitStack [] $ wipe [x | Fre x <- [v,w]] s
>   _                   -> splitStack [] s
> 
> 
> wipe :: [HP] -> State t -> State t
> wipe vs s = s { heap = inserts (heap s) (map (, Nothing) vs) }
> 
> splitStack :: [HP] -> State t -> Bracket t
> splitStack vs s = case stack s of
>   []              -> B [] $ \_ -> (rebuildStack . deTagSt) s
>   (Upd v  : stk)  -> splitStack (v:vs) $ s { stack = stk }
>   -- Drive on the vs too
>   (App vs : stk)  -> badSplitApp vs (heap s) $ splitStack []
>                      $ wipe vs $ s { focus = t :> (focus s :@ map Fre vs) 
>                                    , stack = stk }
>   (Cas as : stk)  -> splitAlts vs (heap s) (focus s) stk as
>   -- Drive on the w too
>   (PrL o w : stk) -> badSplitApp [w] (heap s)
>                      $ splitStack [] $ wipe [w] $
>                      s { focus = t :> Let [focus s] (t :> POp o (Bnd 0) (Fre w)), stack = stk }
>   (PrR o m : stk) -> splitStack [] $
>                      s { focus = t :> Let [t :> PVa m, focus s] 
>                                        (t :> POp o (Bnd 0) (Bnd 1))
>                        , stack = stk }
>   where t = getTag $ focus s
> 
> splitAlts :: [HP] -> Heap t -> Expr t HP -> Stack t -> [Alte t HP] -> Bracket t
> splitAlts vs h fcs stk as = B hls ctx
>   where nxthps = (nextHPs . nextKey) h
>         hls = [ gc $ S (inserts h $ map (, Nothing) ws ++ map (, Just x) vs)
>                        (instantiate' ws y) stk
>               | ((c, nows) :-> y) <- as 
>               , let ws = take nows nxthps 
>               , let x = getTag fcs :> Con c ws ]
>         ctx ys = rebuildHeap (deTagH h) $ () :>
>                  Case (deTag fcs) [ ((c, nows) :-> abstract' ws y)
>                                   | ((c, nows) :-> _) <- as 
>                                   , let ws = take nows nxthps 
>                                   | y <- ys ]
> 
> badisWHNF (_ :> PVa _) = True
> badisWHNF (_ :> Con _ _) = True
> badisWHNF _ = False
> 
> badSplitApp :: [HP] -> Heap t -> Bracket t -> Bracket t
> badSplitApp vs h br = B hls ctx
>   where (vs', sts) = unzip [ (v, S h fcs [])
>                            | v <- vs, Just fcs <- [ join (Map.lookup v h) ] 
>                            {- not (badisWHNF fcs) -} ]
>         hls = sts ++ holes br
>         ctx es = mkLet xs (abstract' vs' $ context br ys)
>           where (xs, ys) = splitAt (length sts) es
> 
> {-
> If there are any non-linear variables or non-value, abstract them.
> i.e. Remove them from the heaps of holes and evaluate independently.
> When reconstructing, let-bind and reinject.
> -}
> abstractNonlinear :: State t -> (Expr () HP -> Expr () HP)
>                   -> Bracket t -> Bracket t
> abstractNonlinear hl ctx br = B hls' ctx'
>   where vs = heap hl `Map.intersection`
>              (Map.unions $ map heap $ holes br)
>         wipe s = s { heap = inserts (heap s) $ map (, Nothing) (Map.keys vs) }
>         hls' = map wipe $ hl : holes br
>         ctx' = undefined
>         
> sharedStruct :: Heap t -> Heap t -> Set HP
> sharedStruct x y = undefined
>   where xs = Map.map (maybe Set.empty $ accessible x) x
>         ys = Map.map (maybe Set.empty $ accessible y) y
>         vs = xs `Map.intersection` ys