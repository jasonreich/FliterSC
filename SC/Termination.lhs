> module SC.Termination where
> 
> import Data.IntMap (IntMap)
> import qualified Data.IntMap as Map
> 
> type Nat = Int
> type TagBag = IntMap Int
> 
> type History = [TagBag]
> 
> data TermRes = Stop | Continue History
> 
> (<|) :: TagBag -> TagBag -> Bool 
> x <| y = Map.keysSet x == Map.keysSet y &&
>          Map.fold (&&) True (Map.intersectionWith (<=) x y)
> 
> terminate :: History -> TagBag -> TermRes
> terminate hist bag | any (<| bag) hist = Stop
>                    | otherwise         = Continue (bag:hist)