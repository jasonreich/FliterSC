> module Fliter.FixSet (fixSet) where
> 
> import Control.Monad
> import Control.Monad.State
> import Data.Set (Set)
> import qualified Data.Set as Set
> 
> fixSet :: Ord a => (a -> Set a) -> Set a -> Set a
> fixSet m xs = execState (fixSet' $ Set.toList xs) Set.empty
>   where fixSet' []     = return ()
>         fixSet' (y:ys) = do
>           seen <- get
>           modify $ Set.insert y
>           fixSet' $ if (y `Set.member` seen)
>             then ys
>             else ys ++ Set.toList (m y)