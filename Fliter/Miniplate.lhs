> module Fliter.Miniplate where
> 
> import Data.Monoid
> 
> data Bracket a = B { children :: [a], context :: [a] -> a }
> 
> class Uniplate a where
>   uniplate :: a -> Bracket a
>
> extract :: (Uniplate a, Monoid b) => (a -> b) -> a -> b
> extract f x = mconcat $ map f $ children $ uniplate x
>
> universe :: (Uniplate a) => a -> [a]
> universe = extract return