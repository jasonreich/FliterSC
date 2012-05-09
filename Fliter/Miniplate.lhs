> module Fliter.Miniplate where
> 
> import Data.Monoid
> 
> data Bracket a = B { children :: [a], context :: [a] -> a }
> 
> class Uniplate a where
>   uniplate :: a -> Bracket a
>
> descend :: (Uniplate a) => (a -> a) -> a -> a
> descend f x = ctx $ map f cs
>   where B cs ctx = uniplate x
>         
> transform :: (Uniplate a) => (a -> a) -> a -> a
> transform f x = f $ ctx $ map (transform f) cs
>   where B cs ctx = uniplate x
>
> extract :: (Uniplate a, Monoid b) => (a -> b) -> a -> b
> extract f x = mconcat $ map f $ children $ uniplate x
>
> universe :: (Uniplate a) => a -> [a]
> universe x = x : concatMap universe (children $ uniplate x)