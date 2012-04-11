import Debug.RocketFuel
import Fliter.Miniplate
import Fliter.Parser
import Fliter.Semantics
import Fliter.Syntax
import Supercompiler
import Example

import Control.Monad
import System.Environment
import System.Exit

scLimit :: Int
scLimit = 1000

stepLimit :: Int
stepLimit = 1000

-- Under bounded evaluation;
-- 1.  Runs a program `p` which may terminate with a value `v`.
-- 2.  Supercompile first function in `p` and call new program
--     `q`.
-- 3.  Runs the supercompiled program `q` which may terminate 
--     with a value `w`.
-- 4.  Passes if; supercompilation terminates *and* (running `p`
--     does not terminate *or* (`q` does terminate and `v == w`).
testProg :: Prog t a -> IO Bool
testProg p_ = do
  fillTank scLimit
  let p = deTagProg $ unsafeEraseProg p_
  let t = execFor stepLimit p initState
  let q = sc p $ mkLam p
  let succeed_q = goesBingo q
  let u = execFor stepLimit q initState
  putStr "> Running program... "
  case t of
    Crash  -> putStrLn $ "Crashed!"
    Halt v -> putStrLn $ "Terminated: " ++ show v
    Cont v -> putStrLn $ "Non-productive."
  putStr "> Supercompiling... "
  if succeed_q
     then do 
       fail $ "Failed!"
       return False   
     else do
       putStrLn $ "Succeeded."
       putStr "> Running supercompiled program... "
       case u of
         Crash  -> putStrLn $ "Crashed!"
         Halt w -> putStrLn $ "Terminated: " ++ show w ++ ""
         Cont w -> putStrLn $ "Non-productive."
       let res = t <| u
       if res then putStrLn "Succeeded!\n" else fail "Failed!" 
       return $ res

testProg' :: (Int, Prog t a) -> IO Bool
testProg' (i, p_) = do
  fillTank scLimit
  let p = deTagProg $ unsafeEraseProg p_
  let t = execFor stepLimit p initState
  let q = sc p $ mkLam p
  let succeed_q = goesBingo q
  let u = execFor stepLimit q initState
  if succeed_q
     then fail $ "@" ++ show i ++ ": Failed on SC!"
     else if t <| u then return True else fail $ "@" ++ show i ++ ": Failed on semantic preservation!"

mkLam :: Prog () a -> (Id, Func () a)
mkLam (Prog ps) = (fId, Lam ar $ () :> ((() :> Fun fId []) :@ [Bnd i | i <- [0..ar - 1]]))
  where (fId, Lam ar _) = last $ filter ((/= "main") . fst) ps ++ ps

goesBingo :: Prog t a -> Bool
goesBingo (Prog p) = or [ True
                        | (_, Lam _ x) <- p 
                        , Con "<BINGO>" [] <- universe $ getRhs $ x ]

(<|) :: Exec (Expr () ()) (Expr () ()) -> Exec (Expr () ()) (Expr () ()) -> Bool
Crash  <| _      = True
Cont _ <| _      = True
Halt v <| Halt w = v == w
Halt v <| _      = False

main = do
  as <- getArgs
  guard $ (not.null) as
  ps <- parseProgs $ head as
  result <- fmap and $ mapM testProg' $ zip [1..] ps
  putStrLn $ "Tested " ++ show (length ps) ++ " programs."
  if result then exitSuccess else exitFailure