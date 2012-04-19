import Debug.RocketFuel
import Fliter.Miniplate
import Fliter.Parser
import Fliter.Semantics
import Fliter.Syntax
import Supercompiler
import Example

import Control.Monad
import Data.IORef
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
testProg :: IORef (Int, Int) -> (Int, Prog t a) -> IO Bool
testProg counters (i, p_) = do
  incCounter counters False
  when (i `mod` 10000 == 0) $ putStrLn $ "(Checked " ++ show i ++ ")"
  fillTank scLimit
  let p = deTagProg $ unsafeEraseProg p_
  let (m, t) = execFor stepLimit p initState
  let q = sc p $ mkLam p
  let succeed_q = goesBingo q
  let (n, u) = execFor stepLimit q initState
  when (n < m) $ incCounter counters True
  if succeed_q
     then do print $ fmap (const ()) p_
             showExec t
             putStrLn ""
             fail $ "@" ++ show i ++ ": Failed on SC!"
     else if t <| u 
             then if (n <= m) 
                     then return True 
                     else do print $ fmap (const ()) p_
                             showExec t
                             putStrLn ""
                             print q
                             putStrLn ""
                             fail $ "@" ++ show i ++ ": Failed on optimisation! " ++ show m ++ " < " ++ show n
             else do print $ fmap (const ()) p_
                     showExec t
                     putStrLn ""
                     print q
                     showExec u
                     putStrLn ""
                     fail $ "@" ++ show i ++ ": Failed on semantic preservation!"

incCounter counters switch = do
  (total, improved) <- readIORef counters
  let total' = if switch then total + 1 else total
  let improved' = if switch then improved else improved + 1
  total' `seq` improved' `seq` writeIORef counters (total', improved')

showExec t = case t of
    Crash  -> putStrLn $ "Crashed!"
    Halt v -> putStrLn $ "Terminated: " ++ show v
    Cont v -> putStrLn $ "Non-productive."

mkLam :: Prog () a -> (Id, Func () a)
mkLam (Prog ps) = (fId, Lam ar $ () :> ((() :> Fun fId []) :@ [Bnd i | i <- [0..ar - 1]]))
  where ps' = filter ((/= "main") . fst) ps
        (fId, Lam ar _) = if null ps' then head ps else last ps'

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
  counters <- newIORef (0, 0)
  as <- getArgs
  guard $ (not.null) as
  ps <- parseProgs $ head as
  mapM_ (testProg counters) $ zip [1..] ps  
  (total, improved) <- readIORef counters
  putStrLn $ "Tested " ++ show total ++ " programs of which " ++ show improved ++ " strictly improved performance."