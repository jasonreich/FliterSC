module RocketFuel where

import Data.IORef
import System.IO.Unsafe

{-# NOINLINE fuelTank #-}
fuelTank :: IORef Int
fuelTank = unsafePerformIO $ newIORef 0

fillTank :: Int -> IO ()
fillTank n = writeIORef fuelTank n

{-# NOINLINE consumeFuel #-}
consumeFuel :: a -> a -> a
consumeFuel empty full = unsafePerformIO $ do
  modifyIORef fuelTank ((+) $ -1)
  value <- readIORef fuelTank
  return $ if value <= 0 then empty else full

readTank :: IO Int
readTank = readIORef fuelTank