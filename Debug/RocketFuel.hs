module Debug.RocketFuel where

import Data.IORef
import System.IO.Unsafe

{-# NOINLINE fuelTank #-}
fuelTank :: IORef (Maybe Int)
fuelTank = unsafePerformIO $ newIORef Nothing

disableTank :: IO ()
disableTank = writeIORef fuelTank Nothing

fillTank :: Int -> IO ()
fillTank n = writeIORef fuelTank (Just n)

{-# NOINLINE consumeFuel #-}
consumeFuel :: a -> a -> a
consumeFuel empty full = unsafePerformIO $ do
  modifyIORef fuelTank (fmap $ (+) $ -1)
  value <- readIORef fuelTank
  return $ if maybe False (<= 0) value then empty else full

readTank :: IO (Maybe Int)
readTank = readIORef fuelTank