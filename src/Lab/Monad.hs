{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Monad
-- Description : Monad for code generation and REPL.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Monad where

import Control.Monad.Except
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import System.Console.Haskeline
import System.IO (stdout)

import Lab.Errors

-- | Lab management monad for REPL input and errors.
newtype Lab a = Lab { unLab :: ExceptT LabError (InputT IO) a}
  deriving (Monad, Functor, Applicative, MonadIO, MonadError LabError, MonadFix)

prompt :: String -> Lab (Maybe String)
prompt = Lab . lift . getInputLine

quit :: MonadIO m => m ()
quit = liftIO $ putStrLn "Goodbye."

renderPretty :: MonadIO m => Doc AnsiStyle -> m ()
renderPretty = liftIO . renderIO stdout . layoutSmart defaultLayoutOptions . (<> hardline)

renderString :: (Show a, MonadIO m) => a -> m ()
renderString = liftIO . print

runLab :: Lab a -> IO (Either LabError a)
runLab = runInputT defaultSettings . runExceptT . unLab
