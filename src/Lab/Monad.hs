{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lab.Monad where

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Control.Monad.Except
import System.Console.Haskeline
import System.IO (stdout)

import Lab.Errors

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

runLab :: Lab a -> InputT IO (Either LabError a)
runLab = runExceptT . unLab
