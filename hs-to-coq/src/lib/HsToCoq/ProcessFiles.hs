{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (processFile, processFileFlags) where

import Control.Monad
import Control.Monad.IO.Class

import System.FilePath

import GHC
import HeaderInfo
import DynFlags
import Bag
import DoCpp

import HsToCoq.Util.TempFiles
import HsToCoq.Util.Messages

parseFileFlags :: GhcMonad m
               => ([Located String] -> [Located String] -> m ())
               -> DynFlags -> FilePath
               -> m DynFlags
parseFileFlags handleExtra dflags file = do
  (fileDflags, restOpts, optWarns) <-
    parseDynamicFilePragma dflags =<< liftIO (getOptionsFromFile dflags file)
  handleExtra restOpts optWarns
  void $ setSessionDynFlags fileDflags
  getSessionDynFlags

processFileFlags :: (GhcMonad m, MonadIO m) => DynFlags -> FilePath -> m DynFlags
processFileFlags = parseFileFlags $ \restOpts optWarns -> do
  printAllIfPresent unLoc "Leftover option" restOpts
  printAllIfPresent unLoc "Option warning"  optWarns

processFile :: GhcMonad m
            => (Located (HsModule RdrName) -> m a) -> DynFlags -> FilePath -> m (Maybe a)
processFile process dflags file = do
  withSrcFile <- do
    dflags' <- processFileFlags dflags file
    pure $ if not $ xopt Opt_Cpp dflags'
           then \fn -> fn dflags' file
           else \fn -> gWithSystemTempFile (takeFileName file) $ \temp _ -> do
                         liftIO $ doCpp dflags' True file temp
                         dflags'' <- processFileFlags dflags temp
                         fn dflags'' temp
  
  withSrcFile $ \fileDflags srcFile ->
    parser <$> liftIO (readFile srcFile) <*> pure fileDflags <*> pure file >>= \case
      Left  errs          -> Nothing <$ printMessages "failed" "error" errs
      Right (warns, lmod) -> do
        printMessages "succeeded" "warning" warns
        Just <$> process lmod
  where
    printMessages result msgType =
      printAll' show
                ("Parsing `" ++ file ++ "' " ++ result)
                (" with " ++ msgType)
      . bagToList