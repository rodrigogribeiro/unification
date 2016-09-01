module Paths_infer (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/rodrigo/Dropbox/projects/coq/infer/infer/.stack-work/install/x86_64-osx/lts-6.7/7.10.3/bin"
libdir     = "/Users/rodrigo/Dropbox/projects/coq/infer/infer/.stack-work/install/x86_64-osx/lts-6.7/7.10.3/lib/x86_64-osx-ghc-7.10.3/infer-0.1.0.0-LATtaxaRTSJFnVvXBzV43n"
datadir    = "/Users/rodrigo/Dropbox/projects/coq/infer/infer/.stack-work/install/x86_64-osx/lts-6.7/7.10.3/share/x86_64-osx-ghc-7.10.3/infer-0.1.0.0"
libexecdir = "/Users/rodrigo/Dropbox/projects/coq/infer/infer/.stack-work/install/x86_64-osx/lts-6.7/7.10.3/libexec"
sysconfdir = "/Users/rodrigo/Dropbox/projects/coq/infer/infer/.stack-work/install/x86_64-osx/lts-6.7/7.10.3/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "infer_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "infer_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "infer_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "infer_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "infer_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
