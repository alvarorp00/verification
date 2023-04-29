{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_session20 (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/alvarorp00/Documents/uam/master/verification/liquid-haskell/session20/.stack-work/install/x86_64-linux-tinfo6/d75bdb7e14101d16d17c0fdbe3008a7eba080e3f578f80183065eed3fbe4ef7c/9.2.5/bin"
libdir     = "/home/alvarorp00/Documents/uam/master/verification/liquid-haskell/session20/.stack-work/install/x86_64-linux-tinfo6/d75bdb7e14101d16d17c0fdbe3008a7eba080e3f578f80183065eed3fbe4ef7c/9.2.5/lib/x86_64-linux-ghc-9.2.5/session20-0.1.0.0-L8LkJC9oP0d96QL0Twe3hA-session20"
dynlibdir  = "/home/alvarorp00/Documents/uam/master/verification/liquid-haskell/session20/.stack-work/install/x86_64-linux-tinfo6/d75bdb7e14101d16d17c0fdbe3008a7eba080e3f578f80183065eed3fbe4ef7c/9.2.5/lib/x86_64-linux-ghc-9.2.5"
datadir    = "/home/alvarorp00/Documents/uam/master/verification/liquid-haskell/session20/.stack-work/install/x86_64-linux-tinfo6/d75bdb7e14101d16d17c0fdbe3008a7eba080e3f578f80183065eed3fbe4ef7c/9.2.5/share/x86_64-linux-ghc-9.2.5/session20-0.1.0.0"
libexecdir = "/home/alvarorp00/Documents/uam/master/verification/liquid-haskell/session20/.stack-work/install/x86_64-linux-tinfo6/d75bdb7e14101d16d17c0fdbe3008a7eba080e3f578f80183065eed3fbe4ef7c/9.2.5/libexec/x86_64-linux-ghc-9.2.5/session20-0.1.0.0"
sysconfdir = "/home/alvarorp00/Documents/uam/master/verification/liquid-haskell/session20/.stack-work/install/x86_64-linux-tinfo6/d75bdb7e14101d16d17c0fdbe3008a7eba080e3f578f80183065eed3fbe4ef7c/9.2.5/etc"

getBinDir     = catchIO (getEnv "session20_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "session20_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "session20_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "session20_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "session20_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "session20_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
