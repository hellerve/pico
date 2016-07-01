module Zepto.Primitives.IOPrimitives where
import Control.Monad (liftM)
import Control.Monad.Except (liftIO, throwError)
import Crypto.Number.Generate (generateBetween)
import System.Directory (doesFileExist, getHomeDirectory, getCurrentDirectory,
                         setCurrentDirectory)
import System.Environment (getEnv, setEnv)
import System.Exit
import System.IO
import System.IO.Error (tryIOError)
import System.Process (readProcessWithExitCode)
import System.Clock

import qualified System.IO.Strict as S (readFile)
import qualified Data.ByteString as BS (readFile)

import Zepto.Types

import Paths_zepto

changeDir :: LispVal -> IOThrowsError LispVal
changeDir (SimpleVal (String dir)) = do
  _ <- liftIO $ setCurrentDirectory dir
  return $ fromSimple $ Bool True
changeDir x = throwError $ TypeMismatch "string" x


getHomeDir :: IOThrowsError LispVal
getHomeDir = do
  dir <- liftIO getHomeDirectory
  return $ fromSimple $ String dir

getZeptoDir :: IOThrowsError LispVal
getZeptoDir = do
  dir <- liftIO $ getDataFileName ""
  return $ fromSimple $ String dir

getCurrentDir :: IOThrowsError LispVal
getCurrentDir = do
  dir <- liftIO getCurrentDirectory
  return $ fromSimple $ String dir

makePort :: IOMode -> [LispVal] -> IOThrowsError LispVal
makePort mode [SimpleVal (String filename)] = do
         fex <- liftIO $ doesFileExist filename
         if not fex && mode == ReadMode
           then return $ fromSimple $ Bool False
           else liftM Port $ liftIO $ openFile filename mode
makePort _ badArgs = throwError $ BadSpecialForm "Cannot evaluate " $ head badArgs

closePort :: [LispVal] -> IOThrowsError LispVal
closePort [Port port] = liftIO $ hClose port >> return (fromSimple (Bool True))
closePort _ = return $ fromSimple $ Bool False

writeProc :: (Handle -> LispVal -> IO a) -> [LispVal] -> IOThrowsError LispVal
writeProc fun [obj] = writeProc fun [obj, Port stdout]
writeProc fun [obj, SimpleVal (Atom ":stdout")] = writeProc fun [obj, Port stdout]
writeProc fun [obj, SimpleVal (Atom ":stderr")] = writeProc fun [obj, Port stderr]
writeProc fun [obj, Port port] = do
      out <- liftIO $ tryIOError (liftIO $ fun port obj)
      case out of
          Left _ -> throwError $ Default "IO Error writing to port"
          Right _ -> return $ fromSimple $ Nil ""
writeProc fun [obj, a@(SimpleVal (Atom ":flush"))] = writeProc fun [obj, Port stdout, a]
writeProc fun [obj, SimpleVal (Atom ":stdout"), a@(SimpleVal (Atom ":flush"))] = writeProc fun [obj, Port stdout, a]
writeProc fun [obj, SimpleVal (Atom ":stderr"), a@(SimpleVal (Atom ":flush"))] = writeProc fun [obj, Port stderr, a]
writeProc fun [obj, Port port, SimpleVal (Atom ":flush")] = do
      out <- liftIO $ tryIOError (liftIO $ fun port obj)
      case out of
          Left _ -> throwError $ Default "IO Error writing to port"
          Right _ -> do
              flush <- liftIO $ tryIOError (liftIO $ hFlush port)
              case flush of
                Left _ -> throwError $ Default "IO Error flushing port"
                Right _ -> return $ fromSimple $ Nil ""
writeProc _ [] = throwError $ NumArgs 1 []
writeProc _ badArgs = throwError $ BadSpecialForm "Cannot evaluate " $ head badArgs

writeCharProc :: [LispVal] -> IOThrowsError LispVal
writeCharProc [obj] = writeCharProc [obj, Port stdout]
writeCharProc [obj, SimpleVal (Atom ":stdout")] = writeCharProc [obj, Port stdout]
writeCharProc [obj, SimpleVal (Atom ":stderr")] = writeCharProc [obj, Port stderr]
writeCharProc [obj@(SimpleVal (Character _)), Port port] = do
      out <- liftIO $ tryIOError (liftIO $ hPutStr port (show obj))
      case out of
          Left _ -> throwError $ Default "IO Error writing to port"
          Right _ -> return $ fromSimple $ Nil ""
writeCharProc [wrong, _] = throwError $ TypeMismatch "char" wrong
writeCharProc [] = throwError $ NumArgs 1 []
writeCharProc badArgs = throwError $ BadSpecialForm "Cannot evaluate " $ head badArgs

print' :: Handle -> LispVal -> IO ()
print' port obj =
      case obj of
          SimpleVal (String str) -> hPutStr port str
          _ -> hPutStr port $ show obj

readContents :: [LispVal] -> IOThrowsError LispVal
readContents [SimpleVal (String filename)] = liftM (SimpleVal . String) $ liftIO $ S.readFile filename
readContents [Port handle] = liftM (SimpleVal . String) $ liftIO $ hGetContents handle
readContents [x] = throwError $ TypeMismatch "string" x
readContents badArgs = throwError $ NumArgs 1 badArgs

readBinaryContents :: [LispVal] -> IOThrowsError LispVal
readBinaryContents [SimpleVal (String filename)] = liftM ByteVector $ liftIO $ BS.readFile filename
readBinaryContents [x] = throwError $ TypeMismatch "string" x
readBinaryContents badArgs = throwError $ NumArgs 1 badArgs

exitProc :: [LispVal] -> IOThrowsError LispVal
exitProc [] = do _ <- liftIO $ tryIOError $ liftIO exitSuccess
                 return $ fromSimple $ Nil ""
exitProc [SimpleVal (Number (NumI 0))] = do _ <- liftIO $ tryIOError $ liftIO exitSuccess
                                            return $ fromSimple $ Nil ""
exitProc [SimpleVal (Number (NumS 0))] = do _ <- liftIO $ tryIOError $ liftIO exitSuccess
                                            return $ fromSimple $ Nil ""
exitProc [SimpleVal (Number (NumI x))] = do _ <- liftIO $ tryIOError $ liftIO $
                                              exitWith $ ExitFailure $ fromInteger x
                                            return $ fromSimple $ Nil ""
exitProc [SimpleVal (Number (NumS x))] = do _ <- liftIO $ tryIOError $ liftIO $
                                              exitWith $ ExitFailure x
                                            return $ fromSimple $ Nil ""
exitProc [x] = throwError $ TypeMismatch "integer" x
exitProc badArg = throwError $ NumArgs 1 badArg

timeProc :: IOThrowsError LispVal
timeProc = do x <- liftIO $ getTime Realtime
              return $ List [makeNum (sec x), makeNum (nsec x)]
    where makeNum n = fromSimple $ Number $ NumI $ fromIntegral n

systemProc :: [LispVal] -> IOThrowsError LispVal
systemProc [SimpleVal (String s)] = do
        x <- liftIO $ tryIOError $ liftIO $ readProcessWithExitCode s [] ""
        case x of
          Right el ->
            case fst3 el of
              ExitSuccess -> return $ List $ fromSimple (Number $ NumI 0) : fromSimple (String $ snd3 el) : [fromSimple $ String $ thd3 el]
              ExitFailure w -> return $ List $ fromSimple (Number $ NumI $ fromIntegral w) : fromSimple (String $ snd3 el) : [fromSimple $ String $ thd3 el]
          Left w -> throwError $ Default $ show w
systemProc [SimpleVal (String s), List given] = do
        let margs = unpackList given
        case margs of
          Right args -> do
            x <- liftIO $ tryIOError $ liftIO $ readProcessWithExitCode s args ""
            case x of
              Right el ->
                case fst3 el of
                  ExitSuccess -> return $ List $ fromSimple (Number $ NumI 0) : fromSimple (String $ snd3 el) : [fromSimple $ String $ thd3 el]
                  ExitFailure w -> return $ List $ fromSimple (Number $ NumI $ fromIntegral w) : fromSimple (String $ snd3 el) : [fromSimple $ String $ thd3 el]
              Left w -> throwError $ Default $ show w
          Left err -> throwError $ TypeMismatch "string" err
    where unpackList :: [LispVal] -> Either LispVal [String]
          unpackList pack =
            if all isString pack
              then Right $ map unpack' pack
              else Left $ notString pack
          isString (SimpleVal (String _)) = True
          isString _ = False
          unpack' (SimpleVal (String e)) = e
          unpack' _ = ""
          notString [] = fromSimple $ Nil ""
          notString (SimpleVal (String _):l) = notString l
          notString (err:_) = err
systemProc [x] = throwError $ TypeMismatch "string" x
systemProc badArg = throwError $ NumArgs 1 badArg

randIntProc :: [LispVal] -> IOThrowsError LispVal
randIntProc [] = randIntProc [fromSimple $ Number $ NumI $ toInteger (minBound :: Int),
                              fromSimple $ Number $ NumI $ toInteger (maxBound :: Int)]
randIntProc [mx] = randIntProc [fromSimple $ Number $ NumI $ toInteger (minBound :: Int), mx]
randIntProc [SimpleVal (Number (NumI mn)), SimpleVal (Number (NumI mx))] = do
  n <- liftIO $ generateBetween mn mx
  return $ fromSimple $ Number $ NumI n
randIntProc [SimpleVal (Number (NumI _)), x] = throwError $ TypeMismatch "integer" x
randIntProc [x, _] = throwError $ TypeMismatch "integer" x
randIntProc x = throwError $ NumArgs 2 x

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

thd3 :: (a, b, c) -> c
thd3 (_, _, x) = x

getEnvProc :: LispVal -> IOThrowsError LispVal
getEnvProc (SimpleVal (String var)) = do
  val <- liftIO $ getEnv var
  return $ fromSimple $ String val
getEnvProc x = throwError $ TypeMismatch "string" x

setEnvProc :: [LispVal] -> IOThrowsError LispVal
setEnvProc [SimpleVal (String var), SimpleVal (String val)] = do
  _ <- liftIO $ setEnv var val
  return $ fromSimple $ Nil ""
setEnvProc [SimpleVal (String _), x] = throwError $ TypeMismatch "string" x
setEnvProc [x, _] = throwError $ TypeMismatch "string" x
setEnvProc x = throwError $ NumArgs 2 x
