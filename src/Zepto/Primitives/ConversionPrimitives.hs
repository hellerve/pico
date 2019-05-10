module Zepto.Primitives.ConversionPrimitives where
import Control.Exception (evaluate)
import Control.Monad.Except (throwError, liftIO)
import Data.Binary (encode, decode)
import Data.ByteString.Lazy (toStrict, fromStrict)
import Data.Char (ord, chr)
import Data.Complex (realPart, imagPart)
import Data.IORef (readIORef)
import Data.HashMap (empty, foldWithKey, insert)
import qualified Data.ByteString.Lazy as BSL (concat)

import Zepto.Types
import Zepto.Variables (allBindings)

env2HashMapDoc :: String
env2HashMapDoc = "converts an environment to a hashmap.\n\
\n\
  params:\n\
    - env: the environment to convert\n\
  complexity: O(n)\n\
  returns: a hashmap mapping the function names as strings to the functions"

env2HashMap :: LispVal -> IOThrowsError LispVal
env2HashMap (Environ x) = do
        env <- liftIO $ allBindings x
        hashmap <- liftIO $ foldWithKey accum (evaluate empty) env
        return $ HashMap hashmap
    where accum k v acc = do
            nv <- readIORef v
            nacc <- liftIO acc
            return $ insert (String $ drop 2 k) nv nacc
env2HashMap x = throwError $ TypeMismatch "env" x

conversionDoc :: String -> String -> String
conversionDoc from to = "convert a " ++ from ++ " to a " ++ to ++ ".\n\
\n\
  params:\n\
    - input: the input " ++ from ++ " to convert\n\
  complexity: O(n)\n\
  returns: " ++ to

symbol2String :: LispVal -> ThrowsError LispVal
symbol2String (SimpleVal (Atom a)) = return $ fromSimple $ String a
symbol2String notAtom = throwError $ TypeMismatch "symbol" notAtom

string2Symbol :: LispVal -> ThrowsError LispVal
string2Symbol (SimpleVal (String s)) = return $ fromSimple $ Atom s
string2Symbol notString = throwError $ TypeMismatch "string" notString

charToInteger :: LispVal -> ThrowsError LispVal
charToInteger (SimpleVal (Character c)) = return $ fromSimple $ Number $ NumI $ toInteger $ ord c
charToInteger notChar = throwError $ TypeMismatch "character" notChar

number2String :: [LispVal] -> ThrowsError LispVal
number2String [SimpleVal (Number x)] = return $ fromSimple $ String $ show x
number2String [SimpleVal (Number x), SimpleVal (Number (NumI y))] = return $ fromSimple $ String $ interpolate (show x) (fromInteger y)
    where interpolate s n = if length s < n then interpolate ('0' : s) n else s
number2String [SimpleVal (Number x), SimpleVal (Number (NumS y))] = return $ fromSimple $ String $ interpolate (show x) y
    where interpolate s n = if length s < n then interpolate ('0' : s) n else s
number2String [SimpleVal (Number _), notNumber] = throwError $ TypeMismatch "integer" notNumber
number2String [notNumber, _] = throwError $ TypeMismatch "number" notNumber
number2String n = throwError $ NumArgs 1 n

integer2Char :: LispVal -> ThrowsError LispVal
integer2Char (SimpleVal (Number (NumI x))) = return $ fromSimple $ Character $ chr $ fromInteger x
integer2Char (SimpleVal (Number (NumS x))) = return $ fromSimple $ Character $ chr x
integer2Char notInt = throwError $ TypeMismatch "integer" notInt

buildNil :: ThrowsError LispVal
buildNil = return $ fromSimple $ Nil ""

buildInf :: ThrowsError LispVal
buildInf = return $ fromSimple $ Number $ NumF $ 1 / 0

list2Simple :: LispVal -> ThrowsError LispVal
list2Simple (List x) = if all simple x
                        then return $ fromSimple $ SimpleList $ map toSimple x
                        else throwError $ BadSpecialForms "expected simple elements"
                             (filter (not . simple) x)
    where simple (SimpleVal _) = True
          simple _ = False
list2Simple notList = throwError $ TypeMismatch "list" notList

simple2List :: LispVal -> ThrowsError LispVal
simple2List (SimpleVal (SimpleList x)) = return $ List $ map fromSimple x
simple2List notList = throwError $ TypeMismatch "list" notList

number2Bytes :: LispVal -> ThrowsError LispVal
number2Bytes (SimpleVal (Number (NumS x))) = return $ ByteVector $ toStrict $ encode x
number2Bytes (SimpleVal (Number (NumI x))) = return $ ByteVector $ toStrict $ encode x
number2Bytes (SimpleVal (Number (NumF x))) = return $ ByteVector $ toStrict $ encode x
number2Bytes (SimpleVal (Number (NumR x))) = return $ ByteVector $ toStrict $ encode x
number2Bytes (SimpleVal (Number (NumC x))) =
        return $ ByteVector $ toStrict $ BSL.concat $ map encode [realPart x, imagPart x]
number2Bytes x = throwError $ TypeMismatch "number" x

bytes2Float :: LispVal -> ThrowsError LispVal
bytes2Float (ByteVector x) = return $ fromSimple $ Number $ NumF $ decode $ fromStrict x
bytes2Float x = throwError $ TypeMismatch "byte-vector" x
