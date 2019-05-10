module Zepto.Primitives.HashPrimitives where

import Control.Monad.Except
import Data.HashMap (keys, elems, member, delete, fromList, toList)

import Zepto.Types

hashKVDoc :: String -> String
hashKVDoc name = "get " ++ name ++ " from hashmap <par>hash</par>.\n\
\n\
  params:\n\
    - hash: the hashmap from which to get the  " ++ name ++ "\n\
  complexity: O(1)\n\
  returns: a list of " ++ name

hashKeys :: [LispVal] -> ThrowsError LispVal
hashKeys [HashMap x] = return $ List $ map SimpleVal (keys x)
hashKeys [x] = throwError $ TypeMismatch "hashmap" x
hashKeys badArgList = throwError $ NumArgs 1 badArgList

hashVals :: [LispVal] -> ThrowsError LispVal
hashVals [HashMap x] = return $ List $ elems x
hashVals [x] = throwError $ TypeMismatch "hashmap" x
hashVals badArgList = throwError $ NumArgs 1 badArgList

inHashDoc :: String
inHashDoc = "check whether an element under the key <par>el</par> is in a\n\
hashmap <par>hash</par>.\n\
\n\
  params:\n\
    - hash: the hashmap to check\n\
    - el: the element to find\n\
  complexity: O(1)\n\
  returns: boolean"

inHash :: [LispVal] -> ThrowsError LispVal
inHash [HashMap x, SimpleVal e] = return $ fromSimple $ Bool $ member e x
inHash [x, SimpleVal _] = throwError $ TypeMismatch "hashmap" x
inHash [HashMap _, e] = throwError $ TypeMismatch "simple value" e
inHash [x, _] = throwError $ TypeMismatch "hashmap and simple value" x
inHash badArgList = throwError $ NumArgs 2 badArgList

makeHashDoc :: String
makeHashDoc = "create a hashmap from a variety of inputs, from other\n\
hashmaps to pairs of keys and values.\n\
\n\
  Example:\n\
    <zepto>\n\
      (make-hash #{1 2} 3 4 [5 6]) ; => #{1 2, 3 4, 5 6}\n\
      (make-hash) ; => #{}\n\
    </zepto>\n\
\n\
  params:\n\
    - args: the arguments to create a hashmap from (varargs)\n\
  complexity: O(n)\n\
  returns: a hashmap"

makeHash :: [LispVal] -> ThrowsError LispVal
makeHash [List x] = makeHash x
makeHash l = case keyVal l [] of
              Right x -> return $ HashMap $ fromList x
              Left x  -> throwError $ TypeMismatch "simple value/hashmap/list" x
    where keyVal [] acc = Right acc
          keyVal (List [x, y] : r) acc = keyVal (x : y : r) acc
          keyVal (SimpleVal x : y : r) acc = keyVal r $ (x, y) : acc
          keyVal (HashMap x : r) acc = keyVal r $ acc ++ toList x
          keyVal (x : _)  _ = Left x

hashRemoveDoc :: String
hashRemoveDoc = "remove an element under the key <par>el</par> from a hashmap\n\
<par>hash</par>.\n\
\n\
  params:\n\
    - hash: the hashmap from which to delete <par>el</par>\n\
    - el: the element to delete\n\
  complexity: O(1)\n\
  returns: the hashmap without <par>el</par>"

hashRemove :: [LispVal] -> ThrowsError LispVal
hashRemove [HashMap x, SimpleVal e] = return $ HashMap $ delete e x
hashRemove [x, SimpleVal _] = throwError $ TypeMismatch "hashmap" x
hashRemove [HashMap _, e] = throwError $ TypeMismatch "simple value" e
hashRemove [x, _] = throwError $ TypeMismatch "hashmap and simple value" x
hashRemove badArgList = throwError $ NumArgs 2 badArgList
