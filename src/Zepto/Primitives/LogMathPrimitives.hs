module Zepto.Primitives.LogMathPrimitives where
import Control.Monad.Except
import Data.Array (elems)
import Data.Bits (shift, (.&.), (.|.), complement, shiftR, shiftL, xor)
import Data.Char
import Data.Complex
import Data.Word (Word32)

import qualified Data.HashMap as DM (toList)
import qualified Data.Ratio as Ratio (numerator, denominator)
import qualified Text.Regex.PCRE.Light.Base as R

import Zepto.Types

eqvDoc :: String
eqvDoc = "check equality of two zepto objects\n\
\n\
  params:\n\
    - a: the first object\n\
    - b: the second object\n\
  complexity: depends on complexity of object\n\
  returns: a boolean"

eqv :: [LispVal] -> ThrowsError LispVal
eqv [SimpleVal (Bool arg1), SimpleVal (Bool arg2)] = return $ fromSimple $ Bool $ arg1 == arg2
eqv [SimpleVal (Number arg1), SimpleVal (Number arg2)] = return $ fromSimple $ Bool $ arg1 == arg2
eqv [SimpleVal (String arg1), SimpleVal (String arg2)] = return $ fromSimple $ Bool $ arg1 == arg2
eqv [SimpleVal (Character arg1), SimpleVal (Character arg2)] = return $ fromSimple $ Bool $ arg1 == arg2
eqv [SimpleVal (Atom arg1), SimpleVal (Atom arg2)] = return $ fromSimple $ Bool $ arg1 == arg2
eqv [SimpleVal (Nil _), SimpleVal (Nil _)] = return $ fromSimple $ Bool True
eqv [DottedList xs x, DottedList ys y] = eqv [List $ xs ++ [x], List $ ys ++ [y]]
-- all of those function checks are dirty hacks
eqv [x@(EvalFunc _ _), y@(EvalFunc _ _)] = return $ fromSimple $ Bool $ show x == show y
eqv [x@(PrimitiveFunc _ _), y@(PrimitiveFunc _ _)] = return $ fromSimple $ Bool $ show x == show y
eqv [Func x _, Func y _] = return $ fromSimple $ Bool $ x == y
eqv [ByteVector x, ByteVector y] = return $ fromSimple $ Bool $ x == y
eqv [x@(IOFunc _ _), y@(IOFunc _ _)] = return $ fromSimple $ Bool $ show x == show y
eqv [SimpleVal (SimpleList arg1), SimpleVal (SimpleList arg2)] =
        return $ fromSimple $ Bool $ (length arg1 == length arg2) &&
                                     and (zipWith (curry eqvPair) arg1 arg2)
    where eqvPair (x, y) = case eqv [fromSimple x, fromSimple y] of
                                  Left _ -> False
                                  Right (SimpleVal (Bool val)) -> val
                                  _ -> False
eqv [List arg1, List arg2] = return $ fromSimple $ Bool $ (length arg1 == length arg2) &&
                                  and (zipWith (curry eqvPair) arg1 arg2)
    where eqvPair (x, y) = case eqv[x, y] of
                              Left _ -> False
                              Right (SimpleVal (Bool val)) -> val
                              _ -> False
eqv [Vector arg1, Vector arg2] = eqv [List (elems arg1), List (elems arg2)]
eqv [HashMap arg1, HashMap arg2] = eqv [List $ mkList (DM.toList arg1), List $ mkList (DM.toList arg2)]
    where mkList [] = []
          mkList ((a, b) : cs) = [fromSimple a, b] ++ mkList cs
eqv [Environ x, Environ y] = return $ fromSimple $ Bool $ x == y
-- TODO: that's both dumb and inefficient
eqv [Error x, Error y] = return $ fromSimple $ Bool $ show x == show y
eqv [SimpleVal (Regex (R.Regex _ x)), SimpleVal (Regex (R.Regex _ y))] =
  return $ fromSimple $ Bool $ x == y
eqv [_, _] = return $ fromSimple $ Bool False
eqv badArgList = throwError $ NumArgs 2 badArgList

eqvList :: ([LispVal] -> ThrowsError LispVal) -> [LispVal] -> ThrowsError LispVal
eqvList eqvFunc [List arg1, List arg2] =
        return $ fromSimple $ Bool $ (length arg1 == length arg2) && all eqvPair (zip arg1 arg2)
    where eqvPair (x1, x2) = case eqvFunc [x1, x2] of
                                Left _                       -> False
                                Right (SimpleVal (Bool val)) -> val
                                _                            -> False
eqvList _ _ = throwError $ InternalError "Unexpected error in eqvList"

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals x y (AnyUnpacker unpacker) =
        do unpacked1 <- unpacker x
           unpacked2 <- unpacker y
           return $ unpacked1 == unpacked2
        `catchError` const (return False)

equal :: [LispVal] ->ThrowsError LispVal
equal [lx@(List _), ly@(List _)] = eqvList equal [lx, ly]
equal [DottedList xs x, DottedList ys y] = equal [List $ xs ++ [x], List $ ys ++ [y]]
equal [Vector arg1, Vector arg2] = eqvList equal [List (elems arg1), List (elems arg2)]
equal [x, y] = do
           primitiveEquals <- liftM or $ mapM (unpackEquals x y)
                              [AnyUnpacker unpackNum, AnyUnpacker unpackStr,
                               AnyUnpacker unpackBool]
           eqvEquals <- eqv [x, y]
           return $ fromSimple $ Bool (primitiveEquals || let (SimpleVal (Bool z)) = eqvEquals in z)
equal badArgList = throwError $ NumArgs 2 badArgList

numericBinOpDoc :: String
numericBinOpDoc = "\n\
\n\
  params:\n\
    - args: varargs of two or more\n\
  complexity: O(n)\n\
  returns: a number"

numericBinop :: (LispNum -> LispNum -> LispNum) -> [LispVal] -> ThrowsError LispVal
numericBinop _ singleVal@[_] = throwError $ NumArgs 2 singleVal
numericBinop op p = liftM (fromSimple . Number . foldl1 op) (mapM unpackNum p)

numericBinopErr :: (LispNum -> LispNum -> ThrowsError LispVal) -> [LispVal] -> ThrowsError LispVal
numericBinopErr op [x, y] = do
    a <- unpackNum x
    b <- unpackNum y
    op a b
numericBinopErr _ l = throwError $ NumArgs 2 l

minDoc :: String
minDoc = "subtract values/negate value\n\
\n\
  params:\n\
    - args: varargs to subtract (negate if only one argument is specified)\n\
  complexity: O(n) where n is the number of arguments\n\
  returns: a numerical value"

numericMinop :: (LispNum -> LispNum -> LispNum) -> [LispVal] -> ThrowsError LispVal
numericMinop _ [SimpleVal (Number l)] = return $ fromSimple $ Number $ negate l
numericMinop op p = liftM (fromSimple . Number . foldl1 op) (mapM unpackNum p)

timesDoc :: String
timesDoc = "multiply  values\n\
\n\
  params:\n\
    - args: varargs to multiply (1 if none is given)\n\
  complexity: O(n) where n is the number of arguments\n\
  returns: a numerical value"

numericTimesop :: (LispNum -> LispNum -> LispNum) -> [LispVal] -> ThrowsError LispVal
numericTimesop _ [] = return $ fromSimple $ Number 1
numericTimesop op p = liftM (fromSimple . Number . foldl1 op) (mapM unpackNum p)

plusDoc :: String
plusDoc = "add values\n\
\n\
  params:\n\
    - args: varargs to sum (0 if none is given)\n\
  complexity: O(n) where n is the number of arguments\n\
  returns: a numerical value"

numericPlusop :: (LispNum -> LispNum -> LispNum) -> [LispVal] -> ThrowsError LispVal
numericPlusop _ [] = return $ fromSimple $ Number 0
numericPlusop _ [SimpleVal (Number l)] = if l > 0 then return $ fromSimple $ Number l
                                      else return $ fromSimple $ Number $ negate l
numericPlusop op p = liftM (fromSimple . Number . foldl1 op) (mapM unpackNum p)

divDoc :: String
divDoc = "divide two or more value\n\
\n\
  params:\n\
    - args: varargs to div\n\
  complexity: O(n) where n is the number of arguments\n\
  returns: a numerical values"

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2
                             then throwError $ NumArgs 2 args
                             else do left <- unpacker $ head args
                                     right <- unpacker $ args !! 1
                                     return $ fromSimple $ Bool $ left `op` right

boolMulDoc :: String
boolMulDoc = "\n\
\n\
params:\n\
 - x: a boolean\n\
 - y: a boolean\n\
complexity: O(1)\n\
returns: a boolean"

boolMulop :: (Bool -> Bool -> Bool) -> [LispVal] -> ThrowsError LispVal
boolMulop op p = liftM (SimpleVal . Bool . foldl1 op) (mapM unpackBool p)

numBoolDoc :: String
numBoolDoc = "\n\
\n\
  params:\n\
    - x: the first arg (can be any numerical type)\n\
    - y: the second arg (can be any numerical type)\n\
  complexity: O(1)\n\
  returns: a boolean"

numBoolBinop :: (LispNum -> LispNum -> Bool) -> [LispVal] -> ThrowsError LispVal
numBoolBinop = boolBinop unpackNum

strBoolDoc :: String
strBoolDoc = "\n\
\n\
  params:\n\
    - x: the first arg (must be a string)\n\
    - y: the second arg (must be a string)\n\
  complexity: O(1)\n\
  returns: a boolean"

strBoolBinop :: (String -> String -> Bool) -> [LispVal] -> ThrowsError LispVal
strBoolBinop = boolBinop unpackStr

strCIBoolBinop :: (String -> String -> Bool) -> [LispVal] -> ThrowsError LispVal
strCIBoolBinop = boolBinop unpackCIStr

unaryDoc :: String -> String -> String
unaryDoc complexity returns = "\n\
\n\
  params:\n\
    - x: the function argument\n\
  complexity: " ++ complexity ++ "\n\
  returns: " ++ returns

unpackNum :: LispVal -> ThrowsError LispNum
unpackNum (SimpleVal (Number n)) = return n
unpackNum notNum = throwError $ TypeMismatch "number" notNum

unpackStr :: LispVal -> ThrowsError String
unpackStr (SimpleVal (String s)) = return s
unpackStr notString = throwError $ TypeMismatch "string" notString

unpackCIStr :: LispVal -> ThrowsError String
unpackCIStr (SimpleVal (String s)) = return $ fmap toLower s
unpackCIStr notString = throwError $ TypeMismatch "string" notString

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (SimpleVal (Bool b)) = return b
unpackBool notBool = throwError $ TypeMismatch "boolean" notBool

roundOpDoc :: String
roundOpDoc = "\n\
\n\
  params:\n\
    - n: number to round (can be any numerical type)\n\
  complexity: O(1)\n\
  returns: the rounded number"

numRound :: (Double -> Integer) -> [LispVal] -> ThrowsError LispVal
numRound _ [n@(SimpleVal (Number (NumI _)))] = return n
numRound _ [n@(SimpleVal (Number (NumS _)))] = return n
numRound op [SimpleVal (Number (NumF n))] = return $ fromSimple $ Number $ NumI $ op n
numRound op [SimpleVal (Number (NumC n))] = return $ fromSimple $ Number $ NumC $ fromInteger (op $ realPart n) :+ fromInteger (op $ imagPart n)
numRound op [SimpleVal (Number (NumR n))] = return $ fromSimple $ Number $ NumI $ op $ fromRational n
numRound _ [x] = throwError $ TypeMismatch "number" x
numRound _ badArgList = throwError $ NumArgs 1 badArgList

makeSmallDoc :: String
makeSmallDoc = "create a small integer from an integer <par>n</par>. If no\n\
number <par>n</par> is provided, 0 will be returned.\n\
\n\
Warning: The number can overflow!\n\
\n\
  params:\n\
    - n: the number to convert\n\
  complexity: O(1)\n\
  returns: small integer"

makeSmall :: [LispVal] -> ThrowsError LispVal
makeSmall [] = return $ fromSimple $ Number $ NumS $ fromInteger 0
makeSmall [SimpleVal (Number (NumI n))] = return $ fromSimple $ Number $ NumS $ fromInteger n
makeSmall [badType] = throwError $ TypeMismatch "integer" badType
makeSmall badArgList = throwError $ NumArgs 1 badArgList

bitwiseDoc :: String
bitwiseDoc = "\n\
\n\
  params:\n\
    - n: the number to perform the operation on\n\
  complexity: O(1)\n\
  returns: the manipulated number"

arithmeticShift :: [LispVal] -> ThrowsError LispVal
arithmeticShift [SimpleVal (Number (NumI n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumI $ shift n (fromInteger s)
arithmeticShift [SimpleVal (Number (NumI n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumI $ shift n s
arithmeticShift [SimpleVal (Number (NumS n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumS $ shift n (fromInteger s)
arithmeticShift [SimpleVal (Number (NumS n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumS $ shift n s
arithmeticShift [badType, SimpleVal (Number _)] = throwError $ TypeMismatch "integer" badType
arithmeticShift [SimpleVal (Number _), badType] = throwError $ TypeMismatch "integer" badType
arithmeticShift [badType, _] = throwError $ TypeMismatch "integer" badType
arithmeticShift badArgList = throwError $ NumArgs 2 badArgList

-- This shouldn't behave differently than shift but somehow it does
shift' :: Word32 -> Int -> Word32
shift' n s = if s > 0 then shiftL n s else shiftR n (abs s)

unsignedArithmeticShift :: [LispVal] -> ThrowsError LispVal
unsignedArithmeticShift [SimpleVal (Number (NumI n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumI $ fromIntegral $ shift' (fromInteger n) (fromInteger s)
unsignedArithmeticShift [SimpleVal (Number (NumI n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumI $ fromIntegral $ shift' (fromInteger n) s
unsignedArithmeticShift [SimpleVal (Number (NumS n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumI $ fromIntegral $ shift' (fromIntegral n) (fromInteger s)
unsignedArithmeticShift [SimpleVal (Number (NumS n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumS $ fromIntegral $ shift' (fromIntegral n) s
unsignedArithmeticShift [badType, SimpleVal (Number _)] = throwError $ TypeMismatch "integer" badType
unsignedArithmeticShift [SimpleVal (Number _), badType] = throwError $ TypeMismatch "integer" badType
unsignedArithmeticShift [badType, _] = throwError $ TypeMismatch "integer" badType
unsignedArithmeticShift badArgList = throwError $ NumArgs 2 badArgList

bitwiseAnd :: [LispVal] -> ThrowsError LispVal
bitwiseAnd [SimpleVal (Number (NumI n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumI $ n .&. s
bitwiseAnd [SimpleVal (Number (NumI n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumI $ n .&. fromIntegral s
bitwiseAnd [SimpleVal (Number (NumS n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumS $ n .&. s
bitwiseAnd [badType, SimpleVal (Number _)] = throwError $ TypeMismatch "integer" badType
bitwiseAnd [SimpleVal (Number _), badType] = throwError $ TypeMismatch "integer" badType
bitwiseAnd [badType, _] = throwError $ TypeMismatch "integer" badType
bitwiseAnd badArgList = throwError $ NumArgs 2 badArgList

bitwiseOr :: [LispVal] -> ThrowsError LispVal
bitwiseOr [SimpleVal (Number (NumI n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumI $ n .|. s
bitwiseOr [SimpleVal (Number (NumI n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumI $ n .|. fromIntegral s
bitwiseOr [SimpleVal (Number (NumS n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumS $ n .|. s
bitwiseOr [badType, SimpleVal (Number _)] = throwError $ TypeMismatch "integer" badType
bitwiseOr [SimpleVal (Number _), badType] = throwError $ TypeMismatch "integer" badType
bitwiseOr [badType, _] = throwError $ TypeMismatch "integer" badType
bitwiseOr badArgList = throwError $ NumArgs 2 badArgList

bitwiseXor :: [LispVal] -> ThrowsError LispVal
bitwiseXor [SimpleVal (Number (NumI n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumI $ xor n s
bitwiseXor [SimpleVal (Number (NumI n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumI $ xor n (fromIntegral s)
bitwiseXor [SimpleVal (Number (NumS n)), SimpleVal (Number (NumI s))] = return $ fromSimple $ Number $ NumS $ xor n (fromIntegral s)
bitwiseXor [SimpleVal (Number (NumS n)), SimpleVal (Number (NumS s))] = return $ fromSimple $ Number $ NumS $ xor n s
bitwiseXor [badType, SimpleVal (Number _)] = throwError $ TypeMismatch "integer" badType
bitwiseXor [SimpleVal (Number _), badType] = throwError $ TypeMismatch "integer" badType
bitwiseXor [badType, _] = throwError $ TypeMismatch "integer" badType
bitwiseXor badArgList = throwError $ NumArgs 2 badArgList

bitwiseNot :: [LispVal] -> ThrowsError LispVal
bitwiseNot [SimpleVal (Number (NumI n))] = return $ fromSimple $ Number $ NumI $ complement (n + n - n)
bitwiseNot [SimpleVal (Number (NumS n))] = return $ fromSimple $ Number $ NumS $ complement (n + n - n)
bitwiseNot [badType] = throwError $ TypeMismatch "integer" badType
bitwiseNot badArgList = throwError $ NumArgs 2 badArgList

real :: LispVal -> ThrowsError LispVal
real (SimpleVal (Number (NumC x))) = return $ fromSimple $ Number $ NumF $ realPart x
real val@(SimpleVal (Number (NumF _))) = return val
real val@(SimpleVal (Number (NumR _))) = return val
real val@(SimpleVal (Number (NumI _))) = return val
real val@(SimpleVal (Number (NumS _))) = return val
real x = throwError $ TypeMismatch "number" x

imaginary :: LispVal -> ThrowsError LispVal
imaginary (SimpleVal (Number (NumC x))) = return $ fromSimple $ Number $ NumF $ imagPart x
imaginary (SimpleVal (Number _)) = return $ fromSimple $ Number $ NumF 0
imaginary x = throwError $ TypeMismatch "number" x

numerator :: LispVal -> ThrowsError LispVal
numerator (SimpleVal (Number (NumR x))) = return $ fromSimple $ Number $ NumI $ Ratio.numerator x
numerator x = throwError $ TypeMismatch "number" x

denominator :: LispVal -> ThrowsError LispVal
denominator (SimpleVal (Number (NumR x))) = return $ fromSimple $ Number $ NumI $ Ratio.denominator x
denominator x = throwError $ TypeMismatch "number" x

numDoc :: String
numDoc = "\n\
\n\
  params:\n\
   - x: can be any numerical type\n\
  complexity: O(1)\n\
  returns: a number (the type of which depends on the input type)"

numOp :: (Double -> Double) -> [LispVal] -> ThrowsError LispVal
numOp op [SimpleVal (Number (NumI n))] = return $ fromSimple $ Number $ NumF $ op $ fromInteger n
numOp op [SimpleVal (Number (NumS n))] = return $ fromSimple $ Number $ NumF $ op $ fromIntegral n
numOp op [SimpleVal (Number (NumF n))] = return $ fromSimple $ Number $ NumF $ op n
numOp op [SimpleVal (Number (NumR n))] = return $ fromSimple $ Number $ NumR $ toRational $ op $ fromRational n
numOp op [SimpleVal (Number (NumC n))] = return $ fromSimple $ Number $ NumC $ op (realPart n) :+ op (imagPart n)
numOp _ [x] = throwError $ TypeMismatch "number" x
numOp _ badArgList = throwError $ NumArgs 1 badArgList

logDoc :: String
logDoc = "the logarithm function\n\
\n\
  params:\n\
    - n: the number to draw the logarithm from\n\
    - base: optional value that represents the logarithm base\n\
  complexity: O(1)\n\
  returns: the logarithm of <par>n</par>"

numLog :: [LispVal] -> ThrowsError LispVal
numLog [SimpleVal (Number (NumI n))] = return $ fromSimple $ Number $ NumF $ log $ fromInteger n
numLog [SimpleVal (Number (NumS n))] = return $ fromSimple $ Number $ NumF $ log (fromIntegral n)
numLog [SimpleVal (Number (NumF n))] = return $ fromSimple $ Number $ NumF $ log n
numLog [SimpleVal (Number (NumR n))] = return $ fromSimple $ Number $ NumF $ log $ fromRational n
numLog [SimpleVal (Number (NumC n))] = return $ fromSimple $ Number $ NumC $ log n
numLog [SimpleVal (Number (NumI n)), SimpleVal (Number (NumI base))] =
    return $ fromSimple $ Number $ NumF $ logBase (fromInteger base) (fromIntegral n)
numLog [SimpleVal (Number (NumS n)), SimpleVal (Number (NumI base))] =
    return $ fromSimple $ Number $ NumF $ logBase (fromIntegral base) (fromIntegral n)
numLog [SimpleVal (Number (NumI n)), SimpleVal (Number (NumS base))] =
    return $ fromSimple $ Number $ NumF $ logBase (fromIntegral base) (fromIntegral n)
numLog [SimpleVal (Number (NumS n)), SimpleVal (Number (NumS base))] =
    return $ fromSimple $ Number $ NumF $ logBase (fromIntegral base) (fromIntegral n)
numLog [SimpleVal (Number (NumF n)), SimpleVal (Number (NumI base))] =
    return $ fromSimple $ Number $ NumF $ logBase (fromInteger base) n
numLog [SimpleVal (Number (NumC n)), SimpleVal (Number (NumI base))] =
    return $ fromSimple $ Number $ NumC $ logBase (fromInteger base) n
numLog [SimpleVal (Number (NumF n)), SimpleVal (Number (NumS base))] =
    return $ fromSimple $ Number $ NumF $ logBase (fromIntegral base) n
numLog [SimpleVal (Number (NumC n)), SimpleVal (Number (NumS base))] =
    return $ fromSimple $ Number $ NumC $ logBase (fromIntegral base) n
numLog [x] = throwError $ TypeMismatch "number" x
numLog badArgList = throwError $ NumArgs 1 badArgList

powDoc :: String
powDoc = "power of function\n\
\n\
params:\n\
  - n: the number to exponentiate\n\
  - exp: the exponent\n\
complexity: O(1)\n\
returns: the power of <par>n</par> to <par>exp</par>"

numPow :: LispNum -> LispNum -> ThrowsError LispVal
numPow (NumI n) wrong@(NumI base) =
    if base > -1
        then return $ fromSimple $ Number $ NumI $ n ^ base
        else throwError $ TypeMismatch "positive" (fromSimple $ Number wrong)
numPow (NumS n) wrong@(NumI base) =
    if base > -1
        then return $ fromSimple $ Number $ NumI $ fromIntegral n ^ base
        else throwError $ TypeMismatch "positive" (fromSimple $ Number wrong)
numPow (NumI n) wrong@(NumS base) =
    if base > -1
        then return $ fromSimple $ Number $ NumI $ n ^ (fromIntegral base::Integer)
        else throwError $ TypeMismatch "positive" (fromSimple $ Number wrong)
numPow (NumS n) wrong@(NumS base) =
    if base > -1
        then return $ fromSimple $ Number $ NumS $ n ^ base
        else throwError $ TypeMismatch "positive" (fromSimple $ Number wrong)
numPow (NumF n) (NumI base) =
    return $ fromSimple $ Number $ NumF $ n ** fromIntegral base
numPow (NumI n) (NumF base) =
    return $ fromSimple $ Number $ NumF $ fromIntegral n ** base
numPow (NumF n) (NumF base) =
    return $ fromSimple $ Number $ NumF $ n ** base
numPow (NumC n) (NumI base) =
    return $ fromSimple $ Number $ NumC $ n ** fromIntegral base
numPow (NumC n) (NumF base) =
    return $ fromSimple $ Number $ NumC $ n ** (base :+ 0)
numPow (NumR n) (NumR base) =
    return $ fromSimple $ Number $ NumF $ fromRational n ** fromRational base
numPow (NumR n) (NumI base) =
    return $ fromSimple $ Number $ NumF $ fromRational n ** fromIntegral base
numPow (NumI n) (NumR base) =
    return $ fromSimple $ Number $ NumF $ fromIntegral n ** fromRational base
numPow (NumR n) (NumF base) =
    return $ fromSimple $ Number $ NumF $ fromRational n ** base
numPow (NumF n) (NumR base) =
    return $ fromSimple $ Number $ NumF $ n ** fromRational base
numPow (NumC n) (NumR base) =
    return $ fromSimple $ Number $ NumC $ n ** (fromRational base :+ 0)
numPow (NumF n) (NumS base) =
    return $ fromSimple $ Number $ NumF $ n ** fromIntegral base
numPow (NumS n) (NumF base) =
    return $ fromSimple $ Number $ NumF $ fromIntegral n ** base
numPow (NumR n) (NumS base) =
    return $ fromSimple $ Number $ NumF $ fromRational n ** fromIntegral base
numPow (NumS n) (NumR base) =
    return $ fromSimple $ Number $ NumF $ fromIntegral n ** fromRational base
numPow (NumC n) (NumS base) =
    return $ fromSimple $ Number $ NumC $ n ** fromIntegral base
numPow _ a@(NumC _) =
    throwError $ TypeMismatch "number (no complex)" (fromSimple $ Number a)

sqrtDoc :: String
sqrtDoc = "the square root function\n\
\n\
  params:\n\
    - arg: the number to draw the square root from (can be any numerical type)\n\
  complexity: O(1)\n\
  returns: the square root of <par>arg</par>"

numSqrt :: [LispVal] -> ThrowsError LispVal
numSqrt [SimpleVal (Number (NumI n))] = if n >= 0 then return $ fromSimple $ Number $ NumF $ sqrt $ fromInteger n
                                                  else return $ fromSimple $ Number $ NumC $ sqrt (fromInteger n :+ 0)
numSqrt [SimpleVal (Number (NumS n))] = if n >= 0 then return $ fromSimple $ Number $ NumF $ sqrt $ fromIntegral n
                                                  else return $ fromSimple $ Number $ NumC $ sqrt (fromIntegral n :+ 0)
numSqrt [SimpleVal (Number (NumF n))] = if n >= 0 then return $ fromSimple $ Number $ NumF $ sqrt n
                                                  else return $ fromSimple $ Number $ NumC $ sqrt (n :+ 0)
numSqrt [SimpleVal (Number (NumC n))] = return $ fromSimple $ Number $ NumC $ sqrt n
numSqrt [SimpleVal (Number (NumR n))] = return $ fromSimple $ Number $ NumF $ sqrt $ fromRational n
numSqrt [x] = throwError $ TypeMismatch "number" x
numSqrt badArgList = throwError $ NumArgs 1 badArgList

