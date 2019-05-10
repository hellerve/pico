{-# LANGUAGE DeriveAnyClass, DeriveGeneric #-}
module Zepto.Types (LispNum(..),
                    Simple(..),
                    LispVal(..),
                    Continuation(..),
                    LispFun(..),
                    LispError(..),
                    Unpacker(AnyUnpacker),
                    ThrowsError,
                    Env(..),
                    IOThrowsError,
                    ToZepto,
                    toZepto,
                    dynToLispVal,
                    showVal,
                    showError,
                    showArgs,
                    fromSimple,
                    toSimple,
                    trapError,
                    extractValue,
                    typeString,
                    nullEnv,
                    nullCont,
                    globalEnv,
                    liftThrows,
                    runIOThrows,
                    runIOThrowsLispVal,
                    throwHistorial,
                    buildCallHistory,
                    toOpaque,
                    fromOpaque,
                    unaryOp,
                    unaryIOOp,
                    noArg,
                    noIOArg,
                    liftLisp,
                    lispErr
                    ) where
import Data.ByteString (ByteString, unpack)
import Data.Complex
import Data.Dynamic
import Data.Fixed
import Data.Hashable
import Data.IORef
import Data.List (foldl')
import Data.Ratio
import Control.Monad
import Control.Monad.Except
import System.IO
import Text.ParserCombinators.Parsec.Error
import qualified GHC.Generics
import qualified Data.HashMap as M
import qualified Data.Array as A
import qualified Text.Regex.PCRE.Light.Base as R

-- | an unpacker for any LispVal
data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

instance Show LispNum where show = showNum
instance Eq LispNum where
    (NumI x) == (NumI y) = x == y
    (NumF x) == (NumI y) = x == fromIntegral y
    (NumI x) == (NumF y) = fromIntegral x == y
    (NumF x) == (NumF y) = x == y
    (NumC x) == (NumC y) = x == y
    (NumC x) == (NumF y) = x == (y :+ 0)
    (NumF x) == (NumC y) = (x :+ 0) == y
    (NumC x) == (NumI y) = x == (fromIntegral y :+ 0)
    (NumI x) == (NumC y) = (fromIntegral x :+ 0) == y
    (NumR x) == (NumR y) = x == y
    (NumR x) == (NumI y) = x == toRational y
    (NumI x) == (NumR y) = toRational x == y
    (NumR x) == (NumF y) = fromRational x == y
    (NumF x) == (NumR y) = x == fromRational y
    (NumR x) == (NumC y) = (fromRational x :+ 0) == y
    (NumC x) == (NumR y) = x == (fromRational y :+ 0)
    (NumS x) == (NumS y) = x == y
    (NumS x) == (NumI y) = toInteger x == y
    (NumI x) == (NumS y) = x == toInteger y
    (NumS x) == (NumF y) = fromIntegral x == y
    (NumF x) == (NumS y) = x == fromIntegral y
    (NumS x) == (NumC y) = (fromIntegral x :+ 0) == y
    (NumC x) == (NumS y) = x == (fromIntegral y :+ 0)
    (NumS x) == (NumR y) = toRational x == y
    (NumR x) == (NumS y) = x == toRational y
instance Ord LispNum where
    compare (NumI x) (NumI y) = compare x y
    compare (NumF x) (NumI y) = compare x (fromIntegral y)
    compare (NumI x) (NumF y) = compare (fromIntegral x) y
    compare (NumF x) (NumF y) = compare x y
    compare (NumC x) (NumC y) = do
        let fx = compare (realPart x) (realPart y)
        if fx == EQ
            then compare (imagPart x) (imagPart y)
            else fx
    compare (NumC x) (NumF y) = do
        let fx = compare (realPart x) y
        if fx == EQ
            then compare (imagPart x) 0
            else fx
    compare (NumF x) (NumC y) = do
        let fx = compare (realPart y) x
        if fx == EQ
            then compare (imagPart y) 0
            else fx
    compare (NumC x) (NumI y) = do
        let fx = compare (realPart x) (fromIntegral y)
        if fx == EQ
            then compare (imagPart x) 0
            else fx
    compare (NumI x) (NumC y) = do
        let fx = compare (realPart y) (fromIntegral x)
        if fx == EQ
            then compare (imagPart y) 0
            else fx
    compare (NumR x) (NumR y) = compare x y
    compare (NumR x) (NumI y) = compare x (toRational y)
    compare (NumI x) (NumR y) = compare (toRational x) y
    compare (NumR x) (NumF y) = compare x (toRational y)
    compare (NumF x) (NumR y) = compare (toRational x) y
    compare (NumR x) (NumC y) = do
        let fx = compare (realPart y) (fromRational x)
        if fx == EQ
            then compare (imagPart y) 0
            else fx
    compare (NumC x) (NumR y) = do
        let fx = compare (realPart x) (fromRational y)
        if fx == EQ
            then compare (imagPart x) 0
            else fx
    compare (NumS x) (NumS y) = compare x y
    compare (NumS x) (NumI y) = compare (toInteger x) y
    compare (NumI x) (NumS y) = compare x (toInteger y)
    compare (NumF x) (NumS y) = compare x (fromIntegral y)
    compare (NumS x) (NumF y) = compare (fromIntegral x) y
    compare (NumR x) (NumS y) = compare x (toRational y)
    compare (NumS x) (NumR y) = compare (toRational x) y
    compare (NumS x) (NumC y) = do
        let fx = compare (realPart y) (fromIntegral x)
        if fx == EQ
            then compare (imagPart y) 0
            else fx
    compare (NumC x) (NumS y) = do
        let fx = compare (realPart x) (fromIntegral y)
        if fx == EQ
            then compare (imagPart x) 0
            else fx
instance Num LispNum where
    (NumI x) + (NumI y) = NumI $ x + y
    (NumF x) + (NumI y) = NumF $ x + fromIntegral y
    (NumI x) + (NumF y) = NumF $ fromIntegral x + y
    (NumF x) + (NumF y) = NumF $ x + y

    (NumC x) + (NumC y) = NumC $ x + y
    (NumC x) + (NumF y) = NumC $ x + (y :+ 0)
    (NumF x) + (NumC y) = NumC $ (x :+ 0) + y
    (NumC x) + (NumI y) = NumC $ x + (fromIntegral y :+ 0)
    (NumI x) + (NumC y) = NumC $ (fromIntegral x :+ 0) + y

    (NumR x) + (NumR y) = NumR $ x + y
    (NumR x) + (NumI y) = NumR $ x + fromIntegral y
    (NumI x) + (NumR y) = NumR $ fromIntegral x + y
    (NumR x) + (NumF y) = NumF $ fromRational x + y
    (NumF x) + (NumR y) = NumF $ x + fromRational y
    (NumR x) + (NumC y) = NumC $ (fromRational x :+ 0) + y
    (NumC x) + (NumR y) = NumC $ (fromRational y :+ 0) + x

    (NumS x) + (NumS y) = NumS $ x + y
    (NumS x) + (NumI y) = NumI $ toInteger x + y
    (NumI x) + (NumS y) = NumI $ x + toInteger y
    (NumS x) + (NumF y) = NumF $ fromIntegral x + y
    (NumF x) + (NumS y) = NumF $ x + fromIntegral y
    (NumS x) + (NumC y) = NumC $ (fromIntegral x :+ 0) + y
    (NumC x) + (NumS y) = NumC $ x + (fromIntegral y :+ 0)
    (NumS x) + (NumR y) = NumR $ fromIntegral x + y
    (NumR x) + (NumS y) = NumR $ x + fromIntegral y

    (NumI x) * (NumI y) = NumI $ x * y
    (NumF x) * (NumI y) = NumF $ x * fromIntegral y
    (NumI x) * (NumF y) = NumF $ fromIntegral x * y
    (NumF x) * (NumF y) = NumF $ x * y

    (NumC x) * (NumC y) = NumC $ x * y
    (NumC x) * (NumF y) = NumC $ x * (y :+ 0)
    (NumF x) * (NumC y) = NumC $ (x :+ 0) * y
    (NumC x) * (NumI y) = NumC $ x * (fromIntegral y :+ 0)
    (NumI x) * (NumC y) = NumC $ (fromIntegral x :+ 0) * y

    (NumR x) * (NumR y) = NumR $ x * y
    (NumI x) * (NumR y) = NumR $ fromIntegral x * y
    (NumR x) * (NumI y) = NumR $ x * fromIntegral y
    (NumF x) * (NumR y) = NumF $ x * fromRational y
    (NumR x) * (NumF y) = NumF $ fromRational x * y
    (NumR x) * (NumC y) = NumC $ (fromRational x :+ 0) * y
    (NumC x) * (NumR y) = NumC $ x * (fromRational y :+ 0)

    (NumS x) * (NumS y) = NumS $ x * y
    (NumS x) * (NumI y) = NumI $ toInteger x * y
    (NumI x) * (NumS y) = NumI $ x * toInteger y
    (NumS x) * (NumF y) = NumF $ fromIntegral x * y
    (NumF x) * (NumS y) = NumF $ x * fromIntegral y
    (NumS x) * (NumR y) = NumR $ toRational x * y
    (NumR x) * (NumS y) = NumR $ x * toRational y
    (NumS x) * (NumC y) = NumC $ (fromIntegral x :+ 0) * y
    (NumC x) * (NumS y) = NumC $ x * (fromIntegral y :+ 0)

    (NumI x) - (NumI y) = NumI $ x - y
    (NumF x) - (NumI y) = NumF $ x - fromIntegral y
    (NumI x) - (NumF y) = NumF $ fromIntegral x - y
    (NumF x) - (NumF y) = NumF $ x - y

    (NumC x) - (NumC y) = NumC $ x - y
    (NumC x) - (NumF y) = NumC $ x - (y :+ 0)
    (NumF x) - (NumC y) = NumC $ (x :+ 0) - y
    (NumC x) - (NumI y) = NumC $ x - (fromIntegral y :+ 0)
    (NumI x) - (NumC y) = NumC $ (fromIntegral x :+ 0) - y

    (NumR x) - (NumR y) = NumR $ x - y
    (NumI x) - (NumR y) = NumR $ fromIntegral x - y
    (NumR x) - (NumI y) = NumR $ x - fromIntegral y
    (NumF x) - (NumR y) = NumF $ x - fromRational y
    (NumR x) - (NumF y) = NumF $ fromRational x - y
    (NumR x) - (NumC y) = NumC $ (fromRational x :+ 0) - y
    (NumC x) - (NumR y) = NumC $ x - (fromRational y :+ 0)

    (NumS x) - (NumS y) = NumS $ x - y
    (NumS x) - (NumI y) = NumI $ toInteger x - y
    (NumI x) - (NumS y) = NumI $ x - toInteger y
    (NumS x) - (NumF y) = NumF $ fromIntegral x - y
    (NumF x) - (NumS y) = NumF $ x - fromIntegral y
    (NumS x) - (NumR y) = NumR $ toRational x - y
    (NumR x) - (NumS y) = NumR $ x - toRational y
    (NumS x) - (NumC y) = NumC $ (fromIntegral x :+ 0) - y
    (NumC x) - (NumS y) = NumC $ x - (fromIntegral y :+ 0)

    negate (NumI x) = NumI $ negate x
    negate (NumF x) = NumF $ negate x
    negate (NumC x) = NumC $ negate x
    negate (NumR x) = NumR $ negate x
    negate (NumS x) = NumS $ negate x
    abs (NumI x) = NumI $ abs x
    abs (NumF x) = NumF $ abs x
    abs (NumC x) = NumC $ abs x
    abs (NumR x) = NumR $ abs x
    abs (NumS x) = NumS $ abs x
    signum (NumI x) = NumI $ signum x
    signum (NumF x) = NumF $ signum x
    signum (NumC x) = NumC $ signum x
    signum (NumR x) = NumR $ signum x
    signum (NumS x) = NumS $ signum x
    fromInteger x = NumI $ fromInteger x
instance Integral LispNum where
    toInteger (NumI x) = x
    toInteger (NumS x) = toInteger x
    toInteger (NumF x) = round x
    toInteger (NumC x) = round $ realPart x
    toInteger (NumR x) = round x
    quotRem (NumI x) (NumI y) = (NumI $ quot x y, NumI $ rem x y)
    quotRem (NumF x) (NumI y) = (NumF $ x / fromIntegral y, NumF $ mod' x (fromIntegral y))
    quotRem (NumI x) (NumF y) = (NumF $ fromIntegral x / y, NumF $ mod' (fromIntegral x) y)
    quotRem (NumF x) (NumF y) = (NumF $ x / y, NumF $ mod' x y)

    quotRem (NumC x) (NumC y) = (NumC $ x / y, NumF $ 1/0)
    quotRem (NumC x) (NumI y) = (NumC $ x / (fromIntegral y :+ 0), NumF $ 1/0)
    quotRem (NumI x) (NumC y) = (NumC $ (fromIntegral x :+ 0) / y, NumF $ 1/0)
    quotRem (NumC x) (NumF y) = (NumC $ x / (y :+ 0), NumF $ 1/0)
    quotRem (NumF x) (NumC y) = (NumC $ (x :+ 0) / y, NumF $ 1/0)

    quotRem (NumR x) (NumR y) = (NumR $ x / fromRational y, NumR $ mod' x y)
    quotRem (NumI x) (NumR y) = (NumR $ toRational x / y, NumR $ mod' (toRational x) y)
    quotRem (NumR x) (NumI y) = (NumR $ x / toRational y, NumR $ mod' x (toRational y))
    quotRem (NumF x) (NumR y) = (NumF $ x / fromRational y, NumF $ mod' x (fromRational y))
    quotRem (NumR x) (NumF y) = (NumF $ fromRational x / y, NumF $ mod' (fromRational x) y)
    quotRem (NumC x) (NumR y) = (NumC $ x / (fromRational y :+ 0), NumF $ 1/0)
    quotRem (NumR x) (NumC y) = (NumC $ (fromRational x :+ 0) / y, NumF $ 1/0)

    quotRem (NumS x) (NumS y) = (NumS $ quot x y, NumS $ rem x y)
    quotRem (NumI x) (NumS y) = (NumI $ quot x (toInteger y), NumI $ rem x (toInteger y))
    quotRem (NumS x) (NumI y) = (NumI $ quot (toInteger x) y, NumI $ rem (toInteger x) y)
    quotRem (NumF x) (NumS y) = (NumF $ x / fromIntegral y, NumF $ mod' x (fromIntegral y))
    quotRem (NumS x) (NumF y) = (NumF $ fromIntegral x / y, NumF $ mod' (fromIntegral x) y)
    quotRem (NumC x) (NumS y) = (NumC $ x / (fromIntegral y :+ 0), NumF $ 1/0)
    quotRem (NumS x) (NumC y) = (NumC $ (fromIntegral x :+ 0) / y, NumF $ 1/0)
    quotRem (NumR x) (NumS y) = (NumR $ x / toRational y, NumR $ mod' x (toRational y))
    quotRem (NumS x) (NumR y) = (NumR $ toRational x / y, NumR $ mod' (toRational x) y)
instance Real LispNum where
    toRational (NumI x) = toRational x
    toRational (NumF x) = toRational x
    toRational (NumC _) = 0
    toRational (NumR x) = x
    toRational (NumS x) = toRational x
instance Enum LispNum where
    toEnum x = NumI $ toInteger x
    fromEnum (NumI x) = fromIntegral x
    fromEnum (NumF x) = round x
    fromEnum (NumC _) = 0
    fromEnum (NumR _) = 0
    fromEnum (NumS x) = fromIntegral x
-- | a LispNum data type comprising a float and an integer
data LispNum = NumI Integer
             | NumF Double
             | NumC (Complex Double)
             | NumR Rational
             | NumS Int
    deriving (Hashable, GHC.Generics.Generic)

instance Hashable a => Hashable (Complex a) where
  hash d = hash (realPart d) + hash (imagPart d)
  hashWithSalt x d = hashWithSalt x (realPart d) + hashWithSalt x (imagPart d)

instance Hashable R.Regex where
  hash (R.Regex _ r)= hash r
  hashWithSalt x (R.Regex _ r)= hashWithSalt x r

data Simple = Atom String
            | Number LispNum
            | String String
            | Regex R.Regex
            | Character Char
            | Bool Bool
            | Nil String
            | SimpleList [Simple]
    deriving (Eq, Ord, Hashable, GHC.Generics.Generic)

instance Show LispVal where show = showVal
-- | a LispVal data type comprising all Lisp data types
data LispVal = SimpleVal Simple
             | List [LispVal]
             | DottedList [LispVal] LispVal
             | Vector (A.Array Int LispVal)
             | ByteVector ByteString
             | HashMap (M.Map Simple LispVal)
             | PrimitiveFunc  String ([LispVal] -> ThrowsError LispVal)
             | IOFunc String ([LispVal] -> IOThrowsError LispVal)
             | Port Handle
             | Func String LispFun
             | EvalFunc String ([LispVal] -> IOThrowsError LispVal)
             | Pointer { pointerVar :: String, pointerEnv :: Env }
             | Environ Env
             | Cont Continuation
             | Opaque Dynamic
             | Error LispError
             | ListComprehension LispVal LispVal LispVal (Maybe LispVal)
             | HashComprehension (LispVal, LispVal) (LispVal, LispVal) LispVal (Maybe LispVal)

data Continuation = Continuation { contClosure :: Env
                                 , cbody :: [LispVal]
                                 , cont :: LispVal
                                 , frameFunc :: Maybe LispVal
                                 , frameEvaledArgs :: Maybe [LispVal]
                                 , callStack :: [(LispVal, String)]
                                 }

-- | a LispFun data type
data LispFun = LispFun { params :: [String]
                       , vararg :: Maybe String
                       , body :: [LispVal]
                       , closure :: Env
                       , docstring :: String
                       }

instance Show LispError where show = showError
-- | a LispError data type comprising all errors that
-- | can be emitted from within the interpreter
data LispError = NumArgs Integer [LispVal]
               | TypeMismatch String LispVal
               | ParseErr ParseError
               | BadSpecialForm String LispVal
               | BadSpecialForms String [LispVal]
               | NotFunction String String
               | UnboundVar String String
               | InternalError String
               | Default String
               | Historial [(LispVal, String)] LispError

instance Eq Env where
    (Environment _ xb xp) == (Environment _ yb yp) = (xb == yb) && (xp == yp)
-- | an Environment type where all variables are stored
data Env = Environment {
        parentEnv :: Maybe Env
      , bindings :: IORef (M.Map String (IORef LispVal))
      , pointers :: IORef (M.Map String (IORef [LispVal]))
}

-- | a ThrowsError type containing either an error or a value
type ThrowsError = Either LispError
-- | a IOThrowsError type containing either an error or an IO
type IOThrowsError = ExceptT LispError IO

globalEnv :: Maybe Env -> Env -> Env
globalEnv (Just prev) Environment{parentEnv=Nothing} = prev
globalEnv Nothing val@Environment{parentEnv=Nothing} = val
globalEnv _ val@Environment{parentEnv=Just parent}=globalEnv (Just val) parent

showNum :: LispNum -> String
showNum (NumF contents) = show contents
showNum (NumI contents) = show contents
showNum (NumC contents) = show (realPart contents) ++ "+" ++ show (imagPart contents) ++ "i"
showNum (NumR contents) = show (numerator contents) ++ "/" ++ show (denominator contents)
showNum (NumS contents) = show contents ++ "s"

-- | a show function for all LispVals
showVal :: LispVal -> String
showVal (SimpleVal (String contents)) = contents
showVal (SimpleVal (Regex (R.Regex _ s))) = show s
showVal (SimpleVal (Atom name)) = name
showVal (SimpleVal (Bool True)) = "#t"
showVal (SimpleVal (Bool False)) = "#f"
showVal (SimpleVal (Character c)) = show c
showVal (SimpleVal (Number n)) = showNum n
showVal (SimpleVal (SimpleList contents)) = "simple(" ++ unwordsList (map SimpleVal contents) ++")"
showVal (List contents) = "(" ++ unwordsList contents ++")"
showVal (Vector contents) = "#(" ++ unwordsList (A.elems contents) ++ ")"
showVal (ByteVector contents) = "b{" ++ unwords (map show (unpack contents)) ++ "}"
showVal (HashMap contents) = "#{" ++ unwordsMap (zip (map SimpleVal (M.keys contents))
                                                     (M.elems contents)) ++ "}"
showVal (PrimitiveFunc name _) = "<primitive: " ++ name ++ ">"
showVal (IOFunc name _) = "<IO primitive: " ++ name ++ ">"
showVal (EvalFunc name _) = "<eval primitive: " ++ name ++ ">"
showVal (Port _) = "<IO port>"
showVal (Opaque _) = "<opaque>"
showVal (Error e) = "<error: " ++ show e ++ ">"
showVal (Func name LispFun {params = args, vararg = varargs, body = _,
                             closure = _, docstring = doc}) =
    doc ++ "\n  source: " ++
    "(" ++ name ++ " (" ++ unwords (fmap show args) ++
        (case varargs of
            Nothing -> ""
            Just arg -> " . " ++ arg) ++ ") ...)"
showVal (DottedList h t) = "(" ++ unwordsList h ++ " . " ++ showVal t ++ ")"
showVal (Pointer p _) = "<pointer " ++ p ++ ">"
showVal (SimpleVal (Nil _)) = "nil"
showVal (Cont _) = "<continuation>"
showVal (Environ _) = "<environment>"
showVal (ListComprehension expr filt _ _) = "<list comprehension: " ++
                                            show expr ++ " : " ++
                                            show filt ++ ">"
showVal (HashComprehension (kexpr, vexpr) (k, v) _ _) = "<hash comprehension: " ++
                                                        show kexpr ++ ", " ++ show vexpr ++
                                                        " : " ++ show k ++ ", " ++
                                                        show v ++ ">"

showTrunc :: LispVal -> String
showTrunc val = let x = show val
                in if length x > 100
                     then take 100 x ++ "...(" ++ show (length x - 100) ++ " more)"
                     else x

-- | a show function for all LispErrors
showError :: LispError -> String
showError (UnboundVar message varname) = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ showTrunc form ++
                                          " (type: " ++ typeString form ++ ")"
showError (BadSpecialForms message forms) = message ++ ": " ++ init (
                                         init $ unwords $
                                         map (\form -> showTrunc form ++
                                              " (type: " ++ typeString form ++
                                              "), ") forms)
showError (NotFunction message func) = message ++ ": " ++ show func
showError (NumArgs expected found) =
      let x = "Expected " ++ show expected ++
              " args; found " ++ show (length found)
      in if not (null found)
              then x ++ "; values are " ++ unwords (map extractStr found)
              else x
    where extractStr val = let y = typeString val
                           in if y /= "function"
                                then showTrunc val ++ " (type: " ++ y ++ ") "
                                else "<compiled function>"
showError (TypeMismatch expected found) =
        let x = typeString found
            y = "Invalid type: expected " ++ expected ++ ", found " ++ x
        in if x /= "function"
              then y ++ " (value: " ++ showTrunc found ++ ")"
              else y
showError (ParseErr parseErr) = "Parse error at " ++ show parseErr
showError (InternalError err) = "Internal error: " ++ err
showError (Default err) = err
showError (Historial cs err) = showCallHistory cs ++ "\n" ++ show err

showCallHistory :: [(LispVal, String)] -> String
showCallHistory cs =
        "Traceback (most recent call last):\n" ++ concatenate cs
    where concatenate [] = ""
          concatenate (x:xs) = showInternal (fst x) ++
                               (if length (snd x) > 0
                                  then "\n\tcalled with: " ++ snd x
                                  else "") ++
                               "\n" ++ concatenate xs

showArgs :: [LispVal] -> String
showArgs args = unwords (map showInternal' args)
  where showInternal' (Func name _) = "<func: " ++ name ++ ">"
        showInternal' x = showInternal x

showInternal :: LispVal -> String
showInternal (PrimitiveFunc name _) = "<primitive: " ++ name ++ ">"
showInternal (IOFunc name _) = "<IO primitive: " ++ name ++ ">"
showInternal (EvalFunc name _) = "<eval primitive: " ++ name ++ ">"
showInternal (Func name LispFun {params = args, vararg = varargs, body = _,
                             closure = _, docstring = doc}) =
    "(" ++ name ++ (if length args > 0 then " " else "") ++ unwords args ++
        (case varargs of
            Nothing -> ""
            Just arg -> " . " ++ arg) ++ ")\n  " ++ take 100 doc
showInternal (Cont _) = "<continuation>"
showInternal (HashMap _) = "<hash-map>"
showInternal HashComprehension{} = "<hash-comprehension>"
showInternal ListComprehension{} = "<list-comprehension>"
showInternal (Environ _) = "<environment>"
showInternal (Vector _) = "<vector>"
showInternal (ByteVector _) = "<byte-vector>"
showInternal (List _) = "<list>"
showInternal (DottedList _ _) = "<dotted-list>"
showInternal (Port _) = "<port>"
showInternal (Pointer _ _) = "<pointer>"
showInternal (SimpleVal (String _)) = "<string>"
showInternal (Opaque _) = "<opaque>"
showInternal (Error _) = "<error>"
showInternal x@(SimpleVal _) = show x

buildCallHistory :: (LispVal, String) -> [(LispVal, String)] -> [(LispVal, String)]
buildCallHistory f h
  | null h = [f]
  | show f == show (head h) = h --dirty dirty hack
  | otherwise = f : lastN 15 h

fromSimple :: Simple -> LispVal
fromSimple = SimpleVal

toSimple :: LispVal -> Simple
toSimple (SimpleVal x) = x
toSimple _ = Nil ""

lastN :: Int -> [a] -> [a]
lastN n xs = drop (length xs - n) xs

throwHistorial :: [(LispVal, String)] -> LispError -> IOThrowsError LispVal
throwHistorial cs (Historial ics e) = throwError $ Historial (mergeCs cs ics) e
    where mergeCs stack merged
            | null stack = merged
            | length stack > 10 = lastN 10 stack
            | otherwise = mergeCs (init stack) (buildCallHistory (last stack) merged)
throwHistorial cs e = throwError $ Historial cs e

typeString :: LispVal -> String
typeString (SimpleVal (Number (NumI _))) = "integer"
typeString (SimpleVal (Number (NumS _))) = "small integer"
typeString (SimpleVal (Number (NumF _))) = "float"
typeString (SimpleVal (Number (NumR _))) = "rational"
typeString (SimpleVal (Number (NumC _))) = "complex"
typeString (SimpleVal (Bool _)) = "boolean"
typeString (SimpleVal (Character _)) = "character"
typeString (SimpleVal (String _)) = "string"
typeString (SimpleVal (Regex _)) = "regex"
typeString (SimpleVal (Atom (':' : _))) = "atom"
typeString (SimpleVal (Atom _)) = "symbol"
typeString (SimpleVal (Nil _)) = "nil"
typeString (SimpleVal (SimpleList _)) = "simple list"
typeString (List _) = "list"
typeString (DottedList _ _) = "dotted list"
typeString (Environ _ ) = "environment"
typeString (Vector _) = "vector"
typeString (HashMap _) = "hashmap"
typeString (PrimitiveFunc _ _) = "primitive"
typeString (IOFunc _ _) = "io primitive"
typeString (EvalFunc _ _) = "eval primitive"
typeString (Port _) = "port"
typeString (Func _ _) = "function"
typeString (Pointer _ _) = "pointer"
typeString (Cont _) = "continuation"
typeString ListComprehension{} = "list comprehension"
typeString HashComprehension{} = "hash comprehension"
typeString (ByteVector _) = "bytevector"
typeString (Opaque _) = "opaque"
typeString (Error _) = "error"

unwordsList :: [LispVal] -> String
unwordsList = unwords . fmap showVal

unwordsMap :: [(LispVal, LispVal)] -> String
unwordsMap = unwords . fmap (\(x, y) -> showVal x ++ " " ++ showVal y ++ ", ")

-- | traps an error and shows it
trapErrorShow :: (MonadError e m, Show e) =>  m String -> m String
trapErrorShow action = catchError action (return . show)

-- | extracts a value from a possible error
extractValue :: ThrowsError a -> a
extractValue (Right val) = val
extractValue (Left x) = error("This should not be happening. " ++
                           "Please consider reporting this incident: " ++
                           show x)

-- | returns a new empty environment
nullEnv :: IO Env
nullEnv = do
    nullb <- newIORef $ M.fromList []
    nullp <- newIORef $ M.fromList []
    return $ Environment Nothing nullb nullp

nullCont :: Env -> LispVal
nullCont env = Cont $ Continuation env [] (fromSimple (Nil "")) Nothing Nothing []

-- | lift a ThrowsError to an IOThrowsError
liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = return val

-- | lift an IOThrowsError to an IO monad
runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = liftM extractValue (runExceptT (trapErrorShow action))

-- | traps errors
trapError :: IOThrowsError LispVal -> IOThrowsError LispVal
trapError action = catchError action (\x -> return $ Error x)

-- | lift an IOThrowsError to an IO monad
runIOThrowsLispVal :: IOThrowsError LispVal -> IO LispVal
runIOThrowsLispVal action = liftM extractValue (runExceptT (trapError action))

dynToLispVal :: Dynamic -> LispVal
dynToLispVal = flip fromDyn (fromSimple $ Nil "")

toOpaque :: Typeable a => a -> LispVal
toOpaque = Opaque . toDyn

fromOpaque :: Typeable a => LispVal -> Maybe a
fromOpaque (Opaque d) = fromDynamic d
fromOpaque _ = Nothing

unaryOp :: (LispVal -> ThrowsError LispVal) -> [LispVal] -> ThrowsError LispVal
unaryOp f [v] = f v
unaryOp _ l = throwError $ NumArgs 1 l

unaryIOOp :: (LispVal -> IOThrowsError LispVal) -> [LispVal] -> IOThrowsError LispVal
unaryIOOp f [v] = f v
unaryIOOp _ l = throwError $ NumArgs 1 l

noArg :: ThrowsError LispVal -> [LispVal] -> ThrowsError LispVal
noArg f [] = f
noArg _ l = throwError $ NumArgs 0 l

noIOArg :: IOThrowsError LispVal -> [LispVal] -> IOThrowsError LispVal
noIOArg f [] = f
noIOArg _ l = throwError $ NumArgs 0 l

lispErr :: LispError -> IOThrowsError LispVal
lispErr = throwError

liftLisp :: IO a -> IOThrowsError a
liftLisp = liftIO

class ToZepto a where
  toZepto :: a -> LispVal

instance ToZepto Integer where
  toZepto = fromSimple . Number . NumI
instance ToZepto Int where
  toZepto = fromSimple . Number . NumS
instance ToZepto Double where
  toZepto = fromSimple . Number . NumF
instance ToZepto a => ToZepto (Maybe a) where
  toZepto Nothing = fromSimple $ Nil ""
  toZepto (Just val) = toZepto val
instance ToZepto Bool where
  toZepto = fromSimple . Bool
instance ToZepto Char where
  toZepto = fromSimple . Character
instance ToZepto ByteString where
  toZepto = ByteVector
instance ToZepto a => ToZepto [a] where
  toZepto = List . map toZepto
