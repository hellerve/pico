module Zepto.Primitives(primitives
                       , ioPrimitives
                       , evalPrimitives
                       , eval
                       , evalString
                       ) where
import Data.Array
import Data.Maybe
import Control.Monad
import Control.Monad.Except
import System.Directory
import System.IO
import System.IO.Error (tryIOError)
import qualified Data.HashMap as DM
import qualified Control.Exception as CE
import qualified Data.ByteString as BS (hPut, cons, splitAt, append, tail, index)

import Paths_zepto
import Zepto.Primitives.CharStrPrimitives
import Zepto.Primitives.ConversionPrimitives
import Zepto.Primitives.EnvironmentPrimitives
import Zepto.Primitives.ErrorPrimitives
import Zepto.Primitives.FunctionPrimitives
import Zepto.Primitives.HashPrimitives
import Zepto.Primitives.IOPrimitives
import Zepto.Primitives.ListPrimitives
import Zepto.Primitives.LoadPrimitives
import Zepto.Primitives.LogMathPrimitives
import Zepto.Primitives.RegexPrimitives
import Zepto.Primitives.SocketPrimitives
import Zepto.Primitives.TypeCheckPrimitives
import Zepto.Primitives.VersionPrimitives
import Zepto.Types
import Zepto.Parser
import Zepto.Variables
import Zepto.Macro

-- | a list of all regular primitives
primitives :: [(String, [LispVal] -> ThrowsError LispVal, String)]
primitives = [ ("+", numericPlusop (+), plusDoc)
             , ("-", numericMinop (-), minDoc)
             , ("*", numericTimesop (*), timesDoc)
             , ("/", numericBinop div, divDoc)
             , ("mod", numericBinop mod, "modulo of two or more values" ++ numericBinOpDoc)
             , ("modulo", numericBinop mod, "modulo of two or more values" ++ numericBinOpDoc)
             , ("quotient", numericBinop quot, "quotient of two or more values" ++ numericBinOpDoc)
             , ("remainder", numericBinop rem, "remainder of two or more values" ++ numericBinOpDoc)
             , ("round", numRound round, "rounds a number" ++ roundOpDoc)
             , ("floor", numRound floor, "floors a number" ++ roundOpDoc)
             , ("ceiling", numRound ceiling, "ceils a number" ++ roundOpDoc)
             , ("truncate", numRound truncate, "truncates a number" ++ roundOpDoc)
             , ("arithmetic-shift", arithmeticShift, "do an arithmetic shift on an integer" ++ bitwiseDoc)
             , ("unsigned-arithmetic-shift", unsignedArithmeticShift, "do an arithmetic shift (zero fill) on an integer" ++ bitwiseDoc)
             , ("bitwise-and", bitwiseAnd, "do a bitwise and on two integers" ++ bitwiseDoc)
             , ("bitwise-or", bitwiseOr, "do a bitwise or on two integers" ++ bitwiseDoc)
             , ("bitwise-xor", bitwiseXor, "do a bitwise xor on two integers" ++ bitwiseDoc)
             , ("bitwise-not", bitwiseNot, "do a bitwise or on one integer" ++ bitwiseDoc)
             , ("real", unaryOp real, "gets real part of a number" ++ unaryDoc "O(1)" "the real part")
             , ("imaginary", unaryOp imaginary, "gets imaginary part of a number" ++ unaryDoc "O(1)" "the imaginary part")
             , ("numerator", unaryOp numerator, "gets numerator of a number" ++ unaryDoc "O(1)" "the numerator")
             , ("denominator", unaryOp denominator, "gets denominator of a number" ++ unaryDoc "O(1)" "the denominator")
             , ("expt", numericBinopErr numPow, powDoc)
             , ("pow", numericBinopErr numPow, powDoc)
             , ("^", numericBinopErr numPow,powDoc)
             , ("**", numericBinopErr numPow, powDoc)
             , ("sqrt", numSqrt, sqrtDoc)
             , ("log", numLog, logDoc)
             , ("abs", numOp abs, "get absolute value" ++ numDoc)
             , ("sin", numOp sin, "sine function" ++ numDoc)
             , ("cos", numOp cos, "cosine function" ++ numDoc)
             , ("tan", numOp tan, "tangens function" ++ numDoc)
             , ("asin", numOp asin, "asine function" ++ numDoc)
             , ("acos", numOp acos, "acosine function" ++ numDoc)
             , ("atan", numOp atan, "atangens function" ++ numDoc)
             , ("=", numBoolBinop (==), "compare equality of two values" ++ numBoolDoc)
             , ("<", numBoolBinop (<), "compare equality of two values" ++ numBoolDoc)
             , (">", numBoolBinop (>), "compare equality of two values" ++ numBoolDoc)
             , ("/=", numBoolBinop (/=), "compare equality of two values" ++ numBoolDoc)
             , (">=", numBoolBinop (>=), "compare equality of two values" ++ numBoolDoc)
             , ("<=", numBoolBinop (<=), "compare equality of two values" ++ numBoolDoc)
             , ("&&", boolMulop (&&), "and operation" ++ boolMulDoc)
             , ("||", boolMulop (||), "or operation" ++ boolMulDoc)

             , ("inspect", inspect, inspectDoc)

             , ("string=?", strBoolBinop (==), "compare equality of two strings" ++ strBoolDoc)
             , ("string>?", strBoolBinop (>), "compare equality of two strings" ++ strBoolDoc)
             , ("string<?", strBoolBinop (<), "compare equality of two strings" ++ strBoolDoc)
             , ("string<=?", strBoolBinop (<=), "compare equality of two strings" ++ strBoolDoc)
             , ("string>=?", strBoolBinop (>=), "compare equality of two strings" ++ strBoolDoc)
             , ("string-ci=?", strCIBoolBinop (==), "compare equality of two strings(case insensitive)" ++ strBoolDoc)
             , ("string-ci>?", strCIBoolBinop (>), "compare equality of two strings(case insensitive)" ++ strBoolDoc)
             , ("string-ci<?", strCIBoolBinop (<), "compare equality of two strings(case insensitive)" ++ strBoolDoc)
             , ("string-ci<=?", strCIBoolBinop (<=), "compare equality of two strings(case insensitive)" ++ strBoolDoc)
             , ("string-ci>=?", strBoolBinop (>=), "compare equality of two strings(case insensitive)" ++ strBoolDoc)
             , ("list:car", unaryOp car, carDoc)
             , ("list:cdr", unaryOp cdr, cdrDoc)
             , ("cons", cons, consDoc)
             , ("eq?", eqv, eqvDoc)
             , ("eqv?", eqv, eqvDoc)
             , ("equal?", equal, eqvDoc)

             , ("error?", unaryOp isError, typecheckDoc "an error")
             , ("pair?", unaryOp isDottedList, typecheckDoc "a pair")
             , ("procedure?", unaryOp isProcedure, typecheckDoc "a procedure")
             , ("number?", unaryOp isNumber, typecheckDoc "a number")
             , ("integer?", unaryOp isInteger, typecheckDoc "an integer")
             , ("float?", unaryOp isFloat, typecheckDoc "a float")
             , ("small-int?", unaryOp isSmall, typecheckDoc "a small int")
             , ("rational?", unaryOp isRational, typecheckDoc "a rational")
             , ("real?", unaryOp isReal, typecheckDoc "a real number")
             , ("list?", unaryOp isList, typecheckDoc "list")
             , ("list:null?", unaryOp isNull, isNullDoc)
             , ("nil?", unaryOp isNil, typecheckDoc "nil")
             , ("symbol?", unaryOp isSymbol, typecheckDoc "symbol")
             , ("atom?", unaryOp isAtom, typecheckDoc "atom")
             , ("vector?", unaryOp isVector, typecheckDoc "vector")
             , ("byte-vector?", unaryOp isByteVector, typecheckDoc "bytevector")
             , ("string?", unaryOp isString, typecheckDoc "string")
             , ("port?", unaryOp isPort, typecheckDoc "port")
             , ("char?", unaryOp isChar, typecheckDoc "char")
             , ("boolean?", unaryOp isBoolean, typecheckDoc "boolean")
             , ("simple?", unaryOp isSimple, typecheckDoc "simple type")
             , ("simple-list?", unaryOp isSimpleList, typecheckDoc "simple list")
             , ("hash-map?", unaryOp isHash, typecheckDoc "hash-map")
             , ("primitive?", unaryOp isPrim, typecheckDoc "primitive")
             , ("function?", unaryOp isFun, typecheckDoc "function")
             , ("env?", unaryOp isEnv, typecheckDoc "env")
             , ("regex?", unaryOp isRegex, typecheckDoc "regex")
             , ("opaque?", unaryOp isOpaque, typecheckDoc "opaque")
             , ("typeof", unaryOp checkType, typeofDoc)
             , ("nil", noArg buildNil, buildDoc "nil")
             , ("inf", noArg buildInf, buildDoc "inf")
             , ("vector", buildVector, buildDoc "vector")
             , ("byte-vector", buildByteVector, buildDoc "bytevector")
             , ("string", buildString, buildDoc "string")
             , ("char:lower-case", unaryOp charDowncase, strCharConvDoc "character" "lower" "1")
             , ("char:upper-case", unaryOp charUpcase, strCharConvDoc "character" "upper" "1")
             , ("string:lower-case", unaryOp stringDowncase, strCharConvDoc "string" "lower" "n")
             , ("string:upper-case", unaryOp stringUpcase, strCharConvDoc "string" "upper" "n")
             , ("vector:length", unaryOp vectorLength, lengthDoc "vector")
             , ("byte-vector:length", unaryOp byteVectorLength, lengthDoc "byte vector")
             , ("vector:subvector", subVector, subvectorDoc)
             , ("byte-vector:subvector", subByteVector, subvectorDoc)
             , ("string:length", unaryOp stringLength, lengthDoc "string")
             , ("string:substitute", stringSub, stringSubDoc)
             , ("make-string", makeString, makeStringDoc)
             , ("make-regex", unaryOp makeRegex, makeRegexDoc)
             , ("make-simple-list", unaryOp list2Simple, conversionDoc "list" "simple list")
             , ("from-simple-list", unaryOp simple2List, conversionDoc "simple list" "list")
             , ("make-vector", makeVector, makeVectorDoc)
             , ("make-small", makeSmall, makeSmallDoc)
             , ("make-hash", makeHash, makeHashDoc)
             , ("make-byte-vector", makeByteVector, makeBVDoc)
             , ("make-error", unaryOp makeError, makeErrorDoc)
             , ("char->integer", unaryOp charToInteger, conversionDoc "char" "integer")
             , ("integer->char", unaryOp integer2Char, conversionDoc "integer" "char")
             , ("vector->list", unaryOp vectorToList, conversionDoc "vector" "list")
             , ("list->vector", unaryOp listToVector, conversionDoc "list" "vector")
             , ("symbol->string", unaryOp symbol2String, conversionDoc "string" "symbol")
             , ("number->string", number2String, conversionDoc "number" "string")
             , ("number->bytes", unaryOp number2Bytes, conversionDoc "number" "bytes")
             , ("bytes->float", unaryOp bytes2Float, conversionDoc "bytes" "float")
             , ("string->symbol", unaryOp string2Symbol, conversionDoc "string" "symbol")
             , ("string->number", stringToNumber, conversionDoc "string" "number")
             , ("string->list", unaryOp stringToList, conversionDoc "string" "list")
             , ("list->string", unaryOp listToString, conversionDoc "list" "string")
             , ("byte-vector->string", unaryOp byteVectorToString, conversionDoc "byte vector" "string")
             , ("string->byte-vector", unaryOp stringToByteVector, conversionDoc "string" "byte vector")
             , ("string:parse", unaryOp stringParse, stringParseDoc)
             , ("substring", substring, substringDoc)
             , ("vector:ref", vectorRef, refDoc "vector")
             , ("byte-vector:ref", byteVectorRef, refDoc "byte vector")
             , ("string:ref", stringRef, refDoc "string")
             , ("string:find", stringFind, stringFindDoc)
             , ("string:append", stringExtend, appendDoc "string")
             , ("byte-vector:append", byteVectorAppend, appendDoc "byte vector")
             , ("list:append", listAppend, appendDoc "list")
             , ("vector:append", vectorAppend, appendDoc "vector")
             , ("+=", allAppend, appendDoc "collection")
             , ("string:extend", stringExtend, extendDoc "string")
             , ("list:extend", listExtend, extendDoc "list")
             , ("vector:extend", vectorExtend, extendDoc "vector")
             , ("byte-vector:extend", byteVectorAppend, extendDoc "byte vector")
             , ("++", allExtend, extendDoc "collection")
             , ("regex:pattern", unaryOp regexPattern, regexPatternDoc)
             , ("regex:matches?", regexMatches, regexMatchesDoc)
             , ("regex:scan", regexScan, regexScanDoc)
             , ("regex:scan-ranges", regexScanO, regexScanODoc)
             , ("regex:sub", regexSub, regexSubDoc)
             , ("regex:gsub", regexGSub, regexGSubDoc)
             , ("regex:split", regexSplit, regexSplitDoc)
             , ("hash:keys", hashKeys, hashKVDoc "keys")
             , ("hash:values", hashVals, hashKVDoc "values")
             , ("hash:contains?", inHash, inHashDoc)
             , ("hash:remove", hashRemove, hashRemoveDoc)
             , ("zepto:version", noArg getVersion, versionDoc)
             , ("zepto:ghc", noArg getGhc, ghcDoc)
             , ("function:name", unaryOp functionName, functionNameDoc)
             , ("function:args", unaryOp functionArgs, functionArgsDoc)
             , ("function:body", unaryOp functionBody, functionBodyDoc)
             , ("function:docstring", unaryOp functionDocs, functionDocsDoc)
             , ("error:text", unaryOp errorText, errorTextDoc)
             , ("error:throw", unaryOp throwZError, throwZErrorDoc)
             ]

-- | a list of all io-bound primitives
ioPrimitives :: [(String, [LispVal] -> IOThrowsError LispVal, String)]
ioPrimitives = [ ("open-input-file", makePort ReadMode, openDoc "reading")
               , ("open-output-file", makePort WriteMode, openDoc "writing")
               , ("close-input-file", closePort, closeFDoc "reading")
               , ("close-output-file", closePort, closeFDoc "writing")
               , ("input-port?", unaryIOOp isInputPort, typecheckDoc "input port")
               , ("output-port?", unaryIOOp isOutputPort, typecheckDoc "output port")
               , ("os:get-home-dir", noIOArg getHomeDir, getHomeDirDoc)
               , ("os:get-current-dir", noIOArg getCurrentDir, getCurrentDirDoc)
               , ("zepto:home", noIOArg getZeptoDir, zeptoDirDoc)
               , ("os:change-dir", unaryIOOp changeDir, changeDirDoc)
               , ("read", readProc, readDoc)
               , ("write", writeProc printInternal, writeDoc)
               , ("read-char", readCharProc hGetChar, peekCharDoc)
               , ("peek-char", readCharProc hLookAhead, readCharDoc)
               , ("write-char", writeCharProc, writeCharDoc)
               , ("display", writeProc print', displayDoc)
               , ("read-contents", readContents, readContentsDoc)
               , ("read-contents-binary", readBinaryContents, readBinContentsDoc)
               , ("parse", readAll, readAllDoc)
               , ("exit", exitProc, exitDoc)
               , ("system", systemProc, systemDoc)
               , ("os:setenv", setEnvProc, setEnvDoc)
               , ("os:getenv", unaryIOOp getEnvProc, getEnvDoc)
               , ("unix-timestamp", noIOArg timeProc, timeDoc)
               , ("make-null-env", makeNullEnv, makeNullEnvDoc)
               , ("make-base-env", makeBaseEnv, makeBaseEnvDoc)
               , ("env->hashmap", unaryIOOp env2HashMap, env2HashMapDoc)

               , ("net:socket", socket, socketDoc)
               , ("net:get-addr-info", getAddrInfo, getAddrInfoDoc)
               , ("net:connect", connect, connectDoc)
               , ("net:recv", recv, recvDoc)
               , ("net:send", send, sendDoc)
               , ("net:bind-socket", bindSocket, bindSocketDoc)
               , ("net:listen", listen, listenDoc)
               , ("net:accept", accept, acceptDoc)
               , ("net:close-socket", close, closeDoc)
               , ("crypto:randint", randIntProc, randIntDoc)
               , ("load-native", loadNative, loadNativeDoc)
               ]

evalPrimitives :: [(String, [LispVal] -> IOThrowsError LispVal, String)]
evalPrimitives = [ ("eval", evalFun, evalDoc)
                 , ("macro-expand", macroEvalFun, macroEvalDoc)
                 , ("apply", evalApply, applyDoc)
                 , ("call-with-current-continuation", evalCallCC, callCCDoc)
                 , ("call/cc", evalCallCC, callCCDoc)
                 , ("catch-error", catchZError, catchErrorDoc)
                 , ("catch-vm-error", catchVMError, catchVMErrorDoc)
                 , ("env:in?", inEnv, inEnvDoc)
                 ]

printInternal :: Handle -> LispVal -> IO ()
printInternal handle val =
    case val of
      ByteVector x -> BS.hPut handle x
      _            -> hPrint handle val

stringToNumber :: [LispVal] -> ThrowsError LispVal
stringToNumber [SimpleVal (String s)] = do
        result <- readExpr s
        case result of
            n@(SimpleVal (Number _)) -> return n
            _ -> return $ fromSimple $ Bool False
stringToNumber [SimpleVal (String s), SimpleVal (Number base)] =
    case base of
        2 -> stringToNumber [fromSimple $ String $ "#b" ++ s]
        8 -> stringToNumber [fromSimple $ String $ "#o" ++ s]
        10 -> stringToNumber [fromSimple $ String s]
        16 -> stringToNumber [fromSimple $ String $ "#x" ++ s]
        _ -> throwError $ Default $ "Invalid base: " ++ show base
stringToNumber [badType] = throwError $ TypeMismatch "string" badType
stringToNumber badArgList = throwError $ NumArgs 1 badArgList

-- | searches all primitives for a possible completion
evalString :: Env -> String -> IO String
evalString env expr =  runIOThrows $ liftM show $
    liftThrows (readExpr expr) >>=
    macroEval env >>=
    eval env (nullCont env)

contEval :: Env -> LispVal -> LispVal -> IOThrowsError LispVal
contEval _ (Cont (Continuation cEnv cBody cCont Nothing Nothing _)) val =
    case cBody of
        [] ->
            case cCont of
                Cont (Continuation nEnv _ _ _ _ _) -> contEval nEnv cCont val
                _ -> return val
        [lval] -> eval cEnv (Cont (Continuation cEnv [] cCont Nothing Nothing [])) lval
        (lval : lvals) -> eval cEnv (Cont (Continuation cEnv lvals cCont Nothing Nothing [])) lval
contEval _ _ _ = throwError $ InternalError "This should never happen"


makeBaseEnvDoc :: String
makeBaseEnvDoc = "makes a bae environment as created at zepto startup.\n\
\n\
  complexity: O(1)\n\
  returns: a base environment"

makeBaseEnv :: [LispVal] -> IOThrowsError LispVal
makeBaseEnv [] = do
    env <- liftIO primitiveBindings
    return $ Environ env
  where
    primitiveBindings = nullEnv >>= flip extendEnv (fmap (makeBind IOFunc) ioPrimitives ++
                                  fmap (makeBind PrimitiveFunc) primitives ++
                                  fmap (makeBind EvalFunc) evalPrimitives)
                  where makeBind constructor (var, func, _) = ((vnamespace, var), constructor var func)
makeBaseEnv args = throwError $ NumArgs 0 args

stringParseDoc :: String
stringParseDoc = "parse a string <par>str</par>.\n\
\n\
  params:\n\
    - str: the string to parse\n\
  complexity: O(n)\n\
  returns: a zepto data structure"

stringParse :: LispVal -> ThrowsError LispVal
stringParse (SimpleVal (String x)) = readExpr x
stringParse x = throwError $ TypeMismatch "string" x

macroEvalDoc :: String
macroEvalDoc = "expand all the macros in a given S-Expression.\n\
  Optionally takes an environment which should be used as a context for\n\
  the expansion.\n\
\n\
  Example:\n\
  <zepto>\n\
    (macro-expand [let ((x 1)) x]) ; => ((lambda (x) x) 1)\n\
  </zepto>\n\
\n\
  params:\n\
    - stmt: the list in which the macros should be expanded\n\
    - env: the environment to use (optional)\n\
  complexity: O(n)\n\
  returns: the expanded version of <zepto>stmt</zepto> as a list"


macroEvalFun :: [LispVal] -> IOThrowsError LispVal
macroEvalFun [Cont (Continuation env _ _ _ _ _), val] = macroEval env val
macroEvalFun [Cont _, val, Environ env] = macroEval env val
macroEvalFun (_ : args) = throwError $ NumArgs 1 args
macroEvalFun _ = throwError $ NumArgs 1 []

evalDoc :: String
evalDoc = "evaluate a list as an S-Expression.\n\
  Optionally takes an environment which should be used as a context for\n\
  the evaluation.\n\
\n\
  Example:\n\
  <zepto>\n\
    (eval `(,+ 1 2)) ; => 3\n\
  </zepto>\n\
\n\
  params:\n\
    - stmt: the list to interpret as a statement\n\
    - env: the environment to use (optional)\n\
  complexity: that of the input expression\n\
  returns: the result of the output of <zepto>stmt</zepto>"

evalFun :: [LispVal] -> IOThrowsError LispVal
evalFun [c@(Cont (Continuation env _ _ _ _ _)), val] = eval env c val
evalFun [c@(Cont _), val, Environ env] = eval env c val
evalFun (_ : args) = throwError $ NumArgs 1 args
evalFun _ = throwError $ NumArgs 1 []

applyDoc :: String
applyDoc = "take a function <par>f</par> and a list of arguments\n\
  <par>args</par> and call the function with those.\n\
\n\
  Example:\n\
  <zepto>\n\
    (apply + [1 2 3]) ; => 6\n\
  </zepto>\n\
\n\
  params:\n\
    - f: the function to call\n\
    - args: the arguments for <par>f</par>\n\
  complexity: that of the function <par>f</par> called with the arguments <par>args</par>\n\
  returns: the result of <par>f</par> called with the arguments <par>args</par>"

evalApply :: [LispVal] -> IOThrowsError LispVal
evalApply [conti@(Cont _), fun, List args] = apply conti fun args
evalApply (conti@(Cont _) : fun : args) = apply conti fun args
evalApply [_, _, arg] = throwError $ TypeMismatch "list" arg
evalApply (_ : args) = throwError $ NumArgs 2 args
evalApply _ = throwError $ NumArgs 2 []

callCCDoc :: String
callCCDoc = "call the function <par>f</par> with the current continuation.\n\
\n\
  params:\n\
    - f: the function to call\n\
  complexity: that of <par>f</par>\n\
  returns: the result of <par>f</par>"

evalCallCC :: [LispVal] -> IOThrowsError LispVal
evalCallCC [conti@(Cont _), fun] =
        case fun of
            Cont _ -> apply conti fun [conti]
            PrimitiveFunc _ f -> do
                result <- liftThrows $ f [conti]
                case conti of
                    Cont (Continuation cEnv _ _ _ _ _) -> contEval cEnv conti result
                    _ -> return result
            Func _ (LispFun _ (Just _) _ _ _) -> apply conti fun [conti]
            Func _ (LispFun aparams _ _ _ _) ->
                if length aparams == 1
                    then apply conti fun [conti]
                    else throwError $ NumArgs (toInteger $ length aparams) [conti]
            other -> throwError $ TypeMismatch "procedure" other
evalCallCC (_ : args) = throwError $ NumArgs 1 args
evalCallCC x = throwError $ NumArgs 1 x

catchErrorDoc :: String
catchErrorDoc = "catches any zepto-defined error in the given quoted\n\
  expression <par>expr</par>. Optionally takes an environment in which\n\
  to call <par>expr</par>.\n\
\n\
  params:\n\
    - expr: the expression to call\n\
    - env: the environment to use (optional)\n\
  complexity: that of <par>expr</par>\n\
  returns: the result of <par>expr</par> or the error that was returned"

catchZError :: [LispVal] -> IOThrowsError LispVal
catchZError [c, x, Environ env] = do
    let res = trapError $ eval env c x
    resX <- liftIO $ runExceptT res
    case resX of
      (Left err) -> return $ Error err
      (Right val) -> return $ val
catchZError [c@(Cont (Continuation env _ _ _ _ _)), x] = catchZError [c, x, Environ env]
catchZError [x, _] = throwError $ TypeMismatch "continuation" x
catchZError x = throwError $ NumArgs 1 (tail x)

catchVMErrorDoc :: String
catchVMErrorDoc = "catches any zepto-defined error in the given quoted\n\
  expression <par>expr</par>. Similar to <fun>catch-error</fun>, but\n\
  also catches VM-internal errors. Optionally takes an environment in which\n\
  to call <par>expr</par>.\n\
\n\
  params:\n\
    - expr: the expression to call\n\
    - env: the environment to use (optional)\n\
  complexity: that of <par>expr</par>\n\
  returns: the result of <par>expr</par> or the error that was returned"


catchVMError :: [LispVal] -> IOThrowsError LispVal
catchVMError [c, x, Environ env] =
          liftIO $ CE.catch (runIOThrowsLispVal $ eval env c x) handler
    where handler :: CE.SomeException -> IO LispVal
          handler msg = return $ fromSimple $ String $ CE.displayException msg
catchVMError [c@(Cont (Continuation env _ _ _ _ _)), x] = catchVMError [c, x, Environ env]
catchVMError [x, _] = throwError $ TypeMismatch "continuation" x
catchVMError x = throwError $ NumArgs 1 (tail x)

findFile' :: String -> ExceptT LispError IO String
findFile' filename = do
        let expanded = expand filename
        fileAsLib <- liftIO $ getDataFileName $ "zepto-stdlib/" ++ filename
        let fileAsLibExpanded = expand fileAsLib
        exists <- fex filename
        existsExpanded <- fex expanded
        existsLib <- fex fileAsLib
        existsLibExpanded <- fex fileAsLibExpanded
        case (exists, existsExpanded, existsLib, existsLibExpanded) of
            (Bool False, Bool False, Bool False, Bool True) -> return fileAsLibExpanded
            (Bool False, Bool False, Bool True, _)          -> return fileAsLib
            (Bool False, Bool True, _, _)                   -> return expanded
            _                                               -> return filename
    where
        expand x = x ++ ".zp"
        fex file = do ex <-liftIO $ doesFileExist file
                      return $ Bool ex

filterAndApply :: String -> LispVal -> Maybe LispVal -> Env
                  -> LispVal -> LispVal -> IOThrowsError LispVal
filterAndApply set ret cond env conti x = do
    newenv <- liftIO $ tryIOError $ liftIO $ copyEnv env
    case newenv of
      Right envval -> do
          _ <- defineVar envval set x
          case cond of
            Nothing -> eval envval conti ret
            Just condition -> do
              t <- eval envval conti condition
              case t of
                SimpleVal (Bool True) -> eval envval conti ret
                _ -> return $ fromSimple $ Nil ""
      Left _ -> return $ fromSimple $ Nil ""

internalApply :: String -> LispVal -> Env -> LispVal
                 -> LispVal -> IOThrowsError LispVal
internalApply set ret env conti x = do
    newenv <- liftIO $ tryIOError $ liftIO $ copyEnv env
    case newenv of
      Right envval -> do
          _ <- defineVar envval set x
          eval envval conti ret
      Left _ -> return $ fromSimple $ Nil ""

isNotNil :: LispVal -> Bool
isNotNil (SimpleVal (Nil _)) = False
isNotNil _ = True

stringifyFunction :: LispVal -> String
stringifyFunction (Func name LispFun {params = args, vararg = varargs, body = _,
                                       closure = _, docstring = doc}) =
    doc ++ "\n  source: " ++
    "(" ++ name ++ " (" ++ unwords (fmap show args) ++
        (case varargs of
            Nothing -> ""
            Just arg -> " . " ++ arg) ++ ") ...)"
stringifyFunction _ = ""

-- | evaluates a parsed expression
eval :: Env -> LispVal -> LispVal -> IOThrowsError LispVal
eval env conti val@(SimpleVal (Nil _)) = contEval env conti val
eval env conti val@(SimpleVal (String _)) = contEval env conti val
eval env conti val@(SimpleVal (Regex _)) = contEval env conti val
eval env conti val@(SimpleVal (Number _)) = contEval env conti val
eval env conti val@(SimpleVal (Bool _)) = contEval env conti val
eval env conti val@(SimpleVal (Character _)) = contEval env conti val
eval env conti val@(Vector _) = contEval env conti val
eval env conti val@(Func _ _) = contEval env conti val
eval env conti val@(IOFunc _ _) = contEval env conti val
eval env conti val@(EvalFunc _ _) = contEval env conti val
eval env conti val@(PrimitiveFunc _ _) = contEval env conti val
eval env conti val@(Opaque _) = contEval env conti val
eval env conti val@(ByteVector _) = contEval env conti val
eval env conti val@(HashMap _) = contEval env conti val
eval env conti val@(Environ _) = contEval env conti val
eval _ _ (List [Vector x, SimpleVal (Number (NumI i))]) = return $ x ! fromIntegral i
eval _ _ (List [Vector x, SimpleVal (Number (NumS i))]) = return $ x ! fromIntegral i
eval _ _ (List [Vector _, wrong@(SimpleVal (Atom (':' : _)))]) =
        throwError $ TypeMismatch "integer" wrong
eval env conti (List [Vector x, SimpleVal (Atom a)]) = do
        i <- getVar env a
        eval env conti (List [Vector x, i])
eval env conti (List [Vector x, expr@(List _)]) = do
        evald <- eval env conti expr
        eval env conti (List [Vector x, evald])
eval _ _ (List [Vector _, x]) = throwError $ TypeMismatch "integer" x
eval _ _ (List [ByteVector x, SimpleVal (Number (NumI i))]) =
        return $ fromSimple $ Number $ NumS $ fromIntegral $ BS.index x (fromIntegral i)
eval _ _ (List [ByteVector x, SimpleVal (Number (NumS i))]) =
        return $ fromSimple $ Number $ NumS $ fromIntegral $ BS.index x (fromIntegral i)
eval _ _ (List [ByteVector _, wrong@(SimpleVal (Atom (':' : _)))]) =
        throwError $ TypeMismatch "integer" wrong
eval env conti (List [ByteVector x, SimpleVal (Atom a)]) = do
        i <- getVar env a
        eval env conti (List [ByteVector x, i])
eval _ _ (List [ByteVector _, x]) = throwError $ TypeMismatch "integer" x
eval _ _ (List [HashMap x, SimpleVal i@(Atom (':' : _))]) = if DM.member i x
        then return $ x DM.! i
        else return $ fromSimple $ Nil ""
eval env conti (List [HashMap x, SimpleVal (Atom a)]) = do
        i <- getVar env a
        eval env conti (List [HashMap x, i])
eval _ _ (List [HashMap x, SimpleVal i]) =
        if DM.member i x
          then return $ x DM.! i
          else return $ fromSimple $ Nil ""
eval env conti (List [HashMap x, form]) = do
        i <- eval env conti form
        eval env conti (List [HashMap x, i])
eval env conti (HashComprehension (keyexpr, valexpr) (SimpleVal (Atom key), SimpleVal (Atom val)) (SimpleVal (Atom iter)) cond) = do
        hash <- contEval env conti =<< getVar env iter
        case hash of
          HashMap e -> do
            keys <- mapM (filterAndApply key keyexpr cond env conti . fromSimple)
                     (DM.keys e)
            vals <- mapM (internalApply val valexpr env conti) (DM.elems e)
            return $ HashMap $ DM.fromList $ buildTuples (map toSimple keys) vals []
          _ -> throwError $ TypeMismatch "hash-map" hash
    where buildTuples :: [Simple] -> [LispVal] -> [(Simple, LispVal)] -> [(Simple, LispVal)]
          buildTuples [] [] l = l
          buildTuples (ax:al) (bx:bl) x = case ax of
            Nil "" -> buildTuples al bl x
            _      -> buildTuples al bl (x ++ [(ax,bx)])
          buildTuples _ _ _ = error "Hash comprehension failed: internal error while building new hash-map"
eval env conti (HashComprehension (keyexpr, valexpr) (SimpleVal (Atom key), SimpleVal (Atom val)) v@(HashMap _) cond) = do
        hash <- contEval env conti v
        case hash of
          HashMap e -> do
            keys <- mapM (filterAndApply key keyexpr cond env conti . fromSimple)
                     (DM.keys e)
            vals <- mapM (internalApply val valexpr env conti) (DM.elems e)
            return $ HashMap $ DM.fromList $ buildTuples (map toSimple keys) vals []
          _ -> throwError $ TypeMismatch "hash-map" hash
    where buildTuples :: [Simple] -> [LispVal] -> [(Simple, LispVal)] -> [(Simple, LispVal)]
          buildTuples [] [] l = l
          buildTuples (ax:al) (bx:bl) x = case ax of
            Nil "" -> buildTuples al bl x
            _      -> buildTuples al bl (x ++ [(ax,bx)])
          buildTuples _ _ _ = error "Hash comprehension failed: internal error while building new hash-map"
eval env conti (ListComprehension ret (SimpleVal (Atom set)) (SimpleVal (Atom iter)) cond) = do
        list <- contEval env conti =<< getVar env iter
        case list of
          List e -> do
            l <- mapM (filterAndApply set ret cond env conti) e
            return $ List $ filter isNotNil l
          _ -> throwError $ TypeMismatch "list" list
eval env conti (ListComprehension ret (SimpleVal (Atom set)) v@(List (SimpleVal (Atom "quote") : _)) cond) = do
        list <- eval env conti v
        case list of
          List e -> do
            l <-mapM (filterAndApply set ret cond env conti) e
            return $ List $ filter isNotNil l
          _ -> throwError $ TypeMismatch "list" list
eval env conti val@(SimpleVal (Atom (':' : _))) = contEval env conti val
eval env conti (SimpleVal (Atom a)) = contEval env conti =<< getVar env a
eval _ _ (List [List [SimpleVal (Atom "quote"), List x], v@(SimpleVal (Number (NumI i)))]) =
        if length x > fromIntegral i
          then return $ x !! fromIntegral i
          else throwError $ BadSpecialForm "index too large" v
eval _ _ (List [List [SimpleVal (Atom "quote"), List x], v@(SimpleVal (Number (NumS i)))]) =
        if length x > i
          then return $ x !! i
          else throwError $ BadSpecialForm "index too large" v
eval _ _ (List [SimpleVal (Atom "quote")]) = throwError $ NumArgs 1 []
eval env conti (List [SimpleVal (Atom "quote"), val]) = contEval env conti val
eval _ _ (List (SimpleVal (Atom "quote") : x)) = throwError $ NumArgs 1 x
eval _ _ (List [SimpleVal (Atom "if")]) = throwError $ NumArgs 3 []
eval env conti (List [SimpleVal (Atom "if"), p, conseq, alt]) = do
        result <- eval env conti p
        case result of
            SimpleVal (Bool False) -> eval env conti alt
            _                      -> eval env conti conseq
eval env conti (List [SimpleVal (Atom "if"), predicate, conseq]) = do
        result <- eval env conti predicate
        case result of
            SimpleVal (Bool True) -> eval env conti conseq
            _                     -> eval env conti $ fromSimple $ Nil ""
eval _ _ (List [SimpleVal (Atom "if"), x]) = throwError $ BadSpecialForm
                            ("if needs a predicate and a consequence "
                            ++ "plus an optional alternative clause")
                            x
eval _ _ (List (SimpleVal (Atom "if") : x)) = throwError $ NumArgs 2 x
eval _ _ (List [SimpleVal (Atom "set!")]) = throwError $ NumArgs 2 []
eval env conti (List [SimpleVal (Atom "set!"), SimpleVal (Atom var), form]) = do
        result <- eval env (nullCont env) form >>= setVar env var
        contEval env conti result
eval _ _ (List [SimpleVal (Atom "set!"), x, _]) = throwError $ BadSpecialForm
                            ("set takes a previously defined variable and "
                            ++ "its new value")
                            x
eval _ _ (List (SimpleVal (Atom "set!") : x)) = throwError $ NumArgs 2 x
eval _ _ (List [SimpleVal (Atom "define")]) = throwError $ NumArgs 2 []
eval _ _ (List [SimpleVal (Atom "define"), a@(SimpleVal (Atom (':' : _))), _]) =
            throwError $ TypeMismatch "symbol" a
eval env conti (List [SimpleVal (Atom "define"), SimpleVal (Atom "_"), form]) = do
        _ <- eval env (nullCont env) form
        contEval env conti $ fromSimple $ Nil ""
eval env conti (List [SimpleVal (Atom "define"), SimpleVal (Atom var), form]) = do
        result <- eval env (nullCont env) form >>= defineVar env var
        contEval env conti result
eval env conti (List (SimpleVal (Atom "define") : List (SimpleVal (Atom var) : p) : SimpleVal (String doc) : b)) =  do
        result <- makeDocFunc var env p b doc >>= defineVar env var
        contEval env conti result
eval env conti (List (SimpleVal (Atom "define") : List (SimpleVal (Atom var) : p) : b)) = do
        result <- makeNormalFunc var env p b >>= defineVar env var
        contEval env conti result
eval env conti (List (SimpleVal (Atom "define") : DottedList (SimpleVal (Atom var) : p) varargs : SimpleVal (String doc) : b)) = do
        result <- makeVarargs var varargs env p b doc >>= defineVar env var
        contEval env conti result
eval env conti (List (SimpleVal (Atom "define") : DottedList (SimpleVal (Atom var) : p) varargs : b)) = do
        result <- makeVarargs var varargs env p b "No documentation" >>= defineVar env var
        contEval env conti result
eval env conti (List (SimpleVal (Atom "lambda") : List p : SimpleVal (String doc) : ensure : b)) =  do
        result <- makeDocFunc "lambda" env p (ensure : b) doc
        contEval env conti result
eval env conti (List (SimpleVal (Atom "lambda") : List p : b)) =  do
        result <- makeNormalFunc "lambda" env p b
        contEval env conti result
eval env conti (List (SimpleVal (Atom "lambda") : DottedList p varargs : SimpleVal (String doc) : ensure : b)) =  do
        result <- makeVarargs "lambda" varargs env p (ensure : b) doc
        contEval env conti result
eval env conti (List (SimpleVal (Atom "lambda") : DottedList p varargs : b)) = do
        result <- makeVarargs "lambda" varargs env p b "lambda"
        contEval env conti result
eval env conti (List (SimpleVal (Atom "lambda") : varargs@(SimpleVal (Atom _)) : SimpleVal (String doc) : ensure : b)) = do
        result <- makeVarargs "lambda" varargs env [] (ensure : b) doc
        contEval env conti result
eval env conti (List (SimpleVal (Atom "lambda") : varargs@(SimpleVal (Atom _)) : b)) = do
        result <- makeVarargs "lambda" varargs env [] b "lambda"
        contEval env conti result
eval _ _ (List [SimpleVal (Atom "lambda")]) = throwError $ NumArgs 2 []
eval _ _ (List (SimpleVal (Atom "lambda") : x)) = throwError $ NumArgs 2 x
eval _ _ (List [SimpleVal (Atom "global-load")]) = throwError $ NumArgs 1 []
eval env conti (List [SimpleVal (Atom "global-load"), SimpleVal (String file)]) = do
        let glob = globalEnv Nothing env
        filename <- findFile' file
        result <- load filename >>= liftM checkLast . mapM (evl glob (nullCont env))
        contEval env conti result
    where evl env' cont' val = macroEval env' val >>= eval env' cont'
          checkLast [] = fromSimple $ Nil ""
          checkLast [x] = x
          checkLast x = last x
eval _ _ (List [SimpleVal (Atom "global-load"), x]) = throwError $ TypeMismatch "string" x
eval _ _ (List (SimpleVal (Atom "global-load") : x)) = throwError $ NumArgs 1 x
eval _ _ (List [SimpleVal (Atom "help")]) = throwError $ NumArgs 1 []
eval _ _ (List [SimpleVal (Atom "doc")]) = throwError $ NumArgs 1 []
eval env _ (List [SimpleVal (Atom "help"), SimpleVal (String val)]) = do
        let x = concat $
                fmap thirdElem (filter filterTuple primitives) ++
                fmap thirdElem (filter filterTuple ioPrimitives)
        if x == ""
            then do
              var <- getVar env val
              case var of
                f@(Func _ _) -> return $ fromSimple $ String $ stringifyFunction f
                IOFunc doc _ -> return $ fromSimple $ String doc
                PrimitiveFunc doc _ -> return $ fromSimple $ String doc
                EvalFunc doc _ -> return $ fromSimple $ String doc
                _ -> throwError $ Default $ val ++ " is not a function"
            else return $ fromSimple $ String x
    where
          filterTuple tuple = (== val) $ firstElem tuple
          firstElem (x, _, _) = x
          thirdElem (_, _, x) = x
eval env _ (List [SimpleVal (Atom "doc"), SimpleVal (String val)]) = do
        let x = concat $
                fmap thirdElem (filter filterTuple primitives) ++
                fmap thirdElem (filter filterTuple ioPrimitives)
        if x == ""
            then do
              var <- getVar env val
              case var of
                f@(Func _ _) -> return $ fromSimple $ String $ stringifyFunction f
                IOFunc doc _ -> return $ fromSimple $ String doc
                PrimitiveFunc doc _ -> return $ fromSimple $ String doc
                EvalFunc doc _ -> return $ fromSimple $ String doc
                _ -> throwError $ Default $ val ++ " is not a function"
            else return $ fromSimple $ String x
    where
          filterTuple tuple = (== val) $ firstElem tuple
          firstElem (x, _, _) = x
          thirdElem (_, _, x) = x
eval env conti (List [SimpleVal (Atom "help"), SimpleVal (Atom val)]) = do
        let x = concat $
                fmap thirdElem (filter filterTuple primitives) ++
                fmap thirdElem (filter filterTuple ioPrimitives)
        if x == ""
            then do
              var <- getVar env val
              case var of
                f@(Func _ _) -> return $ fromSimple $ String $ stringifyFunction f
                IOFunc doc _ -> return $ fromSimple $ String doc
                PrimitiveFunc doc _ -> return $ fromSimple $ String doc
                EvalFunc doc _ -> return $ fromSimple $ String doc
                f@(SimpleVal (Atom _)) -> eval env conti (List [SimpleVal (Atom "help"), f])
                err -> throwError $ Default $ val ++ " is not a function (is: " ++ typeString err ++ ")"
            else return $ fromSimple $ String x
    where
          filterTuple tuple = (== val) $ firstElem tuple
          firstElem (x, _, _) = x
          thirdElem (_, _, x) = x
eval env conti (List [SimpleVal (Atom "doc"), SimpleVal (Atom val)]) = do
        let x = concat $
                fmap thirdElem (filter filterTuple primitives) ++
                fmap thirdElem (filter filterTuple ioPrimitives)
        if x == ""
            then do
              var <- getVar env val
              case var of
                f@(Func _ _) -> return $ fromSimple $ String $ stringifyFunction f
                IOFunc doc _ -> return $ fromSimple $ String doc
                PrimitiveFunc doc _ -> return $ fromSimple $ String doc
                EvalFunc doc _ -> return $ fromSimple $ String doc
                f@(SimpleVal (Atom _)) -> eval env conti (List [SimpleVal (Atom "help"), f])
                _ -> throwError $ Default $ val ++ " is not a function"
            else return $ fromSimple $ String x
    where
          filterTuple tuple = (== val) $ firstElem tuple
          firstElem (x, _, _) = x
          thirdElem (_, _, x) = x
eval env conti (List [SimpleVal (Atom "help"), val]) =
  case val of
    f@(Func _ _) -> return $ fromSimple $ String $ stringifyFunction f
    IOFunc doc _ -> return $ fromSimple $ String doc
    PrimitiveFunc doc _ -> return $ fromSimple $ String doc
    EvalFunc doc _ -> return $ fromSimple $ String doc
    f@(SimpleVal (Atom _)) -> eval env conti (List [SimpleVal (Atom "help"), f])
    x@(List _) -> do
      mevald <- macroEval env x
      evald <- eval env conti mevald
      eval env conti (List [SimpleVal (Atom "help"), evald])
    _ -> throwError $ Default $ show val ++ " cannot be resolved to a function"
eval _ _ (List (SimpleVal (Atom "help") : x)) = throwError $ NumArgs 1 x
eval env conti (List [SimpleVal (Atom "doc"), val]) =
  case val of
    f@(Func _ _) -> return $ fromSimple $ String $ stringifyFunction f
    IOFunc doc _ -> return $ fromSimple $ String doc
    PrimitiveFunc doc _ -> return $ fromSimple $ String doc
    EvalFunc doc _ -> return $ fromSimple $ String doc
    f@(SimpleVal (Atom _)) -> eval env conti (List [SimpleVal (Atom "help"), f])
    x@(List _) -> do
      mevald <- macroEval env x
      evald <- eval env conti mevald
      eval env conti (List [SimpleVal (Atom "help"), evald])
    _ -> throwError $ Default $ show val ++ " cannot be resolved to a function"
eval _ _ (List (SimpleVal (Atom "doc") : x)) = throwError $ NumArgs 1 x
eval _ _ (List [SimpleVal (Atom "quasiquote")]) = throwError $ NumArgs 1 []
eval env conti (List [SimpleVal (Atom "quasiquote"), val]) = contEval env conti =<<doUnQuote env val
    where doUnQuote :: Env -> LispVal -> IOThrowsError LispVal
          doUnQuote e v =
            case v of
                List [SimpleVal (Atom "unquote"), s] -> eval e (nullCont e) s
                List (x : xs) -> liftM List (unquoteListM e (x : xs))
                DottedList xs x -> do
                    rxs <- unquoteListM e xs
                    rx <- doUnQuote e x
                    case rx of
                        List [] -> return $ List rxs
                        List rxlst -> return $ List $ rxs ++ rxlst
                        DottedList rxlst rxlast -> return $ DottedList (rxs ++ rxlst) rxlast
                        _ -> return $ DottedList rxs rx
                Vector vec -> do
                    let len = length (elems vec)
                    vList <- unquoteListM env $ elems vec
                    return $ Vector $ listArray (0, len) vList
                _ -> eval e (nullCont e) (List [SimpleVal (Atom "quote"), v])
          unquoteListM e = foldlM (unquoteListFld e) []
          unquoteListFld e acc v =
            case v of
                List [SimpleVal (Atom "unquote-splicing"), x] -> do
                    value <- eval e (nullCont e) x
                    case value of
                        List t -> return (acc ++ t)
                        _ -> throwError $ TypeMismatch "proper list" value
                _ -> do result <- doUnQuote env v
                        return (acc ++ [result])
          foldlM :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
          foldlM f v (x : xs) = f v x >>= \ a -> foldlM f a xs
          foldlM _ v [] = return v
eval env conti (List [SimpleVal (Atom "string:fill!"), SimpleVal (Atom var), character]) = do
    str <- eval env (nullCont env) =<< getVar env var
    ch <- eval env (nullCont env) character
    case ch of
      (SimpleVal (Character _)) -> do
        result <- eval env (nullCont env) (fillStr(str, ch)) >>= setVar env var
        contEval env conti result
      x -> throwError $ TypeMismatch "character" x
  where fillStr (SimpleVal (String str), SimpleVal (Character ch)) =
            doFillStr (String "", Character ch, length str)
        fillStr (_, _) = fromSimple $ Nil "This should never happen"
        doFillStr (String str, Character ch, left) =
            if left == 0
                then fromSimple $ String str
                else doFillStr(String $ ch : str, Character ch, left - 1)
        doFillStr (_, _, _) = fromSimple $ Nil "This should never happen"
eval env conti (List [SimpleVal (Atom "string:set!"), SimpleVal (Atom var), i, character]) = do
    idx <- eval env (nullCont env) i
    str <- eval env (nullCont env) =<< getVar env var
    case str of
      (SimpleVal (String _)) -> do
          result <- eval env (nullCont env) (substr(str, character, idx)) >>= setVar env var
          contEval env conti result
      x -> throwError $ TypeMismatch "string" x
  where substr (SimpleVal (String str), SimpleVal (Character ch), SimpleVal (Number (NumI j))) =
                              fromSimple . String $ (take (fromInteger j) . drop 0) str ++
                                       [ch] ++
                                       (take (length str) . drop (fromInteger j + 1)) str
        substr (_, _, _) = fromSimple $ Nil "This should never happen"
eval env conti (List [SimpleVal (Atom "vector:set!"), SimpleVal (Atom var), i, object]) = do
    idx <- eval env (nullCont env) i
    obj <- eval env (nullCont env) object
    vec <- eval env (nullCont env) =<< getVar env var
    case vec of
      Vector _ -> do result <- eval env (nullCont env) (updateVector vec idx obj) >>= setVar env var
                     contEval env conti result
      x -> throwError $ TypeMismatch "vector" x
  where updateVector (Vector vec) (SimpleVal (Number (NumI idx))) obj = Vector $ vec//[(fromInteger idx, obj)]
        updateVector _ _ _ = fromSimple $ Nil "This should never happen"
eval _ _ (List (SimpleVal (Atom "vector:set!") : x)) = throwError $ NumArgs 3 x
eval env conti (List [SimpleVal (Atom "byte-vector:set!"), SimpleVal (Atom var), i, object]) = do
    idx <- eval env (nullCont env) i
    obj <- eval env (nullCont env) object
    case obj of
      (SimpleVal (Number (NumS _))) -> do
        vec <- eval env (nullCont env) =<< getVar env var
        case vec of
          ByteVector _ -> do
            result <- eval env (nullCont env) (updateBVector vec idx obj) >>= setVar env var
            contEval env conti result
          x -> throwError $ TypeMismatch "byte-vector" x
      x -> throwError $ TypeMismatch "small int" x
  where updateBVector (ByteVector vec) (SimpleVal (Number (NumI idx))) (SimpleVal (Number (NumS obj))) =
            let (t, d) = BS.splitAt (fromInteger idx) vec
            in ByteVector $ BS.append t (BS.cons (fromIntegral obj) (BS.tail d))
        updateBVector _ _ _ = fromSimple $ Nil ""
eval _ _ (List (SimpleVal (Atom "byte-vector:set!") : x)) = throwError $ NumArgs 3 x
eval env conti (List [SimpleVal (Atom "vector:fill!"), SimpleVal (Atom var), object]) = do
    obj <- eval env (nullCont env) object
    vec <- eval env (nullCont env) =<< getVar env var
    case vec of
      Vector _ -> do result <- eval env (nullCont env) (fillVector vec obj) >>= setVar env var
                     contEval env conti result
      x -> throwError $ TypeMismatch "vector" x
  where fillVector (Vector vec) obj = do
          let l = replicate (lenVector vec) obj
          Vector $ listArray (0, length l - 1) l
        fillVector _ _ = fromSimple $ Nil "This should never happen"
        lenVector v = length (elems v)
eval _ _ (List (SimpleVal (Atom "vector:fill!") : x)) = throwError $ NumArgs 2 x
eval env conti (List (SimpleVal (Atom "begin") : funs))
                        | null funs = eval env conti $ SimpleVal (Nil "")
                        | length funs == 1 = eval env conti (head funs)
                        | otherwise = do
                                    let fs = tail funs
                                    _ <- eval env conti (head funs)
                                    eval env conti (List (SimpleVal (Atom "begin") : fs))
eval env _ (List [SimpleVal (Atom "current-env")]) = return $ Environ env
eval _ _ (List (SimpleVal (Atom "current-env") : x)) = throwError $ NumArgs 0 x
eval env conti (List (function : args)) = do
        func <- eval env (nullCont env) function
        argVals <- mapM (eval env (nullCont env)) args
        case func of
          HashMap _ -> eval env conti (List (func : args))
          Vector _  -> eval env conti (List (func : args))
          ByteVector _  -> eval env conti (List (func : args))
          _         -> apply conti func argVals
eval _ _ badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

readAllDoc :: String
readAllDoc = "read and parse a file. It returns the parsed file as an S-Expression.\n\
\n\
  params:\n\
    - filename: the name of the file to parse\n\
  complexity: O(n)\n\
  returns: a list of expressions"

readAll :: [LispVal] -> IOThrowsError LispVal
readAll [SimpleVal (String filename)] = liftM List $ load filename
readAll badArgs = throwError $ BadSpecialForm "Cannot evaluate " $ head badArgs

load :: String -> IOThrowsError [LispVal]
load filename = do
    res <- liftIO $ doesFileExist filename
    if res
        then liftIO (readFile filename) >>= liftThrows . readExprList
        else throwError $ Default $ "File does not exist: " ++ filename

readDoc :: String
readDoc = "read a line from a file and evaluate the expression, unless\n\
<zepto>:no-eval</zepto> is passed.\n\
If no argument is provided, a line will be read from the standard input.\n\
\n\
  params:\n\
    - args: variable arguments: accepts a port to read from, <zepto>:stdin</zepto> if the line should be read from the standard input or a port\n\
  complexity: O(1)\n\
  returns: the line that was read"

readProc :: [LispVal] -> IOThrowsError LispVal
readProc [] = readProc [Port stdin]
readProc [SimpleVal (Atom ":stdin")] = readProc [Port stdin]
readProc [x@(SimpleVal (Atom ":no-eval"))] = readProc [Port stdin, x]
readProc [SimpleVal (Atom ":stdin"), x@(SimpleVal (Atom ":no-eval"))] = readProc [Port stdin, x]
readProc [Port port, SimpleVal (Atom ":no-eval")] = liftM (fromSimple . String) (liftIO (hGetLine port))
readProc [Port port] = liftIO (hGetLine port) >>= liftThrows . readExpr
readProc badArgs = throwError $ BadSpecialForm "Cannot evaluate " $ head badArgs

readCharDoc :: String
readCharDoc = "read a character from a file <par>f</par> or the standard input.\n\
\n\
  params:\n\
    - f: the file to read a character from; defaults to the standard input (optional)\n\
  complexity: O(1)\n\
  returns: the read character"

peekCharDoc :: String
peekCharDoc = "read a character from a file <par>f</par> or the standard input.\n\
Does not consume the character, i.e. multiple calls to this function will return the same character.\n\
\n\
  params:\n\
    - f: the file to read a character from; defaults to the standard input (optional)\n\
  complexity: O(1)\n\
  returns: the read character"

readCharProc :: (Handle -> IO Char) -> [LispVal] -> IOThrowsError LispVal
readCharProc fun [] = readCharProc fun [Port stdin]
readCharProc fun [Port p] = do
    liftIO $ hSetBuffering p NoBuffering
    input <-  liftIO $ tryIOError (liftIO $ fun p)
    liftIO $ hSetBuffering p LineBuffering
    case input of
        Left _ -> return $ fromSimple $ Bool False
        Right inpChr -> return $ fromSimple $ Character inpChr
readCharProc _ args = if length args == 1
                         then throwError $ TypeMismatch "port" $ List args
                         else throwError $ NumArgs 1 args

apply :: LispVal -> LispVal -> [LispVal] -> IOThrowsError LispVal
apply (Cont (Continuation a b c d e cs)) fn args =
  apply' (Cont (Continuation a b c d e $! buildCallHistory (fn, showArgs args) cs)) fn args
apply _ func args = throwError $ BadSpecialForm "Unable to evaluate form" $ List (func : args)

apply' :: LispVal -> LispVal -> [LispVal] -> IOThrowsError LispVal
apply' _ c@(Cont (Continuation env _ _ _ _ _)) args =
        if toInteger (length args) /= 1
            then throwError $ NumArgs 1 args
            else contEval env c $ head args
apply' (Cont (Continuation _ _ _ _ _ cs)) (IOFunc _ func) args =
        catchError (func args) (throwHistorial cs)
apply' (Cont (Continuation _ _ _ _ _ cs))  (PrimitiveFunc _ func) args =
        catchError (liftThrows $ func args) (throwHistorial cs)
apply' conti@(Cont (Continuation _ _ _ _ _ cs)) (EvalFunc _ fun) args =
        catchError (fun (conti : args)) (throwHistorial cs)
apply' conti@(Cont (Continuation _ _ _ _ _ cs)) (Func _ (LispFun fparams varargs fbody fclosure _)) args =
        if num fparams /= num args && isNothing varargs
            then throwError $ NumArgs (num fparams) args
            else liftIO (extendEnv fclosure $ zip (fmap ((,) vnamespace) fparams) args)
                  >>= bindVarArgs varargs
                  >>= evalBody [(List ((fromSimple $ Atom "begin") : fbody))]
    where
        remainingArgs = drop (length fparams) args
        num = toInteger . length
        evalBody ebody env = case conti of
                                Cont (Continuation _ cBody cCont _ _ _) -> if null cBody
                                    then continueWithContinuation env ebody cCont
                                    else continueWithContinuation env ebody conti
                                _ -> continueWithContinuation env ebody conti
        continueWithContinuation env cebody continuation =
            catchError
              (contEval env (Cont (Continuation env cebody continuation Nothing Nothing [])) $ fromSimple $ Nil "")
              (throwHistorial cs)
        bindVarArgs arg env = case arg of
            Just argName -> liftIO $ extendEnv env [((vnamespace, argName), List remainingArgs)]
            Nothing -> return env
apply' _ func args = throwError $ BadSpecialForm "Unable to evaluate form" $ List (func : args)

makeFunc :: Monad m => String -> Maybe String -> Env -> [LispVal] -> [LispVal] -> String -> m LispVal
makeFunc name varargs env p b doc = return $ Func name $ LispFun (fmap showVal p) varargs b env doc

makeNormalFunc :: String -> Env -> [LispVal] -> [LispVal] -> ExceptT LispError IO LispVal
makeNormalFunc name env p b = makeFunc name Nothing env p b "No documentation available"

makeDocFunc :: String -> Env -> [LispVal] -> [LispVal] -> String -> ExceptT LispError IO LispVal
makeDocFunc name = makeFunc name Nothing

makeVarargs :: String -> LispVal -> Env -> [LispVal] -> [LispVal] -> String -> ExceptT LispError IO LispVal
makeVarargs name = makeFunc name . Just . showVal

