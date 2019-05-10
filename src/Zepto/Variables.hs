module Zepto.Variables where
import Control.Monad.Except
import Data.IORef
import qualified Data.HashMap as DM

import Zepto.Types

isObject :: LispVal -> Bool
isObject (List _) = True
isObject (DottedList _ _) = True
isObject (SimpleVal (String _)) = True
isObject (Vector _) = True
isObject (Pointer _ _) = True
isObject _ = False

-- | the module namespace
mnamespace :: Char
mnamespace = 'm'

-- | the variable namespace
vnamespace :: Char
vnamespace = 'v'

allBindings :: Env -> IO (DM.Map String (IORef LispVal))
allBindings (Environment Nothing b _) = readIORef b
allBindings (Environment (Just parent) b _) = do
        x <- readIORef b
        y <- allBindings parent
        return $ DM.union x y

copyEnv :: Env -> IO Env
copyEnv env = do
        ptrs <- liftIO $ readIORef $ pointers env
        ptrList <- newIORef ptrs
        binds <- liftIO $ readIORef $ bindings env
        bindingListT <- mapM addBind $ DM.toList binds
        bindingList <- newIORef $ DM.fromList bindingListT
        return $ Environment (parentEnv env) bindingList ptrList
    where addBind (name, val) =
            liftIO (readIORef val)
              >>= newIORef
                >>= tuplify name
          tuplify x y = return (x, y)

extendEnv :: Env -> [((Char, String), LispVal)] -> IO Env
extendEnv envRef abindings = do
        bindinglistT <- mapM addBind abindings
        bindinglist <- newIORef $ DM.fromList bindinglistT
        nullPointers <- newIORef $ DM.fromList []
        return $ Environment (Just envRef) bindinglist nullPointers
    where addBind ((namespace, name), val) = do
                ref <- newIORef val
                return (getVarName namespace name, ref)

recExportsFromEnv :: Env -> IO [LispVal]
recExportsFromEnv env = do
        xs <- exportsFromEnv env
        case parentEnv env of
            Just par -> do
                pxs <- liftIO $ recExportsFromEnv par
                return $ xs ++ pxs
            Nothing -> return xs

exportsFromEnv :: Env -> IO [LispVal]
exportsFromEnv env = do
        binds <- liftIO $ readIORef $ bindings env
        return $ getExports [] $ fst $ unzip $ DM.toList binds
    where
        getExports acc (('m':'_':b) : bs) = getExports (SimpleVal (Atom b):acc) bs
        getExports acc (('v':'_':b) : bs) = getExports (SimpleVal (Atom b):acc) bs
        getExports acc (_ : bs) = getExports acc bs
        getExports acc [] = acc

-- | checks whether a variable is bound
isBound :: Env -> String -> IO Bool
isBound envRef = isNamespaceBound envRef vnamespace

-- | checks whether a variable is bound to a namespace
isNamespaceBound :: Env -> Char -> String -> IO Bool
isNamespaceBound envRef prfx var = do
        binds <- liftIO $ readIORef $ bindings envRef
        if DM.member (getVarName prfx var) binds
          then return True
          else
            case parentEnv envRef of
              Just par -> isNamespaceBound par prfx var
              Nothing -> return False


getVarName :: Char -> String -> String
getVarName namespace name = namespace : ('_' : name)

-- | gets a variable from an environment
getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef = getNamespacedVar envRef vnamespace

-- | gets a variable from an environment in a specific namespace
getNamespacedVar :: Env -> Char -> String -> IOThrowsError LispVal
getNamespacedVar envRef namespace var = do
        v <- getNamespacedVar' envRef namespace var
        case v of
            Just a -> return a
            Nothing -> throwError $ UnboundVar "Getting an unbound variable" var

getNamespacedVar' :: Env -> Char -> String -> IOThrowsError (Maybe LispVal)
getNamespacedVar' envRef namespace var = getNamespacedObj' envRef namespace var readIORef

getNamespacedObj' :: Env -> Char -> String -> (IORef LispVal -> IO a) -> IOThrowsError (Maybe a)
getNamespacedObj' envRef namespace var unpackFun = do
        binds <- liftIO $ readIORef $ bindings envRef
        case DM.lookup (getVarName namespace var) binds of
            Just a -> do
                v <- liftIO $ unpackFun a
                return $ Just v
            Nothing -> case parentEnv envRef of
                        Just par -> getNamespacedObj' par namespace var unpackFun
                        Nothing -> return Nothing

setVar, defineVar :: Env -> String -> LispVal -> IOThrowsError LispVal
-- | sets a variable to an environment
setVar envRef = setNamespacedVar envRef vnamespace
-- | defines a variable to an environment
defineVar envRef = defineNamespacedVar envRef vnamespace

-- | sets a variable to an environment in a specific namespace
setNamespacedVar :: Env -> Char -> String -> LispVal -> IOThrowsError LispVal
setNamespacedVar envRef namespace var value =
        case value of
            Pointer p _ ->
                if p == var
                    then return value
                    else next
            _ -> next
    where next = do _ <- updatePointers envRef namespace var
                    setNamespacedVar' envRef namespace var value

setNamespacedVar' :: Env -> Char -> String -> LispVal -> IOThrowsError LispVal
setNamespacedVar' envRef namespace var value = do
    valueToStore <- getValueToStore namespace var envRef value
    setNamespacedVarDirect envRef namespace var valueToStore

setNamespacedVarDirect :: Env -> Char -> String -> LispVal -> IOThrowsError LispVal
setNamespacedVarDirect envRef namespace var valueToStore = do
        env <- liftIO $ readIORef $ bindings envRef
        case DM.lookup (getVarName namespace var) env of
            Just a -> do
                liftIO $ writeIORef a valueToStore
                return valueToStore
            Nothing -> case parentEnv envRef of
                Just par -> setNamespacedVarDirect par namespace var valueToStore
                Nothing -> throwError $ UnboundVar "Setting an unbound variable" var

updatePointers :: Env -> Char -> String -> IOThrowsError LispVal
updatePointers envRef namespace var = do
  ptrs <- liftIO $ readIORef $ pointers envRef
  case DM.lookup (getVarName namespace var) ptrs of
    Just valIORef -> do
      val <- liftIO $ readIORef valIORef
      case val of
        (Pointer pVar pEnv : ps) -> do
          liftIO $ writeIORef valIORef []
          _ <- movePointers pEnv namespace pVar ps
          _ <- pointToNewVar pEnv namespace pVar ps
          existingValue <- getNamespacedVar envRef namespace var
          setNamespacedVar pEnv namespace pVar existingValue
        [] -> return $ SimpleVal $ Nil ""
        _ -> throwError $ InternalError
               "non-pointer value found in updatePointers"
    Nothing -> return $ SimpleVal $ Nil ""
 where
  movePointers :: Env -> Char -> String -> [LispVal] -> IOThrowsError LispVal
  movePointers envRef' namespace' var' ptrs = do
    env <- liftIO $ readIORef $ pointers envRef'
    case DM.lookup (getVarName namespace' var') env of
      Just ps' -> do
        ps <- liftIO $ readIORef ps'
        liftIO $ writeIORef ps' $ ps ++ ptrs
        return $ SimpleVal $ Nil ""
      Nothing -> do
        valueRef <- liftIO $ newIORef ptrs
        liftIO $ writeIORef (pointers envRef') (DM.insert (getVarName namespace var') valueRef env)
        return $ SimpleVal $ Nil ""
  pointToNewVar pEnv namespace' pVar' (Pointer v e : ps) = do
    _ <- setNamespacedVarDirect e namespace' v (Pointer pVar' pEnv)
    pointToNewVar pEnv namespace' pVar' ps
  pointToNewVar _ _ _ [] = return $ SimpleVal $ Nil ""
  pointToNewVar _ _ _ _ = throwError $ InternalError "pointToNewVar"

-- | defines a variable to an environment in a specific namespace
defineNamespacedVar :: Env -> Char -> String -> LispVal -> IOThrowsError LispVal
defineNamespacedVar envRef namespace var value = do
        alreadyDefined <- liftIO $ isNamespaceBound envRef namespace var
        if alreadyDefined
            then setNamespacedVar envRef namespace var value >> return value
            else do
                valueToStore <- getValueToStore namespace var envRef value
                liftIO $ do
                    valueRef <- newIORef valueToStore
                    env <- readIORef $ bindings envRef
                    writeIORef (bindings envRef) (DM.insert (getVarName namespace var) valueRef env)
                    return valueToStore

getValueToStore :: Char -> String -> Env -> LispVal -> IOThrowsError LispVal
getValueToStore n v e (Pointer p pEnv) = addReversePointer n p pEnv n v e
getValueToStore _ _ _ v = return v

addReversePointer :: Char -> String -> Env -> Char -> String -> Env -> IOThrowsError LispVal
addReversePointer namespace var envRef ptrNamespace ptrVar ptrEnvRef = do
    env <- liftIO $ readIORef $ bindings envRef
    case DM.lookup (getVarName namespace var) env of
        Just a -> do
            v <- liftIO $ readIORef a
            if isObject v
                then do
                    ptrs <- liftIO $ readIORef $ pointers envRef
                    case DM.lookup (getVarName namespace var) ptrs of
                        Just valueRef -> liftIO $ do
                            value <- readIORef valueRef
                            writeIORef valueRef (value ++ [Pointer ptrVar ptrEnvRef])
                            return $ Pointer var envRef
                        Nothing -> liftIO $ do
                            valueRef <- newIORef [Pointer ptrVar ptrEnvRef]
                            writeIORef (pointers envRef) (DM.insert (getVarName namespace var) valueRef ptrs)
                            return $ Pointer var envRef
                else return v
        Nothing -> case parentEnv envRef of
            Just par -> addReversePointer namespace var par ptrNamespace ptrVar ptrEnvRef
            Nothing -> throwError $ UnboundVar "Getting an unbound variable" var

-- | binds multiple variables at once
