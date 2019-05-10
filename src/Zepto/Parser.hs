module Zepto.Parser(readExpr, readExprList) where

import Control.Monad
import Control.Monad.Except
import Data.Array
import Data.ByteString (pack)
import Data.Char
import Data.Complex
import Data.Maybe (isJust)
import Data.Ratio
import Data.Word (Word8)
import Numeric
import Text.ParserCombinators.Parsec hiding (spaces)
import Text.Regex.PCRE.Heavy (compileM)
import qualified Data.HashMap as DM
import qualified Data.ByteString.Char8 as C (pack)

import Zepto.Types

symbol :: Parser Char
symbol = oneOf "!$%&|*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space

commaSpace :: Parser ()
commaSpace = do x <- optionMaybe $ spaces
                y <- optionMaybe $ char ','
                z <- optionMaybe $ spaces
                case [x,z] of
                  [Nothing, Nothing] ->
                    if isJust y then return () else fail "Need a separator between values"
                  _ -> return ()

parseRegex :: Parser LispVal
parseRegex = do _ <- string "r/"
                x <- many (noneOf "/")
                _ <- char '/'
                case compileM (C.pack x) [] of
                  Left str -> fail str
                  Right reg -> return $ fromSimple $ Regex reg

parseString :: Parser LispVal
parseString = do _ <- char '"'
                 x <- many (parseEscaped <|> noneOf"\"")
                 _ <- char '"'
                 return $ fromSimple $ String x

parseEscaped :: forall u . GenParser Char u Char
parseEscaped =  do
    _ <- char '\\'
    c <- anyChar
    case c of
        'a' -> return '\a'
        'b' -> return '\b'
        'n' -> return '\n'
        't' -> return '\t'
        'r' -> return '\r'
        '"' -> return '\"'
        _ -> return c

parseAtom :: Parser LispVal
parseAtom = do first <- letter <|> symbol <|> oneOf "."
               rest <- many (letter <|> digit <|> symbol <|> oneOf ".")
               let atom = first : rest
               if atom == "." || (length atom > 1 && first == '/' && last rest == '/')
                   then pzero
                   else return $ fromSimple $ Atom atom

parseNumber :: Parser LispVal
parseNumber = try parseComplex
              <|> try parseRational
              <|> try parseStandardNum
              <|> parseDigital2
              <|> parseHex
              <|> parseOct
              <|> parseBin

parseStandardNum :: Parser LispVal
parseStandardNum = do num <- try parseReal <|> parseDigital1
                      e <- optionMaybe $ oneOf "eE"
                      case e of
                           Just _ -> do base <- parseDigital1
                                        case expt num base of
                                          Just v  -> return v
                                          Nothing -> fail "unexpectedly failed number parse: digit parser likely broken"
                           Nothing -> return num
                where expt (SimpleVal (Number x)) (SimpleVal (Number y)) = Just $ fromSimple $ Number $ x * convert y
                      expt _ _ = Nothing
                      convert x = NumF $ 10 ** fromIntegral x

parseComplex :: Parser LispVal
parseComplex = do
    realParse <- try parseReal <|> parseDigital1
    let realPrt = case realParse of
                        SimpleVal (Number (NumI n)) -> fromInteger n
                        SimpleVal (Number (NumF f)) -> f
                        _ -> 0
    _ <- char '+'
    imagParse <- try parseReal <|> parseDigital1
    let imagPrt = case imagParse of
                        SimpleVal (Number (NumI n)) -> fromInteger n
                        SimpleVal (Number (NumF f)) -> f
                        _ -> 0
    _ <- char 'i'
    return $ fromSimple $ Number $ NumC $ realPrt :+ imagPrt

parseRational :: Parser LispVal
parseRational = do
    numeratorParse <- parseDigital1
    case numeratorParse of
        SimpleVal (Number (NumI n)) -> do
            _ <- char '/'
            sign <- many (oneOf "-")
            num <- many1 digit
            if length sign > 1
                then pzero
                else do
                    let denominatorParse = read $ sign ++ num
                    if denominatorParse == 0
                        then return $ fromSimple $ Number $ NumI 0
                        else return $ fromSimple $ Number $ NumR $ n % denominatorParse
        _ -> pzero

parseReal :: Parser LispVal
parseReal = do neg <- optionMaybe $ string "-"
               before <- many1 digit
               _ <- string "."
               after <- many1 digit
               case neg of
                    Just _ -> (return . fromSimple . Number . NumF . read) ("-" ++ before ++ "." ++ after)
                    Nothing -> (return . fromSimple . Number . NumF . read) (before ++ "." ++ after)

parseDigital1 :: Parser LispVal
parseDigital1 = do neg <- optionMaybe (string "-" <|> string "+")
                   x <- many1 digit
                   case neg of
                      Just "-" -> (return . fromSimple . Number . NumI . read) ("-" ++ x)
                      _        -> (return . fromSimple . Number . NumI . read) x

parseDigital2 :: Parser LispVal
parseDigital2 = do _ <- try $ string "#d"
                   x <- many1 digit
                   (return . fromSimple . Number . NumI . read) x

parseHex :: Parser LispVal
parseHex = do _ <- try $ string "#x"
              x <- many1 hexDigit
              return $ fromSimple $ Number $ NumI (hex2dig x)

parseOct :: Parser LispVal
parseOct = do _ <- try $ string "#o"
              x <- many1 octDigit
              return $ fromSimple $ Number $ NumI (oct2dig x)

parseBin :: Parser LispVal
parseBin = do _ <- try $ string "#b"
              x <- many1 (oneOf "10")
              return $ fromSimple $ Number $ NumI (bin2dig x)

oct2dig :: String -> Integer
oct2dig x = fst $ head $ readOct x

hex2dig :: String -> Integer
hex2dig x = fst $ head $ readHex x

bin2dig :: String -> Integer
bin2dig = bin2digx 0

bin2digx :: Integer -> String -> Integer
bin2digx digint "" = digint

bin2digx digint (x:xs) = let old = 2 * digint + (if x == '0' then 0 else 1) in
                            bin2digx old xs

parseList :: Parser LispVal
parseList = liftM List $ sepBy parseExpr spaces

parseQList :: Parser LispVal
parseQList = do l <- liftM List $ sepBy parseExpr commaSpace
                return $ List [fromSimple $ Atom "quote", l]

parseDottedList :: Parser LispVal
parseDottedList = do h <- endBy parseExpr spaces
                     t <- char '.' >> spaces >> parseExpr
                     return $ DottedList h t

parseQuoted :: Parser LispVal
parseQuoted = do _ <- char '\''
                 x <- parseExpr
                 return $ List [fromSimple $ Atom "quote", x]


parseQuasiquoted :: Parser LispVal
parseQuasiquoted = do _ <- char '`'
                      x <- parseExpr
                      return $ List [fromSimple $ Atom "quasiquote", x]

parseUnquoted :: Parser LispVal
parseUnquoted = do _ <- try (char ',')
                   x <- parseExpr
                   return $ List [fromSimple $ Atom "unquote", x]

parseSpliced :: Parser LispVal
parseSpliced = do _ <- try (string ",@")
                  x <- parseExpr
                  return $ List [fromSimple $ Atom "unquote-splicing", x]

parseVect :: Parser LispVal
parseVect = do vals <- sepBy parseExpr commaSpace
               return $ Vector (listArray (0, length vals -1) vals)

parseByteVect :: Parser LispVal
parseByteVect = do vals <- sepBy parseNumber commaSpace
                   return $ ByteVector $ pack $ map toB vals
    where toB :: LispVal -> Word8
          toB (SimpleVal (Number (NumI x))) = fromInteger x :: Word8
          toB (SimpleVal (Number (NumS x))) = fromIntegral x :: Word8
          toB _ = 0

parseBool :: Parser LispVal
parseBool = do _ <- string "#"
               x <- oneOf "tf"
               case x of
                 't' -> return $ fromSimple $ Bool True
                 'f' -> return $ fromSimple $ Bool False
                 _   -> fail "This will never happen."

parseChar :: Parser LispVal
parseChar = do
  _ <- try (string "#\\")
  c <- anyChar
  r <- many (letter <|> digit)
  let pchr = c : r
  case pchr of
    "alarm"     -> return $ fromSimple $ Character '\a'
    "backspace" -> return $ fromSimple $ Character '\b'
    "delete"    -> return $ fromSimple $ Character '\DEL'
    "escape"    -> return $ fromSimple $ Character '\ESC'
    "newline"   -> return $ fromSimple $ Character '\n'
    "carriage"  -> return $ fromSimple $ Character '\r'
    "null"      -> return $ fromSimple $ Character '\0'
    "return"    -> return $ fromSimple $ Character '\n'
    "space"     -> return $ fromSimple $ Character ' '
    "tab"       -> return $ fromSimple $ Character '\t'
    _ -> case pchr of
        [ch] -> return $ fromSimple $ Character ch
        ('x' : hexs) -> do
            rv <- parseHexScalar hexs
            return $ fromSimple $ Character rv
        _ -> fail $ "Unable to parse as char: " ++
                    pchr ++
                    "; either pass single character (e.g. #\\1) or" ++
                    " hexadecimal compound (e.g. #\\xf00)"

parseHexScalar :: Monad m => String -> m Char
parseHexScalar num = do
    let ns = Numeric.readHex num
    case ns of
        [] -> fail $ "Unable to parse hex value " ++ show num
        _ -> return $ chr $ fst $ head ns

parseComments :: Parser LispVal
parseComments = do _ <- char ';'
                   _ <- many (noneOf "\n")
                   return $ fromSimple $ Nil ""

parseListComp :: Parser LispVal
parseListComp = do _    <- char '['
                   ret  <- parseExpr
                   _    <- string " | "
                   el   <- parseAtom
                   _    <- string " <- "
                   exr  <- parseListBody
                   comma <- optionMaybe $ string ", "
                   case comma of
                     Just _ -> do
                        cond <- parseExpr
                        _ <- char ']'
                        return $ ListComprehension ret el exr (Just cond)
                     Nothing -> do
                        _ <- char ']'
                        return $ ListComprehension ret el exr Nothing
    where parseListBody = parseExpr

parseHashComp :: Parser LispVal
parseHashComp = do _    <- string "#{"
                   kret <- parseExpr
                   _    <- char ' '
                   vret <- parseExpr
                   _    <- string " | "
                   k    <- parseAtom
                   _    <- char ' '
                   v    <- parseAtom
                   _    <- string " <- "
                   exr  <- parseHashBody
                   comma <- optionMaybe $ string ", "
                   case comma of
                     Just _ -> do
                        cond <- parseExpr
                        _ <- char '}'
                        return $ HashComprehension (kret, vret) (k, v) exr (Just cond)
                     Nothing -> do
                        _ <- char '}'
                        return $ HashComprehension (kret, vret) (k, v) exr Nothing
    where parseHashBody = parseExpr

parseHashMap :: Parser LispVal
parseHashMap = do vals <- many parseExprPair
                  case construct [] vals of
                    Right m ->
                      case duplicate (map fst m) of
                        Just d  ->  fail $ "Duplicate key: " ++ show d
                        Nothing -> return $ HashMap $ DM.fromList m
                    Left x  -> fail $ "All values must be simple (offending clause: " ++ show x ++ ")"
    where construct :: [(Simple, LispVal)] -> [[LispVal]] -> Either LispVal [(Simple, LispVal)]
          construct acc [] = Right acc
          construct acc ((SimpleVal a : b : _) : l) = construct ((a, b) : acc) l
          construct _ ((x : _) : _) = Left x
          construct _ ([] : _) = Left $ fromSimple $ Nil ""
          duplicate :: [Simple] -> Maybe LispVal
          duplicate [] = Nothing
          duplicate (x:xs) = if x `elem` xs then Just (fromSimple x) else duplicate xs
          parseExprPair :: Parser [LispVal]
          parseExprPair = do k <- parseExpr
                             _ <- optionMaybe $ commaSpace
                             v <- parseExpr
                             _ <- optionMaybe $ commaSpace
                             return [k, v]

parseExpr :: Parser LispVal
parseExpr = parseComments
        <|> try parseRegex
        <|> parseNumber
        <|> do _ <- try $ string "#("
               x <- parseVect
               _ <- char ')'
               return x
        <|> do _ <- char '{'
               x <- parseVect
               _ <- char '}'
               return x
        <|> do _ <- try $ string "b("
               x <- parseByteVect
               _ <- char ')'
               return x
        <|> do _ <- try $ string "b{"
               x <- parseByteVect
               _ <- char '}'
               return x
        <|> do _ <- try $ string "#u8("
               x <- parseByteVect
               _ <- char ')'
               return x
        <|> parseSpliced
        <|> parseSpliced
        <|> parseString
        <|> parseQuoted
        <|> try parseBool
        <|> parseQuasiquoted
        <|> parseUnquoted
        <|> parseChar
        <|> try parseHashComp
        <|> do _ <- try $ string "#{"
               x <- try parseHashMap
               _ <- char '}'
               return x
        <|> do _ <- char '('
               x <- try parseList <|> parseDottedList
               _ <- char ')'
               return x
        <|> try parseListComp
        <|> do _ <- char '['
               x <- parseQList
               _ <- char ']'
               return x
        <|> try parseAtom

readOrThrow :: Parser a -> String -> ThrowsError a
readOrThrow parser input = case parse parser input input of
      Left err -> throwError $ ParseErr err
      Right val -> return val

-- | read a single expression
readExpr :: String -> ThrowsError LispVal
readExpr = readOrThrow parseExpr

-- | read a list of expressions
readExprList :: String -> ThrowsError [LispVal]
readExprList s = do x <- readOrThrow (endBy parseExpr spaces) (trim (s ++ "\n"))
                    return $ trimNil [] x
    where trim (x:xs) | isSpace x = trim xs
                      | otherwise = x:xs
          trim x = x
          trimNil acc [] = acc
          trimNil acc (SimpleVal (Nil _) : xs) = trimNil acc xs
          trimNil acc (x : xs) = trimNil (acc ++ [x]) xs
