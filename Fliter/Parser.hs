module Fliter.Parser where

import Control.Applicative ((<$>), (<*>), (*>), (<*))
import Control.Monad
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Char
import Data.List
import Data.Word
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as T
import System.IO.Unsafe

import qualified Fliter.EDSL as E
import Fliter.Syntax

identifier = T.identifier haskell
reserved = T.reserved haskell
reservedOp = T.reservedOp haskell
braces = T.braces haskell
semiSep1 = T.semiSep1 haskell
integer = T.integer haskell
parens = T.parens haskell

fun :: [Id] -> Parser Id
fun fs = try $ do v <- identifier
                  guard $ v `elem` fs
                  return v

var :: Parser Id
var = try $ do v <- identifier
               guard $ isLower $ head v
               return v
               
con :: Parser Id
con = try $ do v <- identifier
               guard $ isUpper $ head v
               return v

expr :: [Id] -> Parser (Expr () Id)
expr fs = (E.app) <$> expr' fs <*> many (expr' fs)

expr' :: [Id] -> Parser (Expr () Id)
expr' fs = (E.pVa . fromInteger) <$> integer
       <|> pop "+" (E.+$)
       <|> pop "-" (E.-$)
       <|> pop "==" (E.==$)
       <|> pop "<=" (E.<=$)
       <|> pop "/=" (E./=$)
       <|> E.con <$> con
       <|> E.fun <$> fun fs
       <|> E.var <$> var
       <|> pop "`seq`" (E.seqq)
       <|> reserved "case" *> (E.caseOf <$> expr fs
           <*> (reserved "of" *> braces (semiSep1 (alte fs))))
       <|> reserved "let" *> (E.letIn <$> braces (semiSep1 (bind fs))
           <*> (reserved "in" *> expr fs))
       <|> parens (expr fs)

pop :: String -> (Id -> Id -> Expr () Id) -> Parser (Expr () Id)
pop op f = try (f <$> var <*> (reservedOp op *> var))

bind :: [Id] -> Parser (Id, Expr () Id)
bind fs = (,) <$> var <*> (reservedOp "=" *> expr fs)
           
alte :: [Id] -> Parser (Alte () Id)
alte fs = (E.-->) <$> pat <*> (reservedOp "->" *> expr fs)

pat :: Parser String
pat = (unwords .) . (:) <$> con <*> many var

funcName :: Parser String
funcName = var <* funcBody []

funcBody :: [Id] -> Parser (Func () Id)
funcBody fs = E.lam . unwords <$> many var <*> (reservedOp "=" *> expr fs)

func :: [Id] -> Parser (Id, Func () Id)
func fs = (,) <$> var <*> funcBody fs

prog :: Parser (Prog () Id)
prog = do s <- getParserState
          fs <- braces (semiSep1 funcName)
          setParserState s
          Prog <$> braces (semiSep1 $ func fs)
          
progs :: Parser [Prog () Id]
progs = many prog
          
parseProg :: FilePath -> Prog () Id
parseProg path = either (error "Failed!") id $ 
                 unsafePerformIO $ parseFromFile prog path

parseProgs :: FilePath -> IO [Prog () Id]
parseProgs path = zipWith aux [0..] <$> tail <$> BS.split '~' <$> BS.readFile path
  where aux i str = case parse prog (path ++ '~' : show i) ('{' : BS.unpack str ++ "}") of
          Left err -> error $ show err
          Right p  -> p
  