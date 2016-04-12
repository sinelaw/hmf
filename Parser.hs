--------------------------------------------------------------------------
-- Parse a simple functional programs
-- 
{- expr ::= let binder1; ..; binderN in expr  -- let binding, N >= 1
          | \arg1 .. argN -> expr             -- lambda expression, N >= 1
          | if expr then expr else expr
          | expr :: annot
          | expr1 expr2
          | id                        -- identifier                      
          | integer                   -- integers: [-]{0-9}+                       
          | True                      -- booleans                        
          | False                                                        
          | [expr1,..,exprN]          -- list (N >= 0)                   
          | (expr1,expr2)             -- tuple                           
          | (expr)                    -- parenthesis                     
          | expr1 $ expr2             -- application operator            
          | expr1 : expr2             -- list constructor operator
          | rigid expr                -- experimental rigid keyword

   binder::= id arg1 .. argN = expr   -- let binding: N >= 0

   arg   ::= id                       -- identifier
          | (id :: annot)             -- annotated binder

   annot ::= some ids . type     
          |  type

   type  ::= forall ids . type        -- quantification
          |  type -> type             -- function type
          |  [type]                   -- list type
          |  (type,type)              -- tuple type
          |  (type)                   -- parenthesis
          |  id                       -- type variable
          |  Con                      -- type constructor (Int, Bool, etc)
-}
--------------------------------------------------------------------------
module Parser( readTerm, readType ) where

import Char
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language( haskellDef )

import Types 


--------------------------------------------------------------------------
-- To parse types, we translate bound type variables to identifiers
-- using a state in the parser
--------------------------------------------------------------------------
type Parse a   = CharParser St a
data St    = St { uniq :: Int, idMap :: [(Name,Id)] }


readTerm :: String -> IO Term
readTerm input
  = case runParser (wrap term) (St 0 []) "" input of
      Left err -> fail (show err)
      Right x  -> return x

readType :: String -> Type
readType input
  = case runParser (wrap ptype) (St 0 []) "" input of
      Left err -> error (show err)
      Right x  -> x



wrap :: Parse a -> Parse a
wrap p
  = do	whiteSpace
	x <- p
	eof
	return x

--------------------------------------------------------------------------
-- Parse terms 
--------------------------------------------------------------------------
 


term :: Parse Term
term
  = letTerm <|> lambdaTerm <|> ifTerm <|> annotation
  <?> "term"
  
letTerm
  = do reserved "let"
       binders <- semiSep letBinder
       reserved "in"
       t <- term
       return (foldr ($) t binders)

letBinder :: Parse (Term -> Term)
letBinder
  = do x <- identifier
       args <- many lambdaBinder
       reservedOp "="
       t <- term
       return (Let x (foldr ($) t args))

lambdaTerm
  = do reservedOp "\\"
       bs <- many1 lambdaBinder
       reservedOp "->"
       t  <- term
       return (foldr ($) t bs)

lambdaBinder :: Parse (Term -> Term)
lambdaBinder
  = do n <- identifier
       return (Lam n)
  <|>
    parens (do n <- identifier
               reservedOp "::"
               ann <- pannot
               return (ALam n ann)
           )


ifTerm
  = do reserved "if"
       t1 <- application
       reserved "then"
       t2 <- application
       reserved "else"
       t3 <- application
       return (App (App (App (Var "if") t1) t2) t3)



annotation :: Parse Term
annotation
  = do t <- longapply
       (do reservedOp "::"
           ann <- pannot
           return (Ann t ann)
        <|>
           return t
        )
  <?> "annotation"


longapply 
  = do t1 <- rigidTerm
       (do reservedOp "$"
           t2 <- term
           return (App (App (Var "$") t1) t2)
        <|>
        do reservedOp ":"
           t2 <- term
           return (App (App (Var ":") t1) t2)
        <|>
           return t1)

rigidTerm
  = do reserved "rigid"
       t <- atom
       return (Rigid t)
  <|>
    application
  
application :: Parse Term
application
  = do ts <- many1 atom
       return (foldl1 App ts)

atom :: Parse Term
atom
  = do symbol "("
       t1 <- term
       (do symbol ","
           t2 <- term
           symbol ")"
           return (App (App (Var "(,)") t1) t2)
        <|>
        do symbol ")"
           return t1
        )
  <|>
    do symbol "["
       ts <- commaSep term
       symbol "]"
       return (foldr (\x xs -> App (App (Var ":") x) xs) (Var "[]") ts)
  <|>
    do x <- identifier
       return (Var x)
  <|> 
    do i <- integer
       return (Lit (fromInteger i))
  <?> "expression"




--------------------------------------------------------------------------
-- Parse types 
--------------------------------------------------------------------------
pannot :: Parse Annot
pannot
  = do reserved "some"
       names <- many1 identifier
       withIds names $ \ids ->
        do reservedOp "."
           tp <- ptype
           return (mkAnnot ids tp)
  <|>
    do tp <- ptype
       return (mkAnnot [] tp)
 

ptype
  = do tp <- ptypeEx
       return (normalize tp)

ptypeEx
  = do reserved "forall"
       names <- many1 identifier
       withIds names $ \ids ->
         do reservedOp "."
            tp <- ptype
            return (mkForall ids tp)
  <|> 
    tpfun
  <?> "type"

tpfun
  = do t1 <- tpapp
       (do reservedOp "->"
           t2 <- tpfun
           return (mkFun t1 t2)
        <|>
        return t1
        )

tpapp
  = do tps <- many1 tpatom
       return (foldl1 TApp tps)

tpatom
  = do symbol "("
       tp1 <- ptype
       (do symbol ","
           tp2 <- ptype
           symbol ")"
           return (mkTuple tp1 tp2)
        <|>
        do symbol ")"
           return tp1
        )
  <|>
    do tp <- squares ptype
       return (mkList tp)
  <|>
    do name <- identifier
       if (isUpper (head name))
        then return (TCon name)
        else do id <- lookupId name
                return (TVar (TypeVar id Bound))
  <?> "simple type"
        

--------------------------------------------------------------------------
-- Unique id's for type variables 
--------------------------------------------------------------------------

lookupId :: Name -> Parse Id
lookupId name
  = do st <- getState
       case lookup name (idMap st) of
         Nothing -> fail ("unbound type variable: " ++ name)
         Just id -> return id

withIds :: [Name] -> ([Id] -> Parse a) -> Parse a
withIds names f
  = do st0 <- getState 
       ids <- mapM createId names
       x   <- f ids
       updateState (\st -> st{ idMap = idMap st0 })  -- restore the old idmap
       return x

createId :: Name -> Parse Id
createId name
  = do st <- getState
       let id = uniq st -1
       setState (st{ uniq = id, idMap =  (name,id) : idMap st})
       return id
       

--------------------------------------------------------------------------
-- lexer like Haskell 
--------------------------------------------------------------------------

langDef :: P.LanguageDef st
langDef = haskellDef {	P.reservedNames = ["let", "in", "forall", "some", "if", "then", "else", "rigid" ],
			P.reservedOpNames = ["::", "\\", ".", "->", "$", ":"] }

lexer       = P.makeTokenParser langDef
parens      = P.parens lexer
squares     = P.squares lexer
integer     = P.integer lexer
reservedOp  = P.reservedOp lexer
reserved    = P.reserved lexer
identifier  = P.identifier lexer
dot	    = P.dot lexer
whiteSpace  = P.whiteSpace lexer
lexeme      = P.whiteSpace lexer
symbol      = P.symbol lexer
commaSep    = P.commaSep lexer
semiSep     = P.semiSep lexer