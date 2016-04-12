--------------------------------------------------------------------------
-- Basic definition of types and terms
--------------------------------------------------------------------------
module Types( 
            -- * Definitions
              Name, Id
            , Term(..)
            , Annot(..)
            , Type(..), Rho, Tau

            -- * Terms
            , isAnnot

            -- * Type variables
            , TypeVar(..), Flavour(..)
            , tvId, tvIds, tvFlavour
            , isUni, isBound, isSkolem
            , Rank, rankInf
            , ground, isUniVar
            
            -- * Type operations
            , normalize
            , mkForall, mkAnnot, mkFun, mkTuple, mkList
            , annotAny
            , splitFun
            
            -- * misc
            , union, disjoint, intersect, diff, subseteq
            , assert, assertM

            -- * Features
            , Feature(..)

            ) where

import List( partition )
import PPrint
import Data.IORef( IORef, readIORef )
import System.IO.Unsafe( unsafePerformIO )
--------------------------------------------------------------------------
-- Type inference features
--------------------------------------------------------------------------
data Feature  = SupportRigidAnnotations     -- do not instantiate or generalize type annotations
              | SupportNaryApplications     -- take all arguments into account when doing type inference
              | SupportPropagation          -- propagate types through lambda expressions and let-bindings
              | SupportAppPropagation       -- try to propagate types through applications
              | SupportPropagateToArg       -- propagate parameter types to argument expressions
              deriving Eq


--------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------
type Name = String      

data Term = Var Name              -- x
          | Lit Int               -- 3
          | App Term Term         -- f x
          | Lam Name Term         -- \x -> x
          | ALam Name Annot Term  -- \(x::Int) -> x
          | Let Name Term Term    -- let x = f y in x+1
          | Ann Term Annot        -- (f x) :: Int
          | Rigid Term            -- experimental: rigid x  (do not instantiate/generalize the type of "x")


-- | is an expression annotated?
isAnnot :: Term -> Bool
isAnnot (Rigid expr)          = True
isAnnot (Ann expr ann)        = True
isAnnot (Let name expr body)  = isAnnot body
isAnnot _                     = False


--------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------

type Rho   = Type   -- No outer ForAll
type Tau   = Type   -- No ForAlls anywhere
type Id    = Int    -- Identifiers

-- | Type annotations: "some a. type". A type annotation is closed under "some" type variables
data Annot = Annot [Id] Type    

-- | Types
data Type  = Forall [Id] Rho    -- ^ "forall a1 ... an. rho"
           | TVar TypeVar       -- ^ "a"
           | TCon Name          -- ^ "Int"    
           | TApp Type Type     -- ^ "Maybe Int"


-- | Type variables represent substitutable parts of a type, only |Free| variables can be unified
data TypeVar = TypeVar Id Flavour

-- | A type variable comes in three flavours: bound, as a skolem constant, and unifiable variables
data Flavour = Bound 
             | Skolem 
             | Uni (IORef (Maybe Type)) (IORef Rank)  -- the updateable reference implements substitution

-- | The type variable rank is used for efficient generalization
-- | The rank corresponds with the depth of the earliest lamda binding that refers to
-- | this type variable. The depth of the outermost lambda binding in the environment is 0.
-- | We use an infinite rank (rankInf) for type variables that do not occur in the environment.
-- See: George Kuan and David McQueen, "Efficient ML type inference with ranked type variables"
type Rank = Int

-- | The 'infinite' rank is used for variables that do not occur in the environment 
rankInf :: Rank
rankInf = maxBound

-- Accessors
tvFlavour (TypeVar _ fl) = fl
tvId      (TypeVar id _) = id
tvIds typeVars  = map tvId typeVars

isBound Bound = True
isBound _     = False

isUni (Uni _ _) = True
isUni _         = False

isSkolem Skolem = True
isSkolem _      = False


splitFun :: Type -> Maybe (Type,Type)
splitFun tp
  = case tp of
      TApp (TApp (TCon "->") arg) res  
        -> Just (arg,res)
      _ -> Nothing



ground :: Type -> IO Type
ground tp@(TVar (TypeVar _ (Uni ref _)))
  = do mtp <- readIORef ref
       case mtp of
         Nothing -> return tp
         Just t  -> ground t
ground tp
  = return tp


isUniVar :: Type -> IO Bool
isUniVar tp
  = do t <- ground tp
       case t of
         TVar (TypeVar _ (Uni _ _)) 
            -> return True
         _  -> return False

--------------------------------------------------------------------------
-- Helper functions 
--------------------------------------------------------------------------

mkForall :: [Id] -> Type -> Type
mkForall [] tp
  = tp
mkForall ids tp
  = case tp of
      Forall ids2 tp2  -> mkForall (ids ++ ids2) tp2
      _                -> Forall ids tp

mkAnnot :: [Id] -> Type -> Annot
mkAnnot ids tp
  = Annot ids tp

mkFun :: Type -> Type -> Type
mkFun t1 t2
  = TApp (TApp (TCon "->") t1) t2

mkTuple :: Type -> Type -> Type
mkTuple t1 t2
  = TApp (TApp (TCon "(,)") t1) t2

mkList :: Type -> Type
mkList tp
  = TApp (TCon "[]") tp

-- | the "any type" annotation: (some a. a) 
annotAny :: Annot
annotAny
  = let id = 0 in Annot [id] (TVar (TypeVar id Bound))

--------------------------------------------------------------------------
-- Free type variables and normalization
--------------------------------------------------------------------------

-- | Normalize a type such that quantifiers are ordered with respect to the occurence in the type.
normalize :: Type -> Type
normalize tp
  = snd (normalizeFtv tp)
  where
    normalizeFtv tp
      = case tp of
          Forall ids tp -> case tp of 
                             Forall ids2 tp2 -> normalizeFtv (Forall (ids++ids2) tp2)
                             _               -> let (oftv,ntp) = normalizeFtv tp
                                                    (bound,unbound) = partition (\tv -> tvId tv `elem` ids) oftv
                                                in (unbound, Forall [tvId tv | tv <- bound] ntp)
          TApp t1 t2    -> let (oftv1,nt1) = normalizeFtv t1
                               (oftv2,nt2) = normalizeFtv t2
                           in (oftv1 `union` oftv2, TApp nt1 nt2)
          TVar tv       -> ([tv],tp)
          TCon con      -> ([],tp)


--------------------------------------------------------------------------
-- Order preservering set operations on lists
--------------------------------------------------------------------------
union :: Eq a => [a] -> [a] -> [a]
union xs ys
  = xs ++ (ys `diff` xs)

diff :: Eq a => [a] -> [a] -> [a]
diff xs ys
  = [x | x <- xs, not (x `elem` ys)]

intersect :: Eq a => [a] -> [a] -> [a]
intersect xs ys
  = [x | x <- xs, x `elem` ys]

disjoint :: Eq a => [a] -> [a] -> Bool
disjoint xs ys
  = all (\x -> not (x `elem` ys)) xs

subseteq :: Eq a => [a] -> [a] -> Bool
subseteq xs ys
  = all (`elem` ys) xs

--------------------------------------------------------------------------
-- Assertions
--------------------------------------------------------------------------
assert :: String -> Bool -> a -> a
assert msg test x
  = if test then x else error ("assertion failed: " ++ msg)


assertM :: Monad m => String -> Bool -> m ()
assertM msg test
  = assert msg test (return ())

--------------------------------------------------------------------------
-- Equality for type variables is based solely on the identifier
--------------------------------------------------------------------------
instance Eq TypeVar where
  (TypeVar id1 fl1) == (TypeVar id2 fl2)  = (id1 == id2)

instance Ord TypeVar where
  compare (TypeVar id1 fl1) (TypeVar id2 fl2)  = compare id1 id2



--------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------

instance Pretty Term where
  pretty term = ppTerm PrecTop term

instance Pretty Type where
   pretty tp  = ppTypeEx [] PrecTop tp

instance Pretty Annot where
   pretty ann = ppAnnot ann

instance Pretty TypeVar where
   pretty (TypeVar id Bound)     = text "@" <> pretty id
   pretty (TypeVar id Skolem)    = text "_" <> pretty id
   pretty (TypeVar id (Uni _ _)) = text "$" <> pretty id

instance Show Term where
  show t = show (pretty t)

instance Show Type where
  show t = show (pretty t)

instance Show TypeVar where
  show t = show (pretty t)

instance Show Annot where
  show ann = show (pretty ann)


--------------------------------------------------------------------------
-- Precedence
--------------------------------------------------------------------------
data Prec = PrecTop | PrecAnn | PrecFun | PrecOp | PrecApp | PrecAtom
          deriving (Eq,Ord,Enum)

precType :: Type -> Prec
precType tp
  = case tp of
      Forall _ _                       -> PrecTop
      TApp (TApp (TCon "->") arg) res  -> PrecFun
      TApp (TCon "[]") arg             -> PrecAtom
      TApp _ _                         -> PrecApp
      _                                -> PrecAtom

precTerm :: Term -> Prec
precTerm term
  = case term of
      App (Var "[]") _             -> PrecAtom                      
      App (App (Var "(,)") e1) e2  -> PrecAtom
      App (App (Var "$") e1) e2    -> PrecOp
      App (App (Var ":") e1) e2    -> case elements [e1] e2 of 
                                        Nothing -> PrecOp
                                        Just _  -> PrecAtom

      Let _ _ _     -> PrecTop
      Ann _ _       -> PrecAnn
      Lam _ _       -> PrecFun
      ALam _ _ _    -> PrecFun
      App _ _       -> PrecApp
      Rigid  _      -> PrecFun
      _             -> PrecAtom


--------------------------------------------------------------------------
-- pretty term
--------------------------------------------------------------------------
ppTerm :: Prec -> Term -> Doc
ppTerm prec term
  = (if (prec > precTerm term) then parens else id)
    (ppTermEx prec term)

ppTermEx :: Prec -> Term -> Doc
ppTermEx prec term
  = case term of
      App (App (App (Var "if") t1) t2) t3   -> hang 2 $ text "if" <+> ppTerm PrecApp t1 </> text "then" <+> ppTerm PrecApp t2 </> text "else" <+> ppTerm PrecApp t3
      App (App (Var "(,)") e1) e2           -> parens (ppTerm PrecTop e1 <> comma <> ppTerm PrecTop e2)
      App (App (Var "$") e1) e2             -> ppTerm PrecApp e1 <+> text "$" <+> ppTerm PrecTop e2
      App (App (Var ":") e1) e2             -> case elements [e1] e2 of 
                                                 Nothing -> ppTerm PrecApp e1 <> text ":" <> ppTerm PrecOp e2
                                                 Just es -> list (map (ppTerm PrecTop) es)
    
      App e1 e2      -> ppTerm PrecApp e1 <+> ppTerm PrecAtom e2
      Lam v e        -> char '\\' <> ppLam "->" term 
      ALam v ann e   -> char '\\' <> ppLam "->" term
      Let v rhs e    -> let (bs,body) = binders [(v,rhs)] e
                        in align $ text "let" <+> align (vcat (punctuate semi [text v <+> ppLam "=" rhs | (v,rhs) <- bs])) 
                                   <> (if (length bs > 1) then line else softline)
                                   <> text "in" <+> ppTerm PrecTop body
      Ann e ann      -> ppTerm PrecAtom e <+> text "::" <+> pretty ann
      Rigid e        -> text "rigid" <+> ppTerm PrecTop e
      Var n          -> text n
      Lit i          -> pretty i
  where
    binders acc (Let v rhs e)   = binders ((v,rhs):acc) e
    binders acc e               = (reverse acc, e)

    ppLam arrow (Lam v e)         = text v <+> ppLam arrow e
    ppLam arrow (ALam v ann e)    = parens (text v <> text "::" <> pretty ann) <+> ppLam arrow e
    ppLam arrow e                 = text arrow <+> ppTerm PrecFun e

elements acc (Var "[]")                 = Just (reverse acc)
elements acc (App (App (Var ":") e) es) = elements (e:acc) es
elements acc _                          = Nothing

--------------------------------------------------------------------------
-- Pretty type
--------------------------------------------------------------------------
ppAnnot (Annot ids tp)
  = let nice = niceExtend [] ids
    in (if null ids then empty else (text "some" <+> hsep (map (ppNice nice) ids) <> text ". ")) <>
       ppType nice PrecTop tp
 


ppType :: [(Id,String)] -> Prec -> Type -> Doc
ppType nice prec tp
  = (if (prec > precType tp) then parens else id) (ppTypeEx nice prec tp)

ppTypeEx nice prec tp
  = case tp of
      Forall ids tau 
        -> let nice' = niceExtend nice ids
           in text "forall" <+> hsep (map (ppNice nice') ids) <> dot <+>
              ppType nice' PrecTop tau
      
      TApp (TApp (TCon "->") arg) res  -> ppType nice PrecApp arg <+> text "->" <+> ppType nice PrecFun res
      TApp (TCon "[]") arg             -> brackets (ppType nice PrecTop arg)
      TApp (TApp (TCon "(,)") t1) t2   -> parens (ppType nice PrecTop t1 <> text "," <> ppType nice PrecTop t2)
      TApp tp arg                      -> ppType nice PrecApp tp <+> ppType nice PrecAtom arg
      
      TVar (TypeVar id Bound)          -> ppNice nice id
      TVar (TypeVar id (Uni _ rref))   -> text "$" <> pretty id <> text "_" <> ppRank (unsafePerformIO (readIORef rref))
      TVar (TypeVar id Skolem)         -> text "_" <> pretty id

      TCon name                        -> text name

ppRank :: Rank -> Doc
ppRank r
  = if r == maxBound then text "inf" else pretty r

--------------------------------------------------------------------------
-- Pretty print bound identifiers nicely
--------------------------------------------------------------------------
ppNice nice id
  = case lookup id nice of
      Nothing     -> text ("@" ++ show id) -- this can happen due to updateable references :-( 
      Just name   -> text name

niceExtend :: [(Id,Name)] -> [Id] -> [(Id,Name)]
niceExtend nice ids
  = zip ids (drop (length nice) niceNames) ++ nice
 

niceNames :: [String]
niceNames 
  = [[c] | c <- ['a'..'z']] ++ [[c]++show i | i <- [1::Int ..], c <- ['a'..'z']]

