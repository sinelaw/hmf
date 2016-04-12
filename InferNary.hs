--------------------------------------------------------------------------
-- Type inference
--
-- Optimized HMF type inference extended with "rigid" annotations where 
-- annotations on function bodies and arguments are taken literally and 
-- are not further instantiated. Also, the algorithm looks at all arguments
-- in an N-ary application to find a good instantiation. This means
-- that the order of arguments no longer matters, i.e., if "e1 e2" is well
-- types, than so is "apply e1 e2" and also "revapp e2 e1".
--
-- The algorithm is an optimized version of "InferRigid" where the 
-- generalizations and instantiations are minimized by passing the 
-- expected form of the result type (Generalized or Instantiated).
--------------------------------------------------------------------------
module InferNary( inferType, features ) where

import PPrint
import Types
import Operations   
import Unify        ( unify, subsume, matchfun, matchfunN )
import Gamma

features :: [Feature]
features = [SupportRigidAnnotations
           ,SupportNaryApplications] 

--------------------------------------------------------------------------
-- Infer the type of a term
--------------------------------------------------------------------------
inferType :: Term -> IO Type
inferType term
  = do uniqueReset
       infer Generalized gamma0 term


infer :: Expect -> Gamma -> Term -> Infer Type
infer expect gamma (Var name)
  = maybeInstantiate expect (gammaFind gamma name)

infer expect gamma (Lit i)
  = return (TCon "Int")

infer expect gamma (Let name expr body)
  = do tp  <- infer Generalized gamma expr
       infer expect (gammaExtend gamma name tp) body

infer expect gamma (Lam name expr)
  = do -- we can treat this as an annotated lambda expression: (\x -> e) => (\(x::some a. a) -> e)        
       infer expect gamma (ALam name annotAny expr)       

infer expect gamma (ALam name ann expr)
  = do (some,tp1) <- instantiateAnnot (gammaDepth gamma+1) ann    -- instantiate the "some" quantifiers
       tp2        <- infer Instantiated (gammaExtendLam gamma name tp1) expr
       -- check that we don't infer polytypes for arguments        
       ssome <- subst some
       check (all isTau ssome) ("Using unannoted parameter(s) polymorphically with type(s): " ++ show ssome)  
       -- generalize the result
       maybeGeneralize expect gamma (mkFun tp1 tp2)
      
infer expect gamma (App e1 e2)
  = do let (f,args) = collectArgs [e2] e1
       ftp <- infer Instantiated gamma f
       inferApp ftp args
  where      
    collectArgs args (App e1 e2) = collectArgs (e2:args) e1
    collectArgs args expr        = (expr, args)

    inferApp ftp args
      = do (tpars,res) <- matchfunN ftp (length args)  -- note: when a polymorphic result is returned, |tpars| < |args|
           subsumeInferN gamma (zip tpars args)        -- note: zip automatically drops any remaining args
           let argsLeft = drop (length tpars) args
           if (null argsLeft)
            then maybeInstantiateOrGeneralize expect gamma res
            else inferApp res argsLeft  -- happens with a function returning a polymorphic result

infer expect gamma (Ann expr ann)
  = do -- we can treat annotations just as applications to an annotated identity function: (e::s) => ((\(x::s).x) e)
       tp <- infer Generalized gamma (App (ALam "x" ann (Var "x")) expr)
       -- since we treat annotations as rigid, we need to instantiate the generalized result type back to the annotation again
       (_,atp) <- instantiateAnnot rankInf ann
       subsume atp tp
       subst atp    -- ignore the expected type

infer expect gamma (Rigid expr)
  = infer Generalized gamma expr


--------------------------------------------------------------------------
-- subsume and infer over N arguments at once
--------------------------------------------------------------------------
subsumeInferN :: Gamma -> [(Type,Term)] -> Infer ()
subsumeInferN gamma []
  = return ()
subsumeInferN gamma tps
  = do (tpar,arg,rest) <- pickArgument tps  -- pick a good parameter/argument pair
       targ   <- infer (if isSigma tpar then Generalized else Instantiated) gamma arg
       if isAnnot arg then unify tpar targ  -- do not instantiate rigid types
                      else subsume tpar targ
       subsumeInferN gamma rest       


--------------------------------------------------------------------------
-- Query a type
--------------------------------------------------------------------------

-- | Is this a monotype?  (Only works for types that have been substituted)
isTau (Forall _ _) = False
isTau (TApp t1 t2) = isTau t1 && isTau t2 
isTau _            = True

-- | Is this a polymorphic type?
isSigma (Forall _ _) = True
isSigma _            = False


--------------------------------------------------------------------------
-- The expected form of a type
--------------------------------------------------------------------------

-- | Expected type
data Expect = Instantiated  -- need an instantiated Rho type
            | Generalized   -- need a generalized Sigma type


-- | Instantiate if an Instantiated type was expected
maybeInstantiate :: Expect -> Type -> Infer Type
maybeInstantiate expect tp
  = case expect of
      Instantiated -> instantiate tp
      _            -> return tp

-- | Generalize if a Generalized type was expected
maybeGeneralize :: Expect -> Gamma -> Rho -> Infer Type
maybeGeneralize expect gamma rho
  = case expect of
      Generalized  -> generalize gamma rho
      _            -> return rho

-- | Instantiate or Generalize based on the exepected type
maybeInstantiateOrGeneralize :: Expect -> Gamma -> Type -> Infer Type
maybeInstantiateOrGeneralize expect gamma tp
  = case expect of
      Generalized   -> generalize gamma tp
      Instantiated  -> instantiate tp