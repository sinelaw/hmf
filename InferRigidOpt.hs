--------------------------------------------------------------------------
-- Type inference
--
-- Optimized HMF type inference extended with "rigid" annotations where 
-- annotations on function bodies and arguments are taken literally and 
-- are not further instantiated.
--
-- The algorithm is an optimized version of "InferRigid" where the 
-- generalizations and instantiations are minimized by passing the 
-- expected form of the result type (Generalized or Instantiated).
--------------------------------------------------------------------------
module InferRigidOpt( inferType, features ) where

import PPrint
import Types
import Operations   
import Unify        ( unify, subsume, matchfun )
import Gamma

features :: [Feature]
features = [SupportRigidAnnotations]  -- no special features

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
  = do tp1       <- infer Instantiated gamma e1
       (arg,res) <- matchfun tp1 
       tp2       <- infer (if isSigma arg then Generalized else Instantiated) gamma e2
       if isAnnot e2 then unify arg tp2     -- annotated arguments are not instantiated
                     else subsume arg tp2
       -- note: no need to check for escaping polymorphic types since we check for monotype for arguments in the Lam case
       maybeInstantiateOrGeneralize expect gamma res

infer expect gamma (Ann expr ann)
  = do -- we can treat annotations just as applications to an annotated identity function: (e::s) => ((\(x::s).x) e)
       tp <- infer Generalized gamma (App (ALam "x" ann (Var "x")) expr)
       -- since we treat annotations as rigid, we need to instantiate the generalized result type back to the annotation again
       (_,atp) <- instantiateAnnot rankInf ann
       subsume atp tp
       subst atp    -- ignore the expected type


infer expect gamma (Rigid expr)
  = infer Generalized gamma expr


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