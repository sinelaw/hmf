--------------------------------------------------------------------------
-- Type inference
--
-- Basic type inference algorithm for Plain HMF as described in the paper,
-- extended with rigid type annotations.
--------------------------------------------------------------------------
module InferRigid( inferType, features ) where

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
       infer gamma0 term


infer :: Gamma -> Term -> Infer Type
infer gamma (Var name)
  = return (gammaFind gamma name)

infer gamma (Lit i)
  = return (TCon "Int")

infer gamma (Let name expr body)
  = do tp  <- infer gamma expr
       infer (gammaExtend gamma name tp) body

infer gamma (Lam name expr)
  = do -- we can treat this as an annotated lambda expression: (\x -> e) => (\(x::some a. a) -> e)        
       infer gamma (ALam name annotAny expr)       

infer gamma (ALam name ann expr)
  = do (some,tp1) <- instantiateAnnot (gammaDepth gamma+1) ann    -- instantiate the "some" quantifiers
       tp2        <- infer (gammaExtendLam gamma name tp1) expr
       itp2       <- if isAnnot expr then return tp2              -- annotated results are not instantiated
                                     else instantiate tp2   

       -- check that we don't infer polytypes for arguments        
       ssome <- subst some
       check (all isTau ssome) ("Using unannoted parameter(s) polymorphically with type(s): " ++ show ssome)  
       -- generalize the result
       generalize gamma (mkFun tp1 itp2)
      
infer gamma (App e1 e2)
  = do tp1       <- infer gamma e1
       (arg,res) <- matchfun tp1 
       tp2       <- infer gamma e2
       if isAnnot e2 then unify arg tp2     -- annotated arguments are not instantiated
                     else subsume arg tp2
       -- note: no need to check for escaping polymorphic types since we check for monotype for arguments in the Lam case
       generalize gamma res

infer gamma (Ann expr ann)
  = do -- we can treat annotations just as applications to an annotated identity function: (e::s) => ((\(x::s).x) e)
       tp <- infer gamma (App (ALam "x" ann (Var "x")) expr)
       -- since we treat annotations as rigid, we need to instantiate the generalized result type back to the annotation again
       (_,atp) <- instantiateAnnot rankInf ann
       subsume atp tp
       subst atp    -- ignore the expected type


infer gamma (Rigid expr)
  = infer gamma expr


-- | Is this a monotype?  (Only works for types that have been substituted)
isTau (Forall _ _) = False
isTau (TApp t1 t2) = isTau t1 && isTau t2
isTau _            = True
