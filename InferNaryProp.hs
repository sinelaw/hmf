--------------------------------------------------------------------------
-- Type inference
--
-- Optimized HMF type inference extended with "rigid" annotations where 
-- annotations on function bodies and arguments are taken literally and 
-- are not further instantiated. Also, the algorithm looks at all arguments
-- in an N-ary application to find a good instantiation. This means
-- that the order of arguments no longer matters, i.e., if "e1 e2" is well
-- types, than so is "apply e1 e2" and also "revapp e2 e1".
-- Finally, it propagates type annotations, and optionally types through 
-- applications and to arguments.
--
-- The algorithm is an optimized version of "InferRigid" where the 
-- generalizations and instantiations are minimized by passing the 
-- expected form of the result type (Generalized or Instantiated).
--------------------------------------------------------------------------
module InferNaryProp( inferType, features ) where

import PPrint
import Types
import Operations   
import Unify        ( unify, subsume, matchfun, matchfunN )
import Gamma

features :: [Feature]
features = [ SupportRigidAnnotations
           , SupportNaryApplications 
           , SupportPropagation        -- propagate types

           -- the following two are optional
           , SupportAppPropagation     -- (try to) propagate also through applications
           , SupportPropagateToArg     -- propagate also to arguments
           ]

--------------------------------------------------------------------------
-- Infer the type of a term
--------------------------------------------------------------------------
inferType :: Term -> IO Type
inferType term
  = do uniqueReset
       infer Nothing Generalized gamma0 term

-- | The "expect :: Expect" argument gives the expected form of the result type, Generalized or Instantiated
-- | The "propagated :: Maybe Type" argument gives the propagated type 
infer :: Maybe Type -> Expect -> Gamma -> Term -> Infer Type
infer propagated expect gamma (Var name)
  = maybeInstantiate expect (gammaFind gamma name)

infer propagated expect gamma (Lit i)
  = return (TCon "Int")

infer propagated expect gamma (Let name expr body)
  = do tp  <- infer Nothing Generalized gamma expr
       infer propagated expect (gammaExtend gamma name tp) body

infer propagated expect gamma (Lam name expr)
  = do -- we can treat this as an annotated lambda expression: (\x -> e) => (\(x::some a. a) -> e)        
       (propArg,_,_) <- propagateFun propagated
       case propArg of
         Nothing -> infer propagated expect gamma (ALam name annotAny expr)        -- annotAny == some a. a
         Just tp -> infer propagated expect gamma (ALam name (Annot [] tp) expr)

infer propagated expect gamma (ALam name ann expr)
  = do (_,propRes,expectRes) <- propagateFun propagated
       (some,tp1) <- instantiateAnnot (gammaDepth gamma+1) ann    -- instantiate the "some" quantifiers
       tp2        <- infer propRes expectRes (gammaExtendLam gamma name tp1) expr
       -- check that we don't infer polytypes for arguments        
       ssome <- subst some
       check (all isTau ssome) ("Using unannoted parameter(s) polymorphically with type(s): " ++ show ssome)  
       -- generalize the result
       maybeGeneralize expect gamma (mkFun tp1 tp2)
      
infer propagated expect gamma (App e1 e2)
  = do let (f,args) = collectArgs [e2] e1
       ftp <- infer Nothing Instantiated gamma f
       inferApp ftp args
  where      
    collectArgs args (App e1 e2) = collectArgs (e2:args) e1
    collectArgs args expr        = (expr, args)

    inferApp ftp args
      = do (tpars,res) <- matchfunN ftp (length args)  -- note: when a polymorphic result is returned, |tpars| < |args|
           propagateApp propagated res (length tpars == length args)
           subsumeInferN gamma (zip tpars args)        -- note: zip automatically drops any remaining args
           let argsLeft = drop (length tpars) args
           if (null argsLeft)
            then maybeInstantiateOrGeneralize expect gamma res
            else inferApp res argsLeft  -- happens with a function returning a polymorphic result

infer propagated expect gamma (Ann expr ann)
  = do -- we can treat annotations just as applications to an annotated identity function: (e::s) => ((\(x::s).x) e)
       -- but for type propagation we do it explicitly ourselves
       (_,atp) <- instantiateAnnot rankInf ann
       tp      <- infer (Just atp) (if isSigma atp then Generalized else Instantiated) gamma expr
       subsume atp tp
       subst atp    -- ignore the expected type

infer propagated expect gamma (Rigid expr)
  = infer propagated Generalized gamma expr


--------------------------------------------------------------------------
-- subsume and infer over N arguments at once
--------------------------------------------------------------------------
subsumeInferN :: Gamma -> [(Type,Term)] -> Infer ()
subsumeInferN gamma []
  = return ()
subsumeInferN gamma tps
  = do (tpar,arg,rest) <- pickArgument tps  -- pick a good parameter/argument pair
       targ   <- infer (if SupportPropagateToArg `elem` features then Just tpar else Nothing)
                       (if isSigma tpar then Generalized else Instantiated) gamma arg
       if isAnnot arg then unify tpar targ  -- do not instantiate rigid types
                      else subsume tpar targ
       subsumeInferN gamma rest       


------------------------------------------------------------------------------
-- propagate types   
------------------------------------------------------------------------------

-- | Try to match with a propagated result type
-- | note that we need to instantiate the propagated result type, for example: (returnST 1) :: forall s. ST s Int
propagateApp :: Maybe Type -> Type -> Bool -> Infer ()
propagateApp propagated restp fullyApplied 
  = do univar <- isUniVar restp       
       case propagated of
        Just prop  | fullyApplied && not univar && SupportAppPropagation `elem` features 
                   ->  do rho <- instantiate prop
                          subsume rho restp                          
        _          ->  return ()
  

-- | Try to match the propagated type with a function type, 
-- returning the propagated argument and result type, and the expected instantiation of the result
propagateFun :: Maybe Type -> Infer (Maybe Type, Maybe Type, Expect)
propagateFun propagated
  = case propagated of
      Nothing -> return (Nothing,Nothing,Instantiated)
      Just tp -> do rho <- instantiate tp
                    case splitFun rho of
                      Just (argTp,resTp) -> return (Just argTp, Just resTp,if isSigma resTp then Generalized else Instantiated)
                      Nothing            -> return (Nothing,Nothing,Instantiated)


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