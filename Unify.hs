--------------------------------------------------------------------------
--  Unification and matching
--------------------------------------------------------------------------
module Unify ( subsume
             , unify
             , matchfun
             , matchfunN             
             ) where

import Data.IORef
import PPrint
import Types
import Subst
import Operations


--------------------------------------------------------------------------
-- Function match
--------------------------------------------------------------------------
matchfun :: Type -> Infer (Type,Type)
matchfun tp
  = do rho <- instantiate tp
       case rho of
         TApp (TApp (TCon "->") arg) res
            -> do sarg <- subst arg
                  return (sarg,res)
         TVar (TypeVar _ (Uni ref rref))
            -> do mtp <- readIORef ref
                  case mtp of
                     Just tp  -> matchfun tp
                     Nothing  -> do rank <- readIORef rref
                                    arg <- freshTVar rank
                                    res <- freshTVar rank
                                    writeIORef ref (Just (mkFun arg res))
                                    return (arg,res)
         _ -> failure ("applying a non-function: " ++ show rho)

-- | Match an N-ary function
matchfunN :: Type -> Int -> Infer ([Type],Type)
matchfunN tp n
  = do (arg,res) <- matchfun tp
       collect [arg] res
  where
    collect args res    | length args < n
      = case res of
          TApp (TApp (TCon "->") targ) tres   -> collect (targ:args) tres
          TVar (TypeVar _ (Uni ref rref))     -> do mtp <- readIORef ref
                                                    case mtp of
                                                      Just tp  -> collect args tp
                                                      Nothing  -> return (reverse args,res)        
          Forall _ _  -> return (reverse args,res)
          _           -> failure ("n-ary function match failed: " ++ show (pretty (foldr1 mkFun (reverse (res:args)))))
    collect args res 
      = return (reverse args, res)


--------------------------------------------------------------------------
-- Subsumption
-- "subsume tp1 tp2" returns a substitution S, such that
-- we can instantiate tp2 to some type tp3 and S(tp1) = S(tp3)
--------------------------------------------------------------------------
subsume :: Type -> Type ->  Infer ()
subsume tp1 tp2 
   = do (sks,rho1) <- skolemize tp1
        rho2 <- instantiate tp2
        unify rho1 rho2
        -- check for escaping skolems
        sk1 <- freeSkolems tp1
        sk2 <- freeSkolems tp2
        check (sks `disjoint` (sk1 `union` sk2))  
              ("type is not polymorphic enough in subsume:\n type1: " ++ show tp1 ++ "\n type2: " ++ show tp2)
             

--------------------------------------------------------------------------
-- unification 
--------------------------------------------------------------------------
unify :: Type -> Type -> Infer ()
unify (TCon n1) (TCon n2)   | n1 == n2
  = return ()

unify (TVar v1) (TVar v2)   | v1 == v2
  = return ()

unify (TApp t1 t2) (TApp u1 u2) 
  = do unify t1 u1
       unify t2 u2

unify (TVar v1) t2    | isUni (tvFlavour v1)
  = unifyVar v1 t2

unify t1 (TVar v2)    | isUni (tvFlavour v2)
  = unifyVar v2 t1

-- this case assumes that types are in normal form
unify t1@(Forall ids1 r1) t2@(Forall ids2 r2)   | length ids1 == length ids2
  = do sks <- freshSkolems (length ids1)
       rho1 <- subNew ids1 (map TVar sks) |-> r1
       rho2 <- subNew ids2 (map TVar sks) |-> r2
       unify rho1 rho2
       -- check for escaping skolems
       sk1 <- freeSkolems t1
       sk2 <- freeSkolems t2
       check (sks `disjoint` (sk1 `union` sk2)) 
             ("type is not polymorphic enough in unify:\n type1: " ++ show (pretty t1) ++ "\n type2: " ++ show (pretty t2))                               

unify t1 t2
  = failure ("cannot unify types:\n type1: " ++ show (pretty t1) ++ "\n type2: " ++ show (pretty t2))


-- | Unify a variable
unifyVar tv@(TypeVar id1 (Uni ref1 rref1)) tp2
  = do mtp1 <- readIORef ref1
       case mtp1 of
         Just tp1 -> unify tp1 tp2
         Nothing  -> case tp2 of
                       TVar (TypeVar id2 (Uni ref2 rref2)) 
                          -> do mtp2 <- readIORef ref2
                                case mtp2 of
                                  Just tp3  -> unify (TVar tv) tp3    -- note: we can't shorten here since tv could be an element of tp3
                                  Nothing   -> do writeIORef ref1 (Just tp2)
                                                  -- adjust the lambda-rank of the unifiable variable
                                                  rank1 <- readIORef rref1
                                                  rank2 <- readIORef rref2
                                                  onlyIf (rank2 > rank1) (writeIORef rref2 rank1)
                       _  -> do tvs <- freeTvs tp2
                                check (not (tv `elem` tvs)) ("infinite type: " ++ show tv ++ " and " ++ show tp2)  -- occurs check
                                writeIORef ref1 (Just tp2)
                                -- adjust the lambda-rank of the unifiable variables in tp2
                                rank1 <- readIORef rref1
                                adjustRank rank1 tp2

-- | adjust the lambda-rank of the unifiable variables in a type 
adjustRank :: Rank -> Type -> IO ()
adjustRank rank tp
  = case tp of
      TVar (TypeVar id2 (Uni ref2 rref2))
                      -> do mtp <- readIORef ref2
                            case mtp of
                              Just tp -> adjustRank rank tp
                              Nothing -> do rank2 <- readIORef rref2
                                            onlyIf (rank2 > rank) (writeIORef rref2 rank)
      Forall ids rho  -> adjustRank rank rho
      TApp t1 t2      -> do adjustRank rank t1
                            adjustRank rank t2
      _               -> return ()
                                
                        
       


