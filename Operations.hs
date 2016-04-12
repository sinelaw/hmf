--------------------------------------------------------------------------
--  Common operations on types
--------------------------------------------------------------------------
module Operations(                  
                 -- * Generalization, skolemization and instantiation
                   generalize
                 , skolemize
                 , instantiate
                 , instantiateAnnot
                 , pickArgument

                 -- * Creat fresh type variables
                 , freshSkolems, freshBounds, freshTVar
                 , uniqueReset
                 
                 -- * Inference
                 , Infer
                 , HasTypeVar
                 , freeTvs, freeSkolems, (|->), subst

                 -- * Helpers
                 , message
                 , check, failure
                 , onlyIf
                 ) where

import Debug.Trace( trace )
import Data.IORef( IORef, newIORef, modifyIORef, readIORef, writeIORef )
import System.IO.Unsafe( unsafePerformIO )
import Data.List( sort )
import PPrint
import Types
import Subst
import Gamma


--------------------------------------------------------------------------
-- Generalize
-- Uses efficient generalization by lambda-ranking unifiable variables. See:
-- See: George Kuan and David McQueen, "Efficient ML type inference with ranked type variables"
--------------------------------------------------------------------------
generalize :: Gamma -> Type -> Infer Type
generalize gamma tp
  = do tvsTp <- freeTvs tp
       let depth = gammaDepth gamma
       tvs   <- filterM (\(TypeVar _ (Uni _ rref)) -> do rank <- readIORef rref
                                                         return (rank > depth)) 
                        tvsTp
       assertGen tvsTp tvs -- assert that we generalize correctly
       bvs <- freshTypeVars Bound (length tvs)
       mapM_ (\(bound,(TypeVar _ (Uni ref _))) -> do Nothing <- readIORef ref -- just an assertion
                                                     writeIORef ref (Just (TVar bound))) 
             (zip bvs tvs)
       stp <- subst tp
       return (mkForall (map tvId bvs) stp)
  where
    assertGen tvsTp tvs
      = do -- assert that we generalize correctly
           tvsG  <- freeTvs (gammaCoDomain gamma)
           let tvsX = (tvsTp `diff` tvsG)
           if (sort tvs /= sort tvsX) 
            then failure ("different generalization:\n tvs:  " ++ show (sort tvs) ++ "\ntvsX: " ++ show (show tvsX))
            else return ()



filterM pred []
  = return []
filterM pred (x : xs)
  = do keep <- pred x
       xs'  <- filterM pred xs
       if keep then return (x:xs') else return xs'


--------------------------------------------------------------------------
-- Instantiation 
--------------------------------------------------------------------------

-- | Instantiate a type 
instantiate :: Type -> Infer Rho
instantiate tp
  = do t <- ground tp
       case t of
         Forall ids rho
             -> do tvs  <- freshTVars rankInf (length ids)
                   srho <- subNew ids tvs |-> rho
                   return srho   
         rho -> return rho
            
-- | Instantiate the the "some" quantifiers of an annotation to fresh type variables
instantiateAnnot :: Rank -> Annot -> Infer ([Type],Type)
instantiateAnnot rank (Annot [] tp)
  = return ([],tp)
instantiateAnnot rank (Annot ids tp)
  = do tvs <- freshTVars rank (length ids)
       stp <- subNew ids tvs |-> tp
       return (tvs,stp)


--------------------------------------------------------------------------
-- Skolemization
--------------------------------------------------------------------------
-- | Skolemize a quantified type and return the newly introduced skolem variables
skolemize :: Type -> Infer ([TypeVar],Rho)
skolemize tp
  = do t <- ground tp
       case t of
          Forall ids rho
            -> do sks  <- freshSkolems (length ids)
                  srho <- subNew ids (map TVar sks) |-> rho
                  -- message ("skolemize: " ++ show tp ++ " to " ++ show srho)
                  return (sks, srho)
          _ -> return ([],tp)


--------------------------------------------------------------------------
-- Pick a good argument
--------------------------------------------------------------------------

-- Pick an argument that can be subsumed unambigiously..
-- first we look for annotated arguments since their type is fully determined (and need no type propagation)
-- next, we look at parameters that are not a type variable since those are unambigiously determined (and benefit from type propagation)
-- and finally, we do the ones that are left over (the order of those does not matter since propagation does no longer help)
pickArgument :: [(Type,Term)] -> Infer (Type,Term,[(Type,Term)])
pickArgument tps
  = do ((tpar,arg),rest) <- pickAnnot [] tps
       stpar <- subst tpar
       return (stpar,arg,rest)
  where
    pickAnnot acc ts
      = case ts of
          (t@(tpar,arg):rest)  
              -> if (isAnnot arg)       -- an annoted argument
                  then return (t,reverse acc ++ rest)
                  else pickAnnot (t:acc) rest
          []  -> pickNonTVar [] tps     -- if there are no annotated arguments left, look for a non-typevar parameter          
    pickNonTVar acc ts
      = case ts of
          (t@(tpar,arg):rest)  
              -> do isuni <- isUniVar tpar
                    if (not isuni)      -- a parameter that is not a unifiable type variable
                     then return (t,reverse acc ++ rest)
                     else pickNonTVar (t:acc) rest
          []  -> return (head tps, tail tps)      -- if there are no good ones left, just take the first argument


--------------------------------------------------------------------------
-- Free type variables
--------------------------------------------------------------------------
freeSkolems :: HasTypeVar a => a  -> Infer [TypeVar]
freeSkolems tp
  = do tvs <- ftv tp
       return [tv | tv <- tvs, isSkolem (tvFlavour tv)]


-- | return the free unifiable variables of a type
freeTvs :: HasTypeVar a => a -> Infer [TypeVar]
freeTvs tp
  = do tvs <- ftv tp
       return [tv | tv <- tvs, isUni (tvFlavour tv)]


--------------------------------------------------------------------------
-- Type variables
--------------------------------------------------------------------------

-- | Things that have type variables 
class HasTypeVar a where
  -- | Return the free type variables
  ftv   :: a -> Infer [TypeVar]

  -- | Apply a substitution 
  (|->) :: Sub -> a -> Infer a

  -- | substitute the free reference type variables
  subst :: a -> Infer a



instance HasTypeVar a => HasTypeVar [a] where
  ftv xs
    = do tvss <- mapM ftv xs
         return (foldl union [] tvss)

  sub |-> xs
    = mapM (sub |->) xs

  subst xs
    = mapM subst xs

instance HasTypeVar Type where
  ftv tp
    = case tp of
        Forall ids rho    -> do tvs <- ftv rho
                                return (filter (\tv -> not (tvId tv `elem` ids)) tvs)
        TApp t1 t2        -> do tvs1 <- ftv t1
                                tvs2 <- ftv t2
                                return (tvs1 `union` tvs2)
        TVar tv           -> case tv of
                               TypeVar id (Uni ref _)  
                                  -> do mtp <- readIORef ref
                                        case mtp of
                                          Just tp -> ftv tp
                                          Nothing -> return [tv]
                               _  -> return [tv]
        TCon _            -> return []


  sub |-> tp
    = case tp of
        Forall ids rho    -> do srho <- subRemove sub ids |-> rho
                                return (Forall ids srho)
        TApp t1 t2        -> do st1 <- sub |-> t1
                                st2 <- sub |-> t2
                                return (TApp st1 st2)
        TCon name         -> return tp
        TVar tv           -> case tv of
                               TypeVar id (Uni ref _)  
                                  -> do mtp <- readIORef ref
                                        case mtp of
                                          Just tp -> sub |-> tp
                                          Nothing -> case subLookup sub tv of
                                                       Just newtp -> return newtp
                                                       Nothing    -> return tp
                               _  -> case subLookup sub tv of   -- replace even bound ones, useful for instantiation
                                       Just newtp -> return newtp
                                       Nothing    -> return tp


  subst tp
    = case tp of
        Forall ids rho  -> do srho <- subst rho
                              return (Forall ids srho)
        TApp tp1 tp2    -> do stp1 <- subst tp1
                              stp2 <- subst tp2
                              return (TApp stp1 stp2)
        TVar (TypeVar _ (Uni ref _))
                        -> do mtp <- readIORef ref
                              case mtp of
                                Nothing -> return tp
                                Just t  -> do ft <- subst t
                                              writeIORef ref (Just ft)
                                              return ft
        _               -> return tp



--------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------
check :: Bool -> String -> Infer ()
check pred msg
  = if pred then return () 
            else failure msg

failure :: String -> a
failure msg
  = error ("error: " ++ msg)

message :: String -> Infer ()
message msg
  = putStrLn msg

onlyIf :: Bool -> Infer () -> Infer ()
onlyIf pred inf
  = if pred then inf else return ()

--------------------------------------------------------------------------
-- Fresh type variables 
--------------------------------------------------------------------------
-- | return fresh skolem variables
freshSkolems :: Int -> Infer  [TypeVar]
freshSkolems
  = freshTypeVars Skolem

-- | return fresh bound variables
freshBounds :: Int -> Infer  [TypeVar]
freshBounds
  = freshTypeVars Bound

-- | return fresh unifiable types
freshTVars :: Rank -> Int -> Infer [Type]
freshTVars rank n
  = mapM (\_ -> freshTVar rank) [1..n]

-- | return a fresh unifiable type 
freshTVar :: Rank -> Infer Type
freshTVar rank
  = do ref  <- newIORef Nothing
       rref <- newIORef rank
       tv   <- freshTypeVar (Uni ref rref)
       return (TVar tv)

-- | return fresh type variables of a certain |Flavour|
freshTypeVars :: Flavour -> Int -> Infer  [TypeVar]
freshTypeVars fl n
  = mapM (\_ -> freshTypeVar fl) [1..n]

-- | return a fresh type variable
freshTypeVar :: Flavour -> Infer TypeVar
freshTypeVar fl
  = do id <- freshId
       return (TypeVar id fl)

-- | return a fresh identifier
freshId :: Infer Id
freshId 
  = do id <- unique
       return id


--------------------------------------------------------------------------
-- Infer
--------------------------------------------------------------------------
-- | The type inference monad, just IO for convenience
type Infer a  = IO a  


{-# NOINLINE uniqueInt #-}
uniqueInt :: IORef Int
uniqueInt = unsafePerformIO (newIORef 0)

-- | Quick and dirty unique numbers :-)
unique :: Infer Int
unique = do u <- readIORef uniqueInt
            writeIORef uniqueInt (u+1)
            return u

uniqueReset :: IO ()
uniqueReset
  = writeIORef uniqueInt 0