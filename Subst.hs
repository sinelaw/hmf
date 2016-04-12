--------------------------------------------------------------------------
-- Operations on type variables
--
-- HasTypeVar, ftv, substitution (|->)
-- Subititutions (Sub), Type variables (Tvs), 
--------------------------------------------------------------------------

module Subst( 
              -- * Substitution
                Sub
              , subNew, subEmpty, subIsEmpty
              , subRemove, subLookup
              ) where

import Types
import qualified Data.IntMap as M



--------------------------------------------------------------------------
-- A substitution is an idempotent mapping from type variables to types
--------------------------------------------------------------------------

-- | A substitution from type variables to types
newtype Sub = Sub (M.IntMap Type)

subEmpty
  = Sub (M.empty)

subIsEmpty (Sub s)
  = M.null s 

subSingle :: Id -> Type -> Sub
subSingle id tp
  = Sub (M.singleton id tp)

subNew ids tps
  = Sub (M.fromList (zip ids tps))

subLookup :: Sub -> TypeVar -> Maybe Type
subLookup (Sub s) tv
  = M.lookup (tvId tv) s

subRemove :: Sub -> [Id] -> Sub
subRemove (Sub s) ids
  = Sub (foldr M.delete s ids)


instance Show Sub where
  show (Sub s)  = show s


