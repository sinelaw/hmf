--------------------------------------------------------------------------
-- The type environment Gamma
--------------------------------------------------------------------------
module Gamma( Gamma
            , gamma0  -- the initial gamma
            , gammaFind
            , gammaExtend, gammaExtendLam
            , gammaCoDomain
            , gammaDepth
            ) where

import qualified Data.Map as Map
import Types
import Parser( readType )


--------------------------------------------------------------------------
-- initial gamma 
--------------------------------------------------------------------------
gamma0 :: Gamma
gamma0
  = gammaCreate
      -- builtin functions
      [("(,)", "forall a b. a -> b -> (a,b)")
      ,("[]",  "forall a. [a]")
      ,(":",   "forall a. a -> [a] -> [a]")
      ,("$",   "forall a b. (a -> b) -> a -> b")
      ,("if", "forall a. Bool -> a -> a -> a")
      
      -- standard functions
      ,("id", "forall a. a -> a")
      ,("apply", "forall a b. (a -> b) -> a -> b")
      ,("const", "forall a b. a -> b -> a")
      ,("choose", "forall a. a -> a -> a")
      ,("revapp", "forall a b. a -> (a -> b) -> b")
      ,("undefined", "forall a. a")
      
      -- booleans
      ,("True", "Bool")
      ,("False", "Bool")

      -- integers
      ,("plus", "Int -> Int -> Int")
      ,("lt", "Int -> Int -> Bool")
      ,("gt", "Int -> Int -> Bool")
      ,("inc", "Int -> Int")
      
      -- polymorphic functions
      ,("ids", "[forall a. a -> a]")
      ,("auto", "(forall a. a -> a) -> (forall a. a -> a)")
      ,("xauto", "forall a. (forall b. b -> b) -> a -> a")

      ,("takeAuto", "((forall a. a -> a) -> (forall a. a -> a)) -> (forall a. a -> a)")
      
      -- lists
      ,("single", "forall a. a -> [a]")
      ,("head", "forall a. [a] -> a")
      ,("tail", "forall a. [a] -> [a]")
      ,("map", "forall a b. (a -> b) -> [a] -> [b]")
      ,("length", "forall a. [a] -> Int")
      ,("null", "forall a. [a]-> Bool")

      -- tuples
      ,("fst", "forall a b. (a,b) -> a")
      ,("snd", "forall a b. (a,b) -> b")

      -- ST monad
      ,("runST", "forall a. (forall s. ST s a) -> a")
      ,("newRef", "forall a s. a -> ST s (Ref s a)")
      ,("returnST", "forall a s. a -> ST s a")
      ]
    

--------------------------------------------------------------------------
-- Gamma is a mapping from (term) variables to types 
--------------------------------------------------------------------------

-- | Gamma maps term variables to types
data Gamma  = Gamma Rank (Map.Map Name Type)


gammaCreate :: [(String,String)] -> Gamma
gammaCreate bindings
  = gammaFromList $ [(name,readType tp) | (name,tp) <- bindings]

gammaEmpty 
  = Gamma 0 Map.empty 

gammaFromList xs
  = Gamma 0 (Map.fromList xs)

gammaFind (Gamma d g) name
  = case Map.lookup name g of
      Nothing -> error ("unbound variable: " ++ name)
      Just tp -> tp

gammaExtend (Gamma d g) name tp
  = Gamma d (Map.insert name tp g)

gammaExtendLam (Gamma d g) name tp
  = Gamma (d+1) (Map.insert name tp g)

gammaDepth :: Gamma -> Rank
gammaDepth (Gamma d m)
  = d

instance Show Gamma where
  show (Gamma d g)  = show g


gammaCoDomain :: Gamma -> [Type]
gammaCoDomain (Gamma d g)
  = Map.elems g
