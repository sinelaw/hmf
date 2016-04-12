--------------------------------------------------------------------------
-- Main module:
--------------------------------------------------------------------------
module Main where

import qualified Control.Exception as Exn ( catch )
import PPrint
import Types ( Type, Feature(..) )
import Parser( readType, readTerm )


-- import InferBasic      -- import basic HMF type inference as described in the paper
-- import InferRigid      -- import HMF type inference with support for rigid annotations
-- import InferRigidOpt   -- import optimized HMF type inference with rigid annotations which minimizes generalizations
import InferNary          -- import optimized, with rigid annotations, and taking all arguments into account for N-ary applications
-- import InferNaryProp   -- import optimized, with rigid annotations, taking all arguments into account, and type annotation propagation

--------------------------------------------------------------------------
-- Main functions
--------------------------------------------------------------------------
check :: String -> IO ()
check input
  = do inference input
       putStrLn ""

testAll :: IO ()
testAll 
  = test testsAll

inference :: String -> IO Type       
inference input
  = do term <- readTerm input
       putPretty (text "expr:" <+> align (pretty term) <> linebreak)

       tp <- inferType term
       putPretty (text "type:" <+> align (pretty tp) <> linebreak)
       return tp

--------------------------------------------------------------------------
-- Help
----------------------------------------------------------------------------
main :: IO ()
main = help

help
  = putStrLn $ unlines 
  [ "Usage:"
  , " check \"\\\\x -> x\"     : type check an expression"
  , " testAll              : run all tests"
  , " test testsHM         : run the Hindley-Milner tests"
  , " test testsHR         : run the Higer-rank tests"
  , " test testsRigidAnn   : run the rigid annotations tests"
  , " test testsExists     : run the existential types tests"
  , " test testsPoly       : run the 'poly' keyword tests"
  ]

--------------------------------------------------------------------------
-- Tests 
--------------------------------------------------------------------------
testsAll :: [Test]
testsAll
  = concat 
    [ testsHM             -- Hindley Milner
    , testsHR             -- Higher rank & impredicative
    , testsNary           -- N-ary applications, order of arguments
    , testsExists         -- Encoding of existentials
    , if (SupportRigidAnnotations `elem` features) then testsRigidAnn else []  -- Rigid annotations
    , if (SupportPropagation `elem` features)      then testsProp     else []
    , if (SupportAppPropagation `elem` features)   then testsPropApp  else []
    , if (SupportPropagateToArg `elem` features)   then testsPropArg  else []
    -- , testsRigid         -- Experimental "rigid" keyword
    ]

testsHM
  = -- standard Hindley-Milner tests
    [("\\x -> x", ok "forall a. a -> a")
    ,("\\f x -> f x", ok "forall a b. (a -> b) -> a -> b")
    ,("inc True", Wrong)
    ,("let i = \\x -> x in i i", ok "forall a. a -> a")
    ,("\\i -> i i", Wrong)              -- infinite type
    ,("\\i -> (i 1, i True)", Wrong)    -- polymorphic use of parameter
    ,("single id", ok "forall a. [a -> a]")
    ,("choose (\\x y -> x) (\\x y -> y)", ok "forall a. a -> a -> a")
    ,("choose id", ok "forall a. (a -> a) -> (a -> a)")
    ]

testsHR
  = -- impredicative application and higher rank arguments are fully supported
    [("xauto",ok "forall a. (forall a. a -> a) -> a -> a")     -- just to show the types of xauto and auto
    ,("auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("\\(i :: forall a. a -> a) -> i i", ok "forall a. (forall a. a -> a) -> a -> a")
    ,("auto id", ok "forall a. a -> a")
    ,("apply auto id", ok "forall a. a -> a")
    ,("(single :: (forall a. a -> a) -> [forall a. a->a]) id", ok "[forall a. a-> a]")
    ,("runST (returnST 1)", ok "Int")
    ,("runST (newRef 1)", Wrong)
    ,("apply runST (returnST 1)", ok "Int")
    ,("map xauto ids", ok "forall a. [a -> a]")
    ,("map xauto (map xauto ids)", Wrong)
    ,("map auto ids", ok "[forall a. a -> a]")
    ,("map auto (map auto ids)", ok "[forall a. a -> a]")
    ,("head ids", ok "forall a. a -> a")
    ,("tail ids", ok "[forall a. a -> a]")
    ,("apply tail ids", ok "[forall a. a -> a]")
    ,("map head (single ids)", ok "[forall a. a -> a]")
    ,("apply (map head) (single ids)", ok "[forall a. a -> a]")

    -- check infinite poly types
    ,("(undefined :: some a. [a -> a] -> Int) (undefined :: some c. [(forall d. d -> c) -> c])", Wrong)
    ,("(undefined :: some a. [a -> a] -> Int) (undefined :: [(forall d. d -> d) -> (Int -> Int)])", Wrong)
    ,("(undefined :: some a. [a -> (forall b. b -> b)] -> Int) (undefined :: some c. [(forall d. d -> d) -> c])", ok "Int")

    -- these fail horribly in ghc: (choose auto id) is rejected while ((choose auto) id) is accepted -- so much for parenthesis :-)
    ,("choose id auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("choose auto id", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("choose xauto xauto", ok "forall a. (forall b. b -> b) -> a -> a")
    ,("choose id xauto", Wrong)
    ,("choose xauto id", Wrong)

    -- these fail too in ghc: (choose ids []) is accepted while (choose [] ids) is rejected
    ,("choose [] ids", ok "[forall a. a -> a]")
    ,("choose ids []", ok "[forall a. a -> a]")
    
    -- check escaping skolems
    ,("\\x -> auto x", Wrong)                                                                             -- escape in match
    ,("let poly (xs :: [forall a. a -> a]) = 1 in (\\x -> poly x)", Wrong)                              -- escape in apply
    ,("\\x -> (x :: [forall a. a -> a])", Wrong)                                                          -- escape in apply
    ,("\\x -> let polys (xs :: [forall a . a -> a]) = 1; f y = x in polys [f::some a. forall b. b -> a]",Wrong)  -- escape in unify (with rigid annotations, otherwise we get a skolem mismatch)
    ,("ids :: forall b. [forall a. a -> b]", Wrong)                                                       -- unify different skolems

    -- co/contra variance
    ,("let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g f", Wrong)                                      -- HMF is invariant
    ,("let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g (\\(x :: forall a. a -> a) -> f x)", ok "Int")  -- but we can always use explicit annotations to type such examples

    -- some
    ,("(\\x -> 1) :: some a. a -> a", ok "Int -> Int")
    ,("(\\x -> plus x 1) :: some a. a -> a", ok "Int -> Int")
    ]

testsExists
  = [-- simulating existential types
     ("let pack x f    = \\(open :: some b. forall a. (a,a -> Int) -> b) -> open (x,f); \
          \unpack ex f = ex f; \
          \existsB = pack True (\\b -> if b then 1 else 0); \
          \existsI = pack 1 id; \
          \exs     = [existsB,existsI]\   
      \in unpack (head exs) (\\ex -> (snd ex) (fst ex))"     
     ,ok "Int")
    ]

testsRigidAnn
  = -- test 'rigid' annotations, i.e. annotations are taken literally and do not instantiate or generalize
    [("single (id :: forall a. a -> a)", ok "[forall a. a -> a]")
    ,("(id :: forall a. a -> a) 1", ok "Int")   -- not all annotations are rigid
    ,("(id :: some a. a -> a) 1", ok "Int")
    ,("\\x -> ((\\y -> x) :: some a. forall b. b -> a)", ok "forall a. a -> (forall b. b -> a)")
    ,("\\(f :: forall a. a -> a) -> ((f f) :: forall a. a -> a)", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("revapp (id :: forall a. a -> a) auto", ok "forall a. a -> a")
    ,("choose inc id", ok "Int -> Int")
    ,("choose inc (id :: forall a. a -> a)", Wrong)
    ,("choose inc (id :: some a. a -> a)", ok "Int -> Int")
    ]

testsNary
  = -- tests n-ary applications
    [("revapp id auto", if SupportNaryApplications `elem` features then ok "forall a. a -> a" else Wrong)     -- revapp has a type of the form "a -> .." but with N-ary application this is unambigious
    ,("let f = revapp id in f auto", Wrong)   -- but the application must be apperent
    ,("let f = revapp (id :: forall a. a -> a) in f auto", if SupportRigidAnnotations `elem` features then ok "forall a. a -> a" else Wrong) -- this is ok with rigid annotations
     -- check functions that return polymorphic values
    ,("head ids 1", ok "Int")
    ,("auto id 1", ok "Int")
    ]
    

testsRigid
  = [-- Experimental: the "rigid" keyword prevents instantiation or generalization of the principal type of an expression
     -- this is perhaps more convenient than writing an annotation (but not more expressive)
     ("single (rigid id)", ok "[forall a. a -> a]")  
    ,("let pauto (f :: forall a. a -> a) = rigid f in map pauto ids", ok "[forall a. a -> a]")
    ,("let pauto (f :: forall a. a -> a) = rigid f in map pauto (map pauto ids)", ok "[forall a. a -> a]")
    ,("\\x -> rigid (\\y -> x)", ok "forall a. a -> (forall b. b -> a)")
    ,("\\x -> rigid (\\y -> const x y)", ok "forall a. a -> (forall b. b -> a)")
    ,("let c x = rigid (\\y -> x) in \\x y -> c x y", ok "forall a b. a -> b -> a")
    ,("choose plus (\\x -> id)", ok "Int -> Int -> Int")
    ,("choose plus (\\x -> rigid id)", Wrong)      
    ,("choose inc (rigid id)", Wrong)  
    ,("choose id", ok "forall a. (a -> a) -> (a -> a)")
    ,("choose (rigid id)", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("revapp (rigid id) auto", ok "forall a. a -> a")
    -- manipulate instantiation of each quantifier:
    ,("[const]", ok "forall a b. [a -> b -> a]")
    ,("[rigid const]", ok "[forall a b. a -> b -> a]")    
    ,("[const :: some a. forall b. a -> b -> a]", ok "forall a. [forall b. a -> b -> a]")
    ,("[const :: some b. forall a. a -> b -> a]", ok "forall b. [forall a. a -> b -> a]")
    ]

-- Type propagation tests
testsProp
  = [ -- test type propagation  (SupportPropagation `elem` features)
     ("(\\f -> f f) :: (forall a. a -> a) -> (forall a. a -> a)", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("(let x = 1 in (\\f -> (f x, f True))) :: (forall a. a -> a) -> (Int,Bool)", ok "(forall a. a -> a) -> (Int,Bool)")
    ]

testsPropApp
  = [-- test type propagation through applications (SupportAppPropagation `elem` features)
     ("single id :: [forall a. a -> a]", ok "[forall a. a -> a]")
    ,("returnST 1 :: forall s. ST s Int", ok "forall s. ST s Int")
    ,("auto id :: Int -> Int", ok "Int -> Int")
    ,("head ids 1 :: Int", ok "Int")
    ,("head ids :: Int -> Int", ok "Int -> Int")
    ]

testsPropArg
  = [-- test type propagation to arguments (SupportPropagateToArg `elem` features)
     ("takeAuto (\\f -> f f)", ok "forall a. a -> a")
    ,("[id]: [ids]", ok "[[forall a. a -> a]]")
    ,("([id] :: [forall a. a -> a]) : [[\\x -> x]]", ok "[[forall a. a -> a]]")
    ,("apply takeAuto (\\f -> f f)", ok "forall a. a -> a")
    ,("revapp (\\f -> f f) takeAuto", ok "forall a. a -> a")
    ,("apply (\\f -> choose auto f) (auto :: (forall a. a -> a) -> (forall a. a -> a))", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("revapp (auto :: (forall a. a -> a) -> (forall a. a -> a)) (\\f -> choose auto f)", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ]

-- this is *not* supported by HMF: inference of polymorphic types for arguments that are just passed around..
testsEtaPoly
  = -- in MLF arguments can have an inferred polymorphic type as long as it is not used (or revealed explicitly)
    [("\\x -> auto x", ok "forall a. (forall a. a -> a) -> a -> a")
    ,("\\x -> (auto x, x 1)", Wrong)
    ,("\\x -> (auto x, (x :: forall a. a -> a) 1)", ok "forall a. (forall a. a -> a) -> (a -> a, Int)")
    ,("\\x -> (auto x, (x :: Int -> Int) 1)", Wrong)
    ]

--------------------------------------------------------------------------
-- Test framework
--------------------------------------------------------------------------
type Test = (String,TestResult)
data TestResult  = Ok Type
                 | Wrong

ok :: String -> TestResult
ok stringType 
  = Ok (readType stringType)


test :: [Test] -> IO ()
test ts
  = do xs <- mapM test1 ts
       putStrLn ("\ntested: " ++ show (length ts))
       putStrLn ("failed: " ++ show (sum xs) ++ "\n")

test1 :: Test -> IO Int
test1 (input,Ok resultTp)
  = do tp <- inference input
       if (show tp == show resultTp) 
        then testOk ""
        else testFailed (": test was expected to have type: " ++ show resultTp)
    `Exn.catch` \err ->
      do putStrLn (show err)
         testFailed (": test should be accepted with type: " ++ show resultTp)
       
test1 (input, Wrong)
  = do inference input
       testFailed ": a type error was expected"
    `Exn.catch` \err ->
      do putStrLn (show err)
         testOk " (the input was justly rejected)"

testFailed msg
  = do putStrLn (header ++ "\ntest failed" ++ msg ++ "\n" ++ header ++ "\n")
       return 1
  where
    header = replicate 40 '*'

testOk msg
  = do putStrLn ("ok " ++ msg)
       putStrLn ""
       return 0















