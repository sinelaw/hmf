
This is a small but complete implementation of the HMF type system
described in the paper "HMF: simple type inference for first-class polymorphism",
available at "http://research.microsoft.com/users/daan/pubs.html"

This implementation uses IO references to implement substitution instead of using
explicit substitutions. Also, it uses ranked unification type variables to implement
efficient generalization.

Just load the prototype in GHCi as:

  > ghci Main.hs

and from the GHCi prompt, run the tests:

  *Main> testAll
  ...

or check some expressions yourself:

  *Main> check "\\x -> x"
  expr: \x -> x
  type: forall a. a -> a

  *Main> check "auto"
  expr: auto
  type: forall a. (forall b. b -> b) -> a -> a

  *Main> check "apply auto id"
  expr: apply auto id
  type: forall a. a -> a

  *Main> check "map auto ids"
  expr: map auto ids
  type: forall a. [a -> a]

or get some more help:

  *Main> help
  ...

See the test-cases in "Main.hs" for many more examples, 
and "Gamma.hs" for the standard available functions.

There are three provided variants of HMF type inference that can be selected in Main.hs:
 InferBasic   : Basic HMF type inference 
 InferRigid   : HMF extended with rigid type annotations
 InferRigidOpt: Optimized HMF with rigid annotations with a minimal number generalizations.
 InferNary    : Optimized Rigid HMF with taking all arguments into account for N-ary applications
 InferNaryProp: Optimized Rigid N-ary HMF with full type annotation propagation

Have fun,
-- Daan Leijen.


Modules:
--------------------------------------------------------------------------------------------
PPrint.hs           Pretty printer library
Types.hs            Basic definitions of terms and types
Parser.hs           Basic parser for terms and types
Subst.hs            Substitutions
Gamma.hs            Type environment: also contains standard functions like "const", or "id"
Operations.hs       Basic type operations: instantiate, skolemize etc.
Unify.hs            Unification and matching algorithm

InferBasic.hs       Basic HMF type inference  <--- start with this to learn about HMF inference!!
InferRigid.hs       HMF type inference extended with rigid type annotations
InferRigidOpt.hs    Optimized version with rigid type annotations where generalizations are minimal
InferNary.hs        Optimized Rigid HMF taking all arguments into account for N-ary applications
InferNaryProp.hs    Optimized Rigid N-ary HMF with full type annotation propagation

Main.hs             Main module

