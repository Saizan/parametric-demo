{-# OPTIONS --rewriting --cubical #-}
open import Primitives
open import TypeSystem

--import an implementation of the Graph type former
open import Graph.Source

module IntroExample (f : (X :{#} Set) → X → X) (X :{#} Set) (x :{¶} X) where

  const-x :{¶} ⊤ → X
  const-x _ = x

  --a bridge from ⊤ to X
  R :{#} 𝕀 → Set
  R = / const-x /

  --a path from tt to x
  r : (i :{#} 𝕀) → R i
  r i = push const-x i tt

  --a path from (f ⊤ tt) to (f X x)
  fr : (i :{#} 𝕀) → R i
  fr i = f (R i) (r i)

  --a path from x to (f X x)
  p : (i :{#} 𝕀) → X
  p i = pull const-x i (fr i)

  --apply the degeneracy axiom
  e : x ≡ f X x
  e = path-to-eq p
