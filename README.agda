{-# OPTIONS --cubical --rewriting #-}
module README where

{-
  agda/parametric is an extension of Agda for type-checking ParamDTT. It builds on agda/cubical.
  It is activated by using the option --cubical.
-}

{-
  Import TypeSystem to have some primitives of the type system available.
  See there for more information about its contents.
  (The author most familiar with the internals of Agda, has dared to make some use of Agda's native
  support for record and inductive types types.)
-}
open import TypeSystem

--Some important new features include:

--1) Functions can be annotated with a modality.
postulate
  fpointwise : (A :{¶} Set) → Set
  fcontinuous : (A : Set) → Set
  fparametric : (A :{#} Set) → Set
fcontinuous' : (A :{id} Set) → Set
fcontinuous' a = fcontinuous a
--Other modalities, not introduced in the paper, are supported for experimental reasons.

{-
  2) Constants can be annotated with a modality µ, making them live in context µ \ Γ

  It is instructive to have a look at the context in each of the four goals (A', A'', B', B'') below
-}
module Example (A :{#} Set) (B : Set) where
  --Does not typecheck:
  A' : Set
  A' = {!A!}

  --Does typecheck:
  A'' :{#} Set
  A'' = A

  --Does typecheck
  B' : Set
  B' = B

  --Does not typecheck
  B'' :{¶} Set
  B'' = {!B!}

{-
  3) We have an interval, denoted 𝕀, containing endpoints i0 and i1.
-}
--We just postulate two objects for the sake of the example.
postulate
  --The type ABridge is a bridge from ABridge i0 to ABridge i1 in the universe.
  ABridge : 𝕀 → Set
  {-
    The object aPath is a heterogeneous path from aPath i0 : ABridge i0 to aPath i1 : ABridge i1.
    The bridge ABridge is what gives meaning to this notion of 'heterogeneous path'.
  -}
  aPath : (i :{#} 𝕀) → ABridge i
{-
  The object aPathWeakenedToABridge is a heterogeneous bridge from
  aPathWeakenedToABridge i0 : ABridge i0 to aPathWeakenedToABridge i1 : ABridge i1.
  The bridge ABridge is what gives meaning to this notion of 'heterogeneous bridge'.
-}
aPathWeakenedToABridge : (i : 𝕀) → ABridge i
aPathWeakenedToABridge i = aPath i

{-
  4) We can define partial functions. Only equating to a constant will result in useful computational behaviour.
  The equality face predicate is formed using _≣_ (input: \===)
-}
coerce : ∀ (i : 𝕀) (a0 : ABridge b0) (a1 : ABridge b1) → PartialP ((i ≣ i0) ∨ (i ≣ i1)) (λ _ → ABridge i)
coerce i a0 a1 = λ {((i ≣ i0) = p⊤) → a0
                   ;((i ≣ i1) = p⊤) → a1
                   }
{-                   
  5) We have Glue and Weld.
  Examples of their usage can be found in Graph/Source.agda and Graph/Target.agda
-}


--OBSOLETE NOTATIONS
--At some points in the code, you may encounter obsolete notations.

--Before we had a modality syntax, parametric/pointwise functions were denoted using #Π and ¶Π

fpointwise2 : ¶Π Set (λ _ → Set)
fpointwise2 = fpointwise

fparametric2 : #Π Set (λ _ → Set)
fparametric2 = fparametric

--Implicit functions were denoted using h#Π and h¶Π (h for hidden)

fpointwiseh : h¶Π Set (λ _ → Set)
fpointwiseh {A} = fpointwise A

fparametrich : h#Π Set (λ _ → Set)
fparametrich {A} = fparametric A

--While the type system was still under development, we had a bridge interval 𝔹 and a path interval ℙ,
--with a function ι : 𝔹 → ℙ. Both intervals are now implemented as 𝕀, and ι is the identity. See:

open import Primitives
