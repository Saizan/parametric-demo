{-# OPTIONS --cubical --rewriting #-}
open import Primitives public
--open import Agda.Primitive public

module Church.FinalCoalgebrasCont where

open import TypeSystem public
open import Graph.Source public
open import Church.FibredBy public

--{-# BUILTIN REWRITE _≡_ #-}

--In this file, we prove the existence of final co-algebras for functors (module FinalOfFunctor)
--and indexed functors (module FinalOfIndexedFunctor).
--The Church encodings depend continuously on the algebra structure.

-----------------------------------

{-This module postulates its parameters, rather than getting parameters, because we need to add a rewrite rule.
  In order to make sure that modalities are enforced correctly, we add dummies with modalities id and #.
-}
module FinalOfFunctor (idDummy :{id} Set) (#Dummy :{#} Set) where

  postulate
    F :{#} ∀{ℓ} → Set ℓ → Set ℓ
    F' :{¶} ∀{ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} (f : A → B) → (F A → F B)
    rw-F-id : ∀{ℓ} {A :{#} Set ℓ} → F' (id{ℓ}{A}) ≡ id{ℓ}{F A}
    rw-F-hom : ∀{ℓA ℓB ℓC} {A :{#} Set ℓA} {B :{#} Set ℓB} {C :{#} Set ℓC} {f : A → B} {g : B → C} (fa :{#} F A)
         → F' g (F' f fa) ≡ F'(g ∘ f) fa

  {-# REWRITE rw-F-id #-}
  {-# REWRITE rw-F-hom #-}

  IsCoalg :{#} ∀{ℓ} → (A : Set ℓ) → Set ℓ
  IsCoalg A = A → F A

  IsMph :{#} ∀{ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (matchA : IsCoalg A) (matchB : IsCoalg B) (f : A → B) → Set (ℓA ⊔ ℓB)
  IsMph {ℓA}{ℓB}{A}{B} matchA matchB f = F' f ∘ matchA ≡ matchB ∘ f

  --final co-algebra
  Nu :{#} (ℓ : Level) → Set (lsuc ℓ)
  Nu ℓ = #Σ (Set ℓ) λ X → Σ (IsCoalg X) λ _ → X
  unfold : ∀{ℓ} {X :{#} Set ℓ} (matchX : IsCoalg X) → X → Nu ℓ
  unfold {ℓ}{X} matchX x = [# X , [ matchX , x ] ]
  matchNu : ∀{ℓ} → IsCoalg (Nu ℓ)
  matchNu {ℓ} n = #split n (λ _ → F (Nu ℓ)) (
    λ X matchX,X → split matchX,X (λ _ → F (Nu ℓ)) (
    λ matchX x → F' (unfold matchX) (matchX x)
    ))
  munfold : ∀{ℓ} {X :{#} Set ℓ} (matchX : IsCoalg X) → IsMph matchX matchNu (unfold matchX)
  munfold {ℓ}{X} matchX = refl _


  module NaturalityProven {ℓ :{¶} Level} where
    postulate
      A B :{#} Set ℓ
      matchA : IsCoalg A
      matchB : IsCoalg B
      f :{¶} A → B
      rw-mf : ∀{a : A} → F' f (matchA a) ≡ matchB (f a)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph matchA matchB f
    mf = refl _

    /f/ :{#} (i : 𝕀) → Set ℓ
    /f/ = / f /

    match/f/ : (i :{#} 𝕀) → IsCoalg (/f/ i)
    match/f/ i q = mweld {φ = (i ≣ i0) ∨ (i ≣ i1)} {C = λ _ → F (/f/ i)}
                          (λ a → F' (push f i) (matchA a))
                          (λ { ((i ≣ i0) = p⊤) → matchA
                             ; ((i ≣ i1) = p⊤) → matchB
                             })
                          q

    mpush : (i :{#} 𝕀) → IsMph matchA (match/f/ i) (push f i)
    mpush i = refl _

    naturality-path : (i :{#} 𝕀) → A → Nu ℓ
    naturality-path i = unfold (match/f/ i) ∘ push f i

    naturality :{¶} unfold matchA ≡ unfold matchB ∘ f
    naturality = path-to-eq naturality-path

  module Naturality {ℓ :{¶} Level}
      {A B :{#} Set ℓ}
      (matchA : IsCoalg A)
      (matchB : IsCoalg B)
      (f :{¶} A → B)
      (rw-mf : ∀{a : A} → F' f (matchA a) ≡ matchB (f a))
    where
    postulate
      naturality :{¶} unfold matchA ≡ unfold matchB ∘ f

  upunfold : ∀{ℓ} → Nu ℓ → Nu (lsuc ℓ)
  upunfold = unfold matchNu
  mupunfold : ∀{ℓ} → IsMph matchNu matchNu (upunfold {ℓ})
  mupunfold = refl _

  matchLift : ∀{ℓ} {A :{#} Set ℓ} → IsCoalg A → IsCoalg (Lift A)
  matchLift matchA = F' lift ∘ matchA ∘ lower

  mlift : ∀{ℓ} {A :{#} Set ℓ} (matchA :{#} IsCoalg A) → IsMph matchA (matchLift matchA) lift
  mlift matchA = refl _

  mlower : ∀{ℓ} {A :{#} Set ℓ} (matchA :{#} IsCoalg A) → IsMph (matchLift matchA) matchA lower
  mlower matchA = refl _

  match[_fibred-over_by_] : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} (matchX : IsCoalg X) (matchY : IsCoalg Y) {g : X → Y}
    (mg : IsMph matchX matchY g) → IsCoalg (X fibred-by g)

  match[_fibred-over_by_] {ℓX}{ℓY}{X}{Y} matchX matchY {g} mg p = {!!}
{-
  module LiftingLemma where
    module Core {ℓ :{¶} Level} {X :{#} Set ℓ} (matchX :{¶} IsCoalg X) where
      unfoldlower : Lift X → Nu ℓ
      unfoldlower = unfold matchX ∘ lower

      open Naturality {lsuc ℓ} (matchLift matchX) matchNu unfoldlower (refl _)
      
      naturality' :{¶} (λ liftx → [# Lift X , [¶ matchLift matchX , liftx ] ])
             ≡ (λ liftx → [# Nu ℓ , [¶ matchNu , [# X , [¶ matchX , lower liftx ] ] ] ])
      naturality' = naturality
    open Core

    --Note that Lift is the coercion into the next universe,
    --while lift and matchLift are the identity in ParamDTT
    liftNu : ∀{ℓ} → Nu ℓ → Nu (lsuc ℓ)
    liftNu {ℓ} n = #split n (λ _ → _) (
      λ X matchX,x → ¶split matchX,x (λ _ → _) (
      λ matchX x → [# Lift X , [¶ matchLift matchX , lift x ] ]
      ))
    mliftNu :{¶} ∀{ℓ} → IsMph matchNu matchNu (liftNu {ℓ})
    mliftNu {ℓ} = funext λ n → #split n (λ n' → (F' liftNu ∘ matchNu) n' ≡ (matchNu ∘ liftNu) n') (
      λ X matchX,x → ¶split matchX,x
          (λ matchX,x' → (F' liftNu ∘ matchNu) [# X , matchX,x' ] ≡ (matchNu ∘ liftNu) [# X , matchX,x' ]) (
      λ matchX x → refl _
      ))

    lifting-lemma :{¶} ∀{ℓ} → unfold matchNu ≡ liftNu {ℓ}
    lifting-lemma = funext (λ n → #split n (λ n' → unfold matchNu n' ≡ liftNu n') (
      λ X matchX,x → ¶split matchX,x (λ matchX,x' → unfold matchNu [# X , matchX,x' ] ≡ liftNu [# X , matchX,x' ]) (
      λ matchX x → sym (cong-app (naturality' matchX) (lift x))
      )))
  open LiftingLemma using (liftNu ; mliftNu ; lifting-lemma)

  module FinalityProven {ℓ :{¶} Level} where
    postulate
      A :{#} Set (lsuc ℓ)
      matchA :{¶} IsCoalg A
      f :{¶} A → Nu ℓ
      rw-mf : ∀{a : A} → F' f (matchA a) ≡ matchNu (f a)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph matchA matchNu f
    mf = refl _

    open Naturality {lsuc ℓ} matchA matchNu f (refl _)
    naturality' :{¶} unfold matchA ≡ unfold matchNu ∘ f
    naturality' = naturality

    finality :{¶} unfold matchA ≡ liftNu ∘ f
    finality = J lifting-lemma (λ liftNu' _ → unfold matchA ≡ liftNu' ∘ f) naturality'
-}
