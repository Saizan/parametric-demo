{-# OPTIONS --cubical --rewriting #-}
open import Primitives public
--open import Agda.Primitive public

module Church.FinalCoalgebras where

open import TypeSystem public
open import Graph.Source public

--{-# BUILTIN REWRITE _≡_ #-}

--In this file, we prove the existence of final co-algebras for functors (module FinalOfFunctor)
--and indexed functors (module FinalOfIndexedFunctor).
--The Church encodings depend pointwise on the algebra structure.

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
  Nu ℓ = #Σ (Set ℓ) λ X → ¶Σ (IsCoalg X) λ _ → X
  unfold : ∀{ℓ} {X :{#} Set ℓ} (matchX :{¶} IsCoalg X) → X → Nu ℓ
  unfold {ℓ}{X} matchX x = [# X , [¶ matchX , x ] ]
  matchNu : ∀{ℓ} → IsCoalg (Nu ℓ)
  matchNu {ℓ} n = #split n (λ _ → F (Nu ℓ)) (
    λ X matchX,X → ¶split matchX,X (λ _ → F (Nu ℓ)) (
    λ matchX x → F' (unfold matchX) (matchX x)
    ))
  munfold : ∀{ℓ} {X :{#} Set ℓ} (matchX :{¶} IsCoalg X) → IsMph matchX matchNu (unfold matchX)
  munfold {ℓ}{X} matchX = refl _

  module NaturalityProven {ℓ :{¶} Level} where
    postulate
      A B :{#} Set ℓ
      matchA :{¶} IsCoalg A
      matchB :{¶} IsCoalg B
      f :{¶} A → B
      rw-mf : ∀{a : A} → F' f (matchA a) ≡ matchB (f a)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph matchA matchB f
    mf = refl _

    /f/ :{#} (i : 𝕀) → Set ℓ
    /f/ = / f /

    match/f/ :{¶} (i :{#} 𝕀) → IsCoalg (/f/ i)
    match/f/ i q = mweld {φ = (i ≣ i0) ∨ (i ≣ i1)} {C = λ _ → F (/f/ i)}
                          (λ a → F' (push f i) (matchA a))
                          (λ { ((i ≣ i0) = p⊤) → matchA
                             ; ((i ≣ i1) = p⊤) → matchB
                             })
                          q

    mpush :{¶} (i :{#} 𝕀) → IsMph matchA (match/f/ i) (push f i)
    mpush i = refl _

    naturality-path : (i :{#} 𝕀) → A → Nu ℓ
    naturality-path i = unfold (match/f/ i) ∘ push f i

    naturality :{¶} unfold matchA ≡ unfold matchB ∘ f
    naturality = path-to-eq naturality-path

  module Naturality {ℓ :{¶} Level}
      {A B :{#} Set ℓ}
      (matchA :{¶} IsCoalg A)
      (matchB :{¶} IsCoalg B)
      (f :{¶} A → B)
      (rw-mf : ∀{a : A} → F' f (matchA a) ≡ matchB (f a))
    where
    postulate
      naturality :{¶} unfold matchA ≡ unfold matchB ∘ f

  upunfold : ∀{ℓ} → Nu ℓ → Nu (lsuc ℓ)
  upunfold = unfold matchNu
  mupunfold :{¶} ∀{ℓ} → IsMph matchNu matchNu (upunfold {ℓ})
  mupunfold = refl _

  matchLift : ∀{ℓ} {A :{#} Set ℓ} → IsCoalg A → IsCoalg (Lift A)
  matchLift matchA = F' lift ∘ matchA ∘ lower

  mlift :{¶} ∀{ℓ} {A :{#} Set ℓ} (matchA :{#} IsCoalg A) → IsMph matchA (matchLift matchA) lift
  mlift matchA = refl _

  mlower :{¶} ∀{ℓ} {A :{#} Set ℓ} (matchA :{#} IsCoalg A) → IsMph (matchLift matchA) matchA lower
  mlower matchA = refl _
  
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

------------------------------------------------------

{-This module postulates its parameters, rather than getting parameters, because we need to add a rewrite rule.
  In order to make sure that modalities are enforced correctly, we add dummies with modalities id and #.
-}
module FinalOfIndexedFunctor {ℓZ :{¶} Level} (Z :{#} Set ℓZ) (idDummy :{id} Set) (#Dummy :{#} Set) where

  ZSet :{#} (ℓ : Level) → Set (lsuc ℓ ⊔ ℓZ)
  ZSet ℓ = Z → Set ℓ

  _⇒_ :{#} ∀{ℓA ℓB} (A : ZSet ℓA) (B : ZSet ℓB) → Set (ℓB ⊔ ℓA ⊔ ℓZ)
  A ⇒ B = (z :{#} Z) → A z → B z

  z-id :{#} ∀{ℓ} {A : ZSet ℓ} → A ⇒ A
  z-id i = id
  _⊚_ :{#} ∀{ℓA ℓB ℓC} → {A :{#} ZSet ℓA} {B :{#} ZSet ℓB} {C :{#} ZSet ℓC} (g : B ⇒ C) (f : A ⇒ B) → A ⇒ C
  (g ⊚ f) = λ z → g z ∘ f z

  infixr 9 _⊚_

  postulate
    F :{#} ∀{ℓ} → (ZSet ℓ) → (ZSet ℓ)
    F' :{¶} ∀{ℓA ℓB} {A :{#} ZSet ℓA} {B :{#} ZSet ℓB} → (A ⇒ B) → (F A ⇒ F B)
    rw-F-id : ∀{ℓ} {A : ZSet ℓ} → F' (z-id{ℓ}{A}) ≡ z-id
    rw-F-hom : ∀{ℓA ℓB ℓC} {A : ZSet ℓA} {B : ZSet ℓB} {C : ZSet ℓC}
           {f : A ⇒ B} {g : B ⇒ C}
           (z : Z) → (fa : F A z) → F' g z (F' f z fa) ≡ F' (λ v → g v ∘ f v) z fa

  {-# REWRITE rw-F-id #-}
  {-# REWRITE rw-F-hom #-}
  
  IsCoalg :{#} ∀{ℓ} → (A : ZSet ℓ) → Set (ℓ ⊔ ℓZ)
  IsCoalg A = A ⇒ F A

  IsMph :{#} ∀{ℓA ℓB} {A : ZSet ℓA} {B : ZSet ℓB} (matchA : IsCoalg A) (matchB : IsCoalg B) (f : A ⇒ B) → Set (ℓA ⊔ ℓB ⊔ ℓZ)
  IsMph {ℓA}{ℓB}{A}{B} matchA matchB f = F' f ⊚ matchA ≡ matchB ⊚ f

  --final co-algebra
  Nu :{#} (ℓ : Level) → ZSet (lsuc ℓ ⊔ ℓZ)
  Nu ℓ z = #Σ (ZSet ℓ) λ X → ¶Σ (IsCoalg X) λ _ → X z
  unfold : ∀{ℓ} {X :{#} ZSet ℓ} (matchX :{¶} IsCoalg X) → X ⇒ Nu ℓ
  unfold {ℓ}{X} matchX z x = [# X , [¶ matchX , x ] ]
  matchNu : ∀{ℓ} → IsCoalg (Nu ℓ)
  matchNu {ℓ} z n = #split n (λ _ → F (Nu ℓ) z) (
    λ X matchX,X → ¶split matchX,X (λ _ → F (Nu ℓ) z) (
    λ matchX x → F' (unfold matchX) z (matchX z x)
    ))
  munfold : ∀{ℓ} {X :{#} ZSet ℓ} (matchX :{¶} IsCoalg X) → IsMph matchX matchNu (unfold matchX)
  munfold {ℓ}{X} matchX = refl _

  Z/_/ :{#} ∀{ℓ} {A B : ZSet ℓ} (f :{¶} A ⇒ B) → 𝕀 → ZSet ℓ
  Z/ f / i z = / f z / i
  zpush : ∀{ℓ} {A B :{#} ZSet ℓ} (f :{¶} A ⇒ B) → (i :{#} 𝕀) → A ⇒ Z/ f / i
  zpush f i z a = push (f z) i a
  zpull : ∀{ℓ} {A B :{#} ZSet ℓ} (f :{¶} A ⇒ B) → (i :{#} 𝕀) → Z/ f / i ⇒ B
  zpull f i z q = pull (f z) i q

  module NaturalityProven {ℓ :{¶} Level} where
    postulate
      A B :{#} ZSet ℓ
      matchA :{¶} IsCoalg A
      matchB :{¶} IsCoalg B
      f :{¶} A ⇒ B
      rw-mf : ∀{z}{a : A z} → F' f z (matchA z a) ≡ matchB z (f z a)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph matchA matchB f
    mf = refl _
    /f/ :{#} (i : 𝕀) → ZSet ℓ
    /f/ = Z/ f /
    match/f/ :{¶} (i :{#} 𝕀) → IsCoalg (/f/ i)
    match/f/ i z q = mweld {φ = (i ≣ i0) ∨ (i ≣ i1)} {C = λ _ → F (/f/ i) z}
                          (λ a → F' (zpush f i) z (matchA z a))
                          (λ { ((i ≣ i0) = p⊤) → matchA z
                             ; ((i ≣ i1) = p⊤) → matchB z
                             })
                          q

    mzpush :{¶} (i :{#} 𝕀) → IsMph matchA (match/f/ i) (zpush f i)
    mzpush i = refl _

    naturality-path : (i :{#} 𝕀) → A ⇒ Nu ℓ
    naturality-path i = unfold (match/f/ i) ⊚ zpush f i

    naturality :{¶} unfold matchA ≡ unfold matchB ⊚ f
    naturality = path-to-eq naturality-path

  module Naturality {ℓ :{¶} Level}
      {A B :{#} ZSet ℓ}
      (matchA :{¶} IsCoalg A)
      (matchB :{¶} IsCoalg B)
      (f :{¶} A ⇒ B)
      (rw-mf : ∀{z}{a : A z} → F' f z (matchA z a) ≡ matchB z (f z a))
    where
    postulate
      naturality :{¶} unfold matchA ≡ unfold matchB ⊚ f

  upunfold : ∀{ℓ} → Nu (ℓ ⊔ ℓZ) ⇒ Nu (lsuc (ℓ ⊔ ℓZ))
  upunfold = unfold matchNu
  mupunfold :{¶} ∀{ℓ} → IsMph matchNu matchNu (upunfold {ℓ ⊔ ℓZ})
  mupunfold = refl _

  ZLift : ∀{ℓ} → ZSet ℓ → ZSet (lsuc ℓ)
  ZLift A z = Lift (A z)
  zlift : ∀{ℓ} {A :{#} ZSet ℓ} → A ⇒ ZLift A
  zlift z a = lift a
  zlower : ∀{ℓ} {A :{#} ZSet ℓ} → ZLift A ⇒ A
  zlower z a = lower a

  matchLift : ∀{ℓ} {A :{#} ZSet ℓ} → IsCoalg A → IsCoalg (ZLift A)
  matchLift matchA = F' zlift ⊚ matchA ⊚ zlower
  
  mlift :{¶} ∀{ℓ} {A :{#} ZSet ℓ} (matchA :{#} IsCoalg A) → IsMph matchA (matchLift matchA) zlift
  mlift matchA = refl _

  mlower :{¶} ∀{ℓ} {A :{#} ZSet ℓ} (matchA :{#} IsCoalg A) → IsMph (matchLift matchA) matchA zlower
  mlower matchA = refl _
  
  module LiftingLemma where
    module Core {ℓ :{¶} Level} {X :{#} ZSet (ℓ ⊔ ℓZ)} (matchX :{¶} IsCoalg X) where
      unfoldlower : ZLift X ⇒ Nu (ℓ ⊔ ℓZ)
      unfoldlower = unfold matchX ⊚ zlower

      open Naturality {lsuc (ℓ ⊔ ℓZ)} (matchLift matchX) matchNu unfoldlower (refl _)

      naturality' :{¶} (λ z liftx → [# ZLift X , [¶ matchLift matchX , liftx ] ])
             ≡ (λ z liftx → [# Nu (ℓ ⊔ ℓZ) , [¶ matchNu , [# X , [¶ matchX , lower liftx ] ] ] ])
      naturality' = naturality
    open Core
    
    --Note that Lift is the coercion into the next universe,
    --while lift and matchLift are the identity in ParamDTT
    liftNu : ∀{ℓ} → Nu ℓ ⇒ Nu (lsuc ℓ)
    liftNu {ℓ} z n = #split n (λ _ → _) (
      λ X matchX,x → ¶split matchX,x (λ _ → _) (
      λ matchX x → [# ZLift X , [¶ matchLift matchX , lift x ] ]
      ))
    mliftNu :{¶} ∀{ℓ} → IsMph matchNu matchNu (liftNu {ℓ})
    mliftNu {ℓ} = #funext λ z → funext λ n → #split n (λ n' → (F' liftNu ⊚ matchNu) z n' ≡ (matchNu ⊚ liftNu) z n') (
      λ X matchX,x → ¶split matchX,x
          (λ matchX,x' → (F' liftNu ⊚ matchNu) z [# X , matchX,x' ] ≡ (matchNu ⊚ liftNu) z [# X , matchX,x' ]) (
      λ matchX x → refl _
      ))

    lifting-lemma :{¶} {ℓ :{¶} Level}  → unfold matchNu ≡ liftNu {ℓ ⊔ ℓZ}
    lifting-lemma {ℓ} = #funext λ z → funext λ n → #split n (λ n' → unfold matchNu z n' ≡ liftNu z n') (
      λ X matchX,x → ¶split matchX,x (λ matchX,x' → unfold matchNu z [# X , matchX,x' ] ≡ liftNu z [# X , matchX,x' ]) (
      λ matchX x → sym (cong-app (#cong-app (naturality' {ℓ}{X} matchX) z) (lift x))
      ))

  open LiftingLemma using (liftNu ; mliftNu ; lifting-lemma)
      
  module FinalityProven {ℓ :{¶} Level} where
    postulate
      A :{#} ZSet (lsuc (ℓ ⊔ ℓZ))
      matchA :{¶} IsCoalg A
      f :{¶} A ⇒ Nu (ℓ ⊔ ℓZ)
      rw-mf : ∀{z}{a : A z} → F' f z (matchA z a) ≡ matchNu z (f z a)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph matchA matchNu f
    mf = refl _
    
    open Naturality {lsuc (ℓ ⊔ ℓZ)} matchA matchNu f (refl _)
    naturality' :{¶} unfold matchA ≡ unfold matchNu ⊚ f
    naturality' = naturality

    finality :{¶} unfold matchA ≡ liftNu ⊚ f
    finality = J (lifting-lemma {ℓ ⊔ ℓZ}) (λ liftNu' _ → unfold matchA ≡ liftNu' ⊚ f) naturality'
