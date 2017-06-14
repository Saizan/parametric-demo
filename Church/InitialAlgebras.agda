{-# OPTIONS --cubical --rewriting #-}
open import Primitives public
--open import Agda.Primitive public

module Church.InitialAlgebras where

open import TypeSystem public
open import Graph.Target public

--{-# BUILTIN REWRITE _≡_ #-}

--In this file, we prove the existence of initial algebras for functors (module InitialOfFunctor)
--and indexed functors (module InitialOfIndexedFunctor).
--The Church encodings depend pointwise on the algebra structure.

--------------------------------------------------

{-This module postulates its parameters, rather than getting parameters, because we need to add a rewrite rule.
  In order to make sure that modalities are enforced correctly, we add dummies with modalities id and #.
-}
module InitialOfFunctor (idDummy :{id} Set) (#Dummy :{#} Set) where

  postulate
    F :{#} ∀{ℓ} → Set ℓ → Set ℓ
    F' :{¶} ∀{ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} (f : A → B) → (F A → F B)
    rw-F-id : ∀{ℓ} {A :{#} Set ℓ} → F' (id{ℓ}{A}) ≡ id{ℓ}{F A}
    rw-F-hom : ∀{ℓA ℓB ℓC} {A :{#} Set ℓA} {B :{#} Set ℓB} {C :{#} Set ℓC} {f : A → B} {g : B → C} (fa :{#} F A)
         → F' g (F' f fa) ≡ F'(g ∘ f) fa

  {-# REWRITE rw-F-id #-}
  {-# REWRITE rw-F-hom #-}

  IsAlg :{#} ∀{ℓ} → (A : Set ℓ) → Set ℓ
  IsAlg A = F A → A

  IsMph :{#} ∀{ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (mkA : IsAlg A) (mkB : IsAlg B) (f : A → B) → Set (ℓA ⊔ ℓB)
  IsMph {ℓA}{ℓB}{A}{B} mkA mkB f = f ∘ mkA ≡ mkB ∘ F' f

  --initial algebra
  Mu :{#} (ℓ : Level) → Set (lsuc ℓ)
  Mu ℓ = (X :{#} Set ℓ) → (mkX :{¶} IsAlg X) → X
  fold : ∀{ℓ} {X :{#} Set ℓ} (mkX :{¶} IsAlg X) → (Mu ℓ → X)
  fold {ℓ} {X} mkX m = m X mkX
  mkMu : ∀{ℓ} → IsAlg (Mu ℓ)
  mkMu fm X mkX = mkX (F' (fold mkX) fm)
  mfold :{¶} ∀{ℓ} {X :{#} Set ℓ}  (mkX :{¶} IsAlg X) → IsMph mkMu mkX (fold mkX)
  mfold {ℓ} {X} mkX = refl _

  module NaturalityProven {ℓ :{¶} Level} where
    postulate
      A B :{#} Set ℓ
      mkA :{¶} IsAlg A
      mkB :{¶} IsAlg B
      f :{¶} A → B
      rw-mf : ∀{fa : F A} → f (mkA fa) ≡ mkB (F' f fa)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph mkA mkB f
    mf = refl _

    /f/ :{#} (i : 𝕀) → Set ℓ
    /f/ = / f /
    mk/f/ :{¶} {i :{#} 𝕀} → F (/f/ i) → /f/ i
    mk/f/ {i} fq = glue
      {φ = (i ≣ i0) ∨ (i ≣ i1)}
      (λ { ((i ≣ i0) = p⊤) → mkA fq
         ; ((i ≣ i1) = p⊤) → mkB fq
         })
      (mkB (F' (pull f i) fq))

    mpull :{¶} (i :{#} 𝕀) → IsMph (mk/f/ {i}) mkB (pull f i)
    mpull i = refl _

    naturality-path : (i :{#} 𝕀) → Mu ℓ → B
    naturality-path i = pull f i ∘ fold (mk/f/ {i})

    naturality :{¶} f ∘ fold mkA ≡ fold mkB
    naturality = path-to-eq naturality-path

  module Naturality {ℓ : Level}
      {A B :{#} Set ℓ}
      (mkA :{¶} IsAlg A)
      (mkB :{¶} IsAlg B)
      (f :{¶} A → B)
      (rw-mf : ∀{fa : F A} → f (mkA fa) ≡ mkB (F' f fa)) -- to be instantiated with refl
    where
    postulate
      naturality :{¶} f ∘ fold mkA ≡ fold mkB

  downfold : ∀{ℓ} → Mu (lsuc ℓ) → Mu ℓ
  downfold = fold mkMu
  mdownfold :{¶} ∀{ℓ} → IsMph mkMu mkMu (downfold {ℓ})
  mdownfold = mfold mkMu

  mkLift : ∀{ℓ} {A :{#} Set ℓ} → IsAlg A → IsAlg (Lift A)
  mkLift {ℓ} {A} mkA = lift ∘ mkA ∘ F' lower

  mlift :{¶} ∀{ℓ} {A :{#} Set ℓ} (mkA :{#} IsAlg A) → IsMph mkA (mkLift mkA) lift
  mlift mkA = refl _

  mlower :{¶} ∀{ℓ} {A :{#} Set ℓ} (mkA :{#} IsAlg A) → IsMph (mkLift mkA) mkA lower
  mlower mkA = refl _

  module LoweringLemma where
    module Core {ℓ :{¶} Level} {X :{#} Set ℓ} (mkX :{¶} IsAlg X) where
      lift∘fold : Mu ℓ → Lift X
      lift∘fold = lift ∘ fold mkX

      open Naturality {lsuc ℓ} mkMu (mkLift mkX) lift∘fold (refl _)

      naturality' :{¶} (λ (m : Mu (lsuc ℓ)) → lift (m (Mu ℓ) mkMu X mkX)) ≡
               (λ (m : Mu (lsuc ℓ)) → m (Lift X) (mkLift mkX))
      naturality' = naturality
    open Core

    --Note that Lift is the coercion into the next universe,
    --while lift and mkLift are the identity in ParamDTT
    lowerMu : ∀{ℓ} → Mu (lsuc ℓ) → Mu ℓ
    lowerMu m X mkX = lower (m (Lift X) (mkLift mkX))
    mlowerMu :{¶} ∀{ℓ} → IsMph mkMu mkMu (lowerMu {ℓ})
    mlowerMu = refl _

    lowering-lemma :{¶} ∀{ℓ} → fold mkMu ≡ (lowerMu {ℓ})
    lowering-lemma = funext (λ m → #funext λ X → ¶funext λ mkX → cong lower (cong-app (naturality' mkX) m))
  open LoweringLemma using (lowerMu ; mlowerMu ; lowering-lemma)

  module InitialityProven {ℓ :{¶} Level} where
    postulate
      B :{#} Set (lsuc ℓ)
      mkB :{¶} F B → B
      f :{¶} Mu ℓ → B
      rw-mf : ∀{fm : F (Mu ℓ)} → f (mkMu fm) ≡ mkB (F' f fm)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph mkMu mkB f
    mf = refl _

    open Naturality {lsuc ℓ} mkMu mkB f (refl _)
    naturality' :{¶} f ∘ fold mkMu ≡ fold mkB
    naturality' = naturality

    initiality :{¶} f ∘ lowerMu ≡ fold mkB
    initiality = J (lowering-lemma) (λ lowerMu' _ → f ∘ lowerMu' ≡ fold mkB) naturality'


-------------------------------------------------------------

{-This module postulates its parameters, rather than getting parameters, because we need to add a rewrite rule.
  In order to make sure that modalities are enforced correctly, we add dummies with modalities id and #.
-}
module InitialOfIndexedFunctor {ℓZ :{¶} Level} (Z :{#} Set ℓZ) (idDummy :{id} Set) (#Dummy :{#} Set) where

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

  IsAlg :{#} ∀{ℓ} → (A : ZSet ℓ) → Set (ℓ ⊔ ℓZ)
  IsAlg A = F A ⇒ A

  IsMph :{#} ∀{ℓA ℓB} {A : ZSet ℓA} {B : ZSet ℓB} (mkA : IsAlg A) (mkB : IsAlg B) (f : A ⇒ B) → Set (ℓA ⊔ ℓB ⊔ ℓZ)
  IsMph {ℓA}{ℓB}{A}{B} mkA mkB f = f ⊚ mkA ≡ mkB ⊚ F' f

  --initial algebra
  Mu :{#} (ℓ : Level) → ZSet (lsuc ℓ ⊔ ℓZ)
  Mu ℓ z = (X :{#} ZSet ℓ) → (mkX :{¶} IsAlg X) → X z
  fold : ∀{ℓ} {X :{#} ZSet ℓ} (mkX :{¶} IsAlg X) → (Mu ℓ ⇒ X)
  fold {ℓ} {X} mkX z m = m X mkX
  mkMu : ∀{ℓ} → IsAlg (Mu ℓ)
  mkMu z fm X mkX = mkX z (F' (fold mkX) z fm)
  mfold :{¶} ∀{ℓ} {X :{#} ZSet ℓ} (mkX :{¶} IsAlg X) → IsMph mkMu mkX (fold mkX)
  mfold {ℓ} {X} mkX = refl _

  Z/_/ :{#} ∀{ℓ} {A B : ZSet ℓ} (f :{¶} A ⇒ B) → 𝕀 → ZSet ℓ
  Z/ f / i z = / f z / i
  zpush : ∀{ℓ} {A B :{#} ZSet ℓ} (f :{¶} A ⇒ B) → (i :{#} 𝕀) → A ⇒ Z/ f / i
  zpush f i z a = push (f z) i a
  zpull : ∀{ℓ} {A B :{#} ZSet ℓ} (f :{¶} A ⇒ B) → (i :{#} 𝕀) → Z/ f / i ⇒ B
  zpull f i z q = pull (f z) i q

  module NaturalityProven {ℓ :{¶} Level} where
    postulate
      A B :{#} ZSet ℓ
      mkA :{¶} IsAlg A
      mkB :{¶} IsAlg B
      f :{¶} A ⇒ B
      rw-mf : ∀{z} {fa : F A z} → f z (mkA z fa) ≡ mkB z (F' f z fa)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph mkA mkB f
    mf = refl _
    /f/ :{#} (i : 𝕀) → ZSet ℓ
    /f/ = Z/ f /
    mk/f/ :{¶} {i :{#} 𝕀} → F (/f/ i) ⇒ /f/ i
    mk/f/ {i} z fq = glue
      {φ = (i ≣ i0) ∨ (i ≣ i1)}
      (λ { ((i ≣ i0) = p⊤) → mkA z fq
         ; ((i ≣ i1) = p⊤) → mkB z fq
         })
      (mkB z (F' (zpull f i) z fq))

    mzpull :{¶} (i :{#} 𝕀) → IsMph (mk/f/ {i}) mkB (zpull f i)
    mzpull i = refl _

    naturality-path : (i :{#} 𝕀) → Mu ℓ ⇒ B
    naturality-path i = zpull f i ⊚ fold (mk/f/ {i})

    naturality :{¶} f ⊚ fold mkA ≡ fold mkB
    naturality = path-to-eq naturality-path

  module Naturality {ℓ :{¶} Level}
      {A B :{#} ZSet ℓ}
      (mkA :{¶} IsAlg A)
      (mkB :{¶} IsAlg B)
      (f :{¶} A ⇒ B)
      (rz-mf : ∀{z} {fa : F A z} → f z (mkA z fa) ≡ mkB z (F' f z fa))
    where
    postulate
      naturality :{¶} f ⊚ fold mkA ≡ fold mkB

  downfold : ∀{ℓ} → Mu (lsuc (ℓ ⊔ ℓZ)) ⇒ Mu (ℓ ⊔ ℓZ)
  downfold = fold mkMu
  mdownfold :{¶} ∀{ℓ} → IsMph mkMu mkMu (downfold {ℓ ⊔ ℓZ})
  mdownfold = mfold mkMu

  ZLift : ∀{ℓ} → ZSet ℓ → ZSet (lsuc ℓ)
  ZLift A z = Lift (A z)
  zlift : ∀{ℓ} {A :{#} ZSet ℓ} → A ⇒ ZLift A
  zlift z a = lift a
  zlower : ∀{ℓ} {A :{#} ZSet ℓ} → ZLift A ⇒ A
  zlower z a = lower a

  mkLift : ∀{ℓ} {A :{#} ZSet ℓ} → IsAlg A → IsAlg (ZLift A)
  mkLift {ℓ} {A} mkA = zlift ⊚ mkA ⊚ F' zlower

  mlift :{¶} ∀{ℓ} {A :{#} ZSet ℓ} (mkA :{#} IsAlg A) → IsMph mkA (mkLift mkA) zlift
  mlift mkA = refl _

  mlower :{¶} ∀{ℓ} {A :{#} ZSet ℓ} (mkA :{#} IsAlg A) → IsMph (mkLift mkA) mkA zlower
  mlower mkA = refl _

  module LoweringLemma where
    module Core {ℓ :{¶} Level} {X :{#} ZSet (ℓ ⊔ ℓZ)} (mkX :{¶} IsAlg X) where
      lift∘fold : Mu (ℓ ⊔ ℓZ) ⇒ ZLift X
      lift∘fold = zlift ⊚ fold mkX

      open Naturality {lsuc (ℓ ⊔ ℓZ)} mkMu (mkLift mkX) lift∘fold (refl _)

      naturality' :{¶} (λ z m → lift (m (Mu (ℓ ⊔ ℓZ)) mkMu X mkX))
             ≡ (λ z m → m (ZLift X) (mkLift mkX))
      naturality' = naturality
    open Core

    --Note that Lift is the coercion into the next universe,
    --while lift and mkLift are the identity in ParamDTT
    lowerMu : ∀{ℓ} → Mu (lsuc ℓ) ⇒ Mu ℓ
    lowerMu z m X mkX = lower (m (ZLift X) (mkLift mkX))
    mlowerMu :{¶} ∀{ℓ} → IsMph mkMu mkMu (lowerMu {ℓ})
    mlowerMu = refl _

    lowering-lemma :{¶} {ℓ :{¶} Level} → fold mkMu ≡ (lowerMu {ℓ ⊔ ℓZ})
    lowering-lemma {ℓ} = #funext λ z → funext λ m → #funext λ X → ¶funext λ (mkX : IsAlg X) →
      cong {lsuc (ℓ ⊔ ℓZ)}{ℓ ⊔ ℓZ}{Lift (X z)}{X z} lower (cong-app (#cong-app (naturality' {ℓ} {X} mkX) z) m)
    {-
      J {_}{_}
        {Mu (lsuc (ℓ ⊔ ℓZ)) ⇒ ZLift X}
        {λ z m → lift (m (Mu (ℓ ⊔ ℓZ)) mkMu X mkX)}
        {λ z m → m (ZLift X) (mkLift mkX)}
        (naturality' {ℓ}{X} mkX)
        (λ h _ → (m (Mu (ℓ ⊔ ℓZ)) mkMu X mkX) ≡ lower (h z m)) (refl _)
    -}

  open LoweringLemma using (lowerMu ; mlowerMu ; lowering-lemma)

  module InitialityProven {ℓ :{¶} Level} where
    postulate
      B :{#} ZSet (lsuc (ℓ ⊔ ℓZ))
      mkB :{¶} F B ⇒ B
      f :{¶} Mu (ℓ ⊔ ℓZ) ⇒ B
      rw-mf : ∀{z}{fm : F (Mu _) z} → f z (mkMu z fm) ≡ mkB z (F' f z fm)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph mkMu mkB f
    mf = refl _

    open Naturality {lsuc (ℓ ⊔ ℓZ)} mkMu mkB f (refl _)
    naturality' :{¶} f ⊚ fold mkMu ≡ fold mkB
    naturality' = naturality

    initiality :{¶} f ⊚ lowerMu ≡ fold mkB
    initiality = J (lowering-lemma {ℓ ⊔ ℓZ}) (λ lowerMu' _ → f ⊚ lowerMu' ≡ fold mkB) naturality'
