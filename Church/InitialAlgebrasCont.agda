{-# OPTIONS --cubical --rewriting #-}
open import Primitives public
--open import Agda.Primitive public

module Church.InitialAlgebrasCont where

open import TypeSystem public
open import Graph.Target public
open import Church.FibredBy public

--{-# BUILTIN REWRITE _≡_ #-}

--In this file, we prove the existence of initial algebras for functors (module InitialOfFunctor)
--and indexed functors (module InitialOfIndexedFunctor).
--The Church encodings depend continuously on the algebra structure.

--------------------------------------------------

{-This module postulates its parameters, rather than getting parameters, because we need to add a rewrite rule.
  In order to make sure that modalities are enforced correctly, we add dummies with modalities id and #.
-}
module InitialOfFunctor (idDummy :{id} Set) (#Dummy :{#} Set) where

  postulate
    F :{#} ∀{ℓ} → Set ℓ → Set ℓ
    F' : ∀{ℓA ℓB} {A :{#} Set ℓA} {B :{#} Set ℓB} (f : A → B) → (F A → F B)
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
  Mu ℓ = (X :{#} Set ℓ) → (mkX : IsAlg X) → X
  fold : ∀{ℓ} {X :{#} Set ℓ} (mkX : IsAlg X) → (Mu ℓ → X)
  fold {ℓ} {X} mkX m = m X mkX
  mkMu : ∀{ℓ} → IsAlg (Mu ℓ)
  mkMu fm X mkX = mkX (F' (fold mkX) fm)
  mfold :{¶} ∀{ℓ} {X :{#} Set ℓ}  (mkX : IsAlg X) → IsMph mkMu mkX (fold mkX)
  mfold {ℓ} {X} mkX = refl _

  module NaturalityProven {ℓ :{¶} Level} where
    postulate
      A B :{#} Set ℓ
      mkA : IsAlg A
      mkB : IsAlg B
      f :{¶} A → B
      rw-mf : ∀{fa : F A} → f (mkA fa) ≡ mkB (F' f fa)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph mkA mkB f
    mf = refl _

    /f/ :{#} (i : 𝕀) → Set ℓ
    /f/ = / f /
    mk/f/ : {i :{#} 𝕀} → F (/f/ i) → /f/ i
    mk/f/ {i} fq = glue
      {φ = (i ≣ i0) ∨ (i ≣ i1)}
      (λ { ((i ≣ i0) = p⊤) → mkA fq
         ; ((i ≣ i1) = p⊤) → mkB fq
         })
      (mkB (F' (pull f i) fq))

    mpull : (i :{#} 𝕀) → IsMph (mk/f/ {i}) mkB (pull f i)
    mpull i = refl _

    naturality-path : (i :{#} 𝕀) → Mu ℓ → B
    naturality-path i = pull f i ∘ fold (mk/f/ {i})

    naturality :{¶} f ∘ fold mkA ≡ fold mkB
    naturality = path-to-eq naturality-path

  module Naturality {ℓ :{¶} Level}
      {A B :{#} Set ℓ}
      (mkA : IsAlg A)
      (mkB : IsAlg B)
      (f :{¶} A → B)
      (rw-mf : ∀{fa : F A} → f (mkA fa) ≡ mkB (F' f fa))
    where
    postulate
      naturality :{¶} f ∘ fold mkA ≡ fold mkB

  downfold : ∀{ℓ} → Mu (lsuc ℓ) → Mu ℓ
  downfold = fold mkMu
  mdownfold : ∀{ℓ} → IsMph mkMu mkMu (downfold {ℓ})
  mdownfold = mfold mkMu

  mkLift : ∀{ℓ} {A :{#} Set ℓ} → IsAlg A → IsAlg (Lift A)
  mkLift {ℓ} {A} mkA = lift ∘ mkA ∘ F' lower

  mlift : ∀{ℓ} {A :{#} Set ℓ} (mkA :{#} IsAlg A) → IsMph mkA (mkLift mkA) lift
  mlift mkA = refl _

  mlower : ∀{ℓ} {A :{#} Set ℓ} (mkA :{#} IsAlg A) → IsMph (mkLift mkA) mkA lower
  mlower mkA = refl _

  mk[_fibred-over_by_] : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} (mkX : IsAlg X) (mkY : IsAlg Y) {g : X → Y}
    (mg : IsMph mkX mkY g) → IsAlg (X fibred-by g)
  mk[_fibred-over_by_] {ℓX}{ℓY}{X}{Y} mkX mkY {g} mg fp = [ mkY (F' get-image fp) , [ mkX (F' unfibre fp) ,
        --prove: g (mkX (F' (outfib g) fp)) ≡ mkY (F' (fib g) fp)
        J (sym (cong-app mg (F' unfibre fp))) (λ y _ → y ≡ mkY (F' get-image fp)) (
          --prove: (mkY ∘ F' g) (F' (outfib g) fp) ≡ mkY (F' (fib g) fp)
          cong (λ (fib' : X fibred-by g → Y) → mkY (F' fib' fp)) (
            --prove: g ∘ outfib g ≡ fib g
            funext (λ p → snd (snd p))
          )
        )
    ] ]

  mget-image : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} {mkX : IsAlg X} {mkY : IsAlg Y} {g : X → Y}
    (mg : IsMph mkX mkY g) → IsMph (mk[ mkX fibred-over mkY by mg ]) mkY get-image
  mget-image {ℓX}{ℓY}{X}{Y}{mkX}{mkY}{g} mg = refl _

  {-
  minfib : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} {mkX : IsAlg X} {mkY : IsAlg Y} {g : X → Y}
    (mg : IsMph mkX mkY g) → IsMph mkX (mkFib mkY mg) (infib g)
  minfib {ℓX}{ℓY}{X}{Y}{mkX}{mkY}{g} mg = funext λ fx → {! tedious !}
  -}

  munfibre-by : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} {mkX : IsAlg X} {mkY : IsAlg Y} {g : X → Y}
    (mg : IsMph mkX mkY g) → IsMph (mk[ mkX fibred-over mkY by mg ]) mkX unfibre
  munfibre-by {ℓX}{ℓY}{X}{Y}{mkX}{mkY}{g} mg = refl _

  module LoweringLemma where
    module Core {ℓ :{¶} Level} {X :{#} Set ℓ} (mkX : IsAlg X) where
      lift∘fold : Mu ℓ → Lift X
      lift∘fold = lift ∘ fold mkX

      Mu-fibred :{#} Set (lsuc ℓ)
      Mu-fibred = Mu ℓ fibred-by lift∘fold
      mkMu-fibred : IsAlg Mu-fibred
      mkMu-fibred = mk[ mkMu fibred-over mkLift mkX by refl _ ]
      unfibre-Mu : Mu-fibred → Mu ℓ
      unfibre-Mu = unfibre
      fibre-Mu : Mu ℓ → Mu-fibred
      fibre-Mu = fibre-by lift∘fold

      get-lift∘fold : Mu-fibred → Lift X
      get-lift∘fold = get-image

      open Naturality {lsuc ℓ} mkMu-fibred (mkLift mkX) get-lift∘fold (refl _)
        renaming (naturality to naturality-get-lift∘fold) using ()

      naturality-get-lift∘fold' :{¶} get-lift∘fold ∘ fold mkMu-fibred ≡ fold (mkLift mkX)
      naturality-get-lift∘fold' = naturality-get-lift∘fold

      open Naturality {lsuc ℓ} mkMu-fibred mkMu unfibre (refl _)
        renaming (naturality to naturality-unfibre) using ()

      naturality-unfibre' :{¶} unfibre ∘ fold mkMu-fibred ≡ fold mkMu
      naturality-unfibre' = naturality-unfibre
    open Core

    --Note that Lift is the coercion into the next universe,
    --while lift and mkLift are the identity in ParamDTT
    lowerMu : ∀{ℓ} → Mu (lsuc ℓ) → Mu ℓ
    lowerMu m X mkX = lower (m (Lift X) (mkLift mkX))
    mlowerMu : ∀{ℓ} → IsMph mkMu mkMu (lowerMu {ℓ})
    mlowerMu = refl _

    lowering-lemma :{¶} ∀{ℓ} → fold mkMu ≡ (lowerMu {ℓ})
    lowering-lemma = funext λ m → #funext λ X → funext λ mkX → cong lower (cong-app (
        --Prove: lift∘fold mkX ∘ fold mkMu ≡ fold (mkLift mkX)
        (lift∘fold mkX ∘ fold mkMu ≡ lift∘fold mkX ∘ unfibre ∘ fold (mkMu-fibred mkX)) ∋
          cong (λ f → lift∘fold mkX ∘ f) (sym (naturality-unfibre' mkX)) •
        (lift∘fold mkX ∘ unfibre ∘ fold (mkMu-fibred mkX) ≡ get-lift∘fold mkX ∘ fold (mkMu-fibred mkX)) ∋
          cong (λ f → f ∘ fold (mkMu-fibred mkX)) (fib-lemma (lift∘fold mkX)) •
        (get-lift∘fold mkX ∘ fold (mkMu-fibred mkX) ≡ fold (mkLift mkX)) ∋
          naturality-get-lift∘fold' mkX
      ) m)
  open LoweringLemma using (lowerMu ; mlowerMu ; lowering-lemma)

  module InitialityProven {ℓ :{¶} Level} where
    postulate
      B :{#} Set (lsuc ℓ)
      mkB : F B → B
      f :{¶} Mu ℓ → B
      rw-mf : ∀{fm : F (Mu ℓ)} → f (mkMu fm) ≡ mkB (F' f fm)
    {-# REWRITE rw-mf #-}
    mf : IsMph mkMu mkB f
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
    F' : ∀{ℓA ℓB} {A :{#} ZSet ℓA} {B :{#} ZSet ℓB} → (A ⇒ B) → (F A ⇒ F B)
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
  Mu ℓ z = (X :{#} ZSet ℓ) → (mkX : IsAlg X) → X z
  fold : ∀{ℓ} {X :{#} ZSet ℓ} (mkX : IsAlg X) → (Mu ℓ ⇒ X)
  fold {ℓ} {X} mkX z m = m X mkX
  mkMu : ∀{ℓ} → IsAlg (Mu ℓ)
  mkMu z fm X mkX = mkX z (F' (fold mkX) z fm)
  mfold :{¶} ∀{ℓ} {X :{#} ZSet ℓ} (mkX : IsAlg X) → IsMph mkMu mkX (fold mkX)
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
      mkA : IsAlg A
      mkB : IsAlg B
      f :{¶} A ⇒ B
      rw-mf : ∀{z} {fa : F A z} → f z (mkA z fa) ≡ mkB z (F' f z fa)
    {-# REWRITE rw-mf #-}
    mf :{¶} IsMph mkA mkB f
    mf = refl _

    /f/ :{#} (i : 𝕀) → ZSet ℓ
    /f/ = Z/ f /
    mk/f/ : {i :{#} 𝕀} → F (/f/ i) ⇒ /f/ i
    mk/f/ {i} z fq = glue
      {φ = (i ≣ i0) ∨ (i ≣ i1)}
      (λ { ((i ≣ i0) = p⊤) → mkA z fq
         ; ((i ≣ i1) = p⊤) → mkB z fq
         })
      (mkB z (F' (zpull f i) z fq))

    mzpull : (i :{#} 𝕀) → IsMph (mk/f/ {i}) mkB (zpull f i)
    mzpull i = refl _

    naturality-path : (i :{#} 𝕀) → Mu ℓ ⇒ B
    naturality-path i = zpull f i ⊚ fold (mk/f/ {i})

    naturality :{¶} f ⊚ fold mkA ≡ fold mkB
    naturality = path-to-eq naturality-path

  module Naturality {ℓ :{¶} Level}
      {A B :{#} ZSet ℓ}
      (mkA : IsAlg A)
      (mkB : IsAlg B)
      (f :{¶} A ⇒ B)
      (rz-mf : ∀{z} {fa : F A z} → f z (mkA z fa) ≡ mkB z (F' f z fa))
    where
    postulate
      naturality :{¶} f ⊚ fold mkA ≡ fold mkB

  downfold : ∀{ℓ} → Mu (lsuc (ℓ ⊔ ℓZ)) ⇒ Mu (ℓ ⊔ ℓZ)
  downfold = fold mkMu
  mdownfold : ∀{ℓ} → IsMph mkMu mkMu (downfold {ℓ ⊔ ℓZ})
  mdownfold = mfold mkMu

  ZLift : ∀{ℓ} → ZSet ℓ → ZSet (lsuc ℓ)
  ZLift A z = Lift (A z)
  zlift : ∀{ℓ} {A :{#} ZSet ℓ} → A ⇒ ZLift A
  zlift z a = lift a
  zlower : ∀{ℓ} {A :{#} ZSet ℓ} → ZLift A ⇒ A
  zlower z a = lower a

  mkLift : ∀{ℓ} {A :{#} ZSet ℓ} → IsAlg A → IsAlg (ZLift A)
  mkLift {ℓ} {A} mkA = zlift ⊚ mkA ⊚ F' zlower

  mlift : ∀{ℓ} {A :{#} ZSet ℓ} (mkA :{#} IsAlg A) → IsMph mkA (mkLift mkA) zlift
  mlift mkA = refl _

  mlower : ∀{ℓ} {A :{#} ZSet ℓ} (mkA :{#} IsAlg A) → IsMph (mkLift mkA) mkA zlower
  mlower mkA = refl _

  Z[_fibred-by_] : ∀{ℓX ℓY} (X : ZSet ℓX) {Y : ZSet ℓY} (f : X ⇒ Y) → ZSet (ℓY ⊔ ℓX)
  Z[_fibred-by_] {ℓX}{ℓY} X {Y} f z = X z fibred-by f z

  zfibre-by : ∀{ℓX ℓY} {X :{#} ZSet ℓX} {Y :{#} ZSet ℓY} (f : X ⇒ Y) → X ⇒ Z[ X fibred-by f ]
  zfibre-by f z = fibre-by (f z)

  zunfibre : ∀{ℓX ℓY} {X :{#} ZSet ℓX} {Y :{#} ZSet ℓY} {f :{#} X ⇒ Y} → Z[ X fibred-by f ] ⇒ X
  zunfibre z = unfibre

  zunfibre-by : ∀{ℓX ℓY} {X :{#} ZSet ℓX} {Y :{#} ZSet ℓY} (f :{#} X ⇒ Y) → Z[ X fibred-by f ] ⇒ X
  zunfibre-by f z = unfibre-by (f z)

  zget-image : ∀{ℓX ℓY} {X :{#} ZSet ℓX} {Y :{#} ZSet ℓY} {f :{#} X ⇒ Y} → Z[ X fibred-by f ] ⇒ Y
  zget-image z = get-image

  zfib-lemma : ∀{ℓX ℓY} {X :{#} ZSet ℓX} {Y :{#} ZSet ℓY} (f : X ⇒ Y) → f ⊚ zunfibre-by f ≡ zget-image
  zfib-lemma f = #funext λ z → fib-lemma (f z)

  mkZ[_fibred-over_by_] : ∀{ℓX ℓY} {X :{#} ZSet ℓX} {Y :{#} ZSet ℓY} (mkX : IsAlg X) (mkY : IsAlg Y) {g : X ⇒ Y}
    (mg : IsMph mkX mkY g) → IsAlg Z[ X fibred-by g ]
  mkZ[_fibred-over_by_] {ℓX}{ℓY}{X}{Y} mkX mkY {g} mg z fp = [ mkY z (F' zget-image z fp) , [ mkX z (F' zunfibre z fp) ,
      --prove: g z (mkX z (F' zunfibre z fp)) ≡ mkY z (F' zget-image z fp)
      --i.e. prove: (g ⊚ mkX ⊚ F' zunfibre) z fp ≡ (mkY ⊚ F' zget-image) z fp
      --cong-app (#cong-app {!g ⊚ mkX ⊚ F' zunfibre ≡ mkY ⊚ F' zget-image!} z) fp
      cong-app (#cong-app ( (g ⊚ mkX ⊚ F' zunfibre ≡ mkY ⊚ F' zget-image) ∋ (
        (g ⊚ mkX ⊚ F' zunfibre ≡ mkY ⊚ F' (g ⊚ zunfibre)) ∋
          cong (λ f → f ⊚ F' zunfibre) mg •
        (mkY ⊚ F' (g ⊚ zunfibre) ≡ mkY ⊚ F' zget-image) ∋
          cong (λ f → mkY ⊚ F' f) (zfib-lemma g)
      ) ) z) fp
    ] ]

  module LoweringLemma where
    module Core {ℓ :{¶} Level} {X :{#} ZSet (ℓ ⊔ ℓZ)} (mkX : IsAlg X) where
      lift∘fold : Mu (ℓ ⊔ ℓZ) ⇒ ZLift X
      lift∘fold = zlift ⊚ fold mkX

      Mu-fibred :{#} ZSet (lsuc (ℓ ⊔ ℓZ))
      Mu-fibred = Z[ Mu (ℓ ⊔ ℓZ) fibred-by lift∘fold ]
      mkMu-fibred : IsAlg Mu-fibred
      mkMu-fibred = mkZ[ mkMu fibred-over mkLift mkX by refl _ ]
      unfibre-Mu : Mu-fibred ⇒ Mu (ℓ ⊔ ℓZ)
      unfibre-Mu = zunfibre
      fibre-Mu : Mu (ℓ ⊔ ℓZ) ⇒ Mu-fibred
      fibre-Mu = zfibre-by lift∘fold

      get-lift∘fold : Mu-fibred ⇒ ZLift X
      get-lift∘fold = zget-image

      open Naturality {lsuc (ℓ ⊔ ℓZ)} mkMu-fibred (mkLift mkX) get-lift∘fold (refl _)
        renaming (naturality to naturality-get-lift∘fold) using ()

      naturality-get-lift∘fold' :{¶} get-lift∘fold ⊚ fold mkMu-fibred ≡ fold (mkLift mkX)
      naturality-get-lift∘fold' = naturality-get-lift∘fold

      open Naturality {lsuc (ℓ ⊔ ℓZ)} mkMu-fibred mkMu zunfibre (refl _)
        renaming (naturality to naturality-unfibre) using ()

      naturality-unfibre' :{¶} zunfibre ⊚ fold mkMu-fibred ≡ fold mkMu
      naturality-unfibre' = naturality-unfibre
    --open Core

    --Note that Lift is the coercion into the next universe,
    --while lift and mkLift are the identity in ParamDTT
    lowerMu : ∀{ℓ} → Mu (lsuc ℓ) ⇒ Mu ℓ
    lowerMu z m X mkX = lower (m (ZLift X) (mkLift mkX))
    mlowerMu :{¶} ∀{ℓ} → IsMph mkMu mkMu (lowerMu {ℓ})
    mlowerMu = refl _

    lowering-lemma :{¶} {ℓ :{¶} Level} → fold mkMu ≡ (lowerMu {ℓ ⊔ ℓZ})
    lowering-lemma {ℓ} = #funext λ z → funext λ m → #funext λ X → funext λ mkX → cong lower (cong-app (#cong-app (
        --Prove: lift∘fold mkX ⊚ fold mkMu ≡ fold (mkLift mkX)
        (lift∘fold mkX ⊚ fold mkMu ≡ lift∘fold mkX ⊚ zunfibre ⊚ fold (mkMu-fibred mkX)) ∋
          cong (λ f → lift∘fold mkX ⊚ f) (sym (naturality-unfibre' mkX)) •
        (lift∘fold mkX ⊚ zunfibre ⊚ fold (mkMu-fibred mkX) ≡ get-lift∘fold mkX ⊚ fold (mkMu-fibred mkX)) ∋
          cong (λ f → f ⊚ fold (mkMu-fibred mkX)) (zfib-lemma (lift∘fold mkX)) •
        (get-lift∘fold mkX ⊚ fold (mkMu-fibred mkX) ≡ fold (mkLift mkX)) ∋
          naturality-get-lift∘fold' mkX
      ) z) m)
      where open Core {ℓ}

  open LoweringLemma using (lowerMu ; mlowerMu ; lowering-lemma)

  module InitialityProven {ℓ :{¶} Level} where
    postulate
      B :{#} ZSet (lsuc (ℓ ⊔ ℓZ))
      mkB : F B ⇒ B
      f :{¶} Mu (ℓ ⊔ ℓZ) ⇒ B
      rw-mf : ∀{z}{fm : F (Mu _) z} → f z (mkMu z fm) ≡ mkB z (F' f z fm)
    {-# REWRITE rw-mf #-}
    mf : IsMph mkMu mkB f
    mf = refl _

    open Naturality {lsuc (ℓ ⊔ ℓZ)} mkMu mkB f (refl _)
    naturality' :{¶} f ⊚ fold mkMu ≡ fold mkB
    naturality' = naturality

    initiality :{¶} f ⊚ lowerMu ≡ fold mkB
    initiality = J (lowering-lemma {ℓ ⊔ ℓZ}) (λ lowerMu' _ → f ⊚ lowerMu' ≡ fold mkB) naturality'
