{-# OPTIONS --cubical #-}
module Primitives where

data 𝔹 : Set where
  b0 b1 : 𝔹

{-# BUILTIN BRIDGENAME 𝔹 #-}
{-# BUILTIN BZERO b0 #-}
{-# BUILTIN BONE b1 #-}

data ℙ : Set where
  ι : 𝔹 → ℙ

{-# BUILTIN PATHNAME ℙ #-}
{-# BUILTIN IOTA ι #-}

p0 = ι b0
p1 = ι b1

data Prop : Set where
  p⊤ : Prop

postulate
  p⊥ : Prop

{-# BUILTIN PROP Prop #-}
{-# BUILTIN PTOP p⊤ #-}
{-# BUILTIN PBOT p⊥ #-}

module Original where
  primitive
    primPEq : _
    primPBridge : _
    primPMin : _
    primPMax : _

open Original public renaming (primPEq to _≣_; primPBridge to _∈ι; primPMin to _∧_; primPMax to _∨_)


open import Relation.Binary.PropositionalEquality

private
  module Tests where
    rw-≣ : ∀{i} → (i ≣ i) ≡ p⊤
    rw-≣ = refl

    rw-∈ι : ∀{i : 𝔹} → ι(i) ∈ι ≡ p⊤
    rw-∈ι = refl

    rw-p0≣p1 : (ι b0 ≣ ι b1) ≡ p⊥
    rw-p0≣p1 = refl
    rw-p1≣p0 : (ι b1 ≣ ι b0) ≡ p⊥
    rw-p1≣p0 = refl

    rw-∨⊤ : ∀{φ} → φ ∨ p⊤ ≡ p⊤
    rw-∨⊤ = refl
    rw-⊤∨ : ∀{φ} → p⊤ ∨ φ ≡ p⊤
    rw-⊤∨ = refl
    rw-⊥∨⊥ : p⊥ ∨ p⊥ ≡ p⊥
    rw-⊥∨⊥ = refl

    rw-⊤∧⊤ : p⊤ ∧ p⊤ ≡ p⊤
    rw-⊤∧⊤ = refl
    rw-∧⊥ : ∀{φ} → φ ∧ p⊥ ≡ p⊥
    rw-∧⊥ = refl
    rw-⊥∧ : ∀{φ} → p⊥ ∧ φ ≡ p⊥
    rw-⊥∧ = refl


{-# BUILTIN ISONE        IsOne #-} -- IsOne : I → Setω


postulate
  itIsOne : IsOne p⊤
  IsOne1  : ∀ i j → IsOne i → IsOne (i ∨ j)
  IsOne2  : ∀ i j → IsOne j → IsOne (i ∨ j)

{-# BUILTIN ITISONE      itIsOne  #-}
{-# BUILTIN ISONE1       IsOne1   #-}
{-# BUILTIN ISONE2       IsOne2   #-}
{-# BUILTIN PARTIAL      Partial  #-}
{-# BUILTIN PARTIALP     PartialP #-}


module GluePrims where
 primitive
  primGlue : ∀ {a b} (A : Set a) → ∀ φ → (T : Partial (Set b) φ) → (f : PartialP φ (λ o → T o → A)) → Set b


  prim^glue : ∀ {a b} {A : Set a} {φ : Prop} {T : Partial (Set b) φ}
                {f : PartialP φ (λ o → T o → A)}
                → PartialP φ T → A → primGlue A φ T f

  prim^unglue : ∀ {a b} {A : Set a} {φ : Prop} {T : Partial (Set b) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  → primGlue A φ T f → A


module GluePrims' (dummy : Set₁) = GluePrims
open GluePrims' Set using () renaming (prim^glue to unsafeGlue) public

open GluePrims public renaming (prim^glue to glue; prim^unglue to unglue)


private
  module Tests2 where

    test-unglue0 : ∀ {l} {A : Set l} (let φ = p⊤) {T : Partial (Set l) φ}
                      {f : PartialP φ (λ o → T o → A)}
                      (b : primGlue A φ T f) → unglue {A = A} {φ = φ} {T = T} {f} b ≡ f itIsOne b
    test-unglue0 _ = refl

    test-Glue-beta : ∀ {l} {A : Set l} {φ : Prop} {T : Partial (Set l) φ}
                      {f : PartialP φ (λ o → T o → A)}
                      (t : PartialP φ T) (a : A) → unglue {A = A} {φ = φ} {T = T} {f} (unsafeGlue t a) ≡ a
    test-Glue-beta _ _ = refl

    test-Glue-eta : ∀ {l} {A : Set l} {φ} {T : Partial (Set l) φ}
                      {f : PartialP φ (λ o → T o → A)}
                      (b : primGlue A φ T f) → (unsafeGlue {φ = φ} (\ { _ → b }) (unglue {φ = φ} b)) ≡ b
    test-Glue-eta b = refl

    test-unglue2 : ∀ {l} {A : Set l} (let φ = p⊤)  {T : Partial (Set l) φ}
                      {f : PartialP φ (λ o → T o → A)}
                      (t : PartialP φ T) (a : A) → unglue {A = A} {φ = φ} {T = T} {f} (unsafeGlue {A = A} {φ = φ} {T = T} {f} t a)
                                                   ≡ f itIsOne (t itIsOne) -- = a
    test-unglue2 _ _ = refl

    test-glue0 : ∀ {l} {A : Set l} (let φ = p⊤) {T : Partial (Set l) φ}
                      {f : PartialP φ (λ o → T o → A)}
                      (t : PartialP φ T) (a : A) → (unsafeGlue {A = A} {T = T} {f} t a) ≡ t itIsOne
    test-glue0 _ _ = refl


primitive
  primUnIota : {i : ℙ} → Partial 𝔹 (i ∈ι)

private
  module Tests3 where
    test-systems : ∀ i j → Partial Set ((i ≣ ι b0) ∨ (j ≣ ι b1))
    test-systems i j ((i ≣ ι b0) = p⊤) = 𝔹
    test-systems i j ((j ≣ ι b1) = p⊤) = 𝔹

    test-bridge : ∀ i → Partial Set (i ∈ι)
    test-bridge i _ = 𝔹


    test-UnIota : ∀ i → Partial 𝔹 (i ∈ι)
    test-UnIota i _ = primUnIota {i} itIsOne

postulate
  PathP : ∀ {a} (A : ℙ → Set a) → A p0 → A p1 → Set a
  BridgeP : ∀ {a} (A : 𝔹 → Set a) → A b0 → A b1 → Set a

{-# BUILTIN PATHP PathP #-}
{-# BUILTIN BRIDGEP BridgeP #-}

reflB : ∀ {a} {A : Set a}{x : A} → BridgeP (\ _ → A) x x
reflB {x = x} = \ _ → x

reflP : ∀ {a} {A : Set a}{x : A} → PathP (\ _ → A) x x
reflP {x = x} = \ _ → x

etaP : ∀ {a} {A : Set a}{x y : A} → PathP (\ _ → A) x y → PathP (\ _ → A) x y
etaP b = \ x → b x

etaB : ∀ {a} {A : Set a}{x y : A} → BridgeP (\ _ → A) x y → BridgeP (\ _ → A) x y
etaB b = \ x → b x

pathToBridge : ∀ {a} {A : Set a}{x y : A} → PathP (\ _ → A) x y → BridgeP (\ _ → A) x y
pathToBridge p = \ x → p (ι x)

private
  module Tests4 where
    etaB-test : ∀ {a} {A : Set a}{x y : A} → (b : BridgeP (\ _ → A) x y) → b ≡ etaB b
    etaB-test _ = refl

    etaP-test : ∀ {a} {A : Set a}{x y : A} → (b : BridgeP (\ _ → A) x y) → b ≡ etaB b
    etaP-test _ = refl


fun-ext : ∀ {a} {A : Set a} {b} {B : Set b} → {f g : A → B} → (∀ x → PathP (\ _ → B) (f x) (g x)) → PathP (\ _ → A → B) f g
fun-ext p i x = p x i


{-# BUILTIN SUB Sub #-}

postulate
    inc : ∀ {a} {A : Set a} {φ} (x : A) → Sub {A = A} φ (\ _ → x)

{-# BUILTIN SUBIN inc #-}

primitive
    primSubOut : {a : _} {A : Set a} {φ : Prop} {u : Partial A φ} → Sub φ u → A

private
  module Tests5 where
    ouc-φ : ∀ {a} {A : Set a} (let φ = p⊤) {t : Partial A φ} → (s : Sub {A = A} φ t) → (primSubOut s) ≡ t itIsOne
    ouc-φ s = refl

    ouc-beta : ∀ {a} {A : Set a} {φ} → (a : A) → primSubOut {φ = φ} {u = \ { _ → a }} (inc {φ = φ} a) ≡ a
    ouc-beta a = refl
