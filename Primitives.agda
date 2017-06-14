{-# OPTIONS --cubical #-}
module Primitives where

data 𝕀 : Set where
  i0 i1 : 𝕀

{-# BUILTIN BRIDGENAME 𝕀 #-}
{-# BUILTIN BZERO i0 #-}
{-# BUILTIN BONE i1 #-}

-- The type ℙ is obsolete as we rather use parametric quantification
-- over 𝔹, however it's kept because currently it's still part of the
-- Prop interface.
-- data ℙ : Set where
--   ι : 𝔹 → ℙ

-- {-# BUILTIN PATHNAME ℙ #-}
-- {-# BUILTIN IOTA ι #-}

--𝔹, ℙ, ι, b0, b1, p0, p1 are obsolete
𝔹 : Set
𝔹 = 𝕀
ℙ : Set
ℙ = 𝔹
ι : 𝔹 → ℙ
ι x = x
b0 = i0
b1 = i1
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
    -- primPBridge : _
    primPMin : _
    primPMax : _
    primCoShapePi : _
    primSharpPi : _
    primNSSharpPi : _
    primHCoShapePi : _
    primHSharpPi : _
    primHNSSharpPi : _

open Original public renaming (primPEq to _≣_; {- primPBridge to _∈ι;-} primPMin to _∧_; primPMax to _∨_;
                               primCoShapePi to ¶Π; primSharpPi to #Π; primNSSharpPi to ÷#Π;
                               primHCoShapePi to h¶Π; primHSharpPi to h#Π; primHNSSharpPi to h÷#Π)

¶Π-syntax = ¶Π
#Π-syntax = #Π
÷#Π-syntax = ÷#Π

syntax ¶Π-syntax A (λ x → B) = ¶[ x ∈ A ]→ B
syntax #Π-syntax A (λ x → B) = #[ x ∈ A ]→ B
syntax ÷#Π-syntax A (λ x → B) = ÷#[ x ∈ A ]→ B


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
  primGlue : ∀ {a b} (A : Set a) → ∀ φ → (T : Partial (Set b) φ) → ¶Π (PartialP φ (λ o → T o → A)) \ f → Set b

  -- we comment out the types of the primitives so we get the nicer internal ones, with φ named
  prim^glue : _
   -- ∀ {a b} {A : Set a} → h#Π Prop \ φ → {T : Partial (Set b) φ}
   -- → h¶Π (PartialP φ (λ o → T o → A)) \ f → PartialP φ T → A → primGlue A φ T f

  prim^unglue : _
  -- ∀ {a b} {A : Set a} → h#Π Prop \ φ → {T : Partial (Set b) φ}
  --               → h¶Π (PartialP φ (λ o → T o → A)) \ f →
  --                 primGlue A φ T f → A


module GluePrims' (dummy : Set₁) = GluePrims
open GluePrims' Set using () renaming (prim^glue to unsafeGlue) public

open GluePrims public renaming (prim^glue to glue; prim^unglue to unglue)

-- primitive
--   primUnIota : {i : ℙ} → Partial 𝔹 (i ∈ι)

-- postulate
--   PathP : ∀ {a} (A : ℙ → Set a) → A p0 → A p1 → Set a
--   BridgeP : ∀ {a} (A : 𝔹 → Set a) → A b0 → A b1 → Set a

-- {-# BUILTIN PATHP PathP #-}
-- {-# BUILTIN BRIDGEP BridgeP #-}

-- reflB : ∀ {a} {A : Set a}{x : A} → BridgeP (\ _ → A) x x
-- reflB {x = x} = \ _ → x

-- reflP : ∀ {a} {A : Set a}{x : A} → PathP (\ _ → A) x x
-- reflP {x = x} = \ _ → x

-- etaP : ∀ {a} {A : Set a}{x y : A} → PathP (\ _ → A) x y → PathP (\ _ → A) x y
-- etaP b = \ x → b x

-- etaB : ∀ {a} {A : Set a}{x y : A} → BridgeP (\ _ → A) x y → BridgeP (\ _ → A) x y
-- etaB b = \ x → b x

-- pathToBridge : ∀ {a} {A : Set a}{x y : A} → PathP (\ _ → A) x y → BridgeP (\ _ → A) x y
-- pathToBridge p = \ x → p (ι x)


-- fun-ext : ∀ {a} {A : Set a} {b} {B : Set b} → {f g : A → B} → (∀ x → PathP (\ _ → B) (f x) (g x)) → PathP (\ _ → A → B) f g
-- fun-ext p i x = p x i


-- {-# BUILTIN SUB Sub #-}

-- postulate
--     inc : ∀ {a} {A : Set a} {φ} (x : A) → Sub {A = A} φ (\ _ → x)

-- {-# BUILTIN SUBIN inc #-}

-- primitive
--     primSubOut : {a : _} {A : Set a} {φ : Prop} {u : Partial A φ} → Sub φ u → A
