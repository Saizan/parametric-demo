{-# OPTIONS --rewriting #-}
module Naturality where

open import TypeSystem
open import Graph.Target
import Graph.Span as GraphSpan

record IsFunctor {a b} (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
   constructor con
   field
     map : ∀ {A B :{#} Set a} → (A → B) → F A → F B
     map-id : ∀ {A :{#} Set a} {x} → map (\ (x : A) → x) x ≡ x
     map-∘ : ∀ {A B C :{#} Set a} → (f : B → C) → (g : A → B) → ∀ {x} → map f (map g x) ≡ map (f ∘ g) x


map : ∀ {a b} {F :{#} Set a → Set b} → ([F] : IsFunctor F) → ∀ {A B :{#} Set a} → (A → B) → F A → F B
map (con x _ _) = x

map-id : ∀ {a b} {F :{#} Set a → Set b} → ([F] : IsFunctor F) → ∀ {A :{#} Set a} {x} → map [F] (\ (x : A) → x) x ≡ x
map-id (con _ x _) = x

map-∘ : ∀ {a b} {F :{#} Set a → Set b} → ([F] : IsFunctor F) → ∀ {A B C :{#} Set a} → (f : B → C) → (g : A → B)
        → ∀ {x} → map [F] f (map [F]  g x) ≡ map [F] (f ∘ g) x
map-∘ (con x _ y) = y

module Proof¶ {a b} (F G :{#} Set a → Set b) ([F] : IsFunctor F) ([G] : IsFunctor G)
                 (eta : ∀ (A :{#} Set a) → F A → G A)
                 (A B :{#} Set a) (f :{¶} A → B) where

  /f/ :{#} 𝕀 → Set a
  /f/ = / f /

  eta-nat : ∀ x → (map [G] f ∘ eta A) x ≡ (eta B ∘ map [F] f) x
  eta-nat x = trans (cong (map [G] f ∘ eta A) (sym (map-id {F = F} [F])))
             (trans (path-to-eq (\ i → map [G] (pull f i) (eta (/f/ i) (map [F] (push f i) x))))
                    (map-id [G]))


module ProofId {a b} (F G :{#} Set a → Set b) ([F] : IsFunctor F) ([G] : IsFunctor G)
                 (eta : ∀ (A :{#} Set a) → F A → G A)
                 (A B :{#} Set a) (f : A → B) where

  open GraphSpan f
  module Src = Proof¶ F G [F] [G] eta T A src
  module Tgt = Proof¶ F G [F] [G] eta T B tgt

  eta-nat : ∀ x → (map [G] f ∘ eta A) x ≡ (eta B ∘ map [F] f) x
  eta-nat x = (trans (sym (map-∘ [G] tgt inv))
              (trans (cong (map [G] tgt) (sym z))
              (trans (Tgt.eta-nat (map [F] inv x))
                     (cong (eta B) (map-∘ [F] tgt inv)))))
    where
      q : map [G] inv ((map [G] src ∘ eta T) (map [F] inv x)) ≡
            map [G] inv ((eta A ∘ map [F] src) (map [F] inv x))
      q = cong (map [G] inv) (Src.eta-nat (map [F] inv x))
      z : eta T (map [F] inv x) ≡ (map [G] inv ∘ eta A) x
      z = trans (trans (trans
                (sym (map-id [G]))
                (cong (let H = _ in λ f₁ → map [G] f₁ H) (sym (funext inv-src))))
                (sym (map-∘ [G] inv src)))
         (trans q
         (cong  (map [G] inv ∘ eta A)
         (trans (map-∘ [F] src inv)
                (map-id [F]))))
