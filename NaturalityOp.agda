{-# OPTIONS --rewriting #-}
module NaturalityOp where

open import TypeSystem
open import Graph.Target
import Graph.Span as GraphSpan

record IsFunctor {a b} (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
   constructor con
   field
     map : ∀ {A B :{#} Set a} → (B → A) → F A → F B
     map-id : ∀ {A :{#} Set a} {x} → map (\ (x : A) → x) x ≡ x
     map-∘ : ∀ {A B C :{#} Set a} → (f : C → B) → (g : B → A) → ∀ {x} → map f (map g x) ≡ map (g ∘ f) x


map : ∀ {a b} {F :{#} Set a → Set b} → ([F] : IsFunctor F) → ∀ {A B :{#} Set a} → (B → A) → F A → F B
map (con x _ _) = x

map-id : ∀ {a b} {F :{#} Set a → Set b} → ([F] : IsFunctor F) → ∀ {A :{#} Set a} {x} → map [F] (\ (x : A) → x) x ≡ x
map-id (con _ x _) = x

map-∘ : ∀ {a b} {F :{#} Set a → Set b} → ([F] : IsFunctor F) → ∀ {A B C :{#} Set a} → (f : C → B) → (g : B → A)
        → ∀ {x} → map [F] f (map [F]  g x) ≡ map [F] (g ∘ f) x
map-∘ (con x _ y) = y

module Proof¶ {a}{b} (F G :{#} Set a → Set b) ([F] : IsFunctor F) ([G] : IsFunctor G)
                 (eta : ∀ (A :{#} Set a) → F A → G A)
                 (A B :{#} Set a) (f :{¶} B → A) where

  /f/ :{#} 𝕀 → Set a
  /f/ = / f /

  eta-nat : ∀ x → (map [G] f ∘ eta A) x ≡ (eta B ∘ map [F] f) x
  eta-nat x = sym (trans (sym (map-id [G]))
             (trans (path-to-eq (\ i → map [G] (push f i) (eta (/f/ i) (map [F] (pull f i) x))))
                    (cong (map [G] f ∘ eta A) (map-id [F]))))


module ProofId {a} {b} (F G :{#} Set a → Set b) ([F] : IsFunctor F) ([G] : IsFunctor G)
                 (eta : ∀ (A :{#} Set a) → F A → G A)
                 {A B :{#} Set a} (f : B → A) where

  open GraphSpan f
  module Src = Proof¶ F G [F] [G] eta B T src
  module Tgt = Proof¶ F G [F] [G] eta A T tgt

  eta-nat : ∀ x → (map [G] f ∘ eta A) x ≡ (eta B ∘ map [F] f) x
  eta-nat x = trans (sym (map-∘ [G] inv tgt))
             (trans (cong (map [G] inv) (Tgt.eta-nat x)) (trans (sym (z (map [F] tgt x))) (cong (eta B) (map-∘ [F] inv tgt))))
    where
      q : ∀ z → map [G] inv ((map [G] src ∘ eta B) (map [F] inv z)) ≡
                  map [G] inv ((eta T ∘ map [F] src) (map [F] inv z))
      q z = cong ((map [G] inv)) (Src.eta-nat (map [F] inv z) )
      z : ∀ x → eta B (map [F] inv x) ≡ (map [G] inv ∘ eta T) x
      z x = trans ( (trans (trans
                (sym (map-id [G]))
                (cong (let H = _ in λ f₁ → map [G] f₁ H) (sym (funext src-inv)))
                )
                (sym (map-∘ [G] inv src))) )
         (trans (q x)
       (  (cong  (map [G] inv ∘ eta T)
         (trans (map-∘ [F] src inv)
                (trans ((cong (let H = _ in λ f₁ → map [F] f₁ H) ((funext inv-src)))) (map-id [F]) ))) ))
