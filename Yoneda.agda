module Yoneda where

open import TypeSystem
open import Naturality

module Proof {a}
  (F :{#} Set a → Set a)
  ([F] : IsFunctor F)
  (A :{#} Set a)
  where

  [A→] : IsFunctor {a} (\ X → A → X)
  [A→] = con (λ f g x → f (g x)) (refl _) (λ _ _ → refl _)

  module M = ProofId _ _ [A→] [F]

  Yoneda :{#} Set _
  Yoneda = (X :{#} Set a) → (A → X) → F X

  fwd : Yoneda → F A
  fwd f = f A (\ x → x)

  bwd : F A → Yoneda
  bwd x = \ X r → map [F] r x

  fwd-bwd : ∀ x → fwd (bwd x) ≡ x
  fwd-bwd x = map-id [F]

  bwd-fwd : ∀ x → bwd (fwd x) ≡ x
  bwd-fwd x = #funext (\ X → funext (\ r → M.eta-nat x _ _ r (\ x → x)))

  fwd-inj : ∀ x y → fwd x ≡ fwd y → x ≡ y
  fwd-inj x y p = trans (sym (bwd-fwd x)) (trans (cong bwd p) (bwd-fwd y))


module UniqueMap {a}
    (F :{#} Set a → Set a)
    ([F] : IsFunctor F)
    (map' : ∀ {A B :{#} Set a} → (A → B) → F A → F B)
    (map-id' : ∀ {A :{#} Set a}{x} → map' (\ (x : A) → x) x ≡ x)
      where


    unique-map : ∀ {A B :{#} Set a} → map [F] {A} {B} ≡ map'
    unique-map {A} {B} = funext (\ f → funext (\ x → cong (\ h → h B f)
                           (fwd-inj (\ (B :{#} _) (f : A → B) → map [F] f x) (\ B f → map' f x)
                           (trans (map-id [F]) (sym map-id')))))
       where
        open Proof F [F] A
