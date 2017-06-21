{-# OPTIONS --rewriting #-}
module Yoneda where

open import TypeSystem hiding (ι)
open import Naturality

module Proof {a}
  (F :{#} Set a → Set a)
  ([F] : IsFunctor F)
  (A :{#} Set a)
  where

  [A→] : IsFunctor {a} (λ X → A → X)
  [A→] = con (λ f g x → f (g x)) (refl _) (λ _ _ → refl _)

  module M = ProofId _ _ [A→] [F]

  Yoneda :{#} Set _
  Yoneda = (X :{#} Set a) → (A → X) → F X

  fwd : Yoneda → F A
  fwd f = f A (λ x → x)

  bwd : F A → Yoneda
  bwd x = λ X r → map [F] r x

  fwd-bwd : ∀ x → fwd (bwd x) ≡ x
  fwd-bwd x = map-id [F]

  bwd-fwd : ∀ x → bwd (fwd x) ≡ x
  bwd-fwd x = #funext (λ X → funext (λ r → M.eta-nat x _ _ r (λ x → x)))

  fwd-inj : ∀ x y → fwd x ≡ fwd y → x ≡ y
  fwd-inj x y p = trans (sym (bwd-fwd x)) (trans (cong bwd p) (bwd-fwd y))

-- Corollary: all implementations of map for a given functor are the same.
module UniqueMap {a}
    (F :{#} Set a → Set a)
    ([F] : IsFunctor F)
    (map' : ∀ {A B :{#} Set a} → (A → B) → F A → F B)
    (map-id' : ∀ {A :{#} Set a}{x} → map' (λ (x : A) → x) x ≡ x)
      where


    unique-map : ∀ {A B :{#} Set a} → map [F] {A} {B} ≡ map'
    unique-map {A} {B} = funext (λ f → funext (λ x → cong (λ h → h B f)
                           (fwd-inj (λ (B :{#} _) (f : A → B) → map [F] f x) (λ B f → map' f x)
                           (trans (map-id [F]) (sym map-id')))))
       where
        open Proof F [F] A


module CoProof {a}
  (F :{#} Set a → Set a)
  ([F] : IsFunctor F)
  (A :{#} Set a)
  where

  CoYoneda :{#} Set _
  CoYoneda = #Σ (Set a) λ X → (X → A) × F X

  ι : ∀ {X :{#} Set a} → (X → A) → F X → CoYoneda
  ι {X} r x = [# X , [ r , x ] ]

  ι-nat : ∀ {X Y :{#} Set a} (f : X → Y) → ∀ (r : Y → A) x → ι (r ∘ f) x ≡ ι r (map [F] f x)
  ι-nat f r x = sym (cong (λ h → h x) (q (λ X r → ι (lower r)) f (lift r)))  where
    import NaturalityOp as N
    q = N.ProofId.eta-nat (λ X → Lift (X → A)) (λ X → F X → CoYoneda)
         (N.con (λ f x → lift (λ y → lower x (f y)))
                (refl _) (λ f g → refl _))
         (N.con (λ f x y → x (map [F] f y))
                (λ {A} {x} → funext (λ _ → cong x (map-id [F])))
                (λ f g {x} → funext (λ a → cong x (map-∘ [F] g f))))

  fwd : CoYoneda → F A
  fwd = uncurry# λ X → #uncurry λ f x → map [F] f x

  bwd : F A → CoYoneda
  bwd x = [# A , [ (λ x → x) , x ] ]

  fwd-bwd : ∀ x → fwd (bwd x) ≡ x
  fwd-bwd x = map-id [F]

  bwd-fwd : ∀ x → bwd (fwd x) ≡ x
  bwd-fwd = uncurry# λ X → #uncurry λ f x → sym (ι-nat f (λ x → x) x)
