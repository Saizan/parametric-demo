{-# OPTIONS --rewriting --cubical #-}
open import Primitives
open import TypeSystem

module GlueWeldIsos where

record _≅_ {ℓA ℓB} (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
  field
    fwd : A → B
    bck : B → A
    src-id : bck ∘ fwd ≡ id
    tgt-id : fwd ∘ bck ≡ id
open _≅_

glueSrc : ∀{ℓ φ} (A B :{#} Set ℓ) (T :{#} Partial (Set ℓ) φ) (f :{¶} PartialP φ (λ o → T o → A))
  → (Glue A φ T f → B) ≅ (Weld (A → B) φ (λ o → T o → B) (λ o g → g ∘ f o))
fwd (glueSrc {ℓ} {φ} A B T f) = {!!}
bck (glueSrc {ℓ} {φ} A B T f) wg = mweld {φ = φ}
                                  (λ g ga → g (unglue {φ = φ} ga))
                                  (λ{(φ = p⊤) h → h})
                                  wg
src-id (glueSrc {ℓ} {φ} A B T f) = {!!}
tgt-id (glueSrc {ℓ} {φ} A B T f) = {!!}

weldSrc : ∀{ℓ φ} (A B :{#} Set ℓ) (T :{#} Partial (Set ℓ) φ) (f :{¶} PartialP φ (λ o → A → T o))
  → (Weld A φ T f → B) ≅ (Glue (A → B) φ (λ o → T o → B) (λ o gφ → gφ ∘ f o))
weldSrc {ℓ} {φ} A B T f = record
  { fwd = fwd'
  ; bck = bck'
  ; src-id = funext (λ wg → funext (λ wa → ((bck' ∘ fwd') wg wa ≡ wg wa) ∋
                mweld {φ = φ}
                {C = λ wa' → (bck' ∘ fwd') wg wa' ≡ wg wa'}
                (λ a → refl _)
                (λ {(φ = p⊤) → λ t → refl _})
                wa
             ))
  ; tgt-id = funext (λ gf → {!need η for glue here!})
  }
  where
    fwd' = λ wg → glue {φ = φ}
                  (λ {(φ = p⊤) → wg})
                  (wg ∘ weld {φ = φ})
    bck' = λ gg wa → mweld {φ = φ}
                     (unglue {φ = φ} gg)
                     (λ {(φ = p⊤) → gg})
                     wa

glueTgt : ∀{ℓ φ} (A B :{#} Set ℓ) (T :{#} Partial (Set ℓ) φ) (f :{¶} PartialP φ (λ o → T o → B))
  → (A → Glue B φ T f) ≅ (Glue (A → B) φ (λ o → A → T o) (λ o gφ → f o ∘ gφ))
fwd (glueTgt {ℓ} {φ} A B T f) gf = glue {φ = φ}
                                   (λ {(φ = p⊤) → gf})
                                   (unglue {φ = φ} ∘ gf)
bck (glueTgt {ℓ} {φ} A B T f) gf a = glue {φ = φ}
                                     (λ {(φ = p⊤) → gf a})
                                     (unglue {φ = φ} gf a)
src-id (glueTgt {ℓ} {φ} A B T f) = funext (λ gf → funext (λ a → {!we need η for glue here!}))
tgt-id (glueTgt {ℓ} {φ} A B T f) = funext (λ gf → {!we need η for glue here!})

weldTgt : ∀{ℓ} {φ :{#} _} (A B :{#} Set ℓ) (T :{#} Partial (Set ℓ) φ) (f :{¶} PartialP φ (λ o → B → T o))
  → (A → Weld B φ T f) ≅ (Weld (A → B) φ (λ o → A → T o) (λ o g → f o ∘ g))
fwd (weldTgt {ℓ} {φ} A B T f) = {!!}
bck (weldTgt {ℓ} {φ} A B T f) wg a = mweld {φ = φ}
                                     (λ g → weld {φ = φ} (g a))
                                     (λ {(φ = p⊤) gφ → gφ a})
                                     wg
src-id (weldTgt {ℓ} {φ} A B T f) = {!!}
tgt-id (weldTgt {ℓ} {φ} A B T f) = {!!}

--Conclusion: currently, Glue and Weld behave exactly like Π and Σ.
--Note: weldTgt does not hold semantically. On the left, different edges with the same source in A,
--may have different sources in B that map to the same thing in T.
