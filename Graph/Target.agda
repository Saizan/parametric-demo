{-# OPTIONS --rewriting --cubical #-}
open import Primitives
open import TypeSystem

module Graph.Target where

  --Build a bridge that encodes the graph relation of a function, based on the function's target, using Glue.
  /_/ : ∀{ℓ}{C D : Set ℓ} → (f :{¶} C → D) → (𝕀 → Set ℓ)
  /_/ {ℓ}{C}{D} f i = Glue
                      D
                      ((i ≣ i0) ∨ (i ≣ i1))
                      (λ { ((i ≣ i0) = p⊤) → C
                         ; ((i ≣ i1) = p⊤) → D
                         })
                      (λ { ((i ≣ i0) = p⊤) → f
                         ; ((i ≣ i1) = p⊤) → id
                         })

  push : ∀{ℓ} {C D :{#} Set ℓ} (f :{¶} C → D) (i :{#} 𝕀) → C → / f / i
  push {ℓ}{C}{D} f i c = glue
                      {φ = (i ≣ i0) ∨ (i ≣ i1)}
                      (λ { ((i ≣ i0) = p⊤) → c
                         ; ((i ≣ i1) = p⊤) → f c
                         })
                      (f c)

  pull : ∀{ℓ} {C D :{#} Set ℓ} (f :{¶} C → D) (i :{#} 𝕀) → / f / i → D
  pull f i q = unglue {φ = (i ≣ i0) ∨ (i ≣ i1)} q
