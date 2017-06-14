{-# OPTIONS --rewriting --cubical #-}
open import Primitives
open import TypeSystem

module Graph.Source where

  --Build a bridge that encodes the graph relation of a function, based on the function's source, using Weld.
  /_/ : ∀{ℓ}{C D : Set ℓ} (f :{¶} C → D) → (𝕀 → Set ℓ)
  /_/ {ℓ}{C}{D} f i = Weld
                        C
                        ((i ≣ i0) ∨ (i ≣ i1))
                        (λ { ((i ≣ i0) = p⊤) → C
                           ; ((i ≣ i1) = p⊤) → D
                           })
                        (λ { ((i ≣ i0) = p⊤) → id
                           ; ((i ≣ i1) = p⊤) → f
                           })

  push : ∀{ℓ}  {C D :{#} Set ℓ} (f :{¶} C → D) (i :{#} 𝕀) → C → / f / i
  push {ℓ}{C}{D} f i c = weld {φ = (i ≣ i0) ∨ (i ≣ i1)} c

  pull : ∀{ℓ}  {C D :{#} Set ℓ} (f :{¶} C → D) (i :{#} 𝕀) → / f / i → D
  pull {ℓ}{C}{D} f i q = mweld {φ = (i ≣ i0) ∨ (i ≣ i1)} {C = λ _ → D} (λ c → f c)
                          (λ { ((i ≣ i0) = p⊤) → f
                             ; ((i ≣ i1) = p⊤) → id
                             })
                          q
