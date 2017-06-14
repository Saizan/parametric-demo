{-# OPTIONS --cubical --rewriting #-}
open import Primitives public
--open import Agda.Primitive public

module Church.FibredBy where

open import TypeSystem public

--------------------------------------------------

_fibred-by_ : ∀{ℓX ℓY} (X : Set ℓX) {Y : Set ℓY} (f : X → Y) → Set (ℓY ⊔ ℓX)
_fibred-by_ {ℓX}{ℓY} X {Y} f = Σ[ y ∈ Y ] Σ[ x ∈ X ] (f x ≡ y)

fibre-by : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} (f : X → Y) → X → X fibred-by f
fibre-by f x = [ f x , [ x , refl _ ] ]

unfibre : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} {f :{#} X → Y} → X fibred-by f → X
unfibre p = fst (snd p)

unfibre-by : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} (f :{#} X → Y) → X fibred-by f → X
unfibre-by f p = fst (snd p)

get-image : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} {f :{#} X → Y} → X fibred-by f → Y
get-image = fst

fib-lemma : ∀{ℓX ℓY} {X :{#} Set ℓX} {Y :{#} Set ℓY} (f :{#} X → Y) → f ∘ unfibre-by f ≡ get-image
fib-lemma f = funext λ p → snd (snd p)

