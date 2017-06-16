{-# OPTIONS --rewriting #-}
module Graph.Span {a b} {A :{#} Set a} {B :{#} Set b} (f : A → B) where

open import TypeSystem

T :{#} Set _
T = Σ A (\ a → Σ B \ b → f a ≡ b)

src :{¶} T → A
src = fst

tgt :{¶} T → B
tgt x = fst (snd x)

inv : A → T
inv x = [ x , [ f x , refl _ ] ]

src-inv : ∀ x → src (inv x) ≡ x
src-inv x = refl _

inv-src : ∀ x → (inv (src x)) ≡ x
inv-src = #uncurry (\ x → #uncurry (\ b p → J p (λ y w → inv (src [ x , [ y , w ] ]) ≡ [ x , [ y , w ] ]) (refl _)))

tgt-inv : ∀ x → tgt (inv x) ≡ f x
tgt-inv x = refl _
