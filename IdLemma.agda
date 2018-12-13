{-# OPTIONS --rewriting --cubical #-}
module IdLemma where
open import Primitives
open import TypeSystem
open import Graph.Target


module M (A :{ # } Set) (B :{ # } A → Set) where
    G :{ # } 𝕀 → Set
    G = / fst {_} {_} {A} {B} /

    lemma : (b : ( i :{ # } 𝕀) → G i) → fst (b b0) ≡ (b b1)
    lemma b = path-to-eq (\ i → pull {_} {Σ A B} {A} fst i (b i))

    lemma2 : (b : ( i :{ # } 𝕀) → G i) → B (b b1)
    lemma2 b = subst B (lemma b) (snd (b b0))

    pushG : (i :{#} 𝕀) → Σ A B → G i
    pushG = push fst


id-lemma : (f : (A :{ # } Set) → A → A) (A :{ # } Set) → (x : A) → x ≡ f A x
id-lemma f A x = lemma2 (\ i → f (G i) (pushG i [ x , refl _ ]))
 where
   open M A (_≡_ x)


