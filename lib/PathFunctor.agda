{-# OPTIONS --without-K --rewriting #-}

open import lib.Base using (_==_; ap; _∘_; idf; _$_; refl; J)
open import lib.PathGroupoid using (_∙_; !; ∙-unit-r; anti-whisker-right)

module lib.PathFunctor {i} {A :{ # } Set i} where

-- {- Nondependent stuff -}
-- module _ {j} {B : Type j} (f : A → B) where

--   !-ap : {x y : A} (p : x == y)
--     → ! (ap f p) == ap f (! p)
--   !-ap idp = idp

--   ap-! : {x y : A} (p : x == y)
--     → ap f (! p) == ! (ap f p)
--   ap-! idp = idp

--   ∙-ap : {x y z : A} (p : x == y) (q : y == z)
--     → ap f p ∙ ap f q == ap f (p ∙ q)
--   ∙-ap idp q = idp

--   ap-∙ : {x y z : A} (p : x == y) (q : y == z)
--     → ap f (p ∙ q) == ap f p ∙ ap f q
--   ap-∙ idp q = idp

--   ∙'-ap : {x y z : A} (p : x == y) (q : y == z)
--     → ap f p ∙' ap f q == ap f (p ∙' q)
--   ∙'-ap p idp = idp

--   ap-∙' : {x y z : A} (p : x == y) (q : y == z)
--     → ap f (p ∙' q) == ap f p ∙' ap f q
--   ap-∙' p idp = idp

-- {- Dependent stuff -}
-- module _ {j} {B : A → Type j} (f : Π A B) where

--   apd-∙ : {x y z : A} (p : x == y) (q : y == z)
--     → apd f (p ∙ q) == apd f p ∙ᵈ apd f q
--   apd-∙ idp idp = idp

--   apd-∙' : {x y z : A} (p : x == y) (q : y == z)
--     → apd f (p ∙' q) == apd f p ∙'ᵈ apd f q
--   apd-∙' idp idp = idp

-- {- Over stuff -}
-- module _ {j k} {B : A → Type j} {C : A → Type k} (f : {a : A} → B a → C a) where

--   ap↓-◃ : {x y z : A} {u : B x} {v : B y} {w : B z}
--     {p : x == y} {p' : y == z} (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
--     → ap↓ f (q ◃ r) == ap↓ f q ◃ ap↓ f r
--   ap↓-◃ {p = idp} {p' = idp} idp idp = idp

--   ap↓-▹! : {x y z : A} {u : B x} {v : B y} {w : B z}
--     {p : x == y} {p' : z == y} (q : u == v [ B ↓ p ]) (r : w == v [ B ↓ p' ])
--     → ap↓ f (q ▹! r) == ap↓ f q ▹! ap↓ f r
--   ap↓-▹! {p = idp} {p' = idp} idp idp = idp

{- Fuse and unfuse -}

∘-ap : ∀ {j k} {B :{ # } Set j} {C :{ # } Set k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap g (ap f p) == ap (g ∘ f) p
∘-ap {j} {k} g f {x} p = J {i} {k}  p (\ _ p →  ap g (ap f p) == ap (g ∘ f) p  ) (refl _)

ap-∘ : ∀ {j k} {B :{ # } Set j} {C :{ # } Set k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
ap-∘ g f p = ! (∘-ap g f p)
-- J p (\ _ p → ap (g ∘ f) p == ap g (ap f p)) (refl _)

-- ap-cst : ∀ {j} {B : Set j} (b : B) {x y : A} (p : x == y)
--   → ap (cst b) p == idp
-- ap-cst b idp = idp

ap-idf : {u v : A} (p : u == v) → ap (idf A) p == p
ap-idf p = J p (\ _ p → ap (idf A) p == p) (refl _)

-- {- Functoriality of [coe] -}

-- coe-∙ : {B C : Set i} (p : A == B) (q : B == C) (a : A)
--   → coe (p ∙ q) a == coe q (coe p a)
-- coe-∙ idp q a = idp

-- coe-! : {B : Set i} (p : A == B) → coe (! p) == coe! p
-- coe-! idp = idp

-- coe!-inv-r : {B : Set i} (p : A == B) (b : B)
--   → coe p (coe! p b) == b
-- coe!-inv-r idp b = idp

-- coe!-inv-l : {B : Set i} (p : A == B) (a : A)
--   → coe! p (coe p a) == a
-- coe!-inv-l idp a = idp

-- coe-inv-adj : {B : Set i} (p : A == B) (a : A) →
--   ap (coe p) (coe!-inv-l p a) == coe!-inv-r p (coe p a)
-- coe-inv-adj idp a = idp

-- coe!-inv-adj : {B : Set i} (p : A == B) (b : B) →
--   ap (coe! p) (coe!-inv-r p b) == coe!-inv-l p (coe! p b)
-- coe!-inv-adj idp b = idp

-- coe-ap-! : ∀ {j} (P : A → Set j) {a b : A} (p : a == b)
--   (x : P b)
--   → coe (ap P (! p)) x == coe! (ap P p) x
-- coe-ap-! P idp x = idp

-- {- Functoriality of transport -}
-- trans-∙ : ∀ {j} {B : A → Set j} {x y z : A}
--   (p : x == y) (q : y == z) (b : B x)
--   → transport B (p ∙ q) b == transport B q (transport B p b)
-- trans-∙ idp _ _ = idp

-- trans-∙' : ∀ {j} {B : A → Set j} {x y z : A}
--   (p : x == y) (q : y == z) (b : B x)
--   → transport B (p ∙' q) b == transport B q (transport B p b)
-- trans-∙' _ idp _ = idp

{- Naturality of homotopies -}

htpy-natural : ∀ {j} {B :{ # } Set j} {x y : A} {f g : A → B}
  (p : ∀ x → (f x == g x)) (q : x == y) → ap f q ∙ p y == p x ∙ ap g q
htpy-natural {x = x} {y} {f} {g} p q = J q (\ y q → ap f q ∙ p y == p x ∙ ap g q) (! (∙-unit-r _))

htpy-natural-toid : {f : A → A}
  (p : ∀ (x : A) → f x == x) → (∀ x → ap f (p x) == p (f x))
htpy-natural-toid {f = f} p x = anti-whisker-right (p x) $
  htpy-natural p (p x) ∙ ap (λ q → p (f x) ∙ q) (ap-idf (p x))

-- {- for functions with two arguments -}

-- module _ {j k} {B : Set j} {C : Set k} (f : A → B → C) where

--   ap2 : {x y : A} {w z : B}
--     → (x == y) → (w == z) → f x w == f y z
--   ap2 idp idp = idp

--   ap2-out : {x y : A} {w z : B} (p : x == y) (q : w == z)
--     → ap2 p q == ap (λ u → f u w) p ∙ ap (λ v → f y v) q
--   ap2-out idp idp = idp

--   ap2-idp-l : {x : A} {w z : B} (q : w == z)
--     → ap2 (idp {x = x}) q == ap (f x) q
--   ap2-idp-l idp = idp

--   ap2-idp-r : {x y : A} {w : B} (p : x == y)
--     → ap2 p (idp {x = w}) == ap (λ z → f z w) p
--   ap2-idp-r idp = idp

-- -- unsure where this belongs
-- trans-pathfrom : ∀ {a x y : A} (p : x == y) (q : a == x)
--   → transport (λ x → a == x) p q == q ∙ p
-- trans-pathfrom idp q = ! (∙-unit-r q)
