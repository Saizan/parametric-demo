{-# OPTIONS --without-K --rewriting #-}

open import lib.Base -- using (_==_; refl)

module lib.PathGroupoid where

module _ {i} {A :{ # } Set i} where

  {- Concatenation of paths

  There are two different definitions of concatenation of paths, [_∙_] and [_∙'_],
  with different definitionnal behaviour. Maybe we should have only one but it’s
  sometimes useful to have both (in particular in lib.types.Paths).
  -}

  infixr 8 _∙_ -- _∙'_

  _∙_ : {x y z : A}
    → (x == y → y == z → x == z)
  _∙_ {x} {y} {z} p = J p (\ y p → y ≡ z → x ≡ z) (\ x → x)

  -- _∙'_ : {x y z : A}
  --   → (x == y → y == z → x == z)
  -- q ∙' idp = q

  -- ∙=∙' : {x y z : A} (p : x == y) (q : y == z)
  --   → p ∙ q == p ∙' q
  -- ∙=∙' idp idp = idp

  -- ∙'=∙ : {x y z : A} (p : x == y) (q : y == z)
  --   → p ∙' q == p ∙ q
  -- ∙'=∙ idp idp = idp

  ∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc {x} {y} {z} {t} p q r = J p (\ _ p → (q : _) (r : _) → (p ∙ q) ∙ r == p ∙ (q ∙ r)) (\ _ _ → refl _) q r

  -- ∙'-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
  --   → (p ∙' q) ∙' r == p ∙' (q ∙' r)
  -- ∙'-assoc refl _ refl _ refl _ = refl _

  -- [∙-unit-l] and [∙'-unit-r] are definitional
  -- ∙-unit-l : {x y : A} (q : x == y) → refl _ ∙ q == q
  -- ∙-unit-l q = J q (\ _ q → refl _ ∙ q == q) (refl _) -- refl --refl _ = refl _

  ∙-unit-r : {x y : A} (q : x == y) → q ∙ refl _ == q
  ∙-unit-r q = J q (\ _ q → q ∙ refl _ == q) (refl _)

  -- ∙'-unit-l : {x y : A} (q : x == y) → refl _ ∙' q == q
  -- ∙'-unit-l refl _ = refl _

  {- Reversal of paths -}

  ! : {x y : A} → (x == y → y == x)
  ! = sym

  !-inv-l : {x y : A} (p : x == y) → (! p) ∙ p == refl _
  !-inv-l p = J p (\ _ p → (! p) ∙ p == refl _) (refl _)  -- refl _ = refl _

  -- !-inv'-l : {x y : A} (p : x == y) → (! p) ∙' p == refl _
  -- !-inv'-l refl _ = refl _

  !-inv-r : {x y : A} (p : x == y) → p ∙ (! p) == refl _
  !-inv-r p = J p (\ _ p → p ∙ (! p) == refl _) (refl _) -- refl _ = refl _

  -- !-inv'-r : {x y : A} (p : x == y) → p ∙' (! p) == refl _
  -- !-inv'-r refl _ = refl _

  -- {- Interactions between operations

  -- A lemma of the form [!-∙ …] gives a result of the form [! (_∙_ …) == …],
  -- and so on.
  -- -}

  -- !-∙ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) == ! q ∙ ! p
  -- !-∙ refl _ refl _ = refl _

  -- ∙-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙ ! p == ! (p ∙ q)
  -- ∙-! refl _ refl _ = refl _

  -- !-∙' : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙' q) == ! q ∙' ! p
  -- !-∙' refl _ refl _ = refl _

  -- ∙'-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙' ! p == ! (p ∙' q)
  -- ∙'-! refl _ refl _ = refl _

  -- !-! : {x y : A} (p : x == y) → ! (! p) == p
  -- !-! refl _ = refl _

  -- {- Horizontal compositions -}

  -- _∙2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
  --   → p ∙ q == p' ∙ q'
  -- _∙2_ {p = refl _} refl _ β = β

  -- _∙'2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
  --   → p ∙' q == p' ∙' q'
  -- _∙'2_ {q = refl _} α refl _ = α

  -- refl _∙2refl _ : {x y z : A} (p : x == y) (q : y == z)
  --   → ((refl _ {x = p}) ∙2 (refl _ {x = q})) == refl _
  -- refl _∙2refl _ refl _ refl _ = refl _

  -- refl _∙'2refl _ : {x y z : A} (p : x == y) (q : y == z)
  --   → ((refl _ {x = p}) ∙'2 (refl _ {x = q})) == refl _
  -- refl _∙'2refl _ refl _ refl _ = refl _

-- {-
-- Sometimes we need to restart a new section in order to have everything in the
-- previous one generalized.
-- -}
-- module _ {i} {A : Set i} where
--   {- Whisker and horizontal composition for Eckmann-Hilton argument -}
--   _∙ᵣ_ : {x y z : A} {p p' : x == y} (α : p == p') (q : y == z)
--     → p ∙ q == p' ∙ q
--   _∙ᵣ_ {p = p} {p' = p'} α refl _ = ∙-unit-r p ∙ α ∙ ! (∙-unit-r p')

--   _∙ₗ_ : {x y z : A} {q q' : y == z} (p : x == y) (β : q == q')
--     → p ∙ q == p ∙ q'
--   _∙ₗ_ {q = q} {q' = q'} refl _ β = β

--   _⋆2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
--          (α : p == p') (β : q == q')
--     → p ∙ q == p' ∙ q'
--   _⋆2_ {p' = p'} {q = q} α β = (α ∙ᵣ q) ∙ (p' ∙ₗ β)

--   _⋆'2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
--           (α : p == p') (β : q == q')
--     → p ∙ q == p' ∙ q'
--   _⋆'2_ {p = p} {q' = q'} α β = (p ∙ₗ β) ∙ (α ∙ᵣ q')

--   infix 4 _⋆'2_

--   ⋆2=⋆'2 : {x y z : A} {p p' : x == y} {q q' : y == z}
--            (α : p == p') (β : q == q')
--     → α ⋆2 β == α ⋆'2 β
--   ⋆2=⋆'2 {p = refl _} {q = refl _} refl _ refl _ = refl _

--   infix 4 _⋆2_

module _ {i} {A :{ # } Set i} where

  anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
    → (q ∙ p == r ∙ p → q == r)
  anti-whisker-right {x} p {q} {r} h = J p (λ z p₁ → q ∙ p₁ == r ∙ p₁ → q == r) (\ x → ! (∙-unit-r q) ∙ x ∙ ∙-unit-r r) h

  -- anti-whisker-left : {x y z : A} (p : x == y) {q r : y == z}
  --   → (p ∙ q == p ∙ r → q == r)
  -- anti-whisker-left refl _ h = h


-- {- Dependent stuff -}
-- module _ {i j} {A : Set i} {B : A → Set j} where

--   {- Dependent constant path -}

--   refl _ᵈ : {x : A} {u : B x} → u == u [ B ↓ refl _ ]
--   refl _ᵈ = refl _

--   {- Dependent opposite path -}

--   !ᵈ : {x y : A} {p : x == y} {u : B x} {v : B y}
--     → (u == v [ B ↓ p ] → v == u [ B ↓ (! p)])
--   !ᵈ {p = refl _} = !

--   {- Dependent concatenation -}
--   infix 20 _∙ᵈ_
--   _∙ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
--     {u : B x} {v : B y} {w : B z}
--     → (u == v [ B ↓ p ]
--     → v == w [ B ↓ p' ]
--     → u == w [ B ↓ (p ∙ p') ])
--   _∙ᵈ_ {p = refl _} {p' = refl _} q r = q ∙ r

--   _◃_ = _∙ᵈ_

--   infix 4 _◃_
--   ◃refl _ : {x : A} {v w : B x} (q : w == v)
--     → q ◃ refl _ == q
--   ◃refl _ refl _ = refl _

--   refl _◃ : {x y : A} {p : x == y}
--     {u : B x} {v : B y} (r : u == v [ B ↓ p ])
--     → refl _ ◃ r == r
--   refl _◃ {p = refl _} r = refl _

--   infix 20 _∙'ᵈ_
--   _∙'ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
--     {u : B x} {v : B y} {w : B z}
--     → (u == v [ B ↓ p ]
--     → v == w [ B ↓ p' ]
--     → u == w [ B ↓ (p ∙' p') ])
--   _∙'ᵈ_ {p = refl _} {p' = refl _} q r = q ∙' r

--   _▹_ = _∙'ᵈ_

--   infix 4 _▹_
--   {- That’s not perfect, because [q] could be a dependent path. But in that case
--      this is not well typed… -}
--   refl _▹ : {x : A} {v w : B x} (q : v == w)
--     → refl _ ▹ q == q
--   refl _▹ refl _ = refl _

--   ▹refl _ : {x y : A} {p : x == y}
--     {u : B x} {v : B y} (q : u == v [ B ↓ p ])
--     → q ▹ refl _ == q
--   ▹refl _ {p = refl _} refl _ = refl _

--   infix 4 _▹!_

--   _▹!_ : {x y z : A} {p : x == y} {p' : z == y}
--     {u : B x} {v : B y} {w : B z}
--     → u == v [ B ↓ p ]
--     → w == v [ B ↓ p' ]
--     → u == w [ B ↓ p ∙' (! p') ]
--   _▹!_ {p' = refl _} q refl _ = q

--   refl _▹! : {x : A} {v w : B x} (q : w == v)
--     → refl _ ▹! q == ! q
--   refl _▹! refl _ = refl _

--   infix 4 _!◃_

--   _!◃_ : {x y z : A} {p : y == x} {p' : y == z}
--     {u : B x} {v : B y} {w : B z}
--     → v == u [ B ↓ p ]
--     → v == w [ B ↓ p' ]
--     → u == w [ B ↓ (! p) ∙ p' ]
--   _!◃_ {p = refl _} refl _ q = q

--   !◃refl _ : {x : A} {v w : B x} (q : v == w)
--     → q !◃ refl _ == ! q
--   !◃refl _ refl _ = refl _


--   {-
--   This is some kind of dependent horizontal composition (used in [apd∙]).
--   -}
--   infix 4 _∙2ᵈ_
--   _∙2ᵈ_ : {x y z : Π A B}
--     {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
--     {r : y a == z a} {r' : y a' == z a'}
--     → (q == q'            [ (λ a → x a == y a) ↓ p ])
--     → (r == r'            [ (λ a → y a == z a) ↓ p ])
--     → (q ∙ r == q' ∙ r' [ (λ a → x a == z a) ↓ p ])
--   _∙2ᵈ_ {p = refl _} α β = α ∙2 β

--   infix 4 _∙'2ᵈ_
--   _∙'2ᵈ_ : {x y z : Π A B}
--     {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
--     {r : y a == z a} {r' : y a' == z a'}
--     → (q == q'            [ (λ a → x a == y a) ↓ p ])
--     → (r == r'            [ (λ a → y a == z a) ↓ p ])
--     → (q ∙' r == q' ∙' r' [ (λ a → x a == z a) ↓ p ])
--   _∙'2ᵈ_ {p = refl _} α β = α ∙'2 β

--   {-
--   [apd∙] reduces a term of the form [apd (λ a → q a ∙ r a) p], do not confuse it
--   with [apd-∙] which reduces a term of the form [apd f (p ∙ q)].
--   -}

--   apd∙ : {a a' : A} {x y z : Π A B}
--     (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
--     (p : a == a')
--     → apd (λ a → q a ∙ r a) p == apd q p ∙2ᵈ apd r p
--   apd∙ q r refl _ = ! (refl _∙2refl _ (q _) (r _))

--   apd∙' : {a a' : A} {x y z : Π A B}
--     (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
--     (p : a == a')
--     → apd (λ a → q a ∙' r a) p == apd q p ∙'2ᵈ apd r p
--   apd∙' q r refl _ = ! (refl _∙'2refl _ (q _) (r _))

-- module _ {i j} {A : Set i} {B : A → Set j} where

--   {- Exchange -}

--   ▹-∙'2ᵈ : {x y z : Π A B}
--     {a a' a'' : A} {p : a == a'} {p' : a' == a''}
--     {q0 : x a == y a} {q0' : x a' == y a'}
--     {r0 : y a == z a} {r0' : y a' == z a'}
--     {q0'' : x a'' == y a''} {r0'' : y a'' == z a''}
--     (q : q0 == q0' [ (λ a → x a == y a) ↓ p ])
--     (r : r0 == r0' [ (λ a → y a == z a) ↓ p ])
--     (s : q0' == q0'' [ (λ a → x a == y a) ↓ p' ])
--     (t : r0' == r0'' [ (λ a → y a == z a) ↓ p' ])
--     → (q ∙'2ᵈ r) ▹ (s ∙'2ᵈ t) == (q ▹ s) ∙'2ᵈ (r ▹ t)
--   ▹-∙'2ᵈ {p = refl _} {p' = refl _} {q0} {.q0} {r0} {.r0} refl _ refl _ refl _ refl _ =
--     ap (λ u → (refl _ {x = q0} ∙'2 refl _ {x = r0}) ∙' u) (refl _∙'2refl _ q0 r0)
