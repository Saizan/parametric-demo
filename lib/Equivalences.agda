{-# OPTIONS --without-K --rewriting #-}

open import lib.Base using (lmax; _==_; ap; _=⟨_⟩_; _∎; idf; refl; _∘_)
open import TypeSystem hiding (_∘_)
open import lib.PathGroupoid using (!; _∙_; !-inv-l; ∙-assoc)
open import lib.PathFunctor using (htpy-natural-toid; ap-idf; htpy-natural; ap-∘; ∘-ap)

module lib.Equivalences where


{-
We use the half-adjoint definition of equivalences (but this fact should be
invisible to the user of the library). The constructor of the type of
equivalences is [equiv], it takes two maps and the two proofs that the composites
are equal: [equiv to from to-from from-to]

The type of equivalences between two types [A] and [B] can be written either
[A ≃ B] or [Equiv A B].

Given an equivalence [e] : [A ≃ B], you can extract the two maps as follows:
[–> e] : [A → B] and [<– e] : [B → A] (the dash is an en dash)
The proofs that the composites are the identities are [<–-inv-l] and [<–-inv-r].

The identity equivalence on [A] is [ide A], the composition of two equivalences
is [_∘e_] (function composition order) and the inverse of an equivalence is [_⁻¹]
-}

module _ {i} {j} {A :{ # } Set i} {B :{ # } Set j} where

  -- record is-equiv (f : A → B) : Set (lmax i j)
  --   where
  --   constructor ise-con
  --   field
  --     g : B → A
  --     f-g : (b : B) → f (g b) == b
  --     g-f : (a : A) → g (f a) == a
  --     adj : (a : A) → ap f (g-f a) == f-g (f a)

  is-equiv :{ # } (f : A → B) → Set (lmax i j)
  is-equiv f = Σ (B → A) \ g → Σ ((b : B) → f (g b) == b) \ f-g → Σ ((a : A) → g (f a) == a) \ g-f → ((a : A) → ap f (g-f a) == f-g (f a))

  module is-equiv {f : A → B} (eq : is-equiv f) where
    g = fst eq
    f-g = fst (snd eq)
    g-f = fst (snd (snd eq))
    adj = snd (snd (snd eq))
  ise-con : {f : A → B} →  (g : B → A)
      (f-g : (b : B) → f (g b) == b)
      (g-f : (a : A) → g (f a) == a)
      (adj : (a : A) → ap f (g-f a) == f-g (f a)) → is-equiv f
  ise-con g f-g g-f adj = [ g , [ f-g , [ g-f , adj ] ] ]

  {-
  In order to prove that something is an equivalence, you have to give an inverse
  and a proof that it’s an inverse (you don’t need the adj part).
  [is-eq] is a very, very bad name.
  -}
  is-eq : (f : A → B)
    (g : B → A) (f-g : (b : B) → f (g b) == b)
    (g-f : (a : A) → g (f a) == a) → is-equiv f
  is-eq f g f-g g-f = ise-con g f-g' g-f adj
   where
    f-g' : (b : B) → f (g b) == b
    f-g' b = ! (ap (f ∘ g) (f-g b)) ∙ ap f (g-f (g b)) ∙ f-g b

    adj : (a : A) → ap f (g-f a) == f-g' (f a)
    adj a =
      ap f (g-f a)
        =⟨ ! (!-inv-l (ap (f ∘ g) (f-g (f a)))) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
      (! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f a)
        =⟨ ∙-assoc (! (ap (f ∘ g) (f-g (f a)))) (ap (f ∘ g) (f-g (f a))) _ ⟩
      ! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
        =⟨ lemma |in-ctx (λ q → ! (ap (f ∘ g) (f-g (f a))) ∙ q) ⟩
      ! (ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f (g (f a))) ∙ f-g (f a) ∎
      where
      lemma : ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
           == ap f (g-f (g (f a))) ∙ f-g (f a)
      lemma =
        ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
          =⟨ htpy-natural-toid f-g (f a) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
        f-g (f (g (f a))) ∙ ap f (g-f a)
          =⟨ ! (ap-idf (ap f (g-f a))) |in-ctx (λ q → f-g (f (g (f a))) ∙ q) ⟩
        f-g (f (g (f a))) ∙ ap (idf B) (ap f (g-f a))
          =⟨ ! (htpy-natural f-g (ap f (g-f a))) ⟩
        ap (f ∘ g) (ap f (g-f a)) ∙ f-g (f a)
          =⟨ ap-∘ f g (ap f (g-f a)) |in-ctx (λ q → q ∙ f-g (f a)) ⟩
        ap f (ap g (ap f (g-f a))) ∙ f-g (f a)
          =⟨ (∘-ap g f (g-f a) ∙ htpy-natural-toid g-f a)
             |in-ctx (λ q → ap f q ∙ f-g (f a)) ⟩
        ap f (g-f (g (f a))) ∙ f-g (f a) ∎

infix 4 _≃_

_≃_ : ∀ {i j} (A : Set i) (B : Set j) → Set (lmax i j)
A ≃ B = Σ (A → B) is-equiv

Equiv = _≃_

module _ {i} {j} {A : Set i} {B : Set j} where

  equiv : (f : A → B) (g : B → A) (f-g : (b : B) → f (g b) == b)
          (g-f : (a : A) → g (f a) == a) → A ≃ B
  equiv f g f-g g-f = [ f , is-eq f g f-g g-f ]

  –> : (e : A ≃ B) → (A → B)
  –> e = fst e

  <– : (e : A ≃ B) → (B → A)
  <– e = is-equiv.g (snd e)

  <–-inv-l : (e : A ≃ B) (a : A)
    → (<– e (–> e a) == a)
  <–-inv-l e a = is-equiv.g-f (snd e) a

  <–-inv-r : (e : A ≃ B) (b : B)
    → (–> e (<– e b) == b)
  <–-inv-r e b = is-equiv.f-g (snd e) b

  <–-inv-adj : (e : A ≃ B) (a : A)
    → ap (–> e) (<–-inv-l e a) == <–-inv-r e (–> e a)
  <–-inv-adj e a = is-equiv.adj (snd e) a

  -- Equivalences are "injective"
  equiv-inj : (e : A ≃ B) {x y : A}
    → (–> e x == –> e y → x == y)
  equiv-inj e {x} {y} p = ! (<–-inv-l e x) ∙ ap (<– e) p ∙ <–-inv-l e y

-- idf-is-equiv : ∀ {i} (A : Set i) → is-equiv (idf A)
-- idf-is-equiv A = is-eq _ (idf A) (λ _ → idp) (λ _ → idp)

-- ide : ∀ {i} (A : Set i) → A ≃ A
-- ide A = equiv (idf A) (idf A) (λ _ → idp) (λ _ → idp)

-- infixr 4 _∘e_
-- -- infixr 4 _∘ise_

-- _∘e_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
--   → B ≃ C → A ≃ B → A ≃ C
-- e1 ∘e e2 = equiv (–> e1 ∘ –> e2) (<– e2 ∘ <– e1)
--   (λ c → –> e1 (–> e2 (<– e2 (<– e1 c)))
--                    =⟨ <–-inv-r e2 (<– e1 c) |in-ctx (–> e1) ⟩
--          –> e1 (<– e1 c)  =⟨ <–-inv-r e1 c ⟩
--          c ∎)
--   (λ a → <– e2 (<– e1 (–> e1 (–> e2 a)))
--                    =⟨ <–-inv-l e1 (–> e2 a) |in-ctx (<– e2) ⟩
--          <– e2 (–> e2 a)  =⟨ <–-inv-l e2 a ⟩
--          a ∎)

-- -- _∘ise_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
-- --   {f : A → B} {g : B → C}
-- --   → is-equiv g → is-equiv f → is-equiv (g ∘ f)
-- -- i1 ∘ise i2 = snd ([ _ , i1 ] ∘e [ _ , i2 ])

-- -- _⁻¹ : ∀ {i j} {A : Set i} {B : Set j} → (A ≃ B) → (B ≃ A)
-- -- e ⁻¹ = equiv (<– e) (–> e) (<–-inv-l e) (<–-inv-r e)

-- {- Equational reasoning for equivalences -}
-- infix  3 _≃∎
-- infixr 2 _≃⟨_⟩_

-- _≃⟨_⟩_ : ∀ {i j k} (A : Set i) {B : Set j} {C : Set k} → A ≃ B → B ≃ C → A ≃ C
-- A ≃⟨ u ⟩ v = v ∘e u

-- _≃∎ : ∀ {i} (A : Set i) → A ≃ A
-- _≃∎ = ide


-- {- lifting is an equivalence -}
-- lift-equiv : ∀ {i j} {A : Set i} → Lift {j = j} A ≃ A
-- lift-equiv = equiv lower lift (λ _ → idp) (λ _ → idp)

-- {- Any contractible type is equivalent to (all liftings of) the unit type -}
-- module _ {i} {A : Set i} (h : is-contr A) where
--   contr-equiv-Unit : A ≃ Unit
--   contr-equiv-Unit = equiv (λ _ → unit) (λ _ → fst h) (λ _ → idp) (snd h)

--   contr-equiv-LiftUnit : ∀ {j} → A ≃ Lift {j = j} Unit
--   contr-equiv-LiftUnit = lift-equiv ⁻¹ ∘e contr-equiv-Unit


-- {- An equivalence induces an equivalence on the path spaces -}
-- module _ {i j} {A : Set i} {B : Set j} (e : A ≃ B) where

--   private
--     abstract
--       left-inverse : {x y : A} (p : x == y) → equiv-inj e (ap (–> e) p) == p
--       left-inverse idp = !-inv-l (<–-inv-l e _)

--       right-inverse : {x y : A} (p : –> e x == –> e y)
--         → ap (–> e) (equiv-inj e p) == p
--       right-inverse {x} {y} p =
--         ap f (! (g-f x) ∙ ap g p ∙ (g-f y))
--           =⟨ ap-∙ f (! (g-f x)) (ap g p ∙ (g-f y)) ⟩
--         ap f (! (g-f x)) ∙ ap f (ap g p ∙ (g-f y))
--           =⟨ ap-∙ f (ap g p) (g-f y) |in-ctx (λ q →  ap f (! (g-f x)) ∙ q) ⟩
--         ap f (! (g-f x)) ∙ ap f (ap g p) ∙ ap f (g-f y)
--           =⟨ ∘-ap f g p |in-ctx (λ q → ap f (! (g-f x)) ∙ q ∙ ap f (g-f y)) ⟩
--         ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ ap f (g-f y)
--           =⟨ adj y |in-ctx (λ q →  ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ q) ⟩
--         ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
--           =⟨ ap-! f (g-f x) |in-ctx (λ q → q ∙ ap (f ∘ g) p ∙ (f-g (f y))) ⟩
--         ! (ap f (g-f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
--           =⟨ adj x |in-ctx (λ q →  ! q ∙ ap (f ∘ g) p ∙ (f-g (f y))) ⟩
--         ! (f-g (f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
--           =⟨ htpy-natural f-g p |in-ctx (λ q →  ! (f-g (f x)) ∙ q) ⟩
--         ! (f-g (f x)) ∙ (f-g (f x)) ∙ ap (idf B) p
--           =⟨ ! (∙-assoc (! (f-g (f x))) (f-g (f x)) (ap (idf B) p))
--              ∙ ap (λ q → q ∙ ap (idf B) p) (!-inv-l (f-g (f x))) ∙ ap-idf p ⟩
--         p ∎
--         where f : A → B
--               f = fst e

--               open is-equiv (snd e)

--   equiv-ap : (x y : A) → (x == y) ≃ (–> e x == –> e y)
--   equiv-ap x y = equiv (ap (–> e)) (equiv-inj e) right-inverse left-inverse

-- {- Equivalent types have the same truncation level -}
-- equiv-preserves-level : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ₋₂} (e : A ≃ B)
--   → (has-level n A → has-level n B)
-- equiv-preserves-level {n = ⟨-2⟩} e (x , p) =
--   (–> e x , (λ y → ap (–> e) (p _) ∙ <–-inv-r e y))
-- equiv-preserves-level {n = S n} e c = λ x y →
--    equiv-preserves-level (equiv-ap (e ⁻¹) x y ⁻¹) (c (<– e x) (<– e y))

-- {- This is a collection of type equivalences involving basic type formers.
--    We exclude Empty since Π₁-Empty requires λ=.
-- -}
-- module _ {j} {B : Unit → Set j} where
--   Σ₁-Unit : Σ Unit B ≃ B unit
--   Σ₁-Unit = equiv (λ {(unit , b) → b}) (λ b → (unit , b)) (λ _ → idp) (λ _ → idp)

--   Π₁-Unit : Π Unit B ≃ B unit
--   Π₁-Unit = equiv (λ f → f unit) (λ b _ → b) (λ _ → idp) (λ _ → idp)

-- module _ {i} {A : Set i} where
--   Σ₂-Unit : Σ A (λ _ → Unit) ≃ A
--   Σ₂-Unit = equiv fst (λ a → (a , unit)) (λ _ → idp) (λ _ → idp)

--   Π₂-Unit : Π A (λ _ → Unit) ≃ Unit
--   Π₂-Unit = equiv (λ _ → unit) (λ _ _ → unit) (λ _ → idp) (λ _ → idp)

-- module _ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k} where
--   Σ-assoc : Σ (Σ A B) (uncurry C) ≃ Σ A (λ a → Σ (B a) (C a))
--   Σ-assoc = equiv (λ {((a , b) , c) → (a , (b , c))})
--                   (λ {(a , (b , c)) → ((a , b) , c)}) (λ _ → idp) (λ _ → idp)

--   curry-equiv : Π (Σ A B) (uncurry C) ≃ Π A (λ a → Π (B a) (C a))
--   curry-equiv = equiv curry uncurry (λ _ → idp) (λ _ → idp)

--   {- The type-theoretic axiom of choice -}
--   choice : Π A (λ a → Σ (B a) (λ b → C a b)) ≃ Σ (Π A B) (λ g → Π A (λ a → C a (g a)))
--   choice = equiv f g (λ _ → idp) (λ _ → idp)
--     where f = λ c → ((λ a → fst (c a)) , (λ a → snd (c a)))
--           g = λ d → (λ a → (fst d a , snd d a))

-- {- Homotopy fibers -}
-- hfiber : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (y : B) → Set (lmax i j)
-- hfiber {A = A} f y = Σ A (λ x → f x == y)
