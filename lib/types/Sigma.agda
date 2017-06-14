{-# OPTIONS --without-K --rewriting #-}

open import TypeSystem hiding (_∘_)
open import lib.Equivalences
open import lib.Base
module lib.types.Sigma where

pair= : ∀ {i j} {A :{ # } Set i} {B :{ # } A → Set j}
  {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'}
  (q : PathOver B p b b')
  → [ a , b ] ≡ [ a' , b' ]
pair= {B = B} {a} p {b} = J p (\ a' p → (b' : B a') -> (q : PathOver B p b b')
  → [ a , b ] ≡ [ a' , b' ]) (\ b' q → cong ([_,_] _) q) _

trans-↓ : ∀ {i j} {A :{ # } Set i} (P :{ # } A → Set j) {a₁ a₂ : A}
  (p : a₁ ≡ a₂) (y : P a₂) → subst P (sym p) y == y [ P ↓ p ]
trans-↓ P p = J p (\ a2 p → (y : P a2) → subst P (sym p) y == y [ P ↓ p ]) refl

trans-ap-↓ : ∀ {i j k} {A :{ # } Set i} {B :{ # } Set j} (P :{ # } B → Set k) (h : A → B)
  {a₁ a₂ : A} (p : a₁ ≡ a₂) (y : P (h a₂))
  → subst P (sym (ap h p)) y == y [ P ∘ h ↓ p ]
trans-ap-↓ P h p = J p (\ a2 p → (y : P (h a2)) → subst P (sym (ap h p)) y == y [ P ∘ h ↓ p ]) refl


-- Equivalences in a Σ-type

equiv-Σ-fst : ∀ {i j k} {A :{ # } Set i} {B :{ # } Set j} (P :{ # } B → Set k) {h : A → B}
                  → is-equiv h → (Σ A (P ∘ h)) ≃ (Σ B P)
equiv-Σ-fst {A = A} {B = B} P {h = h} e = [ f , is-eq _ g f-g g-f ]
  where f : Σ A (P ∘ h) → Σ B P
        f = #uncurry \ a r → [ h a , r ]

        g : Σ B P → Σ A (P ∘ h)
        g = #uncurry \ b s → [ is-equiv.g e b , subst P (sym (is-equiv.f-g e b)) s ]

        f-g : ∀ y → f (g y) ≡ y
        f-g = #uncurry \ b s → pair= (is-equiv.f-g e b) (trans-↓ P (is-equiv.f-g e b) s)

        g-f : ∀ x → g (f x) ≡ x
        g-f = #uncurry \ a r →
          pair= (is-equiv.g-f e a)
                (subst (λ q → subst P (sym q) r == r [ P ∘ h ↓ is-equiv.g-f e a ])
                           (is-equiv.adj e a)
                           (trans-ap-↓ P h (is-equiv.g-f e a) r) )

-- equiv-Σ-snd : ∀ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k}
--   → (∀ x → B x ≃ C x) → Σ A B ≃ Σ A C
-- equiv-Σ-snd {A = A} {B = B} {C = C} k = equiv f g f-g g-f
--   where f : Σ A B → Σ A C
--         f (a , b) = (a , fst (k a) b)

--         g : Σ A C → Σ A B
--         g (a , c) = (a , is-equiv.g (snd (k a)) c)

--         f-g : ∀ p → f (g p) ≡ p
--         f-g (a , c) = pair= idp (is-equiv.f-g (snd (k a)) c)

--         g-f : ∀ p → g (f p) ≡ p
--         g-f (a , b) = pair= idp (is-equiv.g-f (snd (k a)) b)

-- -- Two ways of simultaneously applying equivalences in each component.
-- module _ {i₀ i₁ j₀ j₁} {A₀ : Set i₀} {A₁ : Set i₁}
--          {B₀ : A₀ → Set j₀} {B₁ : A₁ → Set j₁} where
--   equiv-Σ : (u : A₀ ≃ A₁) (v : ∀ a → B₀ (<– u a) ≃ B₁ a) → Σ A₀ B₀ ≃ Σ A₁ B₁
--   equiv-Σ u v = Σ A₀ B₀           ≃⟨ equiv-Σ-fst _ (snd (u ⁻¹)) ⁻¹ ⟩
--                 Σ A₁ (B₀ ∘ <– u)  ≃⟨ equiv-Σ-snd v ⟩
--                 Σ A₁ B₁           ≃∎

--   equiv-Σ' : (u : A₀ ≃ A₁) (v : ∀ a → B₀ a ≃ B₁ (–> u a)) → Σ A₀ B₀ ≃ Σ A₁ B₁
--   equiv-Σ' u v = Σ A₀ B₀           ≃⟨ equiv-Σ-snd v ⟩
--                  Σ A₀ (B₁ ∘ –> u)  ≃⟨ equiv-Σ-fst _ (snd u) ⟩
--                  Σ A₁ B₁           ≃∎


-- -- Implementation of [_∙'_] on Σ
-- Σ-∙' : ∀ {i j} {A : Set i} {B : A → Set j}
--   {x y z : A} {p : x ≡ y} {p' : y ≡ z}
--   {u : B x} {v : B y} {w : B z}
--   (q : u ≡ v [ B ↓ p ]) (r : v ≡ w [ B ↓ p' ])
--   → (pair= p q ∙' pair= p' r) ≡ pair= (p ∙' p') (q ∙'ᵈ r)
-- Σ-∙' {p = idp} {p' = idp} q idp = idp

-- -- Implementation of [_∙_] on Σ
-- Σ-∙ : ∀ {i j} {A : Set i} {B : A → Set j}
--   {x y z : A} {p : x ≡ y} {p' : y ≡ z}
--   {u : B x} {v : B y} {w : B z}
--   (q : u ≡ v [ B ↓ p ]) (r : v ≡ w [ B ↓ p' ])
--   → (pair= p q ∙ pair= p' r) ≡ pair= (p ∙ p') (q ∙ᵈ r)
-- Σ-∙ {p = idp} {p' = idp} idp r = idp

-- -- Implementation of [!] on Σ
-- Σ-! : ∀ {i j} {A : Set i} {B : A → Set j}
--   {x y : A} {p : x ≡ y}
--   {u : B x} {v : B y}
--   (q : u ≡ v [ B ↓ p ])
--   → ! (pair= p q) ≡ pair= (! p) (!ᵈ q)
-- Σ-! {p = idp} idp = idp

-- -- Implementation of [_∙'_] on ×
-- ×-∙' : ∀ {i j} {A : Set i} {B : Set j}
--   {x y z : A} (p : x ≡ y) (p' : y ≡ z)
--   {u v w : B} (q : u ≡ v) (q' : v ≡ w)
--   → (pair×= p q ∙' pair×= p' q') ≡ pair×= (p ∙' p') (q ∙' q')
-- ×-∙' idp idp q idp = idp

-- -- Implementation of [_∙_] on ×
-- ×-∙ : ∀ {i j} {A : Set i} {B : Set j}
--   {x y z : A} (p : x ≡ y) (p' : y ≡ z)
--   {u v w : B} (q : u ≡ v) (q' : v ≡ w)
--   → (pair×= p q ∙ pair×= p' q') ≡ pair×= (p ∙ p') (q ∙ q')
-- ×-∙ idp idp idp r = idp

-- -- Implementation of [!] on ×
-- ×-! : ∀ {i j} {A : Set i} {B : Set j}
--   {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v)
--   → ! (pair×= p q) ≡ pair×= (! p) (! q)
-- ×-! idp idp = idp

-- -- Special case of [ap-,]
-- ap-cst,id : ∀ {i j} {A : Set i} (B : A → Set j)
--   {a : A} {x y : B a} (p : x ≡ y)
--   → ap (λ x → _,_ {B = B} a x) p ≡ pair= idp p
-- ap-cst,id B idp = idp

-- -- hfiber fst ≡ B
-- module _ {i j} {A : Set i} {B : A → Set j} where

--   private
--     to : ∀ a → hfiber (fst :> (Σ A B → A)) a → B a
--     to a ((.a , b) , idp) = b

--     from : ∀ (a : A) → B a → hfiber (fst :> (Σ A B → A)) a
--     from a b = (a , b) , idp

--     to-from : ∀ (a : A) (b : B a) → to a (from a b) ≡ b
--     to-from a b = idp

--     from-to : ∀ a b′ → from a (to a b′) ≡ b′
--     from-to a ((.a , b) , idp) = idp

--   hfiber-fst : ∀ a → hfiber (fst :> (Σ A B → A)) a ≃ B a
--   hfiber-fst a = to a , is-eq (to a) (from a) (to-from a) (from-to a)

-- {- Dependent paths in a Σ-type -}
-- module _ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
--   where

--   ↓-Σ-in : {x x' : A} {p : x ≡ x'} {r : B x} {r' : B x'}
--     {s : C x r} {s' : C x' r'}
--     (q : r ≡ r' [ B ↓ p ])
--     → s ≡ s' [ uncurry C ↓ pair= p q ]
--     → (r , s) ≡ (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ]
--   ↓-Σ-in {p = idp} idp t = pair= idp t

--   ↓-Σ-fst : {x x' : A} {p : x ≡ x'} {r : B x} {r' : B x'}
--     {s : C x r} {s' : C x' r'}
--     → (r , s) ≡ (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ]
--     → r ≡ r' [ B ↓ p ]
--   ↓-Σ-fst {p = idp} u = fst= u

--   ↓-Σ-snd : {x x' : A} {p : x ≡ x'} {r : B x} {r' : B x'}
--     {s : C x r} {s' : C x' r'}
--     → (u : (r , s) ≡ (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ])
--     → s ≡ s' [ uncurry C ↓ pair= p (↓-Σ-fst u) ]
--   ↓-Σ-snd {p = idp} idp = idp

--   ↓-Σ-β-fst : {x x' : A} {p : x ≡ x'} {r : B x} {r' : B x'}
--     {s : C x r} {s' : C x' r'}
--     (q : r ≡ r' [ B ↓ p ])
--     (t : s ≡ s' [ uncurry C ↓ pair= p q ])
--     → ↓-Σ-fst (↓-Σ-in q t) ≡ q
--   ↓-Σ-β-fst {p = idp} idp idp = idp

--   ↓-Σ-β-snd : {x x' : A} {p : x ≡ x'} {r : B x} {r' : B x'}
--     {s : C x r} {s' : C x' r'}
--     (q : r ≡ r' [ B ↓ p ])
--     (t : s ≡ s' [ uncurry C ↓ pair= p q ])
--     → ↓-Σ-snd (↓-Σ-in q t) ≡ t
--       [ (λ q' → s ≡ s' [ uncurry C ↓ pair= p q' ]) ↓ ↓-Σ-β-fst q t ]
--   ↓-Σ-β-snd {p = idp} idp idp = idp

--   ↓-Σ-η : {x x' : A} {p : x ≡ x'} {r : B x} {r' : B x'}
--     {s : C x r} {s' : C x' r'}
--     (u : (r , s) ≡ (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ])
--     → ↓-Σ-in (↓-Σ-fst u) (↓-Σ-snd u) ≡ u
--   ↓-Σ-η {p = idp} idp = idp

-- {- Dependent paths in a ×-type -}
-- module _ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k}
--   where

--   ↓-×-in : {x x' : A} {p : x ≡ x'} {r : B x} {r' : B x'}
--     {s : C x} {s' : C x'}
--     → r ≡ r' [ B ↓ p ]
--     → s ≡ s' [ C ↓ p ]
--     → (r , s) ≡ (r' , s') [ (λ x → B x × C x) ↓ p ]
--   ↓-×-in {p = idp} q t = pair×= q t

-- module _ where
--   -- An orphan lemma.
--   ↓-cst×app-in : ∀ {i j k} {A : Set i}
--     {B : Set j} {C : A → B → Set k}
--     {a₁ a₂ : A} (p : a₁ ≡ a₂)
--     {b₁ b₂ : B} (q : b₁ ≡ b₂)
--     {c₁ : C a₁ b₁}{c₂ : C a₂ b₂}
--     → c₁ ≡ c₂ [ uncurry C ↓ pair×= p q ]
--     → (b₁ , c₁) ≡ (b₂ , c₂) [ (λ x → Σ B (C x)) ↓ p ]
--   ↓-cst×app-in idp idp idp = idp

-- {- pair= and pair×= where one argument is reflexivity -}
-- pair=-idp-l : ∀ {i j} {A : Set i} {B : A → Set j} (a : A) {b₁ b₂ : B a}
--   (q : b₁ ≡ b₂) → pair= {B = B} idp q ≡ ap (λ y → (a , y)) q
-- pair=-idp-l _ idp = idp

-- pair×=-idp-l : ∀ {i j} {A : Set i} {B : Set j} (a : A) {b₁ b₂ : B}
--   (q : b₁ ≡ b₂) → pair×= idp q ≡ ap (λ y → (a , y)) q
-- pair×=-idp-l _ idp = idp

-- pair×=-idp-r : ∀ {i j} {A : Set i} {B : Set j} {a₁ a₂ : A} (p : a₁ ≡ a₂)
--   (b : B) → pair×= p idp ≡ ap (λ x → (x , b)) p
-- pair×=-idp-r idp _ = idp

-- pair×=-split-l : ∀ {i j} {A : Set i} {B : Set j} {a₁ a₂ : A} (p : a₁ ≡ a₂)
--   {b₁ b₂ : B} (q : b₁ ≡ b₂)
--   → pair×= p q ≡ ap (λ a → (a , b₁)) p ∙ ap (λ b → (a₂ , b)) q
-- pair×=-split-l idp idp = idp

-- pair×=-split-r : ∀ {i j} {A : Set i} {B : Set j} {a₁ a₂ : A} (p : a₁ ≡ a₂)
--   {b₁ b₂ : B} (q : b₁ ≡ b₂)
--   → pair×= p q ≡ ap (λ b → (a₁ , b)) q ∙ ap (λ a → (a , b₂)) p
-- pair×=-split-r idp idp = idp

-- -- Commutativity of products and derivatives.
-- module _ {i j} {A : Set i} {B : Set j} where
--   ×-comm : Σ A (λ _ → B) ≃ Σ B (λ _ → A)
--   ×-comm = equiv (λ {(a , b) → (b , a)}) (λ {(b , a) → (a , b)}) (λ _ → idp) (λ _ → idp)

-- module _ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k} where
--   Σ₂-×-comm : Σ (Σ A B) (λ ab → C (fst ab)) ≃ Σ (Σ A C) (λ ac → B (fst ac))
--   Σ₂-×-comm = Σ-assoc ⁻¹ ∘e equiv-Σ-snd (λ a → ×-comm) ∘e Σ-assoc

-- module _ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k} where
--   Σ₁-×-comm : Σ A (λ a → Σ B (λ b → C a b)) ≃ Σ B (λ b → Σ A (λ a → C a b))
--   Σ₁-×-comm = Σ-assoc ∘e equiv-Σ-fst _ (snd ×-comm) ∘e Σ-assoc ⁻¹
