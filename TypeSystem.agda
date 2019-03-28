{-# OPTIONS --cubical --rewriting #-}

module TypeSystem where
open import Primitives public
open import Agda.Primitive hiding (i0 ; i1) public


Π : ∀{ℓA ℓB} (A : Set ℓA) → (B : A → Set ℓB) → Set (ℓB ⊔ ℓA)
Π A B = (a : A) → B a
hΠ : ∀{ℓA ℓB} (A : Set ℓA) → (B : A → Set ℓB) → Set (ℓB ⊔ ℓA)
hΠ A B = {a : A} → B a

---------------------------------
-- Identity type --
---------------------------------

postulate
  _≡_ : ∀{ℓ} {A : Set ℓ} (a b : A) → Set ℓ
  refl : ∀{ℓ} {A :{#} Set ℓ} (a :{#} A) → a ≡ a
  J : ∀{ℓA ℓC} {A :{#} Set ℓA} {a b :{#} A} (e : a ≡ b) (C :{#} (y : A) → (w : a ≡ y) → Set ℓC) (c : C a (refl a))
    → C b e
  rw-Jβ : ∀{ℓA ℓC} →
      {A :{#} Set ℓA} →
      {a :{#} A} →
      (C :{#} (y : A) → (w : a ≡ y) → Set ℓC) →
      (c : C a (refl a)) →
      J (refl a) C c ≡ c

infix 1 _≡_

{-# BUILTIN REWRITE _≡_ #-}

{-# REWRITE rw-Jβ #-}

--postulate
--  funext : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : Π A B} → ((x : A) → f x ≡ g x) → f ≡ g

-------------------------------------------
-- Σ-types --
-------------------------------------------

postulate
  Σ #Σ : ∀{ℓA ℓB} → (A : Set ℓA) → (B : A → Set ℓB) → Set (ℓB ⊔ ℓA)
  ¶Σ : ∀{ℓA ℓB} → (A : Set ℓA) → (B : (_ :{¶} A) → Set ℓB) → Set (ℓB ⊔ ℓA)

-- Continuous Σ-type --
-----------------------

postulate
  [_,_] : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (a : A) → (b : B a) → Σ A B
  fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → Σ A B → A
  snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (p : Σ A B) → B (fst p)
  rw-fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (a : A) → (b : B a)
    → fst ([_,_] {_}{_}{A}{B} a b) ≡ a
{-# REWRITE rw-fst #-}
postulate
  rw-snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (a : A) → (b : B a)
    → snd ([_,_] {_}{_}{A}{B} a b) ≡ b
  rw-fst,snd : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → (p : Σ A B)
    → [_,_] {_}{_}{A}{B} (fst p) (snd p) ≡ p
{-# REWRITE rw-snd #-}
{-# REWRITE rw-fst,snd #-}

--An induction principle is definable in terms of fst and snd. We give only the continuous induction pr'ple
split : ∀{ℓA ℓB ℓC} → h#Π (Set ℓA) λ A → h#Π (A → Set ℓB) λ B
    → Π (Σ A B) λ p
    → #Π (Σ A B → Set ℓC) λ C
    → Π (Π A λ a → Π (B a) λ b → C [ a , b ]) λ c
    → C p
split {_}{_}{_} {A}{B} p C c = c (fst p) (snd p)

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀{ℓA ℓB} → (A : Set ℓA) → (B : Set ℓB) → Set (ℓA ⊔ ℓB)
A × B = Σ[ _ ∈ A ] B

#uncurry : ∀ {a b c} → {A :{#} Set a} →  {B :{#} A → Set b} →
                       {C :{#} Σ A B → Set c} →
                       ((x : A) (y : B x) → C [ x , y ]) → (p : Σ A B) → C p
#uncurry f p = f (fst p) (snd p)

-- Parametric Σ-type (∃) --
---------------------------

--We should additionally postulate pointwise and parametric induction principles, but we only include the continuous one.
postulate
  [#_,_] : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} → #Π A λ a → (b : B a) → #Σ A B
  #split : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB}
    → (p : #Σ A B)
    → (C :{#} #Σ A B → Set ℓC)
    → (c : (a :{#} A) → (b : B a) → C [# a , b ])
    → C p
  rw-#Σ-β : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB}
    → (a :{#} A) → (b : B a)
    → (C :{#} #Σ A B → Set ℓC)
    → (c : (a :{#} A) → (b : B a) → C [# a , b ])
    → #split [# a , b ] C c ≡ c a b
{-# REWRITE rw-#Σ-β #-}

infix 2 #Σ-syntax

#Σ-syntax : ∀ {a b} (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
#Σ-syntax = #Σ

syntax #Σ-syntax A (λ x → B) = #Σ[ x ∈ A ] B

uncurry# : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB}
  → {C :{#} #Σ A B → Set ℓC}
  → (c : (a :{#} A) → (b : B a) → C [# a , b ])
  → (p : #Σ A B)
  → C p
uncurry# {C = C} c p = #split p C c


-- Pointwise Σ-type --
----------------------

--We should additionally postulate pointwise and parametric induction principles, but we only include the continuous one.
--With the parametric induction principle, we could define ¶fst and ¶snd
postulate
  [¶_,_] : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (a :{¶} A) → (b : B a) → ¶Σ A B
  ¶split : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB}
    → (p : ¶Σ A B)
    → (C :{#} ¶Σ A B → Set ℓC)
    → (c : (a :{¶} A) → (b : B a) → C [¶ a , b ])
    → C p
  rw-¶Σ-β : ∀{ℓA ℓB ℓC} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB}
    → (a :{¶} A) → (b : B a)
    → (C :{#} ¶Σ A B → Set ℓC)
    → (c : (a :{¶} A) → (b : B a) → C [¶ a , b ])
    → ¶split [¶ a , b ] C c ≡ c a b
{-# REWRITE rw-¶Σ-β #-}

--¶fst : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} → (_ :{#} ¶Σ A B) → A
--¶fst {_}{_}{A}{B} p = ¶split p (λ _ → A) (λ a b → a)

--¶snd : ∀{ℓA ℓB} → h#Π (Set ℓA) λ A → h#Π ((_ :{¶} A) → Set ℓB) λ B → (p : ¶Σ A B) → B (¶fst p)
--¶snd {_}{_}{A}{B} p = ¶split p (λ p → B (¶fst p)) (λ a b → b)

infix 2 ¶Σ-syntax

¶Σ-syntax : ∀ {a b} (A : Set a) → (B : (_ :{¶} A) → Set b) → Set (a ⊔ b)
¶Σ-syntax = ¶Σ

syntax ¶Σ-syntax A (λ x → B) = ¶Σ[ x ∈ A ] B

-------------------------------------------
-- Glueing and Welding --
-------------------------------------------

Glue : ∀{ℓ} (A : Set ℓ) → ∀ φ → (T : Partial (Set ℓ) φ) → (f :{¶} PartialP φ (λ o → T o → A)) → Set ℓ
Glue A φ T f = primGlue A φ T f

module Welding where
  primitive
    primCoGlue : _
    prim^coglue : _ {- {la lb : Level} {A : Set la} #{φ : Prop}
                    {T : .(o : IsOne φ) → Set lb} ¶{f : .(o : IsOne φ) → A → T o} →
                    A → primCoGlue A φ T f -}
    prim^mcoglue : _ {- {la lb lc : Level} #{A : Set la} #{φ : Prop}
                     #{T : .(o : IsOne φ) → Set lb} ¶{f : .(o : IsOne φ) → A → T o}
                     #{C : primCoGlue A φ T f → Set lc}
                     (c0 : (a : A) → C (prim^coglue a))
                     (c : .(o : IsOne φ) (t : T o) → C t) (b : primCoGlue A φ T f) →
                     C b -}
open Welding public renaming (primCoGlue to Weld ; prim^coglue to weld ; prim^mcoglue to mweld)

--Weld : ∀{ℓ} (A : Set ℓ) → ∀ φ → (T : Partial (Set ℓ) φ) → ¶Π (PartialP φ (λ o → A → T o)) λ f → Set ℓ
--Weld A φ T f = primWeld A φ T f

-------------------------------------------
-- Extension types --
-------------------------------------------

postulate
  _[_] : ∀{ℓ} (A : Set ℓ) → ∀ {φ} → (a : Partial A φ) → Set ℓ
  cut : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} (a : A) → A [ (λ {(φ = p⊤) → a}) ]
  paste[_]_ : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} (pa : Partial A φ) → A [ pa ] → A
  rw-ext-def : ∀{ℓ} {A :{#} Set ℓ} (pa : Partial A p⊤) (exta : A [ pa ]) → paste[ pa ] exta ≡ pa itIsOne

{-# REWRITE rw-ext-def #-}

postulate
  rw-ext-β : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} (a : A) → paste[ (λ{(φ = p⊤) → a}) ] cut a ≡ a
  rw-ext-η : ∀{ℓ} {A :{#} Set ℓ} (φ :{#} Prop) (pa : Partial A φ) (exta : A [ pa ]) → cut (paste[ pa ] exta) ≡ exta
  
{-# REWRITE rw-ext-β #-}
{-# REWRITE rw-ext-η #-}

-------------------------------------------
-- PATH DEGENERACY AXIOM --
-------------------------------------------

postulate
  pathDisc : ∀{ℓ} → {A :{#} Set ℓ} → (p :{#} (_ :{#} 𝕀) → A) → p ≡ (λ _ → p b0)

---------------------------------
-- Lifting --
---------------------------------
postulate
  Lift : ∀{ℓ} → Set ℓ → Set (lsuc ℓ)
  lift : ∀{ℓ} → {A :{#} Set ℓ} → A → Lift A
  lower : ∀{ℓ} → {A :{#} Set ℓ} → Lift A → A
  rw-lift-β : ∀{ℓ} → {A :{#} Set ℓ} → (a : A) → lower (lift a) ≡ a
  rw-lift-η : ∀{ℓ} → {A :{#} Set ℓ} → (a : Lift A) → lift (lower a) ≡ a
{-# REWRITE rw-lift-β #-}
{-# REWRITE rw-lift-η #-}


---------------
-- Booleans
---------------

postulate
 Bool : Set
 true false : Bool
 bool : ∀ {a} {A :{ # } Bool → Set a} → A true → A false → ∀ b → A b
 bool-rw1 : ∀ {a} {A :{ # } Bool → Set a} → (t : A true) → (f : A false) → bool {A = A} t f true ≡ t
 bool-rw2 : ∀ {a} {A :{ # } Bool → Set a} → (t : A true) → (f : A false) → bool {A = A} t f false ≡ f

{-# REWRITE bool-rw1 bool-rw2 #-}

infix  0 if_then_else_
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if_then_else_ b t f = bool t f b

_+_ : Set → Set → Set
A + B = Σ Bool \ b → if b then A else B

---------------
-- Unit
---------------

postulate
  ⊤ : Set
  tt : ⊤
  unit : ∀ {a} {A :{ # } ⊤ → Set a} → A tt → ∀ b → A b
  unit-rw : ∀ {a} {A :{ # } ⊤ → Set a} → (t : A tt) → unit {A = A} t tt ≡ t

{-# REWRITE unit-rw #-}

-------------------------------------------
-- AUXILIARY STUFF --
-------------------------------------------

-- FUNCTIONS

id : ∀{ℓ} {A :{#} Set ℓ} → A → A
id a = a

_∘_ : ∀{ℓA ℓB ℓC} →
    {A :{#} Set ℓA} →
    {B :{#} Set ℓB} →
    {C :{#} B → Set ℓC} →
    (g : (b : B) → C b) →
    (f : A → B) →
    ((a : A) → C (f a))
_∘_ {ℓA}{ℓB}{ℓC}{A}{B}{C} g f a = g (f a)

infixr 20 _∘_

-- FUNCTION EXTENSIONALITY

postulate
  funext : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} →
           {f g :{#} (a : A) → B a} →
           ((a : A) → f a ≡ g a) → f ≡ g
  #funext : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} A → Set ℓB} →
           {f g :{#} (a :{#} A) → B a} →
           ((a :{#} A) → f a ≡ g a) → f ≡ g
  ¶funext : ∀{ℓA ℓB} → {A :{#} Set ℓA} → {B :{#} (_ :{¶} A) → Set ℓB} →
           {f g :{#} (a :{¶} A) → B a} →
           ((a :{¶} A) → f a ≡ g a) → f ≡ g

-- PATHS

PathP : ∀{ℓ} (A : 𝕀 → Set ℓ) (a0 : A i0) (a1 : A i1) → Set ℓ
PathP A a0 a1 = (i :{#} 𝕀) → A i [ (λ {((i ≣ i0) = p⊤) → a0 ; ((i ≣ i1) = p⊤) → a1}) ]
Path : ∀{ℓ} {A : Set ℓ} (a0 a1 : A) → Set ℓ
Path {ℓ} {A} a0 a1 = PathP (λ _ → A) a0 a1
_◆_ : ∀{ℓ} {A :{#} 𝕀 → Set ℓ} {a0 : A i0} {a1 : A i1} → PathP A a0 a1 → (i :{#} 𝕀 ) → A i
_◆_ {a0 = a0} {a1} p i = paste[ (λ {((i ≣ i0) = p⊤) → a0 ; ((i ≣ i1) = p⊤) → a1}) ] p i

-- GLUE

Glue⟨_←_,_⟩ : ∀{ℓ} (A : Set ℓ) {φ : Prop} (T : Partial (Set ℓ) φ) (f :{¶} PartialP φ (λ o → T o → A)) → Set ℓ
Glue⟨ A ← T , f ⟩ = Glue A _ T f
glue⟨_↦_⟩ : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} {f :{¶} PartialP φ (λ o → T o → A)}
  (t : PartialP φ T) (exta : A [ (λ{(φ = p⊤) → f _ (t _)}) ]) → Glue⟨ A ← T , f ⟩
glue⟨_↦_⟩ {φ = φ} {f = f} t exta = glue (λ{(φ = p⊤) → t _}) (paste[ (λ{(φ = p⊤) → f _ (t _)}) ] exta)
unglue[_] : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} (f :{¶} PartialP φ (λ o → T o → A))
  → Glue⟨ A ← T , f ⟩ → A
unglue[_] {A = A} {φ = φ} f g = unglue {_}{_}{A}{φ} g

-- WELD

Weld⟨_⇒_,_⟩ : ∀{ℓ} (A : Set ℓ) {φ : Prop} (T : Partial (Set ℓ) φ) (f :{¶} PartialP φ (λ o → A → T o)) → Set ℓ
Weld⟨ A ⇒ T , f ⟩ = Weld A _ T f
weld[_] : ∀{ℓ} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} (f :{¶} PartialP φ (λ o → A → T o))
  → A → Weld⟨ A ⇒ T , f ⟩
weld[_] {A = A} {φ = φ} f a = weld {_}{_}{A}{φ} a
ext-mweld : ∀{ℓ ℓC} {A :{#} Set ℓ} {φ :{#} Prop} {T :{#} Partial (Set ℓ) φ} {f :{¶} PartialP φ (λ o → A → T o)}
  → (C :{#} Weld⟨ A ⇒ T , f ⟩ → Set ℓC)
  → (h : PartialP {ℓ ⊔ ℓC} φ (λ{(φ = p⊤) → (t : T itIsOne) → C t}))
  → ((a : A) → C (weld[ f ] a) [ (λ{(φ = p⊤) → h itIsOne (f _ a)}) ])
  → (w : Weld⟨ A ⇒ T , f ⟩)
  → C w
ext-mweld {φ = φ} {f = f} C h g w =
  mweld {C = C} (λ a → paste[ (λ{(φ = p⊤) → h itIsOne (f _ a)}) ] g a) (λ{(φ = p⊤) → h itIsOne}) w

-- EQUALITY

subst : ∀ {a p} → {A :{#} Set a} → (P :{#} A → Set p) →
         {x₁ :{#} _} → {x₂ :{#} _} → x₁ ≡ x₂ → P x₁ → P x₂
subst P eq p = J eq (\ y _ → P y) p

sym : ∀{ℓ} →
      {A :{#} Set ℓ} →
      {a b :{#} A} →
      b ≡ a → a ≡ b
sym {ℓ}{A}{a}{b} e = J e (λ y w → y ≡ b) (refl b)

trans : ∀ {a} → {A :{#} Set a} → {x y z :{#} A} →
                x ≡ y → y ≡ z → x ≡ z
trans p q = subst (\ x → _ ≡ x) q p

_•_ = trans
infixl 0 _•_

cong : ∀{ℓA ℓB} →
      {A :{#} Set ℓA} →
      {B :{#} Set ℓB} →
      (f :{#} A → B) →
      {a b :{#} A} →
      (a ≡ b) → (f a ≡ f b)
cong {ℓA}{ℓB}{A}{B} f {a}{b} e = J e (λ y w → f a ≡ f y) (refl (f a))

cong-app : ∀{ℓA ℓB} →
      {A :{#} Set ℓA} →
      {B :{#} A → Set ℓB} →
      {f g :{#} (a : A) → B a} →
      (f ≡ g) →
      (a :{#} A) →
      f a ≡ g a
cong-app {ℓA}{ℓB}{A}{B}{f}{g} e a = J e (λ h w → f a ≡ h a) (refl (f a))

#cong-app : ∀{ℓA ℓB} →
      {A :{#} Set ℓA} →
      {B :{#} A → Set ℓB} →
      {f g :{#} (a :{#} A) → B a} →
      (f ≡ g) →
      (a :{#} A) →
      f a ≡ g a
#cong-app {ℓA}{ℓB}{A}{B}{f}{g} e a = J e (λ h w → f a ≡ h a) (refl (f a))


-- ANNOTATION

_∋_ : ∀{ℓ} → (A :{#} Set ℓ) → A → A
A ∋ a = a

-- PATH DEGENERACY

path-to-eq : ∀{ℓ} → {A :{#} Set ℓ} → (p :{#} (_ :{#} 𝕀) → A) → p i0 ≡ p i1
path-to-eq p = sym (#cong-app (pathDisc p) i1)

ext-path-to-eq : ∀{ℓ} → {A :{#} Set ℓ} {a0 a1 : A} → (p :{#} Path a0 a1) → a0 ≡ a1
ext-path-to-eq p = path-to-eq (λ i → p ◆ i)
