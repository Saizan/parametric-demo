module EquivalenceReasoning where
open import TypeSystem
open import lib.Equivalences public



_≅_ : ∀ {la lb} → (A : Set la) (B : Set lb) → Set _
_≅_ = _≃_

con' : ∀ {la lb} {A :{ # } Set la}{B :{ # } Set lb} → (coe : A → B) → (inv : B → A) → (∀ b → coe (inv b) ≡ b) → (∀ b → inv (coe b) ≡ b) → A ≅ B
con' coe inv eq eq' = [ coe , is-eq coe inv eq eq' ]
module _≅_ {la lb} {A : Set la}{B : Set lb} (A≅B : A ≅ B) where


  coe : A → B
  coe = fst A≅B
  inv : B → A
  inv = is-equiv.g (snd A≅B)

  coeinv' : ∀ b → coe (inv b) ≡ b
  coeinv' = is-equiv.f-g (snd A≅B)
  invcoe' : ∀ a → inv (coe a) ≡ a
  invcoe' = is-equiv.g-f (snd A≅B)
  coeinv = \ {a : B} → coeinv' a
  invcoe = \ {a : A} → invcoe' a

con : ∀ {la lb}{A : Set la}{B : Set lb} → (coe : A → B) → (inv : B → A) → (∀ {b} → coe (inv b) ≡ b) → (∀ {b} → inv (coe b) ≡ b) → A ≅ B
con = \ x y z w → con' x y (\ _ → z) (\ _ → w)


module F {i : Level} where
  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _≈⟨_⟩_
  infix  1 begin_

  Carrier = Set i
  _∼_ = _≅_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : Carrier) : Set i where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y

  begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _≈⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x ⟩ relTo y = relTo (let
                                    module x = _≅_ x
                                    module y = _≅_ y
                                                          in con (λ z → _≅_.coe y (_≅_.coe x z))
                                                             (λ z → _≅_.inv x (_≅_.inv y z))
                                                             (trans (cong y.coe x.coeinv) y.coeinv)
                                                             (trans (cong x.inv y.invcoe) x.invcoe))


  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo (con (λ z → z) (λ z → z) (refl _) (refl _))

open F public


module #≅ {la lb} where

  coe : h#Π _ \ (A : Set la) → h#Π _ \ (B : Set lb) → (A≅B : A ≅ B) → A → B
  coe = fst
  inv : h#Π _ \ (A : Set la) → h#Π _ \ (B : Set lb) → (A≅B : A ≅ B) → B → A
  inv eq = is-equiv.g (snd eq)

  coeinv' : h#Π _ \ (A : Set la) → h#Π _ \ (B : Set lb) → (A≅B : A ≅ B) → ∀ b → coe A≅B (inv A≅B b) ≡ b
  coeinv' eq = is-equiv.f-g (snd eq)
  invcoe' : h#Π _ \ (A : Set la) → h#Π _ \ (B : Set lb) → (A≅B : A ≅ B) → ∀ b → inv A≅B (coe A≅B b) ≡ b
  invcoe' eq = is-equiv.g-f (snd eq)
  coeinv : h#Π _ \ (A : Set la) → h#Π _ \ (B : Set lb) → (A≅B : A ≅ B) → ∀ {b} → coe A≅B (inv A≅B b) ≡ b
  coeinv A≅B = coeinv' A≅B _
  invcoe : h#Π _ \ (A : Set la) → h#Π _ \ (B : Set lb) → (A≅B : A ≅ B) → ∀ {b} → inv A≅B (coe A≅B b) ≡ b
  invcoe A≅B = invcoe' A≅B _
