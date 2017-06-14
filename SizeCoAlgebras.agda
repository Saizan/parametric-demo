{-# OPTIONS --rewriting #-}
module SizeCoAlgebras where

open import EquivalenceReasoning

open import Primitives
open import TypeSystem
open import ParamSize

map∀i : ∀ {a b} → {A :{ # } Size → Set a} → {B :{ # } Size → Set b} → (∀i \ i → A i → B i) → ∀i A → ∀i B
map∀i f g i = f i (g i)

map∀i-∘ : ∀ {a b c}{A :{ # } Size → Set a}{B :{ # } Size → Set b}{C :{ # } Size → Set c}
          → {f : ∀i \ i → B i → C i} → {g : ∀i \ i → A i → B i} →
          ∀ x → map∀i f (map∀i g x) ≡ map∀i (\ i x → f i (g i x)) x
map∀i-∘ = \ _ → refl _

map∀i-id : ∀ {a}{A :{ # } Size → Set a} → ∀ x → map∀i {a} {a} {A} {A} (\ i x → x) x ≡ x
map∀i-id = \ _ → refl _

module Final (X :{ # } Set) (F :{ # } (X -> Set) -> (X -> Set))
               (mapF : {A B :{ # } X → Set} → (∀ x → A x → B x) → ∀ x → F A x → F B x)
               (mapF-∘ : {A B C :{ # } X → Set} →
                         {f : ∀ x → A x → B x}{g : ∀ x → B x → C x} →
                         ∀ x a → mapF g x (mapF f x a) ≡ mapF (\ x a → g x (f x a)) x a)
  where

  ■ : (Size → X → Set) → Size → X → Set
  ■ A i x = ∀i \ j → j < i → A j x

  guard : ∀ {A :{ # } Size → Set} → ∀i A → ∀i \ i → ∀i \ j → j < i → A j
  guard f i j _ = f j

  _⇛_ :{ # } (A B : Size → X → Set) → Set
  A ⇛ B = ∀i \ i → ∀ (x : X) → A i x → B i x

  map■ : h#Π _ \ A → h#Π _ \ B →  (A ⇛ B) → ■ A ⇛ ■ B
  map■ f i x a j j< = f j x (a j j<)

  _[■_] : ((X -> Set) -> (X -> Set)) → (Size → X → Set) → (Size → X → Set)
  (F [■ A ]) i x = F (\ y → ■ A i y) x

  map[■ : ∀ {A B} → (A ⇛ B) → (F [■ A ]) ⇛ (F [■ B ])
  map[■ f i x = mapF (\ x → map■ f i x) x

  typecan :{ # } Set₁
  typecan = ∀ {A :{ # } _} → ∀ x → F (\ x' → ∀i \ i → A i x') x
                                 → (∀i \ i → (F [■ A ]) i x)
  can : typecan
  can {A} x y i = mapF (\ _ y → guard y i) x y

  unique-fix : ∀ {A : Size → Set} f → ∀ {u} → (u ≡ \ i → f i (\ j _ → u j)) → u ≡ fix A f
  unique-fix {A} f {u} p = funext (fix _ (λ i x → trans (trans (TypeSystem.cong (λ f₁ → f₁ i) p)
                               (TypeSystem.cong (f i) (funext (λ a → funext \ a< → x a a<))))
                               (TypeSystem.sym (fix-unfold A f i))))

  #unique-fix : ∀ {A :{ # } Size → Set} f → ∀ {u : #Π Size A} → (u ≡ ( \ i → f i (\ j _ → u j) )) → u ≡ #fix A f
  #unique-fix f p = #funext (#fix _ (λ i x → trans (trans (TypeSystem.cong (λ f₁ → f₁ i) p)
                               (TypeSystem.cong (f i) (#funext (λ a → funext \ a< → x a a<))))
                               (TypeSystem.sym (#fix-unfold _ f i))))

  ν̂  :{ # } (Size → X → Set)
  ν̂  = (fix _ (λ i A → F (λ y → ∀i (λ j → ∀ j<i → A j j<i y))))

  inn̂ : (F [■ ν̂  ]) ⇛ ν̂
  inn̂ i x = subst (\ f → f x) (sym (fix-unfold _ (λ i A → F (λ y → ∀i (λ j → ∀ j<i → A j j<i y))) i))

  out̂ : ν̂  ⇛ (F [■ ν̂  ])
  out̂ i x = subst (\ f → f x) (fix-unfold _ (λ i A → F λ y → ∀i λ j → ∀ j<i → A j j<i y) i)

  betâ : h#Π Size \ i → ∀ {x fm} →  out̂ i x (inn̂ i x fm) ≡ fm
  betâ {i} = subst-sym ((fix-unfold _ (λ i A → F (λ y → ∀i (λ j → ∀ j<i → A j j<i y))) i)) where
    subst-sym : ∀ {a} {p} → {A :{ # } Set a} → {P :{ # } A → Set p}
                → {x y :{ # } A} → (eq : x ≡ y) {m : _} → subst P eq (subst P (sym eq) m) ≡ m
    subst-sym {P = P} eq {m} = J eq (\ y eq → (m : _) → subst P eq (subst P (sym eq) m) ≡ m ) refl m

  etâ : h#Π Size \ i → ∀ {x fm} →  inn̂ i x (out̂ i x fm) ≡ fm
  etâ {i} = subst-sym (((fix-unfold _ (λ i A → F (λ y → ∀i (λ j → ∀ j<i → A j j<i y))) i)))
   where
    subst-sym : ∀ {a} {p} → {A :{ # } Set a} → {P :{ # } A → Set p}
                → {x y :{ # } A} → (eq : x ≡ y) {m : _} → subst P (sym eq) (subst P eq m) ≡ m
    subst-sym {P = P} eq {m} = J eq (\ y eq → (m : _) → subst P (sym eq) (subst P eq m) ≡ m ) refl m

  mutual
    unfoldR : ∀ {A :{ # } _} → A ⇛ (F [■ A ]) → #Π Size \ i → _
    unfoldR {A} φ = (λ i unfold' x m → mapF (\ x → map∀i (\ j → \ m j<i → unfold' j j<i x (m j<i))) x (φ i x m))
    unfoldF : ∀ {A :{ # } _} → A ⇛ (F [■ A ]) → #Π Size \ i → _
    unfoldF {A} = \ φ → (λ i unfold' x m →  inn̂ i x (unfoldR φ i unfold' x m) )

    unfold̂ : ∀ {A :{ # } _} → A ⇛ (F [■ A ]) → A ⇛ ν̂
    unfold̂ {A} φ = #fix _    (unfoldF {A} φ)

  unfold̂-mor : ∀ {A} → (φ : A ⇛ (F [■ A ])) → #Π Size \ i → ∀ x fm →
                out̂ i x (unfold̂ φ i x fm) ≡ (map[■ (unfold̂ φ) i x (φ i x fm))
  unfold̂-mor φ i x fm = trans ((cong (λ f → (out̂ i x (f x fm))) (#fix-unfold _ (unfoldF φ) i)))
                            betâ

  unfold̂-mor2 : ∀ {A} → (φ : A ⇛ (F [■ A ])) → #Π Size \ i → ∀ x fm →
                 (unfold̂ φ i x fm) ≡ inn̂ i x (map[■ (unfold̂ φ) i x (φ i x fm))
  unfold̂-mor2 φ i x fm = trans (sym etâ) (cong (inn̂ i x) (unfold̂-mor φ i x fm))

  uniquê : ∀ {A} → (φ : A ⇛ (F [■ A ])) → (h : A ⇛ ν̂ ) →
                 (#Π Size \ i → ∀ x m → map[■ h i x (φ i x m) ≡ out̂ i x (h i x m))
                 → #Π Size \ i → ∀ x m → h i x m ≡ unfold̂ φ i x m
  uniquê φ h [h] i x m = cong (λ g → g i x m) (#unique-fix
                (unfoldF φ)
           {u = h} ( (sym (#funext (λ i → funext (λ x → funext \ m →  trans (cong (inn̂ i x) ([h] i x m)) etâ  )))) ))

  ν :{ # } X → Set
  ν x = ∀i \ i → ν̂  i x


  module F-commutes (comm : ∀ {A :{ # } _} x → is-equiv (can {A} x)) where

    inn : ∀ x → F ν x → ν x
    inn x ts = map∀i (\ i → inn̂ i x) (can x ts)

    out : ∀ x → ν x → F ν x
    out x m = #≅.inv ([ _ , comm x ]) (map∀i (λ i → out̂ i x) m)


    beta : ∀ x m → (out x (inn x m)) ≡ m
    beta x m = trans (cong (#≅.inv ([ _ , comm x ])) (#funext (\ i → betâ))) (#≅.invcoe (([ _ , comm x ])))

    eta : ∀ x m → (inn x (out x m)) ≡ m
    eta x m =  trans (cong (map∀i (λ i → inn̂ i x))
                                (#≅.coeinv' ([ _ , comm x ]) ((map∀i (λ i → out̂ i x) m))))
                    (#funext (\ x → etâ))

    unfold : ∀ {A :{ # } _} → (∀ x → A x → F A x) → ∀ x → A x → ν x
    unfold {A} φ x a i = unfold̂ (λ { i x fm → mapF (\ _ a → guard (\ _ → a) i) x (φ x fm) })
                                      i x a

    unfold-mor : ∀ {A} → (φ : ∀ ix → A ix → F A ix)
               → ∀ ix m → out ix (unfold φ ix m) ≡ mapF (unfold φ) ix (φ ix m)
    unfold-mor φ ix a = trans (cong (#≅.inv ([ _ , comm ix ])) (trans (#funext (\ i → unfold̂-mor _ _ _ _))
                    (#funext (\ x → trans (mapF-∘ {f = λ z a₁ → guard (λ _ → a₁) x} {g = _} ix (φ ix a))
                                          (sym (mapF-∘ {f = _} {g = \ _ y → guard y x} ix (φ ix a)))))))
                    ((#≅.invcoe ([ _ , comm ix ])))

    unfold-mor' : ∀ {A} → (φ : ∀ ix → A ix → F A ix)
               → ∀ ix m → (unfold φ ix m) ≡ inn ix (mapF (unfold φ) ix (φ ix m))
    unfold-mor' φ ix m = trans (sym (eta ix (unfold φ ix m))) (cong (inn ix) (unfold-mor φ ix m))

    unique' : ∀ {A} → (φ : ∀ x → A x → F A x) → (h : ∀ x → A x → ν x) →
                 (∀ x m → inn x (mapF h x (φ x m)) ≡ h x m) → ∀ x m → h x m ≡ unfold φ x m
    unique' φ h [h] x a = #funext (λ i → uniquê _ (λ x₁ x₂ x₃ → h x₂ x₃ x₁) (λ x₁ x₂ m →
                        trans (trans (mapF-∘ x₂ (φ x₂ m)) (trans (sym (mapF-∘ _ _)) (sym betâ)))
                        (cong (\ f → out̂ _ _ (f x₁)) ([h] x₂ m))) i x a)


    unique : ∀ {A} → (φ : ∀ x → A x → F A x) → (h : ∀ x → A x → ν x) →
                 (∀ x m → (mapF h x (φ x m)) ≡ out x (h x m)) → ∀ x m → h x m ≡ unfold φ x m
    unique φ h [h] = unique' _ h (λ x m → trans (cong (inn x) ([h] x m)) (eta x _))
