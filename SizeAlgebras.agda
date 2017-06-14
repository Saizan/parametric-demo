{-# OPTIONS --rewriting #-}
module SizeAlgebras where

open import lib.Equivalences

open import EquivalenceReasoning

open import Primitives
open import TypeSystem
open import ParamSize

map∃i : ∀ {a b} → {A :{ # } Size → Set a} → {B :{ # } Size → Set b} → (∀i \ i → A i → B i) → ∃i A → ∃i B
map∃i f = #split' _ (λ x a → [# x , f x a ])

map∃i-∘ : ∀ {a b c}{A :{ # } Size → Set a}{B :{ # } Size → Set b}{C :{ # } Size → Set c}
          → {f : ∀i \ i → B i → C i} → {g : ∀i \ i → A i → B i} →
          ∀ x → map∃i f (map∃i g x) ≡ map∃i (\ i x → f i (g i x)) x
map∃i-∘ = #split' _ (λ x a → refl _)

map∃i-id : ∀ {a}{A :{ # } Size → Set a} → ∀ x → map∃i {a} {a} {A} {A} (\ i x → x) x ≡ x
map∃i-id = #split' _ (\ x a → refl _)

module Initial (X :{ # } Set) (F :{ # } (X -> Set) -> (X -> Set))
               (mapF : {A B :{ # } X → Set} → (∀ x → A x → B x) → ∀ x → F A x → F B x)
               (mapF-∘ : {A B C :{ # } X → Set} →
                         {f : ∀ x → A x → B x}{g : ∀ x → B x → C x} →
                         ∀ x a → mapF g x (mapF f x a) ≡ mapF (\ x a → g x (f x a)) x a)
  where

  ◆ : (Size → X → Set) → Size → X → Set
  ◆ A i x = ∃i \ j → (j < i) × A j x

  extract : ∀ {A :{ # } Set} → ∀i \ i → (∃i \ j → (j < i) × A) → A
  extract i = #split' _ (\ _ → #uncurry \ _ a → a)

  _⇛_ :{ # } (A B : Size → X → Set) → Set
  A ⇛ B = ∀i \ i → ∀ (x : X) → A i x → B i x

  map◆ : h#Π _ \ A → h#Π _ \ B →  (A ⇛ B) → ◆ A ⇛ ◆ B
  map◆ f i x = #split' _ (λ j → #uncurry \ j<i  a → [# j , [ j<i , f j x a ] ])

  _[◆_] : ((X -> Set) -> (X -> Set)) → (Size → X → Set) → (Size → X → Set)
  (F [◆ A ]) i x = F (\ y → ◆ A i y) x

  map[◆ : ∀ {A B} → (A ⇛ B) → (F [◆ A ]) ⇛ (F [◆ B ])
  map[◆ f i x = mapF (\ x → map◆ f i x) x

  typecan :{ # } Set₁
  typecan = ∀ {A :{ # } _} → ∀ x → (∃i \ i → (F [◆ A ]) i x) →
                      F (\ x' → ∃i \ i → A i x') x
  can : typecan
  can x = #split' _ (λ { i y → mapF (\ x → map∃i (\ _ → snd)) x y })

  unique-fix : ∀ {A : Size → Set} f → ∀ {u} → (u ≡ \ i → f i (\ j _ → u j)) → u ≡ fix A f
  unique-fix {A} f {u} p = funext (fix _ (λ i x → trans (trans (TypeSystem.cong (λ f₁ → f₁ i) p)
                               (TypeSystem.cong (f i) (funext (λ a → funext \ a< → x a a<))))
                               (TypeSystem.sym (fix-unfold A f i))))

  #unique-fix : ∀ {A :{ # } Size → Set} f → ∀ {u : ∀i A} → (u ≡ ( \ i → f i (\ j _ → u j) )) → u ≡ #fix A f
  #unique-fix f p = #funext (#fix _ (λ i x → trans (trans (TypeSystem.cong (λ f₁ → f₁ i) p)
                               (TypeSystem.cong (f i) (#funext (λ a → funext \ a< → x a a<))))
                               (TypeSystem.sym (#fix-unfold _ f i))))

  μ̂  :{ # } (Size → X → Set)
  μ̂  = (fix _ (λ i A → F (λ y → ∃i (λ j → Σ _ (λ j<i → A j j<i y)))))

  inn̂ : (F [◆ μ̂  ]) ⇛ μ̂
  inn̂ i x = subst (\ f → f x) (sym (fix-unfold _ (λ i A → F (λ y → ∃i (λ j → Σ _ (λ j<i → A j j<i y)))) i))

  out̂ : μ̂  ⇛ (F [◆ μ̂  ])
  out̂ i x = subst (\ f → f x) (fix-unfold _ (λ i A → F λ y → ∃i λ j → Σ _ λ j<i → A j j<i y) i)

  betâ : {i :{ # } Size} → ∀ {x fm} →  out̂ i x (inn̂ i x fm) ≡ fm
  betâ {i} = subst-sym ((fix-unfold _ (λ i A → F (λ y → ∃i (λ j → Σ _ (λ j<i → A j j<i y)))) i)) where
    subst-sym : ∀ {a} {p} → {A :{ # } Set a} → {P :{ # } A → Set p}
                → {x y :{ # } A} → (eq : x ≡ y) {m : _} → subst P eq (subst P (sym eq) m) ≡ m
    subst-sym {P = P} eq {m} = J eq (\ y eq → (m : _) → subst P eq (subst P (sym eq) m) ≡ m ) refl m

  etâ : {i :{ # } Size} → ∀ {x fm} → inn̂ i x (out̂ i x fm) ≡ fm
  etâ {i} = subst-sym (((fix-unfold _ (λ i A → F (λ y → ∃i (λ j → Σ _ (λ j<i → A j j<i y)))) i)))
   where
    subst-sym : ∀ {a} {p} → {A :{ # } Set a} → {P :{ # } A → Set p}
                → {x y :{ # } A} → (eq : x ≡ y) {m : _} → subst P (sym eq) (subst P eq m) ≡ m
    subst-sym {P = P} eq {m} = J eq (\ y eq → (m : _) → subst P (sym eq) (subst P eq m) ≡ m ) refl m

  mutual
    foldR : ∀ {A :{ # } _} → (F [◆ A ]) ⇛ A → ∀i \ i → _
    foldR {A} φ = (λ i fold' x m → φ i x (mapF (\ x → map∃i (\ j → #uncurry \ j<i m → [ j<i , fold' j j<i x m ])) x m))
    foldF : ∀ {A :{ # } _} → (F [◆ A ]) ⇛ A → ∀i \ i → _
    foldF {A} = \ φ → (λ i fold' x m → foldR φ i fold' x (out̂ i x m))

    fold̂ : ∀ {A :{ # } _} → (F [◆ A ]) ⇛ A → μ̂  ⇛ A
    fold̂ {A} φ = #fix _    (foldF {A} φ)

  fold̂-mor : ∀ {A} → (φ : (F [◆ A ]) ⇛ A) → ∀i \ i → ∀ x fm → fold̂ φ i x (inn̂ i x fm) ≡ φ i x (map[◆ (fold̂ φ) i x fm)
  fold̂-mor φ i x fm = trans (cong (λ f → f x (inn̂ i x fm)) (#fix-unfold _ (foldF φ) i))
                            (cong (foldR φ _ (\ j _ → #fix _ (foldF φ) j) _) betâ)

  fold̂-mor2 : ∀ {A} → (φ : (F [◆ A ]) ⇛ A) → ∀i \ i → ∀ x m → fold̂ φ i x m ≡ φ i x (map[◆ (fold̂ φ) i x (out̂ i x m))
  fold̂-mor2 φ i x m =((cong (λ f → f x m) (#fix-unfold _ (foldF φ) i)))

  uniquê : ∀ {A} → (φ : (F [◆ A ]) ⇛  A) → (h : μ̂  ⇛ A) →
                 (∀i \ i → ∀ x m → φ i x (map[◆ h i x (out̂ i x m)) ≡ h i x m ) → ∀i \ i → ∀ x m → h i x m ≡ fold̂ φ i x m
  uniquê φ h [h] i x m = cong (λ g → g i x m) (#unique-fix
                ((λ i fold' x m → φ i x (mapF (\ x → map∃i (\ j → #uncurry \ j<i  m → [ j<i , fold' j j<i x m ])) x (out̂ i x m))))
           {u = h} (sym (#funext (λ i → funext (λ x → funext \ m →  [h] i x m )))))

  μ :{ # } X → Set
  μ x = ∃i \ i → μ̂  i x


  module F-commutes (comm : ∀ {A :{ # } _} x → is-equiv (can {A} x)) where

    inn : ∀ x → F μ x → μ x
    inn x ts = map∃i (\ i → inn̂ i x) (#≅.inv ([ _ , comm x ]) ts)

    out : ∀ x → μ x → F μ x
    out x m = can x (map∃i (λ i → out̂ i x) m)


    beta : ∀ x m → (out x (inn x m)) ≡ m
    beta x m = trans (cong (can {A = μ̂ } x)
              (trans (map∃i-∘ m')
              (trans (cong (λ f → map∃i f m') (#funext (λ i → funext (\ a → betâ)))) (map∃i-id m'))))
                           (#≅.coeinv' ([ _ , comm x ]) m)
           where m' = (#≅.inv ([ _ , comm x ]) m)

    eta : ∀ x m → (inn x (out x m)) ≡ m
    eta x m = trans (cong (map∃i (λ i → inn̂ i x)) {#≅.inv ([ _ , comm x ]) (out x m)}
                                (#≅.invcoe' ([ _ , comm x ]) ((map∃i (λ i → out̂ i x) m))))
                    (trans (map∃i-∘ m) (trans (cong (\ f → map∃i f m) (#funext \ x → funext \ z → etâ)) (map∃i-id m)))

    fold : ∀ {A :{ # } _} → (∀ x → F A x → A x) → ∀ x → μ x → A x
    fold {A} φ x = #split' _ (\ i → fold̂ (λ { i x fm → φ x (mapF (\ _ → extract i) x fm) })
                                      i x)

    fold-mor : ∀ {A} → (φ : ∀ ix → F A ix → A ix)
               → ∀ ix m → fold φ ix m ≡ φ ix (mapF (fold φ) ix (out ix m))
    fold-mor φ ix = #split' _ (λ i a → trans ((fold̂-mor2 (λ { i x fm → φ x (mapF (\ _ → extract i) x fm) }) i ix a))
                                             ((cong (φ ix)
                                                    (trans (mapF-∘ _ _)
                                                    (trans (cong (\ f → mapF f ix (out̂ i ix (a)))
                                                           (funext (\ _ → funext (#split' _ (λ _ _ → refl _)))))
                                                           (sym (mapF-∘ _ _)))))))

    fold-mor' : ∀ {A} → (φ : ∀ ix → F A ix → A ix)
               → ∀ ix m → fold φ ix (inn ix m) ≡ φ ix (mapF (fold φ) ix m)
    fold-mor' φ ix m = trans (fold-mor φ ix (inn ix m)) (cong (λ fm → φ ix (mapF (fold φ) ix fm)) (beta ix m))

    unique : ∀ {A} → (φ : ∀ x → F A x → A x) → (h : ∀ x → μ x → A x) →
                 (∀ x m → φ x (mapF h x (out x m)) ≡ h x m) → ∀ x m → h x m ≡ fold φ x m
    unique φ h [h] x = #split' _ (λ i m →
      uniquê (λ { i x fm → φ x (mapF (\ _ → extract i) x fm) })
             (λ i x m → h x ([# i , m ]))
             (λ i x m → trans (cong (φ x)
                                   (trans (mapF-∘ x (out̂ i x m))
                                   (trans (cong (λ f → mapF f x (out̂ i x m))
                                                ((funext (\ x → funext (#split' _ (\ _ _ → refl _)))) ))
                                           (sym (mapF-∘ _ _)))))
                              ([h] x ([# i , m ]))) i x m)

    unique' : ∀ {A} → (φ : ∀ x → F A x → A x) → (h : ∀ x → μ x → A x) →
                 (∀ x m → φ x (mapF h x m) ≡ h x (inn x m)) → ∀ x m → h x m ≡ fold φ x m
    unique' φ h [h] = unique φ h aux
       where
         aux : ∀ x m → φ x (mapF h x (out x m)) ≡ h x m
         aux x m = trans ([h] x (out x m)) (cong (h x) (eta x m))
