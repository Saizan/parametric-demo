{-# OPTIONS --rewriting #-}
module ParamSize where

open import Primitives
open import TypeSystem

open import lib.Equivalences
open import lib.types.Sigma using (equiv-Σ-fst)
import lib.Base using (ap)
open import EquivalenceReasoning

postulate
  Size : Set
  _≤_ : Size → Size → Set
  refl≤ : {x :{ # } Size} → x ≤ x
  max : Size → Size → Size
  max-fst : {i j :{ # } Size} → i ≤ max i j
  max-snd : {i j :{ # } Size} → j ≤ max i j
  s0 : Size
  ↑ : Size → Size
  -- the term `(m ~> n) i` can be implemented in ParamDTT as `fill (i = 0 ? m | i = 1 ? n)`
  _~>_ : Size → Size → 𝕀 → Size
  ~-0 : ∀ i j → (i ~> j) b0 ≡ i
  ~-1 : ∀ i j → (i ~> j) b1 ≡ j

{-# REWRITE ~-0 ~-1 #-}

postulate
  -- the term `≤-~ i f i≤0 i≤1 b` can be implemented in ParamDTT as `fill≤ (b = 0 ? i≤0 | b = 1 i≤1)`
  -- this has type `(fill (b = 0 ∨ b = 1 ? i)) ≤ (fill (b = 0 ? f 0 | b = 1 ? f 1))`, which by t=-Size-codisc
  -- equals `i ≤ f b`
  ≤-~ : ∀ i → (f :{ # } 𝕀 → Size) → (i≤0 : i ≤ f b0) (i≤1 : i ≤ f b1) →
              (b :{ # } 𝕀) → i ≤ f b
  ≤-~0 : ∀ i (f : 𝕀 → Size) → (i≤0 : i ≤ f b0) (i≤1 : i ≤ f b1)
         → ≤-~ i f i≤0 i≤1 b0 ≡ i≤0
  ≤-~1 : ∀ i (f : 𝕀 → Size) → (i≤0 : i ≤ f b0) (i≤1 : i ≤ f b1)
         → ≤-~ i f i≤0 i≤1 b1 ≡ i≤1

{-# REWRITE ≤-~0 ≤-~1 #-}

_<_ : Size → Size → Set
i < j = ↑ i ≤ j

postulate
  fix : ∀ {la} → (A :{ # } Size → Set la) → (∀ i → (∀ j → j < i → A j) → A i) → ∀ i → A i
  #fix : ∀ {la} (A :{ # } Size → Set la) → ((i :{ # } Size) → ((j :{ # } Size) → j < i → A j) → A i) → (i :{ # } Size) → A i
  fix-unfold : ∀ {la} → (A :{ # } Size → Set la) → (f :{ # } ∀ i → (∀ j → j < i → A j) → A i) →
               (i :{ # } Size) → fix A f i ≡ f i (\ j _ → fix A f j)
  #fix-unfold : ∀ {la} → (A :{ # } Size → Set la) → (f :{ # } (i :{ # } Size) → ((j :{ # } Size) → j < i → A j) → A i) →
                 (i :{ # } Size) → #fix A f i ≡ f i (\ j _ → #fix A f j)


∮♯ : ∀ {l} → Set l → Set l
∮♯ A = #Σ A (\ _ → ⊤)

∮♯in : ∀ {l} {A : Set l} → #Π A \ _ → ∮♯ A
∮♯in x = [# x , tt ]

elim∮♯ : ∀ {la lb} {A : Set la} {B : ∮♯ A → Set lb} (f : #Π A \ a → B (∮♯in a)) → ∀ ∮♯a → B ∮♯a
elim∮♯ {B = B} f ∮♯a = #split ∮♯a B (λ x → unit (f x))

#split' : ∀{ℓA ℓB ℓC} → h#Π (Set ℓA) λ A → h#Π (A → Set ℓB) λ B
    → #Π (#Σ A B → Set ℓC) λ C
    → Π (#Π A λ a → Π (B a) λ b → C [# a , b ]) λ c
    → Π (#Σ A B) λ p
    → C p
#split' C f p = #split p C f

Size-squash : ∀ (i j : ∮♯ Size) → i ≡ j
Size-squash = elim∮♯ (\ i → elim∮♯ (\ j → path-to-eq (\ b → ∮♯in ((i ~> j) b))))

∃i : ∀ {l} → (Size → Set l) → Set l
∃i A = #Σ Size A

∃proof : ∀ {l}{A : Set l} → (i j : Size)(a : A) → [# i , a ] ≡ [# j , a ]
∃proof i j a = path-to-eq (\ b → [# (i ~> j) b , a ])

∀i : ∀ {l} (A : Size → Set l) → Set l
∀i A = (#Π Size \ i → A i)

∀proof : ∀ {l}{A :{ # } Set l} → (i j :{ # } Size)(a : ∀i \ _ → A) → a i ≡ a j
∀proof i j a = path-to-eq (\ b → a ((i ~> j) b))

module Sigma2 {la lb} {A : Set la} {B C : A → Set lb} (B≅C : ∀ a → B a ≅ C a) where

  Σ≅ : Σ A B ≅ Σ A C
  Σ≅ = con' (λ x → [ (fst x) , B≅C.coe (snd x) ]) (λ x → [ (fst x) , (B≅C.inv (snd x)) ])
        (#uncurry (\ x y → cong ([_,_] x) (B≅C.coeinv)))
        ((#uncurry (\ x y → cong ([_,_] x) (B≅C.invcoe))) )
       where
           module B≅C {a} = _≅_ ( (B≅C a) )

module #Sigma2 {la lb}  where

  Σ≅ : h#Π _ \ (A : Set la) → h#Π _ \ (B : A → Set lb) → h#Π _ \ (C : A → Set lb) → (B≅C : h#Π _ \ a → B a ≅ C a) → #Σ A B ≅ #Σ A C
  Σ≅ {A} {B} {C} B≅C
    = con' (#split' _ (λ x a → [# x , fst (B≅C {x}) a ])) (#split' _ (λ x a → [# x , #≅.inv (B≅C {x}) a ]))
         (#split' _ (λ x a → cong ([# x ,_]) (#≅.coeinv (B≅C {x})))) ((#split' _ (λ x a → cong ([# x ,_]) (#≅.invcoe (B≅C {x})))))

fromEq : ∀ {l} {A B : Set l} (eq : A ≡ B) → A ≅ B
fromEq {A = A} p = J p (\ B _ → A ≅ B) (con (λ z → z) (λ z → z) (λ {b} → refl _) (λ {a} → refl _))

module SigmaΠ {X : Set} {A : X → Set} {B : (x : X) → A x -> Set} where

  iso : Σ ((x : X) → A x) (λ f → ∀ i → B i (f i)) ≅ ∀ i → Σ (A i) (B i)
  iso = con (λ x i → [ fst x i , snd x i ]) (λ x → [ (λ x₁ → fst (x x₁)) , (λ i → snd (x i)) ]) (refl _) (refl _)

#λ : ∀ {a b} {A :{ # } Set a} {B :{ # } A → Set b} → ((x :{ # } A) → B x) → ((x :{ # } A) → B x)
#λ f = f

module Sigma#Π {X : Set} {A : X → Set} {B : (x : X) → A x -> Set} where

  iso : Σ (#Π X \ (x : X) → A x) (λ f → #Π X \ (x : X) → B x (f x)) ≅ (#Π X \ (x : X) → Σ (A x) (B x))
  iso = con {A = Σ (#Π X \ (x : X) → A x) (λ f → #Π X \ (x : X) → B x (f x))}
            {B = (#Π X \ (x : X) → Σ (A x) (B x))}
            (λ x i → [ fst x i , snd x i ]) (λ x → [ #λ (λ x₁ → fst (x x₁)) , #λ (λ i → snd (x i)) ]) (refl _) (refl _)


module ∀Disc {la li} {A : Set la} {I : Set li} (squash : ∀ (x y : ∮♯ I) → x ≡ y) where

  iso : #Π _ \ (i : I) → A ≅ (#Π I \ _ → A)
  iso i = con {A = A} {B = (#Π I \ _ → A)} (\ a i → a) (\ f → f i) (\ {f} → #funext (\ x → cong (elim∮♯ f) (squash (∮♯in i) (∮♯in x)))) (refl _)

module Top {li}  where
  iso : h#Π _ \ (B : Set li) → (b : B) (Bprop : ∀ (x y : B) → x ≡ y) → ⊤ ≅ B
  iso b Bprop = con' (\ _ → b) (\ _ → tt) (λ b₁ → Bprop b b₁) (unit (refl _))

module Contr {la li}  where
  iso : h#Π _ \ (A : Set la) → h#Π _ \ (B : Set li) → (b : B) (Bprop : ∀ (x y : B) → x ≡ y) → A ≅ (B → A)
  iso {A} {B} b Bprop = con' (λ x x₁ → x) (\ f → f b) (\ f → funext (\ a → cong f (Bprop _ _))) (\ _ → (refl _))


module #Sigma {a b c} {A : Set a}{B : Set b} {C : A → B → Set c} where
  iso : Σ A (\ a → #Σ B \ b → C a b) ≅ (#Σ B \ b → Σ A \ a → C a b)
  iso = con' (#uncurry (\ x → #split' _ (λ x₁ a₁ → [# x₁ , [ x , a₁ ] ]) )) (#split' _ (\ x → #uncurry (λ x₁ y → [ x₁ , [# x , y ] ])))
                 proof3   proof2
    where
      proof2 :
           (b₁ : Σ A (λ z → #Σ B (C z))) →
         #split
         (#split (snd b₁) (λ _ → #Σ B (λ v → Σ A (λ v₁ → C v₁ v)))
          (λ x₁ a₁ → [# x₁ , [ fst b₁ , a₁ ] ]))
         (λ _ → Σ A (λ z → #Σ B (C z)))
         (λ x xy → [ fst xy , [# x , snd xy ] ])
         ≡ b₁
      proof2 = #uncurry (\ x → #split' _ (λ x₁ a₁ → refl _))
      proof3 : (b₁ : #Σ B (λ v → Σ A (λ v₁ → C v₁ v))) →
               #uncurry
            (λ x →
               #split' (λ _ → #Σ B (λ v → Σ A (λ v₁ → C v₁ v)))
               (λ x₁ a₁ → [# x₁ , [ x , a₁ ] ]))
            (#split' (λ _ → Σ A (λ z → #Σ B (λ z₁ → C z z₁)))
             (λ x → #uncurry (λ x₁ y → [ x₁ , [# x , y ] ])) b₁)
            ≡ b₁
      proof3 = #split' _ (\ x → λ a₁ → refl _)

module Plus where

  iso∃i : {A B : Size -> Set} → ((∃i \ i → A i) + (∃i \ j → B j)) ≅ ∃i \ i → A i + B i
  iso∃i {A} {B} = begin
   (∃i (λ i → A i) + ∃i (λ j → B j))                      ≈⟨ Sigma2.Σ≅ (bool (fromEq (refl _)) (fromEq (refl _))) ⟩
   Σ Bool (λ b → (#Σ Size λ i → if b then A i else B i))  ≈⟨ #Sigma.iso  ⟩
   (∃i \ i → A i + B i)                                   ∎

  iso∀i : {A B : Size -> Set} → (∀i A + ∀i B) ≅ (∀i \ i → A i + B i)
  iso∀i {A} {B} = begin
             (∀i A + ∀i B)                                               ≈⟨ Sigma2.Σ≅ (bool (fromEq (refl _)) (fromEq (refl _))) ⟩
             Σ Bool (λ b → ∀i \ i → if b then A i else B i)              ≈⟨ equiv-Σ-fst _ (snd (∀Disc.iso Size-squash s0)) ⟩
             Σ (∀i \ _ → Bool) (λ f → ∀i \ i → if f i then A i else B i) ≈⟨ Sigma#Π.iso ⟩
             (∀i \ i → A i + B i)                                        ∎


equiv-#Π-r : ∀ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k}
  → (#Π A \ x  → B x ≃ C x) → #Π A B ≃ #Π A C
equiv-#Π-r {A = A} {B = B} {C = C} k = con' f g f-g g-f
  where f : #Π A B → #Π A C
        f c x = #≅.coe (k x) (c x)

        g : #Π A C → #Π A B
        g d x = #≅.inv (k x) (d x)

        f-g : ∀ d → f (g d) ≡ d
        f-g d = #funext (λ x →  #≅.coeinv' (k x) (d x))

        g-f : ∀ c → g (f c) ≡ c
        g-f c = #funext (λ x → #≅.invcoe' (k x) (c x))

∃iprop : #Π _ \ x → (x₁ y : #Σ Size (_≤_ (↑ x))) → x₁ ≡ y
∃iprop x = #split' _ (\ i ≤i → #split' _ (\ j ≤j → path-to-eq (\ b → [# ( i ~> j) b , ≤-~ (↑ x) (i ~> j) ≤i ≤j b ])))


equiv-×-fst : ∀ {i j k} → h#Π (Set i) \ A → h#Π (Set j) \ B → h#Π _ \ (P : Set k) →
                  A ≅ B → (A × P) ≃ (B × P)
equiv-×-fst {k = _} {A} {B} {P} e = equiv-Σ-fst (\ _ → P) (snd e)


module Force∀ {l} {A : Size → Set l} where

  iso : (∀i A) ≅ (∀i \ i → ∀i \ j → (j < i) → A j)
  iso = begin (∀i \ j → A j)                      ≈⟨  equiv-#Π-r (\ x →  Contr.iso [# ↑ x , refl≤ ] (∃iprop x))  ⟩
              (∀i \ j → (∃i \ i → j < i) → A j)   ≈⟨  con {A = (∀i \ j → (∃i \ i → j < i)  → A j)}
                                                               {B = (∀i \ i → ∀i \ j → (j < i) → A j)}
                                                               (λ z i j z₁ → z j ([# i , z₁ ])) (λ x j → #split' _ \ i p → x i j p) (refl _)
                                                               (#funext (\ i → funext (#split' _ (\ x p → (refl _)))))  ⟩
              (∀i \ i → ∀i \ j → (j < i) → A j)     ∎


module Force∃ {A : Size → Set} where

  iso : (∃i \ j → A j) ≅ (∃i \ i → ∃i \ j → (↑ j ≤ i) × A j)
  iso = begin (∃i \ j → A j)                           ≈⟨ #Sigma2.Σ≅ (\ {j} → con' (\ a → [ tt , a ]) snd (#uncurry (unit (\ _ → refl _))) (\ _ → (refl _)))  ⟩
              (∃i \ j → ⊤ × A j)                       ≈⟨ #Sigma2.Σ≅ (\ {j} → equiv-×-fst (Top.iso [# ↑ j , refl≤ ] (∃iprop j)))  ⟩
              (∃i \ j → ((∃i \ i → ↑ j ≤ i) × A j))   ≈⟨  shuffling  ⟩
              (∃i \ i → ∃i \ j → (↑ j ≤ i) × A j)       ∎
   where
    shuffling : (∃i \ j → ((∃i \ i → ↑ j ≤ i) × A j)) ≅ (∃i \ i → ∃i \ j → (↑ j ≤ i) × A j)
    shuffling = con' (#split' _ (\ i → #uncurry (#split' _ (\ j → λ a y → [# j , [# i , [ a , y ] ] ] ))))
                     (#split' _ (\ i → #split' _ (\ j → #uncurry (λ x y → [# j , [ [# i , x ] , y ] ]))))
                     (#split' _ (\ i → #split' _ (\ j → #uncurry (λ x y → (refl _)))))
                     ((#split' _ (\ i → #uncurry (#split' _ (\ j → λ a y → (refl _) )))))


module Sigma∃ {A : Set} {B : Size → A → Set} where
  iso : Σ A (\ a → ∃i \ i → B i a) ≅ ∃i (\ i → Σ A (B i))
  iso = #Sigma.iso

module Sigma∀ {A : Set} {B : Size → A → Set} where
  iso : Σ A (\ a → ∀i \ i → B i a) ≅ ∀i (\ i → Σ A (B i))
  iso = begin Σ A (\ a → ∀i \ i → B i a) ≈⟨ equiv-Σ-fst _ (snd (∀Disc.iso Size-squash s0)) ⟩ --
              Σ (∀i \ _ → A) (\ f → ∀i \ i → B i (f i)) ≈⟨ Sigma#Π.iso ⟩
              ∀i (\ i → Σ A (B i)) ∎

module Prod∃ {la lb} {A : Size → Set la}{B : Size → Set lb} where

  iso : ((∃i \ i → A i) × (∃i \ i → B i)) ≅ (∃i \ i → (∃i \ j → (j < i) × A j) × (∃i \ j → (j < i) × B j))
  iso = begin ((∃i \ i → A i) × (∃i \ i → B i))                                    ≈⟨  shuffling  ⟩
              (∃i \ ja → ∃i \ jb → ⊤ × (A ja × B jb))                              ≈⟨  (#Sigma2.Σ≅ \ {ja} → (#Sigma2.Σ≅ \ {jb} →
                                                                                         (equiv-×-fst ( (Times-codisc {ja}{jb}) ))))  ⟩
              (∃i \ ja → ∃i \ jb → (∃i \ i → (ja < i) × (jb < i)) × (A ja × B jb)) ≈⟨  shuffling2  ⟩
              (∃i \ i → (∃i \ j → (j < i) × A j) × (∃i \ j → (j < i) × B j))       ∎
   where
     Times-codisc : h#Π _ \ ja → h#Π _ \ jb → ⊤ ≅ (∃i \ i → (ja < i) × (jb < i))
     Times-codisc {ja} {jb} = Top.iso [# max (↑ ja) (↑ jb) , [ max-fst , max-snd ] ]
                  (#split' _ (\ i p → #split' _ \ j p' → path-to-eq (λ x → [# (i ~> j) x ,
                    [ (≤-~ (↑ ja) ((i ~> j)) (fst p) (fst p')  x) , (≤-~ (↑ jb) ((i ~> j)) (snd p) (snd p') x) ] ])))
     shuffling : ((∃i \ i → A i) × (∃i \ i → B i)) ≅ (∃i \ ja → ∃i \ jb → ⊤ × (A ja × B jb))
     shuffling = con' (#uncurry (#split' _ (\ i a → #split' _ (\ j b → [# i , [# j , [ tt , [ a , b ] ] ] ]))))
                      (#split' _ (\ i → #split' _ (\ j p →  [ [# i , fst (snd p) ] , [# j , snd (snd p) ] ] )))
                      ((#split' _ (\ i → #split' _ (\ _ → #uncurry (unit (\ _ → refl _))))))
                      ((#uncurry (#split' _ (\ i a → #split' _ (\ j b → (refl _))))))
     shuffling2 : (∃i \ ja → ∃i \ jb → (∃i \ i → (ja < i) × (jb < i)) × (A ja × B jb)) ≅ (∃i \ i → (∃i \ j → (j < i) × A j) × (∃i \ j → (j < i) × B j))
     shuffling2 = con' (#split' _ (\ i → #split' _ (\ j → #uncurry (#split' _ (\
                          m → #uncurry \ i< j< → #uncurry \ a b → [# m , [ [# i , [ i< , a ] ] , [# j , [ j< , b ] ] ] ])))))
                       (#split' _ (\ m → #uncurry (#split' _ (\
                          i → #uncurry \ i< a → #split' _ \ j → #uncurry \ j< b -> [# i , [# j , [ [# m , [ i< , j< ] ] , [ a , b ] ] ] ] ))))
                       (#split' _ (\ m → #uncurry (#split' _ (\ i _ → #split' _ (\ j → #uncurry \ _ _ → refl _)))))
                       (#split' _ (\ i → #split' _ (\ j → #uncurry (#split' _ (\ m → \ _ → #uncurry \ _ _ → refl _)))))
