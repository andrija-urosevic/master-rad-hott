{-# OPTIONS --safe --without-K #-}

module Contr where

open import Equiv public 

is-contr : (A : 𝓤 ̇ ) → 𝓤 ̇
is-contr A = Σ c ∶ A , ((x : A) → (c == x))

center : {A : 𝓤 ̇ } → is-contr A → A
center {A} (c , _) = c

contraction : {A : 𝓤 ̇ } → (is-contr-A : is-contr A) → (x : A) → (center is-contr-A == x)
contraction {A} (_ , C) = C

contraction-id-~ : {A : 𝓤 ̇ } → (is-contr-A : is-contr A) → const (center is-contr-A) ~ id
contraction-id-~ {A} (_ , C) = C

𝟙-is-contr : is-contr 𝟙
𝟙-is-contr = ⋆ , 𝟙-induction (Id 𝟙 ⋆) (refl ⋆)

Σ-id-is-contr : {A : 𝓤 ̇ } → (a : A) → is-contr (Σ x ∶ A , (a == x))
Σ-id-is-contr {A} a = (a , refl a) , λ pair → uniqueness-refl a (fst pair) (snd pair)

ev-pt : (A : 𝓤 ̇ ) (a : A) (B : A → 𝓥 ̇ ) → ((x : A) → B x) → B a
ev-pt A a B f = f a

is-singleton : (A : 𝓤 ̇ ) (a : A) → (𝓤 ⁺) ̇
is-singleton A a = (B : A → _) → sec (ev-pt A a B)

singleton-induction-is-contr : (A : 𝓤 ̇ ) (is-contr-A : is-contr A) (B : A → 𝓥 ̇ ) (a : A) 
                             → B a → ((x : A) → B x)
singleton-induction-is-contr A (c , C) B a b x = tr B (C a ⁻¹ · C x ) b

singleton-composition-is-contr : (A : 𝓤 ̇ ) (is-contr-A : is-contr A) (B : A → 𝓥 ̇ ) (a : A) 
                               → (ev-pt A a B) ∘ (singleton-induction-is-contr A is-contr-A B a) ~ id
singleton-composition-is-contr A (c , C) B a b = ap (λ ω → tr B ω b) (left-inv (C a))

is-singleton-is-contr : (A : 𝓤 ̇ ) (is-contr-A : is-contr A) (B : A → 𝓥 ̇ ) (a : A) 
                      → sec (ev-pt A a B)
is-singleton-is-contr A is-contr-A B a = singleton-induction-is-contr A is-contr-A B a 
                                       , singleton-composition-is-contr A is-contr-A B a

is-contr-singleton-induction : (A : 𝓤 ̇ ) (a : A)
                             → ((B : A → 𝓤 ̇ ) → B a → ((x : A) → B x)) → is-contr A
is-contr-singleton-induction A a f = a , f (λ x → a == x) (refl a)

is-contr-is-singleton : (A : 𝓤 ̇ ) (a : A)
                      → is-singleton A a → is-contr A
is-contr-is-singleton A a S = is-contr-singleton-induction A a λ B → fst (S B)

fib : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (b : B) → 𝓤 ⊔ 𝓥 ̇ 
fib f b = Σ λ a → f a == b

is-contr-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) → 𝓤 ⊔ 𝓥 ̇ 
is-contr-map f = (b : _) → is-contr (fib f b)

inv-contr-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) 
              → is-contr-map f → B → A
inv-contr-map f is-contr-map-f b = fst (center (is-contr-map-f b))

is-sec-contr-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B)
                 → (is-contr-map-f : is-contr-map f) → f ∘ inv-contr-map f is-contr-map-f ~ id
is-sec-contr-map f is-contr-map-f b = snd (center (is-contr-map-f b))
 
is-retr-contr-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B)
                 → (is-contr-map-f : is-contr-map f) → inv-contr-map f is-contr-map-f ∘ f ~ id
is-retr-contr-map f is-contr-map-f a = ap fst q
    where
        p : f (inv-contr-map f is-contr-map-f (f a)) == f a
        p = is-sec-contr-map f is-contr-map-f (f a)

        q : (inv-contr-map f is-contr-map-f (f a) , p) == (a , refl (f a))
        q = contraction (is-contr-map-f (f a)) (a , refl (f a))

                                     
is-equiv-contr-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B)
                   → is-contr-map f → is-equiv f 
is-equiv-contr-map f is-contr-map-f = has-inverse-is-equiv 
    (inv-contr-map f is-contr-map-f 
    , (is-sec-contr-map f is-contr-map-f 
    , is-retr-contr-map f is-contr-map-f))

Eq-fib : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (y : B) (s t : fib f y) → 𝓤 ⊔ 𝓥 ̇ 
Eq-fib f y (x , p) (x' , p') = Σ α ∶ x == x' , (p == (ap f α) · p')

Eq-fib-refl : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (y : B) (s : fib f y) 
            → Eq-fib f y s s
Eq-fib-refl f y s = refl _ , refl _

Eq-fib-eq : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (y : B) (s t : fib f y) 
          → s == t → Eq-fib f y s t 
Eq-fib-eq f y s s (refl s) = Eq-fib-refl f y s

eq-Eq-fib : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (y : B) (s t : fib f y) 
          → Eq-fib f y s t → s == t
eq-Eq-fib f y (x , p) (x , p) (refl _ , refl _) = refl _

is-sec-Eq-fib : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (y : B) (s t : fib f y) 
              → Eq-fib-eq f y s t ∘ eq-Eq-fib f y s t ~ id
is-sec-Eq-fib f y (x , p) (x , p) (refl _ , refl _) = refl _

is-retr-Eq-fib : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (y : B) (s t : fib f y) 
               → eq-Eq-fib f y s t ∘ Eq-fib-eq f y s t ~ id
is-retr-Eq-fib f y s s (refl s) = refl _
