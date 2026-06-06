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

is-equiv-Eq-fib : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (y : B) (s t : fib f y)
                → is-equiv (Eq-fib-eq f y s t)
is-equiv-Eq-fib f y s t = (eq-Eq-fib f y s t , is-sec-Eq-fib f y s t) 
                        , (eq-Eq-fib f y s t , is-retr-Eq-fib f y s t)

is-coherently-invertable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) → 𝓤 ⊔ 𝓥 ̇ 
is-coherently-invertable {𝓤} {𝓥} {A} {B} f = Σ g ∶ (B → A) 
                                           , Σ G ∶ (f ∘ g ~ id) 
                                           , Σ H ∶ (g ∘ f ~ id) 
                                           , (G ·r f ~ f ·l H)  

is-coherently-invertable-inverse : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                                 → is-coherently-invertable f → B → A 
is-coherently-invertable-inverse is-coherently-invertable-f = fst is-coherently-invertable-f

is-coherently-invertable-is-sec : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                                → (is-coherently-invertable-f : is-coherently-invertable f) 
                                 → f ∘ is-coherently-invertable-inverse is-coherently-invertable-f ~ id
is-coherently-invertable-is-sec is-coherently-invertable-f = fst (snd is-coherently-invertable-f)

is-coherently-invertable-is-retr : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                                 → (is-coherently-invertable-f : is-coherently-invertable f) 
                                 → is-coherently-invertable-inverse is-coherently-invertable-f ∘ f ~ id
is-coherently-invertable-is-retr is-coherently-invertable-f = fst (snd (snd is-coherently-invertable-f))

is-coherently-invertable-invertable-whiskening : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                                               → (is-coherently-invertable-f : is-coherently-invertable f) 
                                               → (is-coherently-invertable-is-sec is-coherently-invertable-f) ·r f 
                                               ~ f ·l (is-coherently-invertable-is-retr is-coherently-invertable-f)
is-coherently-invertable-invertable-whiskening is-coherently-invertable-f = snd (snd (snd is-coherently-invertable-f)) 

center-fib-coherently-invertable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                                 → is-coherently-invertable f → (b : B) → fib f b
center-fib-coherently-invertable is-coherently-invertable-f b = is-coherently-invertable-inverse is-coherently-invertable-f b 
                                                              , is-coherently-invertable-is-sec is-coherently-invertable-f b

is-contr-coherently-invertable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} 
                               → (is-coherently-invertable-f : is-coherently-invertable f)
                               →  (b : B) →  (s : fib f b) 
                               →  center-fib-coherently-invertable is-coherently-invertable-f b == s
is-contr-coherently-invertable {𝓤} {𝓥} {A} {B} {f} is-coherently-invertable-f b (a , refl _) = eq-Eq-fib f b _ _
    ( H a , (K a · ((right-unit ((f ·l H) a)) ⁻¹)))
    where G = is-coherently-invertable-is-sec is-coherently-invertable-f
          H = is-coherently-invertable-is-retr is-coherently-invertable-f
          K = is-coherently-invertable-invertable-whiskening is-coherently-invertable-f
                                  

is-coherently-invertable-is-contr-fiber : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                                        → is-coherently-invertable f → is-contr-map f
is-coherently-invertable-is-contr-fiber is-coherently-invertable-f b = center-fib-coherently-invertable is-coherently-invertable-f b 
                                                                     , is-contr-coherently-invertable is-coherently-invertable-f b

nat-htpy : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f g : A → B} {x y : A}
         → (H : f ~ g) (p : x == y) → ap f p · H y == H x · ap g p
nat-htpy H (refl x) = right-unit (H x) ⁻¹

nat-htpy-f-id : {A : 𝓤 ̇ } {f : A → A} {x : A}
              → (H : f ~ id) → H (f x) == ap f (H x)
nat-htpy-f-id {𝓤} {A} {f} {x} H = unconcat-right (H (f x)) (ap f (H x)) (H x) 
    ( (H (f x) · H x)          ==⟨ id-to-htpy ⁻¹ ⟩ 
      ((H (f x) · ap id (H x)) ==⟨ nat-htpy' ⁻¹ ⟩ 
      ((ap f (H x) · H x) ∎)))
    where 
        nat-htpy' : ap f (H x) · H x == H (f x) · ap id (H x)
        nat-htpy' = nat-htpy H (H x)

        id-to-htpy : H (f x) · ap id (H x) == H (f x) · (H x)
        id-to-htpy = ap (H (f x) ·_) (ap-id (H x) ⁻¹)

has-inverse-inverse : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} (has-inverse-f : has-inverse f) → B → A
has-inverse-inverse has-inverse-f = fst has-inverse-f

has-inverse-is-sec : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} (has-inverse-f : has-inverse f) → f ∘ has-inverse-inverse has-inverse-f ~ id
has-inverse-is-sec has-inverse-f = fst (snd has-inverse-f)

has-inverse-is-retr : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} (has-inverse-f : has-inverse f) → has-inverse-inverse has-inverse-f ∘ f ~ id 
has-inverse-is-retr has-inverse-f = snd (snd has-inverse-f)

has-inverse-is-sec' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} (has-inverse-f : has-inverse f) → f ∘ has-inverse-inverse has-inverse-f ~ id
has-inverse-is-sec' {𝓤} {𝓥} {A} {B} {f} (g , (G , H)) y = G (f (g y)) ⁻¹ · ap f (H (g y)) · G y 

has-inverse-invertable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} (has-inverse-f : has-inverse f) → f ·l has-inverse-is-retr has-inverse-f ~ has-inverse-is-sec' has-inverse-f ·r f
has-inverse-invertable {𝓤} {𝓥} {A} {B} {f} (g , (G , H)) x = inv-concat (G (f (g (f x)))) (ap f (H x)) (ap f (H (g (f x))) · G (f x)) 
    (
        square-comm-left 
            (G (f (g (f x)))) 
            (ap f (H x)) 
            (ap (f ∘ (g ∘ f)) (H x)) 
            (ap f (H (g (f x)))) 
            (G (f x)) 
            (
                ap (f ∘ (g ∘ f)) (H x)      ==⟨ ap-comp (g ∘ f) f (H x) ⁻¹ ⟩ 
                (ap f (ap (g ∘ f) (H x))    ==⟨ ap (ap f) (nat-htpy-gf-id ⁻¹) ⟩ 
                ((ap f (H (g (f x))))       ∎))
            ) 
            (square ⁻¹) 
    )
    where
        G' = has-inverse-is-sec' (g , (G , H))

        nat-htpy-gf-id : H ((g ∘ f) x) == ap (g ∘ f) (H x)
        nat-htpy-gf-id = nat-htpy-f-id H

        K' : (f ∘ g) ∘ f ~ f
        K' = G ·r f

        square : ap (((f ∘ g) ∘ f)) (H x) · K' (id x) == K' ((g ∘ f) x) · ap (f) (H x)
        square = nat-htpy K' (H x)

has-inverse-is-coherently-invertable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} (has-inverse-f : has-inverse f) → is-coherently-invertable f
has-inverse-is-coherently-invertable has-inverse-f = has-inverse-inverse has-inverse-f 
                                                   , (has-inverse-is-sec' has-inverse-f 
                                                   , (has-inverse-is-retr has-inverse-f 
                                                   , (has-inverse-invertable has-inverse-f ~⁻¹)))

has-inverse-center : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                   → has-inverse f → (b : B) → fib f b
has-inverse-center has-inverse-f b = has-inverse-inverse has-inverse-f b 
                                   , has-inverse-is-sec' has-inverse-f b 

has-inverse-contration : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                       → (has-inverse-f : has-inverse f) → (b : B) → (s : fib f b) →  has-inverse-center has-inverse-f b == s 
has-inverse-contration {𝓤} {𝓥} {A} {B} {f} (g , (G , H)) b (x , refl _) = eq-Eq-fib f b _ _ ((H x) , (((right-unit _) · has-inverse-invertable ((g , (G , H))) x) ⁻¹))

has-inverse-is-contr-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                      → has-inverse f → is-contr-map f
has-inverse-is-contr-map has-inverse-f b = has-inverse-center has-inverse-f b 
                                         , has-inverse-contration has-inverse-f b

is-equiv-is-contr-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                      → is-equiv f → is-contr-map f
is-equiv-is-contr-map is-equiv-f = has-inverse-is-contr-map (is-equiv-has-inverse is-equiv-f)


is-contr-== : {A : 𝓤 ̇ } → is-contr A → (x y : A) → x == y
is-contr-== (c , C) x y = C x ⁻¹ · C y

is-contr-==-contration : {A : 𝓤 ̇ } {x y : A} → (is-contr-A : is-contr A) → (p : x == y) → is-contr-== is-contr-A x y == p
is-contr-==-contration {𝓤} {A} {x} {x} (c , C) (refl x) = left-inv (C x)

is-contr-eq : {A : 𝓤 ̇ } → is-contr A → (x y : A) → is-contr (x == y)
is-contr-eq is-contr-A x y = is-contr-== is-contr-A x y , is-contr-==-contration is-contr-A