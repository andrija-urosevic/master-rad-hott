{-# OPTIONS --without-K --safe #-}

module Equiv where

open import MLTT public

_~_ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (f g : (x : A) → B x) → (𝓤 ⊔ 𝓥) ̇ 
f ~ g = (x : _) → (f x) == (g x)

infixl 10 _~_

refl-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
       → (f : (x : A) → B x) → f ~ f 
refl-~ f x = refl (f x)

inv-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : (x : A) → B x} 
      → f ~ g → g ~ f
inv-~ H x = H x ⁻¹ 

_~⁻¹ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : (x : A) → B x} 
    → f ~ g → g ~ f
H ~⁻¹ = inv-~ H

infixl 12 _~⁻¹

concat-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g h : (x : A) → B x} 
         → f ~ g → g ~ h → f ~ h
concat-~ H K x = H x · K x

_▣_ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g h : (x : A) → B x} 
    → f ~ g → g ~ h → f ~ h 
H ▣ K = concat-~ H K

_~〈_〉_ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f : (x : A) → B x) {g h : (x : A) → B x} 
       → f ~ g → g ~ h → f ~ h
f ~〈 H 〉 K = H ▣ K 

infixl 11 _▣_

assoc-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → {f g h i : (x : A) → B x} 
        → (H : f ~ g) → (K : g ~ h) → (L : h ~ i) 
        → H ▣ K ▣ L ~ H ▣ (K ▣ L)
assoc-~ H K L x = assoc (H x) (K x) (L x)

left-unit-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → {f g : (x : A) → B x} 
            → (H : f ~ g) 
            → refl-~ f ▣ H ~ H 
left-unit-~ H x = left-unit (H x)

right-unit-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : (x : A) → B x} 
             → (H : f ~ g) 
             → H ▣ refl-~ g ~ H
right-unit-~ H x = right-unit (H x)

left-inv-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : (x : A) → B x} 
           → (H : f ~ g)
           → H ~⁻¹ ▣ H ~ refl-~ g 
left-inv-~ H x = left-inv (H x)

right-inv-~ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : (x : A) → B x}
            → (H : f ~ g)
            → H ▣ H ~⁻¹ ~ refl-~ f 
right-inv-~ H x = right-inv (H x)

left-whisk-~ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → {C : 𝓦 ̇ } {f g : A → B}
             → (h : B → C) → (H : f ~ g)
             → h ∘ f ~ h ∘ g
left-whisk-~ h H x = ap h (H x)

_~l_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → {C : 𝓦 ̇ } {f g : A → B}
     → (h : B → C) → (H : f ~ g)
     → h ∘ f ~ h ∘ g
h ~l H = left-whisk-~ h H

right-whisk-~ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → {C : 𝓦 ̇ } {g h : B → C}
              → (f : A → B) → (H : g ~ h)
              → g ∘ f ~ h ∘ f 
right-whisk-~ f H x = H (f x)

_~r_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → {C : 𝓦 ̇ } {g h : B → C}
     → (f : A → B) → (H : g ~ h)
     → g ∘ f ~ h ∘ f 
f ~r H = right-whisk-~ f H 

sec : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
    → (f : A → B)
    → (𝓤 ⊔ 𝓥) ̇ 
sec {𝓤} {𝓥} {A} {B} f = Σ g ∶ (B → A) , (f ∘ g ~ id)

retr : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
     → (f : A → B) 
     → (𝓤 ⊔ 𝓥) ̇
retr {𝓤} {𝓥} {A} {B} f = Σ h ∶ (B → A) , (h ∘ f ~ id)

_retract-of_ : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) → (𝓤 ⊔ 𝓥) ̇
A retract-of B = Σ f ∶ (A → B) , retr f

is-equiv : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
         → (f : A → B) 
         → (𝓤 ⊔ 𝓥) ̇
is-equiv f = sec f × retr f 

_≃_ : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) → (𝓤 ⊔ 𝓥) ̇
A ≃ B = Σ f ∶ (A → B) , is-equiv f

is-equiv-id : (A : 𝓤 ̇ ) → is-equiv (id {𝓤} {A})
is-equiv-id A = (id , refl-~ id) , (id , (refl-~ id))

id-equiv : (A : 𝓤 ̇ ) → A ≃ A 
id-equiv A = id , is-equiv-id A

has-inverse : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (f : A → B) → (𝓤 ⊔ 𝓥) ̇
has-inverse {𝓤} {𝓥} {A} {B} f = Σ g ∶ (B → A) , ((f ∘ g ~ id) × (g ∘ f ~ id))

has-inverse-is-equiv : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                     → has-inverse f → is-equiv f 
has-inverse-is-equiv (g , (H , K)) = (g , H) , (g , K)

is-equiv-aux-htpy : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                  → (is-equiv-f : is-equiv f) 
                  → fst (fst is-equiv-f) ~ fst (snd is-equiv-f)
is-equiv-aux-htpy {𝓤} {𝓥} {B} {A} {f} ((g , G) , (h , H)) y = (g y)          ==⟨ (H (g y)) ⁻¹ ⟩ 
                                                              ((h (f (g y))) ==⟨ ap h (G y) ⟩ 
                                                              ((h y)         ∎))

is-equiv-has-inverse : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B}
                     → is-equiv f → has-inverse f 
is-equiv-has-inverse {𝓤} {𝓥} {B} {A} {f} ((g , G) , (h , H)) = g , (G , (λ x → 
                                                                            (g (f x))  ==⟨ is-equiv-aux-htpy ((g , G) , (h , H)) (f x) ⟩ 
                                                                            ((h (f x)) ==⟨ (H x) ⟩ 
                                                                            (x         ∎))
                                                                        )
                                                                    )

Eq-Σ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
     → (s t : Σ x ∶ A , B x) 
     → (𝓤 ⊔ 𝓥) ̇ 
Eq-Σ {B = B} s t = Σ α ∶ (fst s == fst t) , (tr B α (snd s) == snd t)

refl-Eq-Σ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
          → (s : Σ x ∶ A , B x) → Eq-Σ s s 
refl-Eq-Σ (x , y) = refl x , refl y

pair-eq : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
        → {s t : Σ x ∶ A , B x} 
        → s == t → Eq-Σ s t
pair-eq {s = s} (refl s) = refl-Eq-Σ s

eq-pair' : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
         → {s t : Σ x ∶ A , B x}
         → (α : fst s == fst t) → tr B α (snd s) == snd t
         → s == t 
eq-pair' {B = B} {(x , y)} {(.x , .y)} (refl .x) (refl .y) = refl (x , y)

eq-pair : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
        → {s t : Σ x ∶ A , B x} 
        → Eq-Σ s t → s == t 
eq-pair {B = B} {x , y} {x' , y'} (α , β) = eq-pair' α β

is-sec-eq-pair : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
               → (s t : Σ x ∶ A , B x)
               → (eq-pair {s = s} {t}) ∘ (pair-eq {s = s} {t}) ~ id 
is-sec-eq-pair (x , y) (.x , .y) (refl .(x , y)) = refl (refl (x , y))

is-retr-eq-pair : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
                → (s t : Σ x ∶ A , B x)
                → (pair-eq {s = s} {t}) ∘ (eq-pair {s = s} {t}) ~ id 
is-retr-eq-pair (x , y) (.x , .y) (refl _ , refl _) = refl (refl x , refl y)

is-equiv-eq-pair : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
                 → (s t : Σ x ∶ A , B x)
                 → is-equiv (eq-pair {s = s} {t})
is-equiv-eq-pair s t = has-inverse-is-equiv (pair-eq , (is-sec-eq-pair s t , is-retr-eq-pair s t))

is-equiv-pair-eq :  {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
                 → (s t : Σ x ∶ A , B x)
                 → is-equiv (pair-eq {s = s} {t})
is-equiv-pair-eq s t = has-inverse-is-equiv (eq-pair , (is-retr-eq-pair s t , is-sec-eq-pair s t))

η-rule : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } 
       → (t : Σ x ∶ A , B x)
       → (fst t , snd t) == t 
η-rule (x , y) = eq-pair (refl x , refl y) 

inv-inv-id : {A : 𝓤 ̇ } {x y : A} 
           → (p : x == y) → ((p ⁻¹) ⁻¹) == p
inv-inv-id (refl x) = refl (refl x)

is-equiv-inv : {A : 𝓤 ̇ } (x y : A)
             → is-equiv (λ (p : x == y) → p ⁻¹)
is-equiv-inv x y = has-inverse-is-equiv (_⁻¹ , (inv-inv-id , inv-inv-id))

inv-equiv : {A : 𝓤 ̇ } (x y : A) → (x == y) ≃ (y == x) 
inv-equiv x y = (λ p → p ⁻¹) , is-equiv-inv x y

concat-left : {X : 𝓤 ̇ } {x y : X} → (p : x == y) → (z : X) → y == z → x == z
concat-left p z q = p · q

concat-inv-left : {X : 𝓤 ̇ } {x y : X} → (p : x == y) → (z : X) → x == z → y == z 
concat-inv-left p = concat-left (p ⁻¹)

is-sec-concat-left : {A : 𝓤 ̇ } {x y : A} (p : x == y) (z : A) 
                   → (concat-left p z) ∘ (concat-inv-left p z) ~ id 
is-sec-concat-left (refl _) z = refl

is-retr-concat-left : {A : 𝓤 ̇ } {x y : A} (p : x == y) (z : A)
                    → (concat-inv-left p z) ∘ (concat-left p z) ~ id
is-retr-concat-left (refl _) z = refl

is-equiv-concat-left : {A : 𝓤 ̇ } {x y : A} (p : x == y) (z : A)
                     → is-equiv (concat-left p z)
is-equiv-concat-left p z = has-inverse-is-equiv (concat-inv-left p z , (is-sec-concat-left p z , is-retr-concat-left p z))

concat-left-equiv : {A : 𝓤 ̇ } {x y : A} (p : x == y) (z : A)
                   → (y == z) ≃ (x == z) 
concat-left-equiv p z = concat-left p z , is-equiv-concat-left p z

concat-right : {A : 𝓤 ̇ } (x : A) {y z : A} (q : y == z) → x == y → x == z
concat-right x q p = p · q

concat-inv-right : {A : 𝓤 ̇ } (x : A) {y z : A} (q : y == z) → x == z → x == y 
concat-inv-right x q = concat-right x (q ⁻¹)

is-sec-concat-right : {A : 𝓤 ̇ } (x : A) {y z : A} (q : y == z)
                    → (concat-right x q) ∘ (concat-inv-right x q) ~ id
is-sec-concat-right x (refl _) (refl .x) = refl (refl x)

is-retr-concat-right : {A : 𝓤 ̇ } (x : A) {y z : A} (q : y == z)
                     → (concat-inv-right x q) ∘ (concat-right x q) ~ id 
is-retr-concat-right x (refl _) (refl .x) = refl (refl x)

is-equiv-concat-right : {A : 𝓤 ̇ } (x : A) {y z : A} (q : y == z) 
                      → is-equiv (concat-right x q)
is-equiv-concat-right x q = has-inverse-is-equiv (concat-inv-right x q , (is-sec-concat-right x q , is-retr-concat-right x q))

concat-right-equiv : {A : 𝓤 ̇ } (x : A) {y z : A} (q : y == z) 
                   → (x == y) ≃ (x == z)
concat-right-equiv x q = concat-right x q , is-equiv-concat-right x q

tr-inv : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A} (p : x == y) → B y → B x
tr-inv B p = tr B (p ⁻¹)

is-sec-tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A} (p : x == y) → (tr B p) ∘ (tr-inv B p) ~ id 
is-sec-tr B (refl _) bx = refl bx

is-retr-tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A} (p : x == y) → (tr-inv B p) ∘ (tr B p) ~ id
is-retr-tr B (refl _) bx = refl bx

is-equiv-tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A} (p : x == y) → is-equiv (tr B p)
is-equiv-tr B p = has-inverse-is-equiv (tr-inv B p , (is-sec-tr B p , is-retr-tr B p))

tr-equiv : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A} (p : x == y) → B x ≃ B y 
tr-equiv B p = tr B p , is-equiv-tr B p

is-equiv-htpy' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} (g : A → B) (H : f ~ g) → is-equiv g → is-equiv f 
is-equiv-htpy' g H ((gs , issec) , (gr , isretr)) = (gs , ((λ x → H (gs x))    ▣ issec)) 
                                                  , (gr , ((λ x → ap gr (H x)) ▣ isretr))

is-equiv-htpy : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) {g : A → B} (H : f ~ g) → is-equiv f → is-equiv g 
is-equiv-htpy f H = is-equiv-htpy' f (H ~⁻¹)

triangle-section : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
                 → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (S : sec h) 
                 → (g ~ (f ∘ (fst S)))
triangle-section f g h H (s , issec) = ((λ x → H (s x)) ▣ λ x → ap g (issec x)) ~⁻¹

section-comp : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ }
             → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) 
             → sec h → sec f → sec g 
section-comp f g h H (sec-h , is-sec-h) (sec-f , is-sec-f) = (h ∘ sec-f) , ((λ x → H (sec-f x)) ~⁻¹ ▣ is-sec-f)

section-comp' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ }
              → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) 
              → sec h → sec g → sec f
section-comp' f g h H (sec-h , is-sec-h) (sec-g , is-sec-g) = (sec-h ∘ sec-g) 
                                                            , ((λ x → H (sec-h (sec-g x))) 
                                                                    ▣ ((λ x → ap g (is-sec-h (sec-g x)))
                                                                ▣ is-sec-g))

triangle-retration : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
                   → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (R : retr g)
                   → h ~ (fst R ∘ f)
triangle-retration f g h H (retr-g , is-retr-g) = ((λ x → ap retr-g (H x)) ▣ λ x → is-retr-g (h x)) ~⁻¹

retraction-comp : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ }
                → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) 
                → retr g → retr f → retr h
retraction-comp f g h H (retr-g , is-retr-g) (retr-f , is-retr-f) = (retr-f ∘ g) , ((((λ x → ap retr-f (H x))) ~⁻¹) ▣ is-retr-f)

retraction-comp' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
                 → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
                 → retr g → retr h → retr f 
retraction-comp' f g h H (retr-g , is-retr-g) (retr-h , is-retr-h) = (retr-h ∘ retr-g) 
                                                                   , (((λ x → ap (retr-h ∘ retr-g) (H x)) 
                                                                            ▣ λ x → ap retr-h (is-retr-g (h x))) 
                                                                        ▣ is-retr-h)

is-equiv-comp : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
              → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
              → is-equiv h → is-equiv g → is-equiv f 
is-equiv-comp f g h H (sec-h , retr-h) (sec-g , retr-g) = section-comp' f g h H sec-h sec-g 
                                                        , retraction-comp' f g h H retr-g retr-h

is-equiv-comp' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
               → (g : B → X) (h : A → B)
               → is-equiv h → is-equiv g → is-equiv (g ∘ h)
is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h (refl-~ λ x → g (h x))

equiv-comp : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
           → B ≃ X → A ≃ B → A ≃ X  
equiv-comp (g , is-equiv-g) (h , is-equiv-h) = (g ∘ h) , is-equiv-comp' g h is-equiv-h is-equiv-g

_∘e_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
     → B ≃ X → A ≃ B → A ≃ X 
_∘e_ = equiv-comp

is-equiv-left-factor : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
                     → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
                     → is-equiv f → is-equiv h → is-equiv g
is-equiv-left-factor f g h H (sec-f , retr-f) (sec-h , retr-h) = section-comp f g h H sec-h sec-f 
                                                               , retraction-comp' g f (fst sec-h) 
                                                                    (triangle-section f g h H sec-h) 
                                                                    retr-f (h , snd sec-h)

is-equiv-right-factor : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
                      → (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
                      → is-equiv g → is-equiv f → is-equiv h
is-equiv-right-factor f g h H (sec-g , retr-g) (sec-f , retr-f) = section-comp' h (fst retr-g) f 
                                                                    (triangle-retration f g h H retr-g) 
                                                                    sec-f (g , snd retr-g) 
                                                                , retraction-comp f g h H retr-g retr-f

is-equiv-left-factor' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
                      → (g : B → X) (h : A → B)
                      → is-equiv (g ∘ h) → is-equiv h → is-equiv g
is-equiv-left-factor' g h = is-equiv-left-factor (g ∘ h) g h (refl-~ (g ∘ h))

is-equiv-right-factor' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } 
                       → (g : B → X) (h : A → B)
                       → is-equiv g → is-equiv (g ∘ h) → is-equiv h
is-equiv-right-factor' g h = is-equiv-right-factor (g ∘ h) g h (refl-~ (g ∘ h))

is-equiv-is-sec-is-equiv : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                         → (f : A → B) (g : B → A)
                         → is-equiv f → (f ∘ g) ~ id → is-equiv g
is-equiv-is-sec-is-equiv {B = B} f g e-f H = is-equiv-right-factor id f g (H ~⁻¹) e-f (is-equiv-id B)

is-equiv-is-retr-is-equiv : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                          → (f : A → B) (g : B → A)
                          → is-equiv f → (g ∘ f) ~ id → is-equiv g
is-equiv-is-retr-is-equiv {A = A} f g e-f H = is-equiv-left-factor id g f (H ~⁻¹) (is-equiv-id A) e-f

Σ-swap : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (C : A → B → 𝓦 ̇ )
       → Σ x ∶ A , Σ y ∶ B , C x y → Σ y ∶ B , Σ x ∶ A , C x y
Σ-swap A B C (x , (y , c)) = y , (x , c)

Σ-swap' : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (C : A → B → 𝓦 ̇ )
        → Σ y ∶ B , Σ x ∶ A , C x y → Σ x ∶ A , Σ y ∶ B , C x y
Σ-swap' A B C (y , (x , c)) = x , (y , c)

Σ-swap'-Σ-swap-id : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (C : A → B → 𝓦 ̇ )
                  → (Σ-swap' A B C ∘ Σ-swap A B C) ~ id
Σ-swap'-Σ-swap-id A B C (x , (y , c)) = refl (x , (y , c))

Σ-swap-Σ-swap'-id : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (C : A → B → 𝓦 ̇ )
                  → (Σ-swap A B C ∘ Σ-swap' A B C) ~ id
Σ-swap-Σ-swap'-id A B C (y , (x , c)) = refl (y , (x , c))

is-equiv-Σ-swap : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (C : A → B → 𝓦 ̇ )
                → is-equiv (Σ-swap A B C)
is-equiv-Σ-swap A B C = has-inverse-is-equiv (Σ-swap' A B C , ((Σ-swap-Σ-swap'-id A B C) , Σ-swap'-Σ-swap-id A B C))

Σ-assoc : (A : 𝓤 ̇ ) (B : A → 𝓥 ̇) (C : A → 𝓦 ̇ )
        → Σ u ∶ (Σ x ∶ A , B x) , C (fst u) → Σ v ∶ (Σ x ∶ A , C x) , B (fst v)
Σ-assoc A B C ((x , y) , c) = (x , c) , y

Σ-assoc' : (A : 𝓤 ̇ ) (B : A → 𝓥 ̇) (C : A → 𝓦 ̇ )
         → Σ v ∶ (Σ x ∶ A , C x) , B (fst v) → Σ u ∶ (Σ x ∶ A , B x) , C (fst u)
Σ-assoc' A B C ((x , c) , y) = (x , y) , c

Σ-assoc'-Σ-assoc-id : (A : 𝓤 ̇ ) (B : A → 𝓥 ̇) (C : A → 𝓦 ̇ )
                    → (Σ-assoc' A B C) ∘ (Σ-assoc A B C) ~ id 
Σ-assoc'-Σ-assoc-id A B C ((x , y) , c) = refl (((x , y) , c))

Σ-assoc-Σ-assoc'-id : (A : 𝓤 ̇ ) (B : A → 𝓥 ̇) (C : A → 𝓦 ̇ )
                    → (Σ-assoc A B C) ∘ (Σ-assoc' A B C) ~ id 
Σ-assoc-Σ-assoc'-id A B C ((x , c) , y) = refl ((x , c) , y)

is-equiv-Σ-assoc : (A : 𝓤 ̇ ) (B : A → 𝓥 ̇) (C : A → 𝓦 ̇ )
                 → is-equiv (Σ-assoc A B C)
is-equiv-Σ-assoc A B C = has-inverse-is-equiv (Σ-assoc' A B C , ((Σ-assoc-Σ-assoc'-id A B C) , (Σ-assoc'-Σ-assoc-id A B C)))

+→-id : (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) → ((id {X = A}) +→ (id {X = B})) ~ id
+→-id A B (inl x) = refl (inl x)
+→-id A B (inr x) = refl (inr x)

+→-comp : {𝓤₀ 𝓤₁ 𝓤₂ : Universe} {𝓥₀ 𝓥₁ 𝓥₂ : Universe} 
        → {A : 𝓤₀ ̇ } {B : 𝓥₀ ̇ } {A' : 𝓤₁ ̇ } {B' : 𝓥₁ ̇ } {A'' : 𝓤₂ ̇ } {B'' : 𝓥₂ ̇ }
        → (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') 
        → ((f' ∘ f) +→ (g' ∘ g)) ~ ((f' +→ g') ∘ (f +→ g))
+→-comp f f' g g' (inl x) = refl (inl (f' (f x)))
+→-comp f f' g g' (inr x) = refl (inr (g' (g x)))

+→-htpy : {𝓤₀ 𝓤₁ : Universe} {𝓥₀ 𝓥₁ : Universe}
        → {A : 𝓤₀ ̇ } {B : 𝓥₀ ̇ } {A' : 𝓤₁ ̇ } {B' : 𝓥₁ ̇ } 
        → {f f' : A → A'} {g g' : B → B'}
        → (H : f ~ f') (K : g ~ g')
        → (f +→ g) ~ (f' +→ g')
+→-htpy H K (inl x) = ap inl (H x)
+→-htpy H K (inr x) = ap inr (K x)

+→-is-equiv : {𝓤₀ 𝓤₁ : Universe} {𝓥₀ 𝓥₁ : Universe}
        → {A : 𝓤₀ ̇ } {B : 𝓥₀ ̇ } {A' : 𝓤₁ ̇ } {B' : 𝓥₁ ̇ }
        → {f : A → A'} {g : B → B'}
        → is-equiv f → is-equiv g → is-equiv (f +→ g)
+→-is-equiv {A = A} {B = B} {A' = A'} {B' = B'} {f = f} {g = g} 
            ((sf , is-sec-f) , (rf , is-retr-f)) 
            ((sg , is-sec-g) , (rg , is-retr-g)) = 
                (
                    (sf +→ sg) , 
                    (((f +→ g) ∘ (sf +→ sg) ) ~〈 inv-~ (+→-comp sf f sg g) 〉 
                    (((f ∘ sf) +→ (g ∘ sg))   ~〈 +→-htpy is-sec-f is-sec-g 〉 
                                                 +→-id A' B'))) 
            ,   (
                   (rf +→ rg) , 
                   (((rf +→ rg) ∘ (f +→ g)) ~〈 inv-~ (+→-comp f rf g rg) 〉 
                   (((rf ∘ f) +→ (rg ∘ g))  ~〈 +→-htpy is-retr-f is-retr-g 〉 
                                               +→-id A B)))  
