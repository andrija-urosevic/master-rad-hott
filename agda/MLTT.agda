{-# OPTIONS --without-K --safe #-}

module MLTT where

open import Universes public

variable 𝓤 𝓥 𝓦 : Universe 

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (P : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → P x 
𝟘-induction P ()

𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A 
𝟘-recursion A p = 𝟘-induction (λ _ → A) p

!𝟘 : (A : 𝓤 ̇) → 𝟘 → A 
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇ 
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

data 𝟙 : 𝓤₀ ̇ where
    ⋆ : 𝟙

𝟙-induction : (P : 𝟙 → 𝓤 ̇ ) → P ⋆ → (x : 𝟙) → P x 
𝟙-induction P p ⋆ = p

𝟙-recursion : (A : 𝓤 ̇ ) → A → 𝟙 → A
𝟙-recursion A a x = 𝟙-induction (λ _ → A) a x

!𝟙 : {A : 𝓤 ̇ } → A → 𝟙
!𝟙 a = ⋆

data _+_ (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
    inl : X → X + Y 
    inr : Y → X + Y 

+-induction : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (P : X + Y → 𝓤 ̇ )
            → ((x : X) → P (inl x))
            → ((y : Y) → P (inr y))
            → (z : X + Y) → P z
+-induction P pₗ pᵣ (inl x) = pₗ x
+-induction P pₗ pᵣ (inr y) = pᵣ y

𝟚 : 𝓤₀ ̇ 
𝟚 = 𝟙 + 𝟙

pattern true  = inl ⋆
pattern false = inr ⋆

𝟚-induction : (P : 𝟚 → 𝓤 ̇ ) 
            → (P true)
            → (P false)
            → (b : 𝟚) → (P b)
𝟚-induction P p₀ p₁ true  = p₀
𝟚-induction P p₀ p₁ false = p₁

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
    constructor
        _,_
    field
        x : X
        y : Y x

fst : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
fst (x , y) = x

snd : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (fst z)
snd (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → P (x , y))
            → ((x , y) : Σ Y) → P (x , y)
Σ-induction p (x , y) = p x y

carry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → P (x , y))
      → ((x : X) (y : Y x) → P (x , y))
carry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝓤 ̇ } → X → X 
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X 
𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
(g ∘ f) x = g (f x) 

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type_of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type_of {𝓤} {X} x = X 

data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇ where
    refl : (x : X) → Id X x x

_==_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x == y = Id _ x y

𝕁 : (X : 𝓤 ̇ ) (A : (x y : X) → x == y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → ((x y : X) (p : x == y) → A x y p)
𝕁 X A f x y (refl x) = f x
