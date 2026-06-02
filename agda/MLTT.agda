{-# OPTIONS --without-K --safe #-}

module MLTT where

open import Universes public

variable 𝓤 𝓥 𝓦 : Universe 

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → (g : (y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
(g ∘ f) x = g (f x) 

id : {X : 𝓤 ̇ } → X → X 
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X 
𝑖𝑑 X = id

const : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
      → X → Y → X
const x _ = x

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X 

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (P : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → P x 
𝟘-induction P ()

𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A 
𝟘-recursion A p = 𝟘-induction (λ _ → A) p

!𝟘 : {A : 𝓤 ̇ } → 𝟘 → A 
!𝟘 {𝓤} {A} = 𝟘-recursion A

empty : 𝓤 ̇ → 𝓤 ̇ 
empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

¬-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (¬ Y → ¬ X)
¬-functor f ny x = ny (f x)

¬¬ : 𝓤 ̇ → 𝓤 ̇ 
¬¬ X = ¬ (¬ X)

¬¬-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (¬¬ X → ¬¬ Y)
¬¬-functor f nnx ny = nnx (¬-functor f ny)

¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬¬ X = ¬ (¬ (¬ X))

¬¬¬-→-¬ : (X : 𝓤 ̇ ) → ¬¬¬ X → ¬ X
¬¬¬-→-¬ X nnx x = nnx λ nx → nx x

data 𝟙 : 𝓤₀ ̇ where
    ⋆ : 𝟙

𝟙-induction : (P : 𝟙 → 𝓤 ̇ ) → P ⋆ → (x : 𝟙) → P x 
𝟙-induction P p ⋆ = p

𝟙-recursion : (A : 𝓤 ̇ ) → A → 𝟙 → A
𝟙-recursion A = 𝟙-induction (λ _ → A)

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

+-recursion : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : 𝓤 ̇ ) 
            → (X → A) 
            → (Y → A) 
            → X + Y → A
+-recursion A f g (inl x) = f x
+-recursion A f g (inr x) = g x

n-n-n+ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬ A → ¬ B → ¬ (A + B)
n-n-n+ f g (inl a) = f a
n-n-n+ f g (inr b) = g b

_+→_ : {𝓤₀ 𝓤₁ : Universe} {𝓥₀ 𝓥₁ : Universe} 
     → {A : 𝓤₀ ̇ } {X : 𝓤₁ ̇ } {B : 𝓥₀ ̇ } {Y : 𝓥₁ ̇ } 
     → (f : A → X) (g : B → Y) 
     → (A + B) → (X + Y)
(f +→ g) (inl x) = inl (f x)
(f +→ g) (inr x) = inr (g x)

+-left-empty : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } 
             → empty X 
             → X + Y → Y
+-left-empty {𝓤} {X} {Y} ex = +-recursion Y (!𝟘 ∘ ex) id 

+-rigth-empty : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
              → empty Y
              → X + Y → X 
+-rigth-empty {𝓤} {X} {Y} ex = +-recursion X id (!𝟘 ∘ ex)

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

syntax -Σ X (λ x → y) = Σ x ∶ X , y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → P (x , y))
            → ((x , y) : Σ Y) → P (x , y)
Σ-induction f (x , y) = f x y

carry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → P (x , y))
      → ((x : X) (y : Y x) → P (x , y))
carry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ∶ X , Y

×-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {P : X × Y → 𝓦 ̇ }
            → ((x : X) (y : Y) → P (x , y))
            → ((x , y) : X × Y) → P (x , y)
×-induction f (x , y) = f x y   

_↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↔ Y = (X → Y) × (Y → X)

¬-×-¬ : {X : 𝓤 ̇ } → ¬ (X × ¬ X)
¬-×-¬ (x , nx) = nx x

¬-↔-¬ : {X : 𝓤 ̇ } → ¬ (X ↔ ¬ X)
¬-↔-¬ (fnxx , fxnx) = fnxx (fxnx λ x → fnxx x x) (fxnx λ x → fnxx x x)

→-¬¬ : {X : 𝓤 ̇ } → X → ¬¬ X
→-¬¬ x nx = nx x

→-¬¬-→-¬¬-→-¬¬ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → ¬¬ Y) → (¬¬ X → ¬¬ Y)
→-¬¬-→-¬¬-→-¬¬ f nnx ny = nnx (λ x → f x ny)

¬¬-¬¬-→ : (X : 𝓤 ̇ ) → ¬¬ (¬¬ X → X)
¬¬-¬¬-→ X nf = (λ nx → nf λ nnx → 𝟘-induction (λ x → X) (nnx nx) ) λ x → nf λ nnx → x

¬¬-→-→-→ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → ¬¬ (((X → Y) → X) → X)
¬¬-→-→-→ X Y nxyxx = (λ (nx : ¬ X) → nxyxx λ f → f λ x → 𝟘-recursion Y (nx x)) λ x → nxyxx λ _ → x

¬¬-→-+-→ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → ¬¬ ((X → Y) + (Y → X))
¬¬-→-+-→ X Y n = (λ (nx : ¬ X) → ¬-functor inl n (λ (x : X) → 𝟘-recursion Y (nx x))) (λ (x : X) → ¬-functor inr n λ _ → x) 

¬¬-+-¬ : (X : 𝓤 ̇ ) → ¬¬ (X + ¬ X)
¬¬-+-¬ X nxcnx = (λ (nx : ¬ X) → ¬-functor inl nxcnx (𝟘-recursion X (nxcnx (inr nx)))) (λ x → nxcnx (inl x))

+-¬-→-¬¬-→ : (X : 𝓤 ̇ ) → (X + ¬ X) → (¬¬ X → X)
+-¬-→-¬¬-→ X (inl x) _ = x
+-¬-→-¬¬-→ X (inr nx) nnx = 𝟘-recursion X (nnx nx)

¬¬-→-¬¬-→-→-¬¬ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → ¬¬ (X → ¬¬ Y) → (X → ¬¬ Y)
¬¬-→-¬¬-→-→-¬¬ X Y nf x = ¬¬¬-→-¬ (¬ Y) (¬¬-functor (λ (g : X → ¬¬ Y) → g x) nf)

¬¬-¬¬-×-¬¬-→-¬¬-×-¬¬ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → ¬¬ (¬¬ X × ¬¬ Y) → (¬¬ X × ¬¬ Y)
¬¬-¬¬-×-¬¬-→-¬¬-×-¬¬ X Y f = ¬¬¬-→-¬ (¬ X) (¬¬-functor fst f) , ¬¬¬-→-¬ (¬ Y) (¬¬-functor snd f) 

¬¬-×-↔-¬¬-×-¬¬ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → ¬¬ (X × Y) ↔ (¬¬ X × ¬¬ Y)
¬¬-×-↔-¬¬-×-¬¬ X Y = (λ nnxcy → (λ nx → nnxcy (λ xcy → nx (Σ.x xcy))) , λ ny → nnxcy λ xcy → ny (Σ.y xcy)) , λ nnxcnny nxcy → Σ.x nnxcnny (λ x → Σ.y nnxcnny (λ y → nxcy (x , y)))

Π : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
Π {𝓤} {𝓥} {X} P = (x : X) → P x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇ where
    refl : (x : X) → Id X x x

infixl 10 _==_
infixr 11 _·_

_==_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x == y = Id _ x y

𝕁 : (X : 𝓤 ̇ ) (P : (x y : X) → x == y → 𝓥 ̇ )
  → ((x : X) → P x x (refl x))
  → ((x y : X) (p : x == y) → P x y p)
𝕁 X P f x y (refl x) = f x

ℍ : {X : 𝓤 ̇ } (x : X) (P : (y : X) → x == y → 𝓥 ̇ )
  → P x (refl x)
  → (y : X) (p : x == y)
  → P y p 
ℍ x P p-refl y (refl x) = p-refl

ℍ-recursion : {X : 𝓤 ̇ } (x : X) (P : X → 𝓥 ̇ )
            → P x
            → (y : X) 
            → (x == y)
            → P y
ℍ-recursion x P = ℍ x λ y _ → P y 

𝕁' : (X : 𝓤 ̇ ) (P : (x y : X) → x == y → 𝓥 ̇ )
   → ((x : X) → P x x (refl x))
   → ((x y : X) (p : x == y) → P x y p) 
𝕁' X P f x = ℍ x (P x) (f x)

𝕁-same-as-𝕁' : (X : 𝓤 ̇ ) (P : (x y : X) → x == y → 𝓥 ̇ ) (f : (x : X) → P x x (refl x)) (x y : X) (p : x == y) 
            → 𝕁 X P f x y p == 𝕁' X P f x y p 
𝕁-same-as-𝕁' X P f x x (refl x) = refl (f x)

tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A}
   → x == y → B x → B y
tr B (refl x) = λ x → x

tr-𝕁 : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A}
     → x == y → B x → B y
tr-𝕁 {𝓤} {𝓥} {X} B {x} {y} = 𝕁 X (λ x y _ → B x → B y) (λ x bₓ → bₓ) x y

tr-ℍ : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A}
     → x == y → B x → B y
tr-ℍ B {x} {y} p bₓ = ℍ-recursion x B bₓ y p

tr-𝕁-same-as-tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A} (p : x == y)
                → tr-𝕁 B p == tr B p
tr-𝕁-same-as-tr B (refl x) = refl (λ bₓ → bₓ)

tr-ℍ-same-as-tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A} (p : x == y)
                → tr-ℍ B p == tr B p
tr-ℍ-same-as-tr B (refl x) = refl (λ bₓ → bₓ)

_·_ : {X : 𝓤 ̇ } {x y z : X} → x == y → y == z → x == z
refl _ · q = q

_==⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x == y → y == z → x == z
x ==⟨ p ⟩ q = p · q

_∎ : {X : 𝓤 ̇ } (x : X) → x == x
x ∎ = refl x

_⁻¹ : {X : 𝓤 ̇ } {x y : X} → x == y → y == x 
(refl x) ⁻¹ = refl x

assoc : {X : 𝓤 ̇ } {x y z w : X} 
        (p : x == y) (q : y == z) (r : z == w)
      → (p · q) · r == p · (q · r)
assoc (refl _) q r = refl (q · r)

left-unit : {X : 𝓤 ̇ } {x y : X} (p : x == y)
          → (refl x) · p == p 
left-unit (refl x) = refl (refl x)

right-unit : {X : 𝓤 ̇ } {x y : X} (p : x == y)
           → p · (refl y) == p
right-unit (refl x) = refl (refl x)

left-inv : {X : 𝓤 ̇ } {x y : X} (p : x == y)
         → p ⁻¹ · p == refl y
left-inv (refl x) = refl (refl x)

right-inv : {X : 𝓤 ̇ } {x y : X} (p : x == y)
          → p · p ⁻¹ == refl x 
right-inv (refl x) = refl (refl x)

double-inv : {X : 𝓤 ̇ } {x y : X} (p : x == y)
           → (p ⁻¹ ) ⁻¹ == p
double-inv (refl x) = refl (refl x)
  
ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} 
   → x == y → f x == f y 
ap f (refl x) = refl (f x)

ap-id : {X : 𝓤 ̇ } {x y : X} (p : x == y) 
      → p == ap id p
ap-id (refl x) = refl (refl x)

ap-comp : {X : 𝓤 ̇ } (f g : X → X) {x y z : X} (p : x == y)
        → ap g (ap f p) == ap (g ∘ f) p
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X) 
        → ap f (refl x) == refl (f x)
ap-refl f x = refl (refl (f x))

ap-inv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x == y) 
       → ap f (p ⁻¹) == (ap f p) ⁻¹
ap-inv f (refl x) = refl (ap f (refl x))

ap-concat : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x == y) (q : y == z)
          → ap f (p · q) == ap f p · ap f q 
ap-concat f (refl x) q = refl (ap f q)

apd : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (f : (x : X) → Y x) {x y : X} (p : x == y)
    → tr Y p (f x) == f y
apd f (refl x) = refl (f x)

uniqueness-refl : {X : 𝓤 ̇ } (x y : X) (p : x == y) 
                → (x , refl x) == (y , p) 
uniqueness-refl x x (refl x) = refl (x , (refl x))

distributive-inv-concat : {X : 𝓤 ̇ } {x y z : X} (p : x == y) (q : y == z)
                        → (p · q) ⁻¹ == q ⁻¹ · p ⁻¹
distributive-inv-concat (refl x) (refl x) = refl (refl x)

inv-concat : {X : 𝓤 ̇ } {x y z : X} (p : x == y) (q : y == z) (r : x == z)
           → p · q == r → q == p ⁻¹ · r 
inv-concat (refl x) q r = λ α → α

concat-inv : {X : 𝓤 ̇ } {x y z : X} (p : x == y) (q : y == z) (r : x == z)
           → p · q == r → p == r · q ⁻¹
concat-inv p (refl y) r = λ α → p             ==⟨ (right-unit p) ⁻¹ ⟩ 
                                ((p · refl y) ==⟨ α ⟩ 
                                (r            ==⟨ (right-unit r) ⁻¹ ⟩ 
                                ((r · refl y) ∎)))

lift : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {x y : A} (p : x == y) (b : B x) 
     → (x , b) == (y , tr B p b)
lift (refl x) b = refl (x , b)

decidable : (A : 𝓤 ̇ ) → 𝓤 ⊔ 𝓤 ̇ 
decidable A = A + ¬ A

decidable-𝟘 : decidable 𝟘
decidable-𝟘 = inr (λ x → x)

decidable-𝟙 : decidable 𝟙
decidable-𝟙 = inl ⋆
 
decidable-+ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → decidable A → decidable B → decidable (A + B)
decidable-+ (inl a) (inl b) = inl (inl a)
decidable-+ (inl a) (inr g) = inl (inl a)
decidable-+ (inr f) (inl b) = inl (inr b)
decidable-+ (inr f) (inr g) = inr (n-n-n+ f g)

decidable-× : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → decidable A → decidable B → decidable (A × B)
decidable-× (inl a) (inl b) = inl (a , b)
decidable-× (inl a) (inr g) = inr (λ x → g (snd x))
decidable-× (inr f) (inl b) = inr (λ x → f (fst x))
decidable-× (inr f) (inr g) = inr (λ x → f (fst x))

decidable-→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → decidable A → decidable B → decidable (A → B)
decidable-→                 (inl a) (inl b) = inl (λ x → b)
decidable-→                 (inl a) (inr g) = inr (λ h → g (h a))
decidable-→ {𝓤} {𝓥} {A} {B} (inr f) (inl b) = inl (λ x → 𝟘-recursion B (f x))
decidable-→ {𝓤} {𝓥} {A} {B} (inr f) (inr g) = inl (λ x → 𝟘-recursion B (f x))

decidable-↔ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → decidable A → decidable B → decidable (A ↔ B)
decidable-↔                 (inl a) (inl b) = inl ((λ x → b) , (λ x → a))
decidable-↔                 (inl a) (inr g) = inr (λ x → g (fst x a))
decidable-↔                 (inr f) (inl b) = inr (λ x → f (snd x b))
decidable-↔ {𝓤} {𝓥} {A} {B} (inr f) (inr g) = inl ((λ x → 𝟘-recursion B (f x)) , (λ x → 𝟘-recursion A (g x)))

decidable-¬ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → decidable A → decidable (¬ A)
decidable-¬ (inl a) = inr (λ f → f a)
decidable-¬ (inr f) = inl f

decidable-== : (A : 𝓤 ̇ ) → A → A → 𝓤 ̇ 
decidable-== A = λ x y → decidable (x == y)

decidable-iff : {A : 𝓤 ̇ } {B : 𝓤 ̇ } → (A ↔ B) → (decidable A ↔ decidable B) 
decidable-iff (f , g) = (f +→ ¬-functor g) , (g +→ (¬-functor f)) 