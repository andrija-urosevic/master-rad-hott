\AgdaHide{
\begin{code}

{-# OPTIONS --without-K --safe #-}

module Appendix where

open import Universes public

variable 𝓤 𝓥 𝓦 : Universe 


\end{code}
}

\subsection{Опште}

\begin{code}
_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → (g : (y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
(g ∘ f) x = g (f x) 

id : {X : 𝓤 ̇ } → X → X 
id x = x
\end{code}

\subsection{Празан тип}

\begin{code}
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
\end{code}

\subsection{Јединични тип}

\begin{code}
data 𝟙 : 𝓤₀ ̇ where
    ⋆ : 𝟙

𝟙-induction : (P : 𝟙 → 𝓤 ̇ ) → P ⋆ → (x : 𝟙) → P x 
𝟙-induction P p ⋆ = p

𝟙-recursion : (A : 𝓤 ̇ ) → A → 𝟙 → A
𝟙-recursion A = 𝟙-induction (λ _ → A)

!𝟙 : {A : 𝓤 ̇ } → A → 𝟙
!𝟙 a = ⋆
\end{code}

\subsection{Тип копроизвода}

\begin{code}
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

_+→_ : {A X : 𝓤 ̇ } {B Y : 𝓤 ̇ } (f : A → X) (g : B → Y) 
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
+-rigth-empty {𝓤} {X} {Y} ey = +-recursion X id (!𝟘 ∘ ey)
\end{code}

\newpage%
\subsection{Тип зависних парова}

\begin{code}
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

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → P (x , y))
            → ((x , y) : Σ Y) → P (x , y)
Σ-induction f (x , y) = f x y

carry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → P (x , y))
      → ((x : X) (y : Y x) → P (x , y))
carry f x y = f (x , y)

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

×-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {P : X × Y → 𝓦 ̇ }
            → ((x : X) (y : Y) → P (x , y))
            → ((x , y) : X × Y) → P (x , y)
×-induction f (x , y) = f x y 

_↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↔ Y = (X → Y) × (Y → X)
\end{code}

\subsection{Типови идентитета}

\begin{code}
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

tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A}
   → x == y → B x → B y
tr B (refl x) = λ x → x

lift : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {x y : A} (p : x == y) (b : B x) 
     → (x , b) == (y , tr B p b)
lift (refl x) b = refl (x , b)
\end{code}

\subsection{Природни бројеви}

\begin{code}
data ℕ : 𝓤₀ ̇ where
    zero : ℕ
    succ : ℕ → ℕ
    
{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (P : ℕ → 𝓤 ̇ )
            → P 0
            → ((n : ℕ) → P n → P (succ n))
            → (n : ℕ) → P n
ℕ-induction P p₀ pₛ zero     = p₀
ℕ-induction P p₀ pₛ (succ n) = pₛ n (ℕ-induction P p₀ pₛ n)

ℕ-recursion : (A : 𝓤 ̇ )
            → A 
            → (ℕ → A → A)
            → ℕ → A
ℕ-recursion A = ℕ-induction (λ _ → A)






ℕ-iteration : (A : 𝓤 ̇ )
            → A
            → (A → A)
            → ℕ → A 
ℕ-iteration A a f = ℕ-recursion A a (λ _ a → f a)

infixl 20 _+ℕ_
infixl 21 _*ℕ_
infixr 22 _^ℕ_
infixl 23 _!

_+ℕ_ : ℕ → ℕ → ℕ
0 +ℕ n        = n 
(succ m) +ℕ n = succ (m +ℕ n)

_*ℕ_ : ℕ → ℕ → ℕ
0 *ℕ n        = 0 
(succ m) *ℕ n = m *ℕ n +ℕ n

_^ℕ_ : ℕ → ℕ → ℕ
m ^ℕ 0        = 1
m ^ℕ (succ n) = m *ℕ m ^ℕ n

_! : ℕ → ℕ
0 !        = 1
(succ n) ! = succ n *ℕ n !

_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇ 
0      ≤ℕ n      = 𝟙 
succ m ≤ℕ 0      = 𝟘 
succ m ≤ℕ succ n = m ≤ℕ n

left-zero-law-+ℕ : (n : ℕ) → 0 +ℕ n == n 
left-zero-law-+ℕ n = refl n

right-zero-law-+ℕ : (n : ℕ) → n +ℕ 0 == n
right-zero-law-+ℕ 0        = refl 0
right-zero-law-+ℕ (succ n) = ap succ (right-zero-law-+ℕ n)

left-unit-law-+ℕ : (n : ℕ) → 1 +ℕ n == succ n 
left-unit-law-+ℕ n = refl (succ n)

right-unit-law-+ℕ : (n : ℕ) → n +ℕ 1 == succ n 
right-unit-law-+ℕ 0        = refl 1
right-unit-law-+ℕ (succ n) = ap succ (right-unit-law-+ℕ n)

left-succ-law-+ℕ : (m n : ℕ) → succ m +ℕ n == succ (m +ℕ n)
left-succ-law-+ℕ m n = refl (succ (m +ℕ n))

right-succ-law-+ℕ : (m n : ℕ) → m +ℕ succ n == succ (m +ℕ n)
right-succ-law-+ℕ 0        n = refl (succ n)
right-succ-law-+ℕ (succ m) n = ap succ (right-succ-law-+ℕ m n)

associative-+ℕ : (m n k : ℕ) → (m +ℕ n) +ℕ k == m +ℕ (n +ℕ k) 
associative-+ℕ 0        n k = refl (n +ℕ k)
associative-+ℕ (succ m) n k = ap succ (associative-+ℕ m n k)

commutative-+ℕ : (m n : ℕ) → m +ℕ n == n +ℕ m 
commutative-+ℕ 0        n = right-zero-law-+ℕ n ⁻¹
commutative-+ℕ (succ m) n = (succ (m +ℕ n))  ==⟨ ap succ (commutative-+ℕ m n) ⟩ 
                            ((succ (n +ℕ m)) ==⟨ right-succ-law-+ℕ n m ⁻¹ ⟩ 
                            ((n +ℕ succ m)   ∎))

Eq-ℕ : ℕ → ℕ → 𝓤₀ ̇
Eq-ℕ 0        0        = 𝟙
Eq-ℕ 0        (succ n) = 𝟘 
Eq-ℕ (succ m) 0        = 𝟘 
Eq-ℕ (succ m) (succ n) = Eq-ℕ m n

relf-Eq-ℕ : (n : ℕ) → Eq-ℕ n n 
relf-Eq-ℕ 0        = ⋆ 
relf-Eq-ℕ (succ n) = relf-Eq-ℕ n

id-Eq-ℕ : {m n : ℕ} → m == n → Eq-ℕ m n 
id-Eq-ℕ {m} {n} p = tr (Eq-ℕ m) p (relf-Eq-ℕ m)

Eq-ℕ-id : (m n : ℕ) → Eq-ℕ m n → m == n
Eq-ℕ-id 0        0        eq = refl 0
Eq-ℕ-id (succ m) (succ n) eq = ap succ (Eq-ℕ-id m n eq)

injective-succ-ℕ : (m n : ℕ) → succ m == succ n → m == n
injective-succ-ℕ m n e = Eq-ℕ-id m n (id-Eq-ℕ e)

peano-7-axiom : (n m : ℕ) → (m == n) ↔ (succ m == succ n)
peano-7-axiom n m = ap succ , injective-succ-ℕ m n

peano-8-axiom : (n : ℕ) → ¬ (0 == succ n)
peano-8-axiom n = id-Eq-ℕ

\end{code}

\subsection{Булов тип}

\begin{code}
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

if_then_else : {P : 𝟚 → 𝓤 ̇ }
             → (b : 𝟚)
             → (P true)
             → (P false)
             → (P b)
if true  then x else y = x
if false then x else y = y
\end{code}