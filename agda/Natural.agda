{-# OPTIONS --without-K --safe #-}

module Natural where

open import MLTT public

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
m +ℕ 0        = m 
m +ℕ (succ n) = succ (m +ℕ n)

_*ℕ_ : ℕ → ℕ → ℕ
m *ℕ 0        = 0 
m *ℕ (succ n) = m +ℕ m *ℕ n

_^ℕ_ : ℕ → ℕ → ℕ
m ^ℕ 0        = 1
m ^ℕ (succ n) = m *ℕ m ^ℕ n

minℕ : ℕ → ℕ → ℕ
minℕ 0        0        = 0
minℕ (succ m) 0        = 0
minℕ 0        (succ n) = 0
minℕ (succ m) (succ n) = succ (minℕ m n)

maxℕ : ℕ → ℕ → ℕ
maxℕ 0        0        = 0
maxℕ (succ m) 0        = succ m
maxℕ 0        (succ n) = succ n
maxℕ (succ m) (succ n) = succ (minℕ m n)

_! : ℕ → ℕ
0 !        = 1
(succ n) ! = succ n *ℕ n !

triangle : ℕ → ℕ
triangle 0        = 0
triangle (succ n) = triangle n +ℕ succ n

fibonacci : ℕ → ℕ
fibonacci 0               = 0
fibonacci 1               = 1
fibonacci (succ (succ n)) = fibonacci (succ n) +ℕ fibonacci n

binomial-coef : ℕ → ℕ → ℕ
binomial-coef 0        0        = 1
binomial-coef 0        (succ k) = 0
binomial-coef (succ n) 0        = 1
binomial-coef (succ n) (succ k) = binomial-coef n k +ℕ binomial-coef n (succ k)

double : ℕ → ℕ
double 0 = 0
double (succ n) = succ (succ (double n))

div2 : ℕ → ℕ
div2 0 = 0
div2 1 = 0
div2 (succ (succ n)) = succ (div2 n)

add : ℕ → ℕ → ℕ
add m n = ℕ-recursion ℕ m (λ _ x → succ x) n

mul : ℕ → ℕ → ℕ       
mul m n = ℕ-recursion ℕ 0 (λ _ x → add m x) n

pow : ℕ → ℕ → ℕ
pow m n = ℕ-recursion ℕ 1 (λ _ x → mul m x) n

left-unit-law-+ℕ : (n : ℕ) → 0 +ℕ n == n 
left-unit-law-+ℕ 0        = refl 0 
left-unit-law-+ℕ (succ n) = ap succ (left-unit-law-+ℕ n)

right-unit-law-+ℕ : (n : ℕ) → n +ℕ 0 == n
right-unit-law-+ℕ = refl

left-succ-law-+ℕ : (m n : ℕ) → succ m +ℕ n == succ (m +ℕ n)
left-succ-law-+ℕ m 0        = refl (succ m)
left-succ-law-+ℕ m (succ n) = ap succ (left-succ-law-+ℕ m n)

right-succ-law-+ℕ : (m n : ℕ) → m +ℕ succ n == succ (m +ℕ n)
right-succ-law-+ℕ m n = refl (succ (m +ℕ n))

associative-+ℕ : (m n k : ℕ) → (m +ℕ n) +ℕ k == m +ℕ (n +ℕ k) 
associative-+ℕ m n 0        = refl (m +ℕ n)
associative-+ℕ m n (succ k) = ap succ (associative-+ℕ m n k)

commutative-+ℕ : (m n : ℕ) → m +ℕ n == n +ℕ m 
commutative-+ℕ 0 n        = left-unit-law-+ℕ n
commutative-+ℕ (succ m) n = (succ m +ℕ n)  ==⟨ left-succ-law-+ℕ m n ⟩ 
                            (succ (m +ℕ n) ==⟨ ap succ (commutative-+ℕ m n) ⟩ 
                            (succ (n +ℕ m) ∎))

left-zero-law-*ℕ : (n : ℕ) → 0 *ℕ n == 0
left-zero-law-*ℕ 0        = refl 0 
left-zero-law-*ℕ (succ n) = (0 +ℕ 0 *ℕ n) ==⟨ left-unit-law-+ℕ (0 *ℕ n) ⟩ 
                            ((0 *ℕ n)     ==⟨ left-zero-law-*ℕ n ⟩ 
                            (0            ∎))

right-zero-law-*ℕ : (m : ℕ) → m *ℕ 0 == 0
right-zero-law-*ℕ m = refl 0

left-unit-law-*ℕ : (n : ℕ) → 1 *ℕ n == n 
left-unit-law-*ℕ 0        = refl 0 
left-unit-law-*ℕ (succ n) = (1 +ℕ 1 *ℕ n)            ==⟨ left-succ-law-+ℕ zero (1 *ℕ n) ⟩ 
                            ((succ (zero +ℕ 1 *ℕ n)) ==⟨ (ap succ (left-unit-law-+ℕ (1 *ℕ n))) ⟩ 
                            ((succ (1 *ℕ n))         ==⟨ ap succ (left-unit-law-*ℕ n) ⟩ 
                            ((succ n)                ∎))) 
                        
right-unit-law-*ℕ : (m : ℕ) → m *ℕ 1 == m 
right-unit-law-*ℕ m = refl m

left-succ-law-*ℕ : (m n : ℕ) → m *ℕ (succ n) == m +ℕ m *ℕ n 
left-succ-law-*ℕ m n = refl (m +ℕ m *ℕ n)

right-succ-law-*ℕ : (m n : ℕ) → (succ m) *ℕ n == m *ℕ n +ℕ n 
right-succ-law-*ℕ m 0        = refl 0 
right-succ-law-*ℕ m (succ n) = (succ m +ℕ succ m *ℕ n)      ==⟨ ap (λ x → succ m +ℕ x) (right-succ-law-*ℕ m n) ⟩ 
                               ((succ m +ℕ (m *ℕ n +ℕ n))   ==⟨ left-succ-law-+ℕ m (m *ℕ n +ℕ n) ⟩ 
                               ((succ (m +ℕ (m *ℕ n +ℕ n))) ==⟨ ap succ (associative-+ℕ m (m *ℕ n) n ⁻¹) ⟩ 
                               ((succ (m +ℕ m *ℕ n +ℕ n))   ∎))) 

commutative-*ℕ : (m n : ℕ) → m *ℕ n == n *ℕ m 
commutative-*ℕ m 0        = (left-zero-law-*ℕ m) ⁻¹ 
commutative-*ℕ m (succ n) = (m +ℕ m *ℕ n)  ==⟨ commutative-+ℕ m (m *ℕ n) ⟩ 
                            ((m *ℕ n +ℕ m) ==⟨ ap (λ x → x +ℕ m) (commutative-*ℕ m n) ⟩ 
                            ((n *ℕ m +ℕ m) ==⟨ right-succ-law-*ℕ n m ⁻¹ ⟩ 
                            ((succ n *ℕ m) ∎)))

