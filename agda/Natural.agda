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
0 +ℕ n        = n 
(succ m) +ℕ n = succ (m +ℕ n)

_*ℕ_ : ℕ → ℕ → ℕ
0 *ℕ n        = 0 
(succ m) *ℕ n = m *ℕ n +ℕ n

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

left-zero-law-*ℕ : (n : ℕ) → 0 *ℕ n == 0
left-zero-law-*ℕ 0        = refl 0 
left-zero-law-*ℕ (succ n) = (0 +ℕ 0 *ℕ n) ==⟨ left-zero-law-+ℕ (0 *ℕ n) ⟩ 
                            ((0 *ℕ n)     ==⟨ left-zero-law-*ℕ n ⟩ 
                            (0            ∎))

right-zero-law-*ℕ : (m : ℕ) → m *ℕ 0 == 0
right-zero-law-*ℕ 0 = refl 0
right-zero-law-*ℕ (succ m) = (m *ℕ 0 +ℕ 0) ==⟨ right-zero-law-+ℕ (m *ℕ zero) ⟩ 
                             ((m *ℕ 0)     ==⟨ right-zero-law-*ℕ m ⟩ 
                             (0            ∎))

left-unit-law-*ℕ : (n : ℕ) → 1 *ℕ n == n 
left-unit-law-*ℕ n = refl n

right-unit-law-*ℕ : (m : ℕ) → m *ℕ 1 == m 
right-unit-law-*ℕ 0        = refl 0
right-unit-law-*ℕ (succ m) = (m *ℕ 1 +ℕ 1) ==⟨ ap (λ x → x +ℕ 1) (right-unit-law-*ℕ m) ⟩ 
                             ((m +ℕ 1)     ==⟨ right-unit-law-+ℕ m ⟩ 
                             ((succ m)     ∎))

right-succ-law-*ℕ : (m n : ℕ) → m *ℕ (succ n) == m *ℕ n +ℕ m
right-succ-law-*ℕ 0        n = refl 0
right-succ-law-*ℕ (succ m) n = (m *ℕ succ n +ℕ succ n)    ==⟨ ap (λ x → x +ℕ succ n) (right-succ-law-*ℕ m n) ⟩ 
                               ((m *ℕ n +ℕ m +ℕ succ n)   ==⟨ associative-+ℕ (m *ℕ n) m (succ n) ⟩ 
                               ((m *ℕ n +ℕ (m +ℕ succ n)) ==⟨ ap (λ x → m *ℕ n +ℕ x) (commutative-+ℕ m (succ n)) ⟩ 
                               ((m *ℕ n +ℕ succ (n +ℕ m)) ==⟨ ap (λ x → m *ℕ n +ℕ x) (right-succ-law-+ℕ n m ⁻¹) ⟩ 
                               ((m *ℕ n +ℕ (n +ℕ succ m)) ==⟨ (associative-+ℕ (m *ℕ n) n (succ m)) ⁻¹ ⟩ 
                               ((m *ℕ n +ℕ n +ℕ succ m)   ∎)))))

left-succ-law-*ℕ : (m n : ℕ) → (succ m) *ℕ n == m *ℕ n +ℕ n 
left-succ-law-*ℕ m n = refl (m *ℕ n +ℕ n)

commutative-*ℕ : (m n : ℕ) → m *ℕ n == n *ℕ m 
commutative-*ℕ m 0        = right-zero-law-*ℕ m
commutative-*ℕ m (succ n) = (m *ℕ succ n)  ==⟨ right-succ-law-*ℕ m n ⟩ 
                            ((m *ℕ n +ℕ m) ==⟨ ap (λ x → x +ℕ m) (commutative-*ℕ m n) ⟩ 
                            ((n *ℕ m +ℕ m) ==⟨ left-succ-law-*ℕ n m ⁻¹ ⟩ 
                            ((n *ℕ m +ℕ m) ∎)))

right-distirbutive-ℕ : (m n k : ℕ) → (m +ℕ n) *ℕ k == m *ℕ k +ℕ n *ℕ k 
right-distirbutive-ℕ 0 n k = refl (n *ℕ k)
right-distirbutive-ℕ (succ m) n k = ((m +ℕ n) *ℕ k +ℕ k)       ==⟨ ap (λ x → x +ℕ k) (right-distirbutive-ℕ m n k) ⟩ 
                                    ((m *ℕ k +ℕ n *ℕ k +ℕ k)   ==⟨ associative-+ℕ (m *ℕ k) (n *ℕ k) k ⟩ 
                                    ((m *ℕ k +ℕ (n *ℕ k +ℕ k)) ==⟨ ap (λ x → m *ℕ k +ℕ x) (commutative-+ℕ (n *ℕ k) k) ⟩ 
                                    ((m *ℕ k +ℕ (k +ℕ n *ℕ k)) ==⟨ associative-+ℕ (m *ℕ k) k (n *ℕ k) ⁻¹ ⟩ 
                                    ((m *ℕ k +ℕ k +ℕ n *ℕ k)   ==⟨ ap (λ x → x +ℕ n *ℕ k) (left-succ-law-*ℕ m k ⁻¹) ⟩ 
                                    ((m *ℕ k +ℕ k +ℕ n *ℕ k)   ∎)))))

left-distirbutive-ℕ : (m n k : ℕ) → m *ℕ (n +ℕ k) == m *ℕ n +ℕ m *ℕ k 
left-distirbutive-ℕ m n k = (m *ℕ (n +ℕ k))     ==⟨ commutative-*ℕ m (n +ℕ k) ⟩ 
                            (((n +ℕ k) *ℕ m)    ==⟨ right-distirbutive-ℕ n k m ⟩ 
                            ((n *ℕ m +ℕ k *ℕ m) ==⟨ ap (λ x → x +ℕ k *ℕ m) (commutative-*ℕ n m) ⟩ 
                            ((m *ℕ n +ℕ k *ℕ m) ==⟨ ap (λ x → m *ℕ n +ℕ x) (commutative-*ℕ k m) ⟩ 
                            ((m *ℕ n +ℕ m *ℕ k) ∎))))

associative-*ℕ : (m n k : ℕ) → (m *ℕ n) *ℕ k == m *ℕ (n *ℕ k)
associative-*ℕ 0        n k = refl 0
associative-*ℕ (succ m) n k = ((m *ℕ n +ℕ n) *ℕ k)       ==⟨ right-distirbutive-ℕ (m *ℕ n) n k ⟩ 
                              ((m *ℕ n *ℕ k +ℕ n *ℕ k)   ==⟨ ap (λ x → x +ℕ n *ℕ k) (associative-*ℕ m n k) ⟩ 
                              ((m *ℕ (n *ℕ k) +ℕ n *ℕ k) ==⟨ left-succ-law-*ℕ m (n *ℕ k) ⁻¹ ⟩ 
                              ((m *ℕ (n *ℕ k) +ℕ n *ℕ k) ∎)))

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

decidable-Eq-ℕ : (m n : ℕ) → decidable (Eq-ℕ m n)
decidable-Eq-ℕ 0        0        = inl ⋆
decidable-Eq-ℕ 0        (succ n) = inr (λ x → x)
decidable-Eq-ℕ (succ m) 0        = inr (λ x → x)
decidable-Eq-ℕ (succ m) (succ n) = decidable-Eq-ℕ m n

peano-7-axiom : (n m : ℕ) → (m == n) ↔ (succ m == succ n)
peano-7-axiom n m = ap succ , injective-succ-ℕ m n

peano-8-axiom : (n : ℕ) → ¬ (0 == succ n)
peano-8-axiom n = id-Eq-ℕ

peano-8-axiom' : (n : ℕ) → ¬ (succ n == 0)
peano-8-axiom' n = id-Eq-ℕ

left-injective-+ℕ : (k m n : ℕ) → k +ℕ m == k +ℕ n → m == n
left-injective-+ℕ 0        m n p = p
left-injective-+ℕ (succ k) m n p = left-injective-+ℕ k m n (injective-succ-ℕ (k +ℕ m) (k +ℕ n) p)

right-injective-+ℕ : (k m n : ℕ) → m +ℕ k == n +ℕ k → m == n 
right-injective-+ℕ 0        m n p = m         ==⟨ right-zero-law-+ℕ m ⁻¹ ⟩ 
                                    ((m +ℕ 0) ==⟨ p ⟩ 
                                    ((n +ℕ 0) ==⟨ right-zero-law-+ℕ n ⟩ 
                                    (n        ∎)))
right-injective-+ℕ (succ k) m n p = right-injective-+ℕ k m n (injective-succ-ℕ (m +ℕ k) (n +ℕ k) ((succ (m +ℕ k))  ==⟨ right-succ-law-+ℕ m k ⁻¹ ⟩ 
                                                                                                  ((m +ℕ succ k)   ==⟨ p ⟩ 
                                                                                                  ((n +ℕ succ k)   ==⟨ right-succ-law-+ℕ n k ⟩ 
                                                                                                  ((succ (n +ℕ k)) ∎)))))

left-reflective-+ℕ : (k m n : ℕ) → m == n → k +ℕ m == k +ℕ n 
left-reflective-+ℕ 0        m n p = p
left-reflective-+ℕ (succ k) m n p = ap succ (left-reflective-+ℕ k m n p)

right-reflective-+ℕ : (k m n : ℕ) → m == n → m +ℕ k == n +ℕ k 
right-reflective-+ℕ 0        m n p = (m +ℕ 0)  ==⟨ right-zero-law-+ℕ m ⟩ 
                                     (m        ==⟨ p ⟩ 
                                     (n        ==⟨ ((right-zero-law-+ℕ n) ⁻¹) ⟩ 
                                     ((n +ℕ 0) ∎)))
right-reflective-+ℕ (succ k) m n p = (m +ℕ succ k)    ==⟨ right-succ-law-+ℕ m k ⟩ 
                                     ((succ (m +ℕ k)) ==⟨ ap succ (commutative-+ℕ m k) ⟩ 
                                     ((succ (k +ℕ m)) ==⟨ ap (λ x → succ (k +ℕ x)) p ⟩ 
                                     ((succ (k +ℕ n)) ==⟨ ap succ (commutative-+ℕ k n) ⟩ 
                                     ((succ (n +ℕ k)) ==⟨ right-succ-law-+ℕ n k ⁻¹ ⟩ 
                                     ((n +ℕ succ k)   ∎)))))

right-injective-*ℕ : (k m n : ℕ) → m *ℕ (succ k) == n *ℕ (succ k) → m == n 
right-injective-*ℕ k 0        0        p = refl 0
right-injective-*ℕ k 0        (succ n) p = 𝟘-recursion 
                                            (Id ℕ zero (succ n)) 
                                            (peano-8-axiom (n *ℕ succ k +ℕ k) (0                         ==⟨ p ⟩ 
                                                                              ((n *ℕ succ k +ℕ succ k)   ==⟨ right-succ-law-+ℕ (n *ℕ succ k) k ⟩ 
                                                                              ((succ (n *ℕ succ k +ℕ k)) ∎))))
right-injective-*ℕ k (succ m) 0        p = 𝟘-recursion 
                                            (Id ℕ (succ m) zero) 
                                            (peano-8-axiom (m *ℕ succ k +ℕ k) (0 ==⟨ (p ⁻¹) ⟩ 
                                                                              ((m *ℕ succ k +ℕ succ k) ==⟨ right-succ-law-+ℕ (m *ℕ succ k) k ⟩ 
                                                                              ((succ (m *ℕ succ k +ℕ k)) ∎))))
right-injective-*ℕ k (succ m) (succ n) p = ap succ (right-injective-*ℕ k m n (right-injective-+ℕ (succ k) (m *ℕ succ k) (n *ℕ succ k) p))

left-injective-*ℕ : (k m n : ℕ) → (succ k) *ℕ m == (succ k) *ℕ n → m == n 
left-injective-*ℕ k m n p = right-injective-*ℕ k m n ((m *ℕ succ k) ==⟨ commutative-*ℕ m (succ k) ⟩ 
                                                     ((k *ℕ m +ℕ m) ==⟨ p ⟩ 
                                                     ((k *ℕ n +ℕ n) ==⟨ left-succ-law-*ℕ k n ⁻¹ ⟩ 
                                                     ((succ k *ℕ n) ==⟨ commutative-*ℕ (succ k) n ⟩ 
                                                     ((n *ℕ succ k) ∎)))))
                                             
right-neq-+ℕ : (m n : ℕ) → ¬ (m == m +ℕ succ n)
right-neq-+ℕ (succ m) n p = right-neq-+ℕ m n (injective-succ-ℕ  m (m +ℕ succ n) p)

left-neq-+ℕ : (m n : ℕ) → ¬ (m == succ n +ℕ m)
left-neq-+ℕ m n p = right-neq-+ℕ m n (m               ==⟨ p ⟩ 
                                     ((succ (n +ℕ m)) ==⟨ ap succ (commutative-+ℕ n m) ⟩ 
                                     ((succ (m +ℕ n)) ==⟨ right-succ-law-+ℕ m n ⁻¹ ⟩ 
                                     ((m +ℕ succ n)   ∎))))

right-neq-*ℕ : (m n : ℕ) → ¬ (succ m == succ m *ℕ (succ (succ n)))
right-neq-*ℕ m n p = right-neq-+ℕ (succ m) (m *ℕ succ n +ℕ n) (succ m                                ==⟨ p ⟩ 
                                                              ((m *ℕ succ (succ n) +ℕ succ (succ n)) ==⟨ right-succ-law-+ℕ (m *ℕ succ (succ n)) (succ n) ⟩ 
                                                              ((succ (m *ℕ succ (succ n) +ℕ succ n)) ==⟨ ap (λ x → succ (x +ℕ succ n)) (right-succ-law-*ℕ m (succ n)) ⟩ 
                                                              ((succ (m *ℕ succ n +ℕ m +ℕ succ n))   ==⟨ ap (λ x → succ (x +ℕ succ n)) (commutative-+ℕ (m *ℕ succ n) m) ⟩ 
                                                              ((succ (m +ℕ m *ℕ succ n +ℕ succ n))   ==⟨ ap (λ x → succ x) (associative-+ℕ m (m *ℕ succ n) (succ n)) ⟩ 
                                                              ((succ (m +ℕ (m *ℕ succ n +ℕ succ n))) ==⟨ ap (λ x → succ (m +ℕ x)) (right-succ-law-+ℕ (m *ℕ succ n) n) ⟩ 
                                                              ((succ (m +ℕ succ (m *ℕ succ n +ℕ n))) ∎)))))))

left-neq-*ℕ : (m n : ℕ) → ¬ (succ m == (succ (succ n)) *ℕ succ m)
left-neq-*ℕ m n p = right-neq-*ℕ m n ((succ m)                     ==⟨ p ⟩ 
                                      (((succ (succ n)) *ℕ succ m) ==⟨ commutative-*ℕ (succ (succ n)) (succ m) ⟩ 
                                      ((succ m *ℕ (succ (succ n))) ∎))) 

_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇ 
0      ≤ℕ n      = 𝟙 
succ m ≤ℕ 0      = 𝟘 
succ m ≤ℕ succ n = m ≤ℕ n

reflexive-≤ℕ : (m : ℕ) → m ≤ℕ m 
reflexive-≤ℕ 0        = ⋆ 
reflexive-≤ℕ (succ m) = reflexive-≤ℕ m

antisymmetric-≤ℕ : (m n : ℕ) → m ≤ℕ n → n ≤ℕ m → m == n 
antisymmetric-≤ℕ 0        0        p q = refl 0
antisymmetric-≤ℕ 0        (succ n) p q = 𝟘-recursion (Id ℕ 0 (succ n)) q
antisymmetric-≤ℕ (succ m) 0        p q = 𝟘-recursion (Id ℕ (succ m) 0) p 
antisymmetric-≤ℕ (succ m) (succ n) p q = ap succ (antisymmetric-≤ℕ m n p q)

transitive-≤ℕ : (m n k : ℕ) → m ≤ℕ n → n ≤ℕ k → m ≤ℕ k 
transitive-≤ℕ 0        n        k        p q = ⋆
transitive-≤ℕ (succ m) (succ n) 0        p q = q
transitive-≤ℕ (succ m) (succ n) (succ k) p q = transitive-≤ℕ m n k p q

decidable-≤ℕ : (m n : ℕ) → decidable (m ≤ℕ n)
decidable-≤ℕ 0        0        = inl ⋆
decidable-≤ℕ 0        (succ n) = inl ⋆
decidable-≤ℕ (succ m) 0        = inr (λ x → x)
decidable-≤ℕ (succ m) (succ n) = decidable-≤ℕ m n

preserve-order-+ℕ : (k m n : ℕ) → (m ≤ℕ n) → ((k +ℕ m) ≤ℕ (k +ℕ n))
preserve-order-+ℕ 0        m n p = p
preserve-order-+ℕ (succ k) m n p = preserve-order-+ℕ k m n p

reflects-order-+ℕ : (k m n : ℕ) → ((k +ℕ m) ≤ℕ (k +ℕ n)) → (m ≤ℕ n)
reflects-order-+ℕ 0        m n p = p
reflects-order-+ℕ (succ k) m n p = reflects-order-+ℕ k m n p

preserve-order-succ-ℕ : (m n : ℕ) → (m ≤ℕ n) → (succ m ≤ℕ succ n)
preserve-order-succ-ℕ m n p = p

reflects-order-succ-ℕ : (m n : ℕ) → (succ m ≤ℕ succ n) → m ≤ℕ n 
reflects-order-succ-ℕ m n p = p

left-zero-law-≤ℕ : (n : ℕ) → (n +ℕ 0) ≤ℕ n
left-zero-law-≤ℕ 0        = ⋆
left-zero-law-≤ℕ (succ n) = left-zero-law-≤ℕ n

right-zero-law-≤ℕ : (n : ℕ) → n ≤ℕ (n +ℕ 0)
right-zero-law-≤ℕ 0        = ⋆
right-zero-law-≤ℕ (succ n) = right-zero-law-≤ℕ n

succ-law-≤ℕ : (n : ℕ) → n ≤ℕ succ n 
succ-law-≤ℕ 0        = ⋆
succ-law-≤ℕ (succ n) = succ-law-≤ℕ n

left-succ-law-≤ℕ : (m n : ℕ) → succ m ≤ℕ n → m ≤ℕ n 
left-succ-law-≤ℕ 0        (succ n) p = ⋆
left-succ-law-≤ℕ (succ m) (succ n) p = left-succ-law-≤ℕ m n p

right-succ-law-≤ℕ : (m n : ℕ) → m ≤ℕ n → m ≤ℕ succ n 
right-succ-law-≤ℕ zero     n        p = ⋆
right-succ-law-≤ℕ (succ m) (succ n) p = right-succ-law-≤ℕ m n p 

unit-law-≤ℕ : (n : ℕ) → n ≤ℕ succ n 
unit-law-≤ℕ 0        = ⋆
unit-law-≤ℕ (succ n) = unit-law-≤ℕ n

concat-id-leq-id : (x₁ x₂ x₃ x₄ : ℕ) → x₁ == x₂ → x₂ ≤ℕ x₃ → x₃ == x₄ → x₁ ≤ℕ x₄
concat-id-leq-id x₁ x₂ x₃ x₄ (refl _) q (refl _) = q

concat-leq-id : (x₁ x₂ x₃ : ℕ) → x₁ ≤ℕ x₂ → x₂ == x₃ → x₁ ≤ℕ x₃
concat-leq-id x₁ x₂ x₃ p (refl _) = p 

concat-id-leq : (x₁ x₂ x₃ : ℕ) → x₁ == x₂ → x₂ ≤ℕ x₃ → x₁ ≤ℕ x₃
concat-id-leq x₁ x₂ x₃ (refl _) q = q

_<ℕ_ : ℕ → ℕ → 𝓤₀ ̇ 
m      <ℕ 0      = 𝟘
0      <ℕ succ n = 𝟙
succ m <ℕ succ n = m <ℕ n 

antireflexive-<ℕ : (n : ℕ) → ¬ (n <ℕ n)
antireflexive-<ℕ 0        p = p
antireflexive-<ℕ (succ n) p = antireflexive-<ℕ n p

antisymmetric-<ℕ : (m n : ℕ) → m <ℕ n → n <ℕ m → n == m 
antisymmetric-<ℕ (succ m) (succ n) p q = ap succ (antisymmetric-<ℕ m n p q)

transitive-<ℕ : (m n k : ℕ) → m <ℕ n → n <ℕ k → m <ℕ k 
transitive-<ℕ 0        (succ n) (succ k) p q = ⋆
transitive-<ℕ (succ m) (succ n) (succ k) p q = transitive-<ℕ m n k p q

decidable-<ℕ : (m n : ℕ) → decidable (m <ℕ n)
decidable-<ℕ 0        0        = inr (λ x → x)
decidable-<ℕ 0        (succ n) = inl ⋆
decidable-<ℕ (succ m) 0        = inr (λ x → x)
decidable-<ℕ (succ m) (succ n) = decidable-<ℕ m n

succ-law-<ℕ : (n : ℕ) → n <ℕ succ n 
succ-law-<ℕ zero = ⋆
succ-law-<ℕ (succ n) = succ-law-<ℕ n

unit-law-<ℕ : (n : ℕ) → n <ℕ (n +ℕ 1)
unit-law-<ℕ 0        = ⋆
unit-law-<ℕ (succ n) = unit-law-<ℕ n

right-unit-law-<ℕ : (m n : ℕ) → m <ℕ n → m <ℕ (n +ℕ 1)
right-unit-law-<ℕ 0        (succ n) p = ⋆
right-unit-law-<ℕ (succ m) (succ n) p = right-unit-law-<ℕ m n p 

neq-<ℕ : (m n : ℕ) → m <ℕ n → ¬ (m == n)
neq-<ℕ zero (succ n) p = λ ()
neq-<ℕ (succ m) (succ n) p q = neq-<ℕ m n p (injective-succ-ℕ m n q)

distℕ : ℕ → ℕ → ℕ
distℕ 0        n        = n
distℕ (succ m) 0        = (succ m)
distℕ (succ m) (succ n) = distℕ m n

id-zero-distℕ : (m n : ℕ) → m == n → distℕ m n == 0
id-zero-distℕ 0        0        p = refl 0
id-zero-distℕ (succ m) (succ n) p = id-zero-distℕ m n (injective-succ-ℕ m n p)

zero-id-distℕ : (m n : ℕ) → distℕ m n == 0 → m == n
zero-id-distℕ 0        0        p = refl 0
zero-id-distℕ (succ m) (succ n) p = ap succ (zero-id-distℕ m n p)

symmetric-distℕ : (m n : ℕ) → distℕ m n == distℕ n m
symmetric-distℕ 0        0        = refl 0
symmetric-distℕ 0        (succ n) = refl (succ n) 
symmetric-distℕ (succ m) 0        = refl (succ m) 
symmetric-distℕ (succ m) (succ n) = symmetric-distℕ m n

left-zero-law-distℕ : (n : ℕ) → distℕ 0 n == n 
left-zero-law-distℕ n = refl n

right-zero-law-distℕ : (n : ℕ) → distℕ n 0 == n 
right-zero-law-distℕ 0        = refl 0
right-zero-law-distℕ (succ n) = refl (succ n)

dist-leq-+ℕ : (m n : ℕ) → distℕ m n ≤ℕ (m +ℕ n)
dist-leq-+ℕ 0        0        = ⋆
dist-leq-+ℕ 0        (succ n) = dist-leq-+ℕ 0 n
dist-leq-+ℕ (succ m) 0        = right-zero-law-≤ℕ m
dist-leq-+ℕ (succ m) (succ n) = right-succ-law-≤ℕ (distℕ m n) (m +ℕ succ n) 
                                    (transitive-≤ℕ (distℕ m n)     (m +ℕ n)        (m +ℕ succ n) (dist-leq-+ℕ m n)
                                    (transitive-≤ℕ (m +ℕ n)        (succ (m +ℕ n)) (m +ℕ succ n) (succ-law-≤ℕ (m +ℕ n))
                                    (concat-leq-id (succ (m +ℕ n)) (succ (m +ℕ n)) (m +ℕ succ n) (reflexive-≤ℕ (m +ℕ n)) (right-succ-law-+ℕ m n ⁻¹))))

triangle-inequality : (m n k : ℕ) → distℕ m n ≤ℕ (distℕ m k +ℕ distℕ k n) 
triangle-inequality 0        0        k        = ⋆
triangle-inequality 0        (succ n) 0        = triangle-inequality zero n zero
triangle-inequality 0        (succ n) (succ k) = triangle-inequality zero n k 
triangle-inequality (succ m) 0        0        = right-zero-law-≤ℕ m
triangle-inequality (succ m) 0        (succ k) = concat-leq-id (succ m) (succ (distℕ m k +ℕ k)) (distℕ m k +ℕ succ k) 
                                                    (preserve-order-succ-ℕ m (distℕ m k +ℕ k) 
                                                        (concat-id-leq-id m (distℕ m 0) (distℕ m k +ℕ distℕ k 0) (distℕ m k +ℕ k) 
                                                            (right-zero-law-distℕ m ⁻¹) 
                                                            (triangle-inequality m 0 k) 
                                                            (ap (λ x → distℕ m k +ℕ x) (right-zero-law-distℕ k)))) 
                                                    (right-succ-law-+ℕ (distℕ m k) k ⁻¹)
triangle-inequality (succ m) (succ n) 0        = right-succ-law-≤ℕ (distℕ m n) (m +ℕ succ n) 
                                                    (concat-leq-id (distℕ m n) (succ (m +ℕ n)) (m +ℕ succ n) 
                                                        (right-succ-law-≤ℕ (distℕ m n) (m +ℕ n) (dist-leq-+ℕ m n)) 
                                                        (right-succ-law-+ℕ m n ⁻¹))
triangle-inequality (succ m) (succ n) (succ k) = triangle-inequality m n k

Fin : ℕ → 𝓤₀ ̇
Fin 0         = 𝟘
Fin (succ k) = Fin k + 𝟙

inclusion-Fin : (k : ℕ) → Fin k → Fin (succ k) 
inclusion-Fin k = inl

Fin-nat : {k : ℕ} → Fin k → ℕ
Fin-nat {succ k} (inl x) = Fin-nat x
Fin-nat {succ k} (inr x) = k

upper-bound-Fin-nat : {k : ℕ} → (x : Fin k) → Fin-nat x <ℕ k 
upper-bound-Fin-nat {succ k} (inl x) = transitive-<ℕ (Fin-nat x) k (succ k) (upper-bound-Fin-nat x) (succ-law-<ℕ k)
upper-bound-Fin-nat {succ k} (inr x) = succ-law-<ℕ k

injective-Fin-nat : {k : ℕ} → {x y : Fin k} → Fin-nat x == Fin-nat y → x == y 
injective-Fin-nat {succ k} {inl x} {inl y} p = ap inl (injective-Fin-nat p)
injective-Fin-nat {succ k} {inl x} {inr ⋆} p = 𝟘-recursion (inl x == inr ⋆) (neq-<ℕ (Fin-nat x) k (upper-bound-Fin-nat x) p)  
injective-Fin-nat {succ k} {inr ⋆} {inl y} p = 𝟘-recursion (inr ⋆ == inl y) (neq-<ℕ (Fin-nat y) k (upper-bound-Fin-nat y) (p ⁻¹)) 
injective-Fin-nat {succ k} {inr ⋆} {inr ⋆} p = refl (inr ⋆)    

zero-Fin : {k : ℕ} → Fin (succ k) 
zero-Fin {0}      = inr ⋆ 
zero-Fin {succ k} = inl zero-Fin

skip-zero-Fin : {k : ℕ} → Fin k → Fin (succ k)
skip-zero-Fin {succ k} (inl x) = inl (skip-zero-Fin x) 
skip-zero-Fin {succ k} (inr ⋆) = inr ⋆

succ-Fin : {k : ℕ} → Fin k → Fin k 
succ-Fin {succ k} (inl x) = skip-zero-Fin x 
succ-Fin {succ k} (inr ⋆) = zero-Fin  

Fin-nat-zero : {k : ℕ} → Fin-nat (zero-Fin {k}) == 0 
Fin-nat-zero {0}      = refl zero
Fin-nat-zero {succ k} = Fin-nat-zero {k}

Fin-nat-skip-zero : {k : ℕ} → (x : Fin k) → Fin-nat (skip-zero-Fin x) == Fin-nat x +ℕ 1
Fin-nat-skip-zero {succ k} (inl x) = Fin-nat-skip-zero x
Fin-nat-skip-zero {succ k} (inr ⋆) = right-unit-law-+ℕ k ⁻¹

Eq-Fin : {k : ℕ} → Fin k → Fin k → 𝓤₀ ̇ 
Eq-Fin {succ k} (inl x) (inl y) = Eq-Fin x y
Eq-Fin {succ k} (inl x) (inr ⋆) = 𝟘
Eq-Fin {succ k} (inr ⋆) (inl y) = 𝟘
Eq-Fin {succ k} (inr ⋆) (inr ⋆) = 𝟙

relf-Eq-Fin : {k : ℕ} → (x : Fin k) → Eq-Fin x x 
relf-Eq-Fin {succ k} (inl x) = relf-Eq-Fin x
relf-Eq-Fin {succ k} (inr ⋆) = ⋆

id-Eq-Fin : {k : ℕ} → {x y : Fin k} → x == y → Eq-Fin x y 
id-Eq-Fin {k} (refl _) = relf-Eq-Fin {k} _

Eq-id-Fin : {k : ℕ} → {x y : Fin k} → Eq-Fin x y → x == y 
Eq-id-Fin {succ k} {inl x} {inl y} p = ap inl (Eq-id-Fin p)
Eq-id-Fin {succ k} {inl x} {inr ⋆} ()
Eq-id-Fin {succ k} {inr ⋆} {inr ⋆} ⋆ = refl (inr ⋆) 

decidable-Eq-Fin : {k : ℕ} (x y : Fin k) → decidable (Eq-Fin x y)
decidable-Eq-Fin {succ k} (inl x) (inl y) = decidable-Eq-Fin x y
decidable-Eq-Fin {succ k} (inl x) (inr ⋆) = decidable-𝟘
decidable-Eq-Fin {succ k} (inr ⋆) (inl y) = decidable-𝟘
decidable-Eq-Fin {succ k} (inr ⋆) (inr ⋆) = decidable-𝟙 

injective-inclusion-Fin : {k : ℕ} → {x y : Fin k} → inclusion-Fin k x == inclusion-Fin k y → x == y 
injective-inclusion-Fin p = Eq-id-Fin (id-Eq-Fin p)

zero-neq-succ-Fin : {k : ℕ} → {x : Fin k} → ¬ (succ-Fin (inclusion-Fin k x) == zero-Fin)
zero-neq-succ-Fin {succ k} {inl x} p = zero-neq-succ-Fin (injective-inclusion-Fin p) 
zero-neq-succ-Fin {succ k} {inr ⋆} p = id-Eq-Fin p

injective-skip-zero-Fin : {k : ℕ} → {x y : Fin k} → skip-zero-Fin x == skip-zero-Fin y → x == y
injective-skip-zero-Fin {succ k} {inl x} {inl y} p = ap inl (injective-skip-zero-Fin (injective-inclusion-Fin p))
injective-skip-zero-Fin {succ k} {inl x} {inr ⋆} p = 𝟘-recursion (inl x == inr ⋆) (id-Eq-Fin p)
injective-skip-zero-Fin {succ k} {inr ⋆} {inl y} p = 𝟘-recursion (inr ⋆ == inl y) (id-Eq-Fin p)
injective-skip-zero-Fin {succ k} {inr ⋆} {inr ⋆} p = refl (inr ⋆)

injective-succ-Fin : {k : ℕ} → {x y : Fin k} → succ-Fin x == succ-Fin y → x == y
injective-succ-Fin {succ k} {inl x} {inl y} p = ap inl (injective-skip-zero-Fin p)
injective-succ-Fin {succ k} {inl x} {inr ⋆} p = 𝟘-recursion (inl x == inr ⋆) (zero-neq-succ-Fin p)
injective-succ-Fin {succ k} {inr ⋆} {inl y} p = 𝟘-recursion (inr ⋆ == inl y) (zero-neq-succ-Fin (p ⁻¹))
injective-succ-Fin {succ k} {inr ⋆} {inr ⋆} p = refl (inr ⋆)

neg-one-Fin : {k : ℕ} → Fin (succ k)
neg-one-Fin {k} = inr ⋆

neg-two-Fin : {k : ℕ} → Fin (succ k)
neg-two-Fin {0}      = inr ⋆ 
neg-two-Fin {succ k} = inl (inr ⋆)

skip-neg-two-Fin : {k : ℕ} → Fin k → Fin (succ k)
skip-neg-two-Fin {succ k} (inl x) = inl (inl x)
skip-neg-two-Fin {succ k} (inr ⋆) = inr ⋆

pred-Fin : {k : ℕ} → Fin k → Fin k 
pred-Fin {succ k} (inl x) = skip-neg-two-Fin (pred-Fin x)
pred-Fin {succ k} (inr x) = neg-two-Fin

pred-zero-Fin : {k : ℕ} → pred-Fin {succ k} zero-Fin == neg-one-Fin
pred-zero-Fin {0}      = refl (inr ⋆)
pred-zero-Fin {succ k} = ap skip-neg-two-Fin pred-zero-Fin

succ-skip-neg-two-Fin : {k : ℕ} → (x : Fin k) → succ-Fin (skip-neg-two-Fin x) == inl (succ-Fin  x)
succ-skip-neg-two-Fin {succ k} (inl x) = refl (inl (skip-zero-Fin x))
succ-skip-neg-two-Fin {succ k} (inr ⋆) = refl (inl zero-Fin)

succ-pred-id-Fin : {k : ℕ} → (x : Fin k) → succ-Fin (pred-Fin x) == x
succ-pred-id-Fin {succ 0}        (inr ⋆) = refl (inr ⋆)
succ-pred-id-Fin {succ (succ k)} (inl x) = (succ-Fin (skip-neg-two-Fin (pred-Fin x)))   ==⟨ succ-skip-neg-two-Fin (pred-Fin x) ⟩
                                           (inl (succ-Fin (pred-Fin x))                 ==⟨ ap inl (succ-pred-id-Fin x) ⟩
                                           (inl x                                       ∎))
succ-pred-id-Fin {succ (succ k)} (inr ⋆) = refl (inr ⋆)

pred-succ-id-Fin : {k : ℕ} → (x : Fin k) → pred-Fin (succ-Fin x) == x 
pred-succ-id-Fin {succ 0}        (inr ⋆)       = refl (inr ⋆)
pred-succ-id-Fin {succ (succ k)} (inl (inl x)) = ap skip-neg-two-Fin (pred-succ-id-Fin (inl x))
pred-succ-id-Fin {succ (succ k)} (inl (inr ⋆)) = refl (inl (inr ⋆)) 
pred-succ-id-Fin {succ (succ k)} (inr ⋆)       = pred-zero-Fin
