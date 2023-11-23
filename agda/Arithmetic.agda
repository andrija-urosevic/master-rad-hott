{-# OPTIONS --without-K --safe #-}

module Arithmetic where

open import MLTT public

infixl 20 _+ℕ_
infixl 21 _*ℕ_
infixr 22 _^ℕ_
infixl 23 _!

_+ℕ_ : ℕ → ℕ → ℕ
m +ℕ 0        = m 
m +ℕ (succ n) = succ (m +ℕ n)

_*ℕ_ : ℕ → ℕ → ℕ
m *ℕ 0        = m 
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