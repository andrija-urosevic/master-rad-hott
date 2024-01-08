{-# OPTIONS --without-K --safe #-}

module Integer where

open import Natural public

ℤ : 𝓤₀ ̇
ℤ = ℕ + (𝟙 + ℕ)

pattern 0ℤ  = inr (inl ⋆)
pattern +1ℤ  = inr (inr 0)
pattern -1ℤ = inl 0

+ℤ_ : ℕ → ℤ
+ℤ n = (inr ∘ inr) n

-ℤ_ : ℕ → ℤ
-ℤ n = inl n

ℤ-induction : (P : ℤ → 𝓤 ̇ )
            → P -1ℤ
            → ((n : ℕ) → P (-ℤ n) → P (-ℤ (succ n)))
            → P 0ℤ
            → P +1ℤ
            → ((n : ℕ) → P (+ℤ n) → P (+ℤ (succ n)))
            → (k : ℤ) → P k
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inl zero)           = p-neg-1
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inl (succ x))       = p-neg-succ x (ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inl x))
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inr true)           = p-zero
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inr (inr zero))     = p-pos-1
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inr (inr (succ x))) = p-pos-succ x (ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inr (inr x))) 

succℤ : ℤ → ℤ
succℤ -1ℤ = 0ℤ
succℤ (inl (succ x)) = -ℤ x
succℤ 0ℤ = +1ℤ
succℤ +1ℤ = +ℤ 1
succℤ (inr (inr (succ x))) = +ℤ (succ (succ x))
 
predℤ : ℤ → ℤ
predℤ -1ℤ = -ℤ (succ 0)
predℤ (inl (succ x)) = -ℤ (succ (succ x))
predℤ 0ℤ = -1ℤ
predℤ +1ℤ = 0ℤ 
predℤ (inr (inr (succ x))) = +ℤ (succ x)

_+ℤ_ : ℤ → ℤ → ℤ
-1ℤ +ℤ y = predℤ y
inl (succ x) +ℤ y = predℤ (inl x +ℤ y) 
0ℤ +ℤ y = y
+1ℤ +ℤ y = succℤ y 
inr (inr (succ x)) +ℤ y = succℤ (inr (inr x) +ℤ y)

negℤ : ℤ → ℤ
negℤ (inl x) = +ℤ x
negℤ 0ℤ = 0ℤ
negℤ (inr (inr x)) = -ℤ x

_*ℤ_ : ℤ → ℤ → ℤ
-1ℤ *ℤ y = negℤ y
inl (succ x) *ℤ y = negℤ y +ℤ ((inl x) *ℤ y) 
0ℤ *ℤ y = 0ℤ
+1ℤ *ℤ y = y 
inr (inr (succ x)) *ℤ y = y +ℤ ((inr (inr x)) *ℤ y)


