{-# OPTIONS --without-K --safe #-}

module Integer where

open import Natural public

ℤ : 𝓤₀ ̇
ℤ = ℕ + (𝟙 + ℕ)

pattern 0ℤ  = inr (inl ⋆)
pattern +1ℤ  = inr (inr 0)
pattern -1ℤ = inl 0

+ℤ_ : ℕ → ℤ
+ℤ n = inr (inr n)

-ℤ_ : ℕ → ℤ
-ℤ n = inl n

ℤ-induction : (P : ℤ → 𝓤 ̇ )
            → P -1ℤ
            → ((n : ℕ) → P (-ℤ n) → P (-ℤ (succ n)))
            → P 0ℤ
            → P +1ℤ
            → ((n : ℕ) → P (+ℤ n) → P (+ℤ (succ n)))
            → (k : ℤ) → P k
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ -1ℤ                  = p-neg-1
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inl (succ x))       = p-neg-succ x (ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inl x))
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ 0ℤ                   = p-zero
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ +1ℤ                  = p-pos-1
ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inr (inr (succ x))) = p-pos-succ x (ℤ-induction P p-neg-1 p-neg-succ p-zero p-pos-1 p-pos-succ (inr (inr x))) 

succℤ : ℤ → ℤ
succℤ -1ℤ            = 0ℤ
succℤ (inl (succ x)) = -ℤ x
succℤ 0ℤ             = +1ℤ
succℤ (inr (inr x))  = +ℤ (succ x)
 
predℤ : ℤ → ℤ
predℤ (inl x)              = -ℤ (succ x)
predℤ 0ℤ                   = -1ℤ
predℤ +1ℤ                  = 0ℤ
predℤ (inr (inr (succ x))) = +ℤ x

infixl 21 _+ℤ_
infixl 22 _*ℤ_

_+ℤ_ : ℤ → ℤ → ℤ
-1ℤ                +ℤ y = predℤ y
inl (succ x)       +ℤ y = predℤ (inl x +ℤ y) 
0ℤ                 +ℤ y = y
+1ℤ                +ℤ y = succℤ y 
inr (inr (succ x)) +ℤ y = succℤ (inr (inr x) +ℤ y)

add-ℤ : ℤ → ℤ → ℤ
add-ℤ k l = l +ℤ k 

negℤ : ℤ → ℤ
negℤ (inl x)       = +ℤ x
negℤ 0ℤ            = 0ℤ
negℤ (inr (inr x)) = -ℤ x

negℤ-negℤ-id : (k : ℤ) → negℤ (negℤ k) == k 
negℤ-negℤ-id (inl x)       = refl (inl x)
negℤ-negℤ-id 0ℤ            = refl 0ℤ
negℤ-negℤ-id (inr (inr x)) = refl (inr (inr x))

neg-pred-succ-neg : (k : ℤ) → negℤ (predℤ k) == succℤ (negℤ k)
neg-pred-succ-neg -1ℤ                  = refl (inr (inr 1))
neg-pred-succ-neg (inl (succ x))       = refl (inr (inr (succ (succ x))))
neg-pred-succ-neg 0ℤ                   = refl +1ℤ
neg-pred-succ-neg +1ℤ                  = refl 0ℤ
neg-pred-succ-neg (inr (inr (succ x))) = refl (inl x)

neg-succ-pred-neg : (k : ℤ) → negℤ (succℤ k) == predℤ (negℤ k)
neg-succ-pred-neg -1ℤ                  = refl 0ℤ
neg-succ-pred-neg (inl (succ x))       = refl (inr (inr x))
neg-succ-pred-neg 0ℤ                   = refl (inl zero)
neg-succ-pred-neg +1ℤ                  = refl (inl 1)
neg-succ-pred-neg (inr (inr (succ x))) = refl (inl (succ (succ x)))

_*ℤ_ : ℤ → ℤ → ℤ
-1ℤ *ℤ y                = negℤ y
inl (succ x) *ℤ y       = negℤ y +ℤ ((inl x) *ℤ y) 
0ℤ *ℤ y                 = 0ℤ
+1ℤ *ℤ y                = y 
inr (inr (succ x)) *ℤ y = y +ℤ ((inr (inr x)) *ℤ y)

succ-pred-id : (k : ℤ) → succℤ (predℤ k) == k
succ-pred-id -1ℤ                  = refl -1ℤ
succ-pred-id (inl (succ x))       = refl (inl (succ x))
succ-pred-id 0ℤ                   = refl 0ℤ
succ-pred-id +1ℤ                  = refl +1ℤ
succ-pred-id (inr (inr (succ x))) = refl (inr (inr (succ x)))

pred-succ-id : (k : ℤ) → predℤ (succℤ k) == k 
pred-succ-id -1ℤ                  = refl -1ℤ
pred-succ-id (inl (succ x))       = refl (inl (succ x))
pred-succ-id 0ℤ                   = refl 0ℤ
pred-succ-id +1ℤ                  = refl +1ℤ 
pred-succ-id (inr (inr (succ x))) = refl (inr (inr (succ x)))

left-unit-law-+ℤ : (k : ℤ) → 0ℤ +ℤ k == k
left-unit-law-+ℤ -1ℤ                  = refl -1ℤ
left-unit-law-+ℤ (inl (succ x))       = refl (inl (succ x))
left-unit-law-+ℤ 0ℤ                   = refl 0ℤ 
left-unit-law-+ℤ +1ℤ                  = refl +1ℤ 
left-unit-law-+ℤ (inr (inr (succ x))) = refl (inr (inr (succ x)))

right-unit-law-+ℤ : (k : ℤ) → k +ℤ 0ℤ == k 
right-unit-law-+ℤ -1ℤ                  = refl -1ℤ
right-unit-law-+ℤ (inl (succ x))       = (predℤ (inl x +ℤ 0ℤ)) ==⟨ ap predℤ (right-unit-law-+ℤ (inl x)) ⟩ 
                                         ((inl (succ x))       ∎)
right-unit-law-+ℤ 0ℤ                   = refl 0ℤ
right-unit-law-+ℤ +1ℤ                  = refl +1ℤ 
right-unit-law-+ℤ (inr (inr (succ x))) = (succℤ (inr (inr x) +ℤ 0ℤ)) ==⟨ ap succℤ (right-unit-law-+ℤ (inr (inr x))) ⟩ 
                                         ((inr (inr (succ x)))       ∎)

left-pred-law-+ℤ : (k l : ℤ) → predℤ k +ℤ l == predℤ (k +ℤ l)
left-pred-law-+ℤ -1ℤ                  l = refl (predℤ (predℤ l))
left-pred-law-+ℤ (inl (succ x))       l = refl (predℤ (predℤ (inl x +ℤ l)))
left-pred-law-+ℤ 0ℤ                   l = refl (predℤ l)
left-pred-law-+ℤ +1ℤ                  l = pred-succ-id l ⁻¹
left-pred-law-+ℤ (inr (inr (succ x))) l = pred-succ-id (inr (inr x) +ℤ l) ⁻¹

right-pred-law-+ℤ : (k l : ℤ) → k +ℤ predℤ l == predℤ (k +ℤ l)
right-pred-law-+ℤ -1ℤ                  l = refl (predℤ (predℤ l))
right-pred-law-+ℤ (inl (succ x))       l = (predℤ (inl x +ℤ predℤ l))    ==⟨ ap predℤ (right-pred-law-+ℤ (inl x) l) ⟩ 
                                           ((predℤ (predℤ (inl x +ℤ l))) ∎)
right-pred-law-+ℤ 0ℤ                   l = refl (predℤ l)
right-pred-law-+ℤ +1ℤ                  l = (succℤ (predℤ l)) ==⟨ succ-pred-id l ⟩ 
                                           (l                ==⟨ pred-succ-id l ⁻¹ ⟩ 
                                           ((predℤ (succℤ l)) ∎)) 
right-pred-law-+ℤ (inr (inr (succ x))) l = (succℤ (inr (inr x) +ℤ predℤ l))    ==⟨ ap succℤ (right-pred-law-+ℤ (inr (inr x)) l) ⟩ 
                                           (succℤ (predℤ (inr (inr x) +ℤ l))   ==⟨ succ-pred-id (inr (inr x) +ℤ l) ⟩ 
                                           ((inr (inr x) +ℤ l)                 ==⟨ pred-succ-id (inr (inr x) +ℤ l) ⁻¹ ⟩ 
                                           ((predℤ (succℤ (inr (inr x) +ℤ l))) ∎)))

left-succ-law-+ℤ : (k l : ℤ) → succℤ k +ℤ l == succℤ (k +ℤ l)
left-succ-law-+ℤ -1ℤ                  l = succ-pred-id l ⁻¹
left-succ-law-+ℤ (inl (succ x))       l = succ-pred-id (inl x +ℤ l) ⁻¹
left-succ-law-+ℤ 0ℤ                   l = refl (succℤ l)
left-succ-law-+ℤ +1ℤ                  l = refl (succℤ (succℤ l))
left-succ-law-+ℤ (inr (inr (succ x))) l = refl (succℤ (succℤ (inr (inr x) +ℤ l)))

right-succ-law-+ℤ : (k l : ℤ) → k +ℤ succℤ l == succℤ (k +ℤ l)
right-succ-law-+ℤ -1ℤ                   l = predℤ (succℤ l)    ==⟨ pred-succ-id l ⟩ 
                                            (l                 ==⟨ succ-pred-id l ⁻¹ ⟩ 
                                            ((succℤ (predℤ l)) ∎))
right-succ-law-+ℤ (inl (succ x))       l = (predℤ (inl x +ℤ succℤ l))    ==⟨ ap predℤ (right-succ-law-+ℤ (inl x) l) ⟩ 
                                           ((predℤ (succℤ (inl x +ℤ l))) ==⟨ pred-succ-id (inl x +ℤ l) ⟩ 
                                           ((inl x +ℤ l)                 ==⟨ succ-pred-id (inl x +ℤ l) ⁻¹ ⟩ 
                                           ((succℤ (predℤ (inl x +ℤ l))) ∎)))
right-succ-law-+ℤ 0ℤ                   l = refl (succℤ l)
right-succ-law-+ℤ +1ℤ                  l = refl (succℤ (succℤ l))
right-succ-law-+ℤ (inr (inr (succ x))) l = (succℤ (inr (inr x) +ℤ succℤ l))    ==⟨ (ap succℤ (right-succ-law-+ℤ (inr (inr x)) l)) ⟩ 
                                           ((succℤ (succℤ (inr (inr x) +ℤ l))) ∎)

associative-+ℤ : (k l p : ℤ) → (k +ℤ l) +ℤ p == k +ℤ (l +ℤ p)
associative-+ℤ -1ℤ                  l p = left-pred-law-+ℤ l p
associative-+ℤ (inl (succ x))       l p = (predℤ (inl x +ℤ l) +ℤ p)    ==⟨ (left-pred-law-+ℤ (inl x +ℤ l) p) ⟩ 
                                          (predℤ ((inl x +ℤ l) +ℤ p)   ==⟨ ap predℤ (associative-+ℤ (inl x) l p) ⟩ 
                                          ((predℤ (inl x +ℤ (l +ℤ p))) ==⟨ (left-pred-law-+ℤ (inl x) (l +ℤ p)) ⁻¹ ⟩ 
                                          ((predℤ (inl x +ℤ (l +ℤ p))) ∎)))
associative-+ℤ 0ℤ                   l p = refl (l +ℤ p)
associative-+ℤ +1ℤ                  l p = left-succ-law-+ℤ l p 
associative-+ℤ (inr (inr (succ x))) l p = (succℤ (inr (inr x) +ℤ l) +ℤ p)    ==⟨ (left-succ-law-+ℤ (inr (inr x) +ℤ l) p) ⟩ 
                                          ((succℤ ((inr (inr x) +ℤ l) +ℤ p)) ==⟨ ap succℤ (associative-+ℤ (inr (inr x)) l p) ⟩ 
                                          ((succℤ (inr (inr x) +ℤ (l +ℤ p))) ==⟨ (left-succ-law-+ℤ (inr (inr x)) (l +ℤ p)) ⁻¹ ⟩ 
                                          ((succℤ (inr (inr x) +ℤ (l +ℤ p))) ∎)))

commutative-+ℤ : (k l : ℤ) → k +ℤ l == l +ℤ k 
commutative-+ℤ -1ℤ                  l = (predℤ l)        ==⟨ left-pred-law-+ℤ 0ℤ l ⟩ 
                                        (predℤ (0ℤ +ℤ l) ==⟨ ap predℤ (commutative-+ℤ 0ℤ l) ⟩ 
                                        (predℤ (l +ℤ 0ℤ) ==⟨ (right-pred-law-+ℤ l 0ℤ) ⁻¹ ⟩ 
                                        ((l +ℤ inl zero) ∎)))
commutative-+ℤ (inl (succ x))       l = (predℤ (inl x +ℤ l))  ==⟨ ap predℤ (commutative-+ℤ (inl x) l) ⟩ 
                                        ((predℤ (l +ℤ inl x)) ==⟨ (right-pred-law-+ℤ l (inl x)) ⁻¹ ⟩ 
                                        ((l +ℤ inl (succ x))  ∎))
commutative-+ℤ 0ℤ                   l = l          ==⟨ (right-unit-law-+ℤ l) ⁻¹ ⟩ 
                                        ((l +ℤ 0ℤ) ∎)
commutative-+ℤ +1ℤ                  l = (0ℤ +ℤ succℤ l)        ==⟨ left-succ-law-+ℤ 0ℤ l ⟩
                                        (succℤ (0ℤ +ℤ l)       ==⟨ ap succℤ (commutative-+ℤ 0ℤ l) ⟩
                                        (succℤ (l +ℤ 0ℤ)       ==⟨ right-succ-law-+ℤ l 0ℤ ⁻¹ ⟩ 
                                        ((l +ℤ inr (inr zero)) ∎)))
commutative-+ℤ (inr (inr (succ x))) l = (succℤ (inr (inr x) +ℤ l))  ==⟨ ap succℤ (commutative-+ℤ (inr (inr x)) l) ⟩ 
                                        ((succℤ (l +ℤ inr (inr x))) ==⟨ right-succ-law-+ℤ l (inr (inr x)) ⁻¹ ⟩ 
                                        ((l +ℤ inr (inr (succ x)))  ∎))

left-inverse-law-+ℤ : (k : ℤ) → negℤ k +ℤ k == 0ℤ
left-inverse-law-+ℤ -1ℤ                  = refl 0ℤ
left-inverse-law-+ℤ (inl (succ x))       = (succℤ (inr (inr x) +ℤ inl (succ x)))   ==⟨ ap succℤ (right-pred-law-+ℤ (inr (inr x)) (inl x)) ⟩ 
                                           ((succℤ (predℤ (inr (inr x) +ℤ inl x))) ==⟨ succ-pred-id (inr (inr x) +ℤ inl x) ⟩ 
                                           ((inr (inr x) +ℤ inl x)                 ==⟨ left-inverse-law-+ℤ (inl x) ⟩ 
                                           (0ℤ                                     ∎)))
left-inverse-law-+ℤ 0ℤ                   = refl 0ℤ
left-inverse-law-+ℤ +1ℤ                  = refl 0ℤ
left-inverse-law-+ℤ (inr (inr (succ x))) = (predℤ (inl x +ℤ inr (inr (succ x))))   ==⟨ ap predℤ (right-succ-law-+ℤ (inl x) (inr (inr x))) ⟩ 
                                           ((predℤ (succℤ (inl x +ℤ inr (inr x)))) ==⟨ pred-succ-id (inl x +ℤ inr (inr x)) ⟩ 
                                           ((inl x +ℤ inr (inr x))                 ==⟨ (left-inverse-law-+ℤ (inr (inr x))) ⟩ 
                                           (0ℤ                                     ∎))) 
  
right-inverse-law-+ℤ : (k : ℤ) → k +ℤ negℤ k == 0ℤ
right-inverse-law-+ℤ k = (k +ℤ negℤ k)  ==⟨ (commutative-+ℤ k (negℤ k)) ⟩ 
                         ((negℤ k +ℤ k) ==⟨ (left-inverse-law-+ℤ k) ⟩ 
                         (0ℤ            ∎))

left-zero-law-*ℤ : (k : ℤ) → 0ℤ *ℤ k == 0ℤ
left-zero-law-*ℤ k = refl 0ℤ

right-zero-law-*ℤ : (k : ℤ) → k *ℤ 0ℤ == 0ℤ
right-zero-law-*ℤ -1ℤ                  = refl 0ℤ
right-zero-law-*ℤ (inl (succ x))       = right-zero-law-*ℤ (inl x) 
right-zero-law-*ℤ 0ℤ                   = refl 0ℤ 
right-zero-law-*ℤ +1ℤ                  = refl 0ℤ 
right-zero-law-*ℤ (inr (inr (succ x))) = right-zero-law-*ℤ (inr (inr x))

left-unit-law-*ℤ : (k : ℤ) → +1ℤ *ℤ k == k 
left-unit-law-*ℤ k = refl k

right-unit-law-*ℤ : (k : ℤ) → k *ℤ +1ℤ == k 
right-unit-law-*ℤ -1ℤ                  = refl -1ℤ
right-unit-law-*ℤ (inl (succ x))       = (predℤ (inl x *ℤ +1ℤ)) ==⟨ ap predℤ (right-unit-law-*ℤ (inl x)) ⟩ 
                                         ((inl (succ x))        ∎)
right-unit-law-*ℤ 0ℤ                   = refl 0ℤ
right-unit-law-*ℤ +1ℤ                  = refl +1ℤ 
right-unit-law-*ℤ (inr (inr (succ x))) = succℤ (inr (inr x) *ℤ +1ℤ) ==⟨ ap succℤ (right-unit-law-*ℤ (inr (inr x))) ⟩ 
                                         ((inr (inr (succ x)))      ∎)

left-pred-law-*ℤ : (k l : ℤ) → predℤ k *ℤ l == k *ℤ l +ℤ (negℤ l)
left-pred-law-*ℤ -1ℤ                  l = refl (negℤ l +ℤ negℤ l)
left-pred-law-*ℤ (inl (succ x))       l = (negℤ l +ℤ (negℤ l +ℤ inl x *ℤ l))  ==⟨ ap (λ y → negℤ l +ℤ y) (commutative-+ℤ (negℤ l) (inl x *ℤ l)) ⟩ 
                                          ((negℤ l +ℤ (inl x *ℤ l +ℤ negℤ l)) ==⟨ associative-+ℤ (negℤ l) (inl x *ℤ l) (negℤ l) ⁻¹ ⟩ 
                                          ((negℤ l +ℤ inl x *ℤ l +ℤ negℤ l)   ∎))
left-pred-law-*ℤ 0ℤ                   l = refl (negℤ l)
left-pred-law-*ℤ +1ℤ                  l = right-inverse-law-+ℤ l ⁻¹ 
left-pred-law-*ℤ (inr (inr (succ x))) l = ((l +ℤ inr (inr x) *ℤ l +ℤ negℤ l)   ==⟨ commutative-+ℤ (l +ℤ inr (inr x) *ℤ l) (negℤ l) ⟩ 
                                          ((negℤ l +ℤ (l +ℤ inr (inr x) *ℤ l)) ==⟨ (associative-+ℤ (negℤ l) l (inr (inr x) *ℤ l)) ⁻¹ ⟩ 
                                          ((negℤ l +ℤ l +ℤ inr (inr x) *ℤ l)   ==⟨ ap (λ y → y +ℤ inr (inr x) *ℤ l) (left-inverse-law-+ℤ l) ⟩ 
                                          ((inr (inr x) *ℤ l)                  ∎)))) ⁻¹

left-succ-law-*ℤ : (k l : ℤ) → (succℤ k) *ℤ l == k *ℤ l +ℤ l
left-succ-law-*ℤ -1ℤ                  l = left-inverse-law-+ℤ l ⁻¹
left-succ-law-*ℤ (inl (succ x))       l = ((negℤ l +ℤ inl x *ℤ l +ℤ l)   ==⟨ commutative-+ℤ (negℤ l +ℤ inl x *ℤ l) l ⟩ 
                                          ((l +ℤ (negℤ l +ℤ inl x *ℤ l)) ==⟨ associative-+ℤ l (negℤ l) (inl x *ℤ l) ⁻¹ ⟩ 
                                          (((l +ℤ negℤ l) +ℤ inl x *ℤ l) ==⟨ ap (λ y → y +ℤ inl x *ℤ l) (right-inverse-law-+ℤ l) ⟩ 
                                          ((inl x *ℤ l)                  ∎)))) ⁻¹
left-succ-law-*ℤ 0ℤ                   l = refl l 
left-succ-law-*ℤ +1ℤ                  l = refl (l +ℤ l) 
left-succ-law-*ℤ (inr (inr (succ x))) l = (l +ℤ (l +ℤ inr (inr x) *ℤ l))  ==⟨ ap (λ y → l +ℤ y) (commutative-+ℤ l (inr (inr x) *ℤ l)) ⟩ 
                                          ((l +ℤ (inr (inr x) *ℤ l +ℤ l)) ==⟨ associative-+ℤ l (inr (inr x) *ℤ l) l ⁻¹ ⟩ 
                                          ((l +ℤ inr (inr x) *ℤ l +ℤ l)   ∎))

neg-+-neg-+-neg : (k l : ℤ) → negℤ (k +ℤ l) == negℤ k +ℤ negℤ l 
neg-+-neg-+-neg -1ℤ                  l = neg-pred-succ-neg l
neg-+-neg-+-neg (inl (succ x))       l = negℤ (predℤ (inl x +ℤ l))       ==⟨ neg-pred-succ-neg (inl x +ℤ l) ⟩ 
                                        ((succℤ (negℤ (inl x +ℤ l)))     ==⟨ ap succℤ (neg-+-neg-+-neg (inl x) l) ⟩ 
                                        ((succℤ (inr (inr x) +ℤ negℤ l)) ∎))
neg-+-neg-+-neg 0ℤ                   l = refl (negℤ l)
neg-+-neg-+-neg +1ℤ                  l = neg-succ-pred-neg l
neg-+-neg-+-neg (inr (inr (succ x))) l = (negℤ (succℤ (inr (inr x) +ℤ l)))  ==⟨ neg-succ-pred-neg (inr (inr x) +ℤ l) ⟩ 
                                         ((predℤ (negℤ (inr (inr x) +ℤ l))) ==⟨ ap predℤ (neg-+-neg-+-neg (inr (inr x)) l) ⟩ 
                                         ((predℤ (inl x +ℤ negℤ l))         ∎))

left-neg-law-ℤ : (k l : ℤ) → negℤ (k *ℤ l) == negℤ k *ℤ l
left-neg-law-ℤ -1ℤ                  l = negℤ-negℤ-id l
left-neg-law-ℤ (inl (succ x))       l = ((negℤ (negℤ l +ℤ inl x *ℤ l))        ==⟨ neg-+-neg-+-neg (negℤ l) (inl x *ℤ l) ⟩ 
                                        ((negℤ (negℤ l) +ℤ negℤ (inl x *ℤ l)) ==⟨ ap (λ y → y +ℤ negℤ (inl x *ℤ l)) (negℤ-negℤ-id l) ⟩ 
                                        ((l +ℤ negℤ (inl x *ℤ l))             ==⟨ ap (λ y → l +ℤ y) (left-neg-law-ℤ (inl x) l ) ⟩ 
                                        ((l +ℤ inr (inr x) *ℤ l)              ∎))))
left-neg-law-ℤ 0ℤ                   l = refl 0ℤ
left-neg-law-ℤ +1ℤ                  l = refl (negℤ l)
left-neg-law-ℤ (inr (inr (succ x))) l = ((negℤ (l +ℤ inr (inr x) *ℤ l))      ==⟨ neg-+-neg-+-neg l (inr (inr x) *ℤ l) ⟩ 
                                        ((negℤ l +ℤ negℤ (inr (inr x) *ℤ l)) ==⟨ ap (λ y → negℤ l +ℤ y) (left-neg-law-ℤ (inr (inr x)) l) ⟩ 
                                        ((negℤ l +ℤ inl x *ℤ l)              ∎)))

right-neg-law-ℤ : (k l : ℤ) → negℤ (k *ℤ l) == k *ℤ negℤ l 
right-neg-law-ℤ -1ℤ                  l = refl (negℤ (negℤ l))
right-neg-law-ℤ (inl (succ x))       l = (negℤ (negℤ l +ℤ inl x *ℤ l))         ==⟨ neg-+-neg-+-neg (negℤ l) (inl x *ℤ l) ⟩ 
                                         ((negℤ (negℤ l) +ℤ negℤ (inl x *ℤ l)) ==⟨ ap (λ y → negℤ (negℤ l) +ℤ y) (right-neg-law-ℤ (inl x) l) ⟩ 
                                         ((negℤ (negℤ l) +ℤ inl x *ℤ negℤ l)   ∎))
right-neg-law-ℤ 0ℤ                   l = refl 0ℤ
right-neg-law-ℤ +1ℤ                  l = refl (negℤ l)
right-neg-law-ℤ (inr (inr (succ x))) l = (negℤ (l +ℤ inr (inr x) *ℤ l))       ==⟨ neg-+-neg-+-neg l (inr (inr x) *ℤ l) ⟩ 
                                         ((negℤ l +ℤ negℤ (inr (inr x) *ℤ l)) ==⟨ ap (λ y → negℤ l +ℤ y) (right-neg-law-ℤ (inr (inr x)) l) ⟩ 
                                         ((negℤ l +ℤ inr (inr x) *ℤ negℤ l)   ∎))

left-distirbutive-ℤ : (k l p : ℤ) → k *ℤ (l +ℤ p) == k *ℤ l +ℤ k *ℤ p 
left-distirbutive-ℤ -1ℤ                  l p = neg-+-neg-+-neg l p
left-distirbutive-ℤ (inl (succ x))       l p = (negℤ (l +ℤ p) +ℤ inl x *ℤ (l +ℤ p))              ==⟨ ap (λ y → y +ℤ inl x *ℤ (l +ℤ p)) (neg-+-neg-+-neg l p) ⟩ 
                                               ((negℤ l +ℤ negℤ p +ℤ inl x *ℤ (l +ℤ p))          ==⟨ ap (λ y → negℤ l +ℤ negℤ p +ℤ y) (left-distirbutive-ℤ (inl x) l p) ⟩ 
                                               ((negℤ l +ℤ negℤ p +ℤ (inl x *ℤ l +ℤ inl x *ℤ p)) ==⟨ (associative-+ℤ (negℤ l +ℤ negℤ p) (inl x *ℤ l) (inl x *ℤ p)) ⁻¹ ⟩ 
                                               ((negℤ l +ℤ negℤ p +ℤ inl x *ℤ l +ℤ inl x *ℤ p)   ==⟨ ap (λ y → y +ℤ inl x *ℤ p) (associative-+ℤ (negℤ l) (negℤ p) (inl x *ℤ l)) ⟩ 
                                               ((negℤ l +ℤ (negℤ p +ℤ inl x *ℤ l) +ℤ inl x *ℤ p) ==⟨ ap (λ y → negℤ l +ℤ y +ℤ inl x *ℤ p) (commutative-+ℤ (negℤ p) (inl x *ℤ l)) ⟩ 
                                               ((negℤ l +ℤ (inl x *ℤ l +ℤ negℤ p) +ℤ inl x *ℤ p) ==⟨ ap (λ y → y +ℤ inl x *ℤ p) ((associative-+ℤ (negℤ l) (inl x *ℤ l) (negℤ p)) ⁻¹) ⟩ 
                                               ((negℤ l +ℤ inl x *ℤ l +ℤ negℤ p +ℤ inl x *ℤ p)   ==⟨ associative-+ℤ (negℤ l +ℤ inl x *ℤ l) (negℤ p) (inl x *ℤ p) ⟩ 
                                               ((negℤ l +ℤ inl x *ℤ l +ℤ (negℤ p +ℤ inl x *ℤ p)) ∎)))))))
left-distirbutive-ℤ 0ℤ                   l p = refl 0ℤ
left-distirbutive-ℤ +1ℤ                  l p = refl (l +ℤ p)
left-distirbutive-ℤ (inr (inr (succ x))) l p = (l +ℤ p +ℤ inr (inr x) *ℤ (l +ℤ p))                 ==⟨ ap (λ y → l +ℤ p +ℤ y) (left-distirbutive-ℤ (inr (inr x)) l p) ⟩ 
                                               ((l +ℤ p +ℤ (inr (inr x) *ℤ l +ℤ inr (inr x) *ℤ p)) ==⟨ associative-+ℤ (l +ℤ p) (inr (inr x) *ℤ l) (inr (inr x) *ℤ p) ⁻¹ ⟩ 
                                               ((l +ℤ p +ℤ inr (inr x) *ℤ l +ℤ inr (inr x) *ℤ p)   ==⟨ ap (λ y → y +ℤ inr (inr x) *ℤ p) (associative-+ℤ l p (inr (inr x) *ℤ l)) ⟩ 
                                               ((l +ℤ (p +ℤ inr (inr x) *ℤ l) +ℤ inr (inr x) *ℤ p) ==⟨ ap (λ y → l +ℤ y +ℤ inr (inr x) *ℤ p) (commutative-+ℤ p (inr (inr x) *ℤ l)) ⟩ 
                                               ((l +ℤ (inr (inr x) *ℤ l +ℤ p) +ℤ inr (inr x) *ℤ p) ==⟨ ap (λ y → y +ℤ inr (inr x) *ℤ p) ((associative-+ℤ l (inr (inr x) *ℤ l) p) ⁻¹) ⟩ 
                                               ((l +ℤ inr (inr x) *ℤ l +ℤ p +ℤ inr (inr x) *ℤ p)   ==⟨ associative-+ℤ (l +ℤ inr (inr x) *ℤ l) p (inr (inr x) *ℤ p) ⟩ 
                                               ((l +ℤ inr (inr x) *ℤ l +ℤ (p +ℤ inr (inr x) *ℤ p)) ∎))))))

right-distirbutive-ℤ : (k l p : ℤ) → (k +ℤ l) *ℤ p == k *ℤ p +ℤ l *ℤ p
right-distirbutive-ℤ -1ℤ                  l p = (predℤ l *ℤ p)      ==⟨ left-pred-law-*ℤ l p ⟩ 
                                                ((l *ℤ p +ℤ negℤ p) ==⟨ commutative-+ℤ (l *ℤ p) (negℤ p) ⟩ 
                                                ((negℤ p +ℤ l *ℤ p) ∎))
right-distirbutive-ℤ (inl (succ x))       l p = (predℤ (inl x +ℤ l) *ℤ p)           ==⟨ left-pred-law-*ℤ (inl x +ℤ l) p ⟩ 
                                                (((inl x +ℤ l) *ℤ p +ℤ negℤ p)      ==⟨ commutative-+ℤ ((inl x +ℤ l) *ℤ p) (negℤ p) ⟩ 
                                                ((negℤ p +ℤ (inl x +ℤ l) *ℤ p)      ==⟨ ap (λ y → negℤ p +ℤ y) (right-distirbutive-ℤ (inl x) l p) ⟩ 
                                                ((negℤ p +ℤ (inl x *ℤ p +ℤ l *ℤ p)) ==⟨ associative-+ℤ (negℤ p) (inl x *ℤ p) (l *ℤ p) ⁻¹ ⟩ 
                                                ((negℤ p +ℤ inl x *ℤ p +ℤ l *ℤ p)   ∎))))
right-distirbutive-ℤ 0ℤ                   l p = refl (l *ℤ p)
right-distirbutive-ℤ +1ℤ                  l p = (succℤ l *ℤ p) ==⟨ left-succ-law-*ℤ l p ⟩ 
                                                ((l *ℤ p +ℤ p) ==⟨ commutative-+ℤ (l *ℤ p) p ⟩ 
                                                ((p +ℤ l *ℤ p) ∎))
right-distirbutive-ℤ (inr (inr (succ x))) l p = (succℤ (inr (inr x) +ℤ l) *ℤ p)      ==⟨ left-succ-law-*ℤ (inr (inr x) +ℤ l) p ⟩ 
                                                (((inr (inr x) +ℤ l) *ℤ p +ℤ p)      ==⟨ commutative-+ℤ ((inr (inr x) +ℤ l) *ℤ p) p ⟩ 
                                                ((p +ℤ (inr (inr x) +ℤ l) *ℤ p)      ==⟨ ap (λ y → p +ℤ y) (right-distirbutive-ℤ (inr (inr x)) l p) ⟩ 
                                                ((p +ℤ (inr (inr x) *ℤ p +ℤ l *ℤ p)) ==⟨ (associative-+ℤ p (inr (inr x) *ℤ p) (l *ℤ p)) ⁻¹ ⟩ 
                                                ((p +ℤ inr (inr x) *ℤ p +ℤ l *ℤ p)   ∎))))

associative-*ℤ : (k l p : ℤ) → (k *ℤ l) *ℤ p == k *ℤ (l *ℤ p)
associative-*ℤ -1ℤ                  l p = left-neg-law-ℤ l p ⁻¹
associative-*ℤ (inl (succ x))       l p = ((negℤ l +ℤ inl x *ℤ l) *ℤ p)         ==⟨ right-distirbutive-ℤ (negℤ l) (inl x *ℤ l) p ⟩ 
                                          ((negℤ l *ℤ p +ℤ inl x *ℤ l *ℤ p)     ==⟨ (ap (λ y → y +ℤ inl x *ℤ l *ℤ p) ((left-neg-law-ℤ l p) ⁻¹)) ⟩ 
                                          ((negℤ (l *ℤ p) +ℤ inl x *ℤ l *ℤ p)   ==⟨ (ap (λ y → negℤ (l *ℤ p) +ℤ y) (associative-*ℤ (inl x) l p)) ⟩ 
                                          ((negℤ (l *ℤ p) +ℤ inl x *ℤ (l *ℤ p)) ∎)))
associative-*ℤ 0ℤ                   l p = refl 0ℤ
associative-*ℤ +1ℤ                  l p = refl (l *ℤ p)
associative-*ℤ (inr (inr (succ x))) l p = ((l +ℤ inr (inr x) *ℤ l) *ℤ p)       ==⟨ (right-distirbutive-ℤ l (inr (inr x) *ℤ l) p) ⟩ 
                                          ((l *ℤ p +ℤ inr (inr x) *ℤ l *ℤ p)   ==⟨ ap (λ y → l *ℤ p +ℤ y) (associative-*ℤ (inr (inr x)) l p) ⟩ 
                                          ((l *ℤ p +ℤ inr (inr x) *ℤ (l *ℤ p)) ∎))

commutative-*ℤ : (k l : ℤ) → k *ℤ l == l *ℤ k 
commutative-*ℤ -1ℤ                  l = (negℤ l)           ==⟨ ap negℤ (right-unit-law-*ℤ l) ⁻¹ ⟩ 
                                        ((negℤ (l *ℤ +1ℤ)) ==⟨ right-neg-law-ℤ l +1ℤ ⟩ 
                                        ((l *ℤ inl zero)   ∎))
commutative-*ℤ (inl (succ x))       l = (negℤ l +ℤ inl x *ℤ l)           ==⟨ ap (λ y → negℤ l +ℤ y) (commutative-*ℤ (inl x) l) ⟩ 
                                        ((negℤ l +ℤ l *ℤ inl x)          ==⟨ ap (λ y → negℤ y +ℤ l *ℤ inl x) (right-unit-law-*ℤ l ⁻¹) ⟩ 
                                        ((negℤ (l *ℤ +1ℤ) +ℤ l *ℤ inl x) ==⟨ ap (λ y → y +ℤ l *ℤ inl x) (right-neg-law-ℤ l +1ℤ) ⟩ 
                                        ((l *ℤ inl zero +ℤ l *ℤ inl x)   ==⟨ ((left-distirbutive-ℤ l -1ℤ (inl x)) ⁻¹) ⟩ 
                                        ((l *ℤ inl (succ x))             ∎))))
commutative-*ℤ 0ℤ                   l = right-zero-law-*ℤ l ⁻¹
commutative-*ℤ +1ℤ                  l = right-unit-law-*ℤ l ⁻¹ 
commutative-*ℤ (inr (inr (succ x))) l = (l +ℤ inr (inr x) *ℤ l)         ==⟨ ap (λ y → l +ℤ y) (commutative-*ℤ (inr (inr x)) l) ⟩ 
                                        ((l +ℤ l *ℤ inr (inr x))        ==⟨ ap (λ y → y +ℤ l *ℤ inr (inr x)) ((right-unit-law-*ℤ l) ⁻¹) ⟩ 
                                        ((l *ℤ +1ℤ +ℤ l *ℤ inr (inr x)) ==⟨ (left-distirbutive-ℤ l +1ℤ (inr (inr x))) ⁻¹ ⟩ 
                                        ((l *ℤ inr (inr (succ x)))      ∎)))   