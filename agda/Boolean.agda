{-# OPTIONS --without-K --safe #-}

module Boolean where

open import MLTT public

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

¬𝟚 : 𝟚 → 𝟚
¬𝟚 true  = false
¬𝟚 false = true

_∧𝟚_ : 𝟚 → 𝟚 → 𝟚
true  ∧𝟚 true  = true
true  ∧𝟚 false = false
false ∧𝟚 true  = false
false ∧𝟚 false = false

_∨𝟚_ : 𝟚 → 𝟚 → 𝟚
true  ∨𝟚 true  = true
true  ∨𝟚 false = true
false ∨𝟚 true  = true
false ∨𝟚 false = false

Eq-𝟚 : 𝟚 → 𝟚 → 𝓤₀ ̇
Eq-𝟚 true  true  = 𝟙
Eq-𝟚 true  false = 𝟘
Eq-𝟚 false true  = 𝟘
Eq-𝟚 false false = 𝟙

id-Eq-𝟚 : (x y : 𝟚) → (x == y) ↔ Eq-𝟚 x y
id-Eq-𝟚 true  true  = (λ x → ⋆) , (λ x → refl true)
id-Eq-𝟚 true  false = (λ ()) , (λ ()) 
id-Eq-𝟚 false true  = (λ ()) , (λ ())
id-Eq-𝟚 false false = (λ x → ⋆) , (λ x → refl false)

not-id-neg-𝟚 : (x : 𝟚) → ¬ (x == ¬𝟚 x)
not-id-neg-𝟚 true  = λ ()
not-id-neg-𝟚 false = λ ()

