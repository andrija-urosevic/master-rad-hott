{-# OPTIONS --without-K --safe #-}

module List where

open import Natural public

data List {𝓤} (X : 𝓤 ̇) : 𝓤 ̇ where
    nil  : List X
    cons : X → List X → List X

[] : {X : 𝓤 ̇ } → List X
[] = nil

_∷_ : {X : 𝓤 ̇ } → X → List X → List X
x ∷ xs = cons x xs 

List-induction : {X : 𝓤 ̇ } → X → List X 
List-induction x = x ∷ []

fold : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (b : Y) (f : X → (Y → Y)) → List X → Y
fold acc f nil         = acc
fold acc f (cons x xs) = f x (fold acc f xs)

map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → List X → List Y
map f nil         = nil
map f (cons x xs) = cons (f x) (map f xs)

length : {X : 𝓤 ̇ } → List X → ℕ
length nil         = 0 
length (cons x xs) = succ (length xs)

sum : List ℕ → ℕ
sum nil         = 0 
sum (cons x xs) = x +ℕ sum xs

product : List ℕ → ℕ
product nil = 1
product (cons x xs) = x *ℕ product xs

concat : {X : 𝓤 ̇ } → List X → List X → List X 
concat nil ys = ys 
concat (cons x xs) ys = cons x (concat xs ys)

flatten : {X : 𝓤 ̇ } → List (List X) → List X
flatten nil = nil 
flatten (cons xs xss) = concat xs (flatten xss)

reverse : {X : 𝓤 ̇ } → List X → List X 
reverse nil = nil 
reverse (cons x xs) = concat (reverse xs) (List-induction x)
