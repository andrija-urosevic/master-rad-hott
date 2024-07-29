{-# OPTIONS --without-K --safe #-}

module List where

open import Natural public
open import Boolean public

data List {𝓤} (X : 𝓤 ̇) : 𝓤 ̇ where
    nil  : List X
    cons : X → List X → List X

[] : {X : 𝓤 ̇ } → List X
[] = nil

_∷_ : {X : 𝓤 ̇ } → X → List X → List X
x ∷ xs = cons x xs 

List-induction : {X : 𝓤 ̇ } → X → List X 
List-induction x = x ∷ []

tail : {X : 𝓤 ̇ } → (List X) → List X 
tail nil         = nil
tail (cons x xs) = xs

is-nil : {X : 𝓤 ̇ } → (List X) → 𝓤₀ ̇
is-nil nil         = 𝟙
is-nil (cons x xs) = 𝟘

is-nonnil : {X : 𝓤 ̇ } → (List X) → 𝓤₀ ̇
is-nonnil xs = ¬ (is-nil xs)

is-nonnil-cons : {X : 𝓤 ̇ } → (x : X) → (xs : List X) → (List X) → is-nonnil (cons x xs)
is-nonnil-cons x xs = λ _ z → z

fold : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y → Y) → List X → Y → Y
fold f nil         acc = acc
fold f (cons x xs) acc = fold f xs (f x acc) 

foldl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : Y → X → Y) → Y → List X → Y 
foldl f acc nil         = acc
foldl f acc (cons x xs) = foldl f (f acc x) xs

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
product nil         = 1
product (cons x xs) = x *ℕ product xs

concat : {X : 𝓤 ̇ } → List X → List X → List X 
concat nil         ys = ys 
concat (cons x xs) ys = cons x (concat xs ys)

flatten : {X : 𝓤 ̇ } → List (List X) → List X
flatten nil           = nil 
flatten (cons xs xss) = concat xs (flatten xss)

reverse : {X : 𝓤 ̇ } → List X → List X 
reverse nil         = nil 
reverse (cons x xs) = concat (reverse xs) (List-induction x)

filter : {X : 𝓤 ̇ } → (X → 𝟚) → List X → List X 
filter f nil         = nil 
filter f (cons x xs) = if (f x) then (cons x (filter f xs)) else (filter f xs)

length-append : {X : 𝓤 ̇ } (xs ys : List X) 
              → length (concat xs ys) == length xs +ℕ length ys
length-append nil         ys = refl (length ys)
length-append (cons x xs) ys = ap succ (length-append xs ys)

length-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
           → (f : X → Y) (xs : List X)
           → length (map f xs) == length xs
length-map f nil         = refl zero
length-map f (cons x xs) = ap succ (length-map f xs)

length-reverse : {X : 𝓤 ̇ } (xs : List X) 
               → length (reverse xs) == length xs 
length-reverse nil = refl zero
length-reverse (cons x xs) = (length (concat (reverse xs) (cons x nil))) ==⟨ length-append (reverse xs) (cons x nil) ⟩ 
                             ((length (reverse xs) +ℕ 1)                 ==⟨ right-unit-law-+ℕ (length (reverse xs)) ⟩ 
                             (succ (length (reverse xs))                 ==⟨ ap succ (length-reverse xs) ⟩ 
                             (succ (length xs)                           ∎)))
 
length-tail : {X : 𝓤 ̇ } (xs : List X)
            → ¬ (xs == nil) → length (tail xs) +ℕ 1 == length xs
length-tail nil         p = 𝟘-recursion (Id ℕ 1 0) (p (refl nil))
length-tail (cons x xs) _ = right-unit-law-+ℕ (length xs)

concat-assoc : {X : 𝓤 ̇ } (xs ys zs : List X) 
             → concat (concat xs ys) zs == concat xs (concat ys zs)
concat-assoc nil         ys zs = refl (concat ys zs)
concat-assoc (cons x xs) ys zs = ap (cons x) (concat-assoc xs ys zs)

concat-nil : {X : 𝓤 ̇ } (xs : List X)
           → concat xs nil == xs
concat-nil nil         = refl nil
concat-nil (cons x xs) = ap (cons x) (concat-nil xs)

map-id : {X : 𝓤 ̇ } (xs : List X)
       → map (λ x → x) xs == xs
map-id nil         = refl nil
map-id (cons x xs) = ap (cons x) (map-id xs)

map-tail : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
         → (f : X → Y) 
         → (xs : List X)
         → map f (tail xs) == tail (map f xs)
map-tail f nil         = refl nil
map-tail f (cons x xs) = refl (map f xs)

map-concat : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
           → (f : X → Y) 
           → (xs ys : List X) 
           → map f (concat xs ys) == concat (map f xs) (map f ys)
map-concat f nil         ys = refl (map f ys) 
map-concat f (cons x xs) ys = ap (cons (f x)) (map-concat f xs ys)

map-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        → (g : Y → Z)
        → (f : X → Y)
        → (xs : List X) 
        → map g (map f xs) == map (g ∘ f) xs
map-map g f nil         = refl nil 
map-map g f (cons x xs) = ap (cons (g (f x))) (map-map g f xs)

map-comp-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
             → (g : Y → Z)
             → (f : X → Y)
             → (xs : List X)
             → (map g ∘ map f) xs == map (g ∘ f) xs
map-comp-map g f nil         = refl nil 
map-comp-map g f (cons x xs) = ap (cons (g (f x))) (map-comp-map g f xs)

map-reverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
            → (f : X → Y)
            → (xs : List X)
            → reverse (map f xs) == map f (reverse xs)
map-reverse f nil = refl nil        
map-reverse f (cons x xs) = (concat (reverse (map f xs)) (cons (f x) nil))  ==⟨ ap (λ z → concat z (cons (f x) nil)) (map-reverse f xs) ⟩ 
                            (concat (map f (reverse xs)) (cons (f x) nil)   ==⟨ map-concat f (reverse xs) (cons x nil) ⁻¹ ⟩ 
                            (map f (concat (reverse xs) (cons x nil))       ∎)) 

map-reflective : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
               → (f : X → Y)
               → (xs ys : List X)
               → xs == ys → map f xs == map f ys 
map-reflective f xs ys p = ap (map f) p

reverse-concat : {X : 𝓤 ̇ } (xs ys : List X)
               → reverse (concat xs ys) == concat (reverse ys) (reverse xs)
reverse-concat nil ys = concat-nil (reverse ys) ⁻¹
reverse-concat (cons x xs) ys = (concat (reverse (concat xs ys)) (cons x nil))          ==⟨ ap (λ z → concat z (cons x nil)) (reverse-concat xs ys) ⟩ 
                                (concat (concat (reverse ys) (reverse xs)) (cons x nil) ==⟨ concat-assoc (reverse ys) (reverse xs) (cons x nil) ⟩ 
                                (concat (reverse ys) (concat (reverse xs) (cons x nil)) ∎))

reverse-reverse-id : {X : 𝓤 ̇ } (xs : List X)
                   → reverse (reverse xs) == xs
reverse-reverse-id nil = refl nil
reverse-reverse-id (cons x xs) = (reverse (concat (reverse xs) (cons x nil))) ==⟨ reverse-concat (reverse xs) (cons x nil) ⟩ 
                                 (cons x (reverse (reverse xs))               ==⟨ ap (cons x) (reverse-reverse-id xs) ⟩ 
                                 (cons x xs                                   ∎))

reverse-reflective : {X : 𝓤 ̇ } (xs ys : List X)
                   → xs == ys → reverse xs == reverse ys
reverse-reflective xs ys p = ap reverse p

flatten-concat : {X : 𝓤 ̇ } (xss yss : List (List X))
               → flatten (concat xss yss) == concat (flatten xss) (flatten yss)
flatten-concat nil yss           = refl (flatten yss) 
flatten-concat (cons xs xss) yss = (concat xs (flatten (concat xss yss)))          ==⟨ ap (concat xs) (flatten-concat xss yss) ⟩ 
                                   (concat xs (concat (flatten xss) (flatten yss)) ==⟨ concat-assoc xs (flatten xss) (flatten yss) ⁻¹ ⟩ 
                                   (concat (concat xs (flatten xss)) (flatten yss) ∎))

map-flatten : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
            → (f : X → Y) 
            → (xss : List (List X))
            → map f (flatten xss) == flatten (map (map f) xss)
map-flatten f nil           = refl nil 
map-flatten f (cons xs xss) = (map f (concat xs (flatten xss)))                ==⟨ map-concat f xs (flatten xss) ⟩ 
                              (concat (map f xs) (map f (flatten xss))         ==⟨ ap (concat (map f xs)) (map-flatten f xss) ⟩ 
                              (concat (map f xs) (flatten (map (map f) xss))   ∎)) 

flatten-cons-nil : {X : 𝓤 ̇ } 
                 → (xss : List X)
                 → flatten (cons xss nil) == xss
flatten-cons-nil nil         = refl nil
flatten-cons-nil (cons xs xss) = ap (cons xs) (flatten-cons-nil xss)

reverse-flatten : {X : 𝓤 ̇ } 
                → (xss : List (List X))
                → reverse (flatten xss) == flatten (map reverse (reverse xss))
reverse-flatten nil         = refl nil 
reverse-flatten (cons xs xss) = (reverse (concat xs (flatten xss)))                                             ==⟨ reverse-concat xs (flatten xss) ⟩ 
                                (concat (reverse (flatten xss)) (reverse xs)                                    ==⟨ ap (λ z → concat z (reverse xs)) (reverse-flatten xss) ⟩ 
                                (concat (flatten (map reverse (reverse xss))) (reverse xs)                      ==⟨ ap (concat (flatten (map reverse (reverse xss)))) (flatten-cons-nil (reverse xs) ⁻¹) ⟩ 
                                (concat (flatten (map reverse (reverse xss))) (flatten (cons (reverse xs) nil)) ==⟨ flatten-concat (map reverse (reverse xss)) (cons (reverse xs) nil) ⁻¹ ⟩ 
                                (flatten (concat (map reverse (reverse xss)) (cons (reverse xs) nil))           ==⟨ refl (flatten (concat (map reverse (reverse xss)) (cons (reverse xs) nil))) ⟩ 
                                (flatten (concat (map reverse (reverse xss)) (map reverse (cons xs nil)))       ==⟨ ap flatten (map-concat reverse (reverse xss) (cons xs nil) ⁻¹) ⟩
                                (flatten (map reverse (concat (reverse xss) (cons xs nil)))                     ∎))))))

if-then-else-concat : {X : 𝓤 ̇ }
                    → (b : 𝟚)
                    → (xs ys zs : List X)
                    → (if b then (concat xs zs) else (concat ys zs)) == concat (if b then xs else ys) zs
if-then-else-concat true  xs ys zs = refl (concat xs zs)
if-then-else-concat false xs ys zs = refl (concat ys zs)

filter-concat : {X : 𝓤 ̇ } 
              → (f : X → 𝟚) 
              → (xs ys : List X)
              → filter f (concat xs ys) == concat (filter f xs) (filter f ys)
filter-concat f nil         ys = refl (filter f ys) 
filter-concat f (cons x xs) ys = (if f x then cons x (filter f (concat xs ys)) else (filter f (concat xs ys)))                      ==⟨ ap (λ z → if (f x) then (cons x z) else z) (filter-concat f xs ys) ⟩ 
                                 (if f x then cons x (concat (filter f xs) (filter f ys)) else (concat (filter f xs) (filter f ys)) ==⟨ if-then-else-concat (f x) (cons x (filter f xs)) (filter f xs) (filter f ys) ⟩ 
                                 (concat (if f x then cons x (filter f xs) else (filter f xs)) (filter f ys)                        ∎))

fold-concat : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
            → (f : X → Y → Y) 
            → (xs ys : List X)
            → (acc : Y)
            → fold f (concat xs ys) acc == (fold f ys (fold f xs acc))
fold-concat f nil         ys acc = refl (fold f ys acc)
fold-concat f (cons x xs) ys acc = fold-concat f xs ys (f x acc)

fold-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } 
         → (g : Y → Z → Z) (f : X → Y) 
         → (xs : List X)
         → (acc : Z)
         → fold g (map f xs) acc == fold (g ∘ f) xs acc
fold-map g f nil         acc = refl acc
fold-map g f (cons x xs) acc = fold-map g f xs (g (f x) acc)

fold-cons-concat-reverse : {X : 𝓤 ̇ }
                         → (xs : List X)
                         → (acc : List X)
                         → fold cons xs acc == concat (reverse xs) acc
fold-cons-concat-reverse nil         acc = refl acc
fold-cons-concat-reverse (cons x xs) acc = fold cons xs (cons x acc)                      ==⟨ fold-cons-concat-reverse xs (cons x acc) ⟩ 
                                           (concat (reverse xs) (cons x acc)              ==⟨ refl (concat (reverse xs) (cons x acc)) ⟩ 
                                           (concat (reverse xs) (concat (cons x nil) acc) ==⟨ concat-assoc (reverse xs) (cons x nil) acc ⁻¹ ⟩ 
                                           (concat (concat (reverse xs) (cons x nil)) acc ∎)))

fold-cons-reverse : {X : 𝓤 ̇ } 
                  → (xs : List X)
                  → fold cons xs nil == reverse xs 
fold-cons-reverse xs = (fold cons xs nil)       ==⟨ fold-cons-concat-reverse xs nil ⟩ 
                       (concat (reverse xs) nil ==⟨ concat-nil (reverse xs) ⟩ 
                       (reverse xs              ∎))

fold-concat-flatten-reverse : {X : 𝓤 ̇ }
                            → (xss : List (List X))
                            → (acc : List X)
                            → fold concat xss acc == concat (flatten (reverse xss)) acc
fold-concat-flatten-reverse nil           acc = refl acc
fold-concat-flatten-reverse (cons xs xss) acc = (fold concat xss (concat xs acc))                                    ==⟨ fold-concat-flatten-reverse xss (concat xs acc) ⟩ 
                                                (concat (flatten (reverse xss)) (concat xs acc)                      ==⟨ ap (λ z → concat (flatten (reverse xss)) (concat z acc)) (concat-nil xs ⁻¹) ⟩ 
                                                (concat (flatten (reverse xss)) (concat (flatten (cons xs nil)) acc) ==⟨ (concat-assoc (flatten (reverse xss)) (flatten (cons xs nil)) acc) ⁻¹ ⟩ 
                                                (concat (concat (flatten (reverse xss)) (flatten (cons xs nil))) acc ==⟨ ap (λ z → concat z acc) ((flatten-concat (reverse xss) (cons xs nil)) ⁻¹) ⟩ 
                                                (concat (flatten (concat (reverse xss) (cons xs nil))) acc           ∎))))
