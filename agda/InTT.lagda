\AgdaHide{
\begin{code}

{-# OPTIONS --without-K --safe #-}

module InTT where

open import Universes public

variable 𝓤 𝓥 𝓦 : Universe 


\end{code}
}

\subsection{Тип зависних функција}

Тип зависних функција као такав постоји у језику \textsc{Agda} и није га потребно дефинисати. За фамилију типова $P$ над типом $X$, тип зависних функција $\prod_{(x : X)} P (x)$ у језику \textsc{Agda} записујемо као $(x : X) \to P~x$. Са друге стране, \textsc{Agda} је веома изражајна и омогућава нам да дефинишемо синтаксу на коју смо навикли:

\begin{code}
Π : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
Π {𝓤} {𝓥} {X} P = (x : X) → P x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b
\end{code}
Ова синтакса се веома ретко користи у библиотеци јер је подразумевани начин записивања зависних функција једноставнији.

На основу дефиниције идентитета~\ref{def:id} можемо дефинисати следећу функцију: 
\begin{code}
id : {X : 𝓤 ̇ } → X → X 
id x = x
\end{code}

На основу дефиниције композиције функција~\ref{def:comp} можемо дефинисати следећу функцију:

\begin{code}
_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → (g : (y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
(g ∘ f) x = g (f x)
\end{code}

\subsection{Празан тип}

На основу правила $\0$-form празан тип можемо формирати из празног контекста, односно $\0 : \mathcal{U}_0$. Поред тога, празан тип нема ни један конструктор. У језику \textsc{Agda} то записујемо као:

\begin{code}
data 𝟘 : 𝓤₀ ̇ where
\end{code}

Правило индукције $\0$-ind заједно са недостатком правила израчунавања у језику \textsc{Agda} записујемо као:
\begin{code}
𝟘-induction : (P : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → P x 
𝟘-induction P ()
\end{code}
Приметимо да овде $()$ означава да празан тип нема конструкторе.

Правило рекурзије $\0$-rec уводимо преко правила индукције:
\begin{code}
𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A 
𝟘-recursion A p = 𝟘-induction (λ _ → A) p

!𝟘 : {A : 𝓤 ̇ } → 𝟘 → A 
!𝟘 {𝓤} {A} = 𝟘-recursion A
\end{code}
Приметимо да израз $(λ~\_ \to A)$ означава да тип $A$ не зависи од $x : \0$, односно да тип $A$ није фамилија типова. Функција $!\0$ је само облик рекурзије који имплицитно закључује тип $A$.

Дефиницију празног типа и негације~\ref{def:empty}, као и дефиницију дупле негације у језику \textsc{Agda} записујемо као:
\begin{code}
empty : 𝓤 ̇ → 𝓤 ̇ 
empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

¬¬ : 𝓤 ̇ → 𝓤 ̇ 
¬¬ X = ¬ (¬ X)
\end{code}

Дупла негација се понаша као функтор, односно можемо конструисати елемент $\neg\neg$-$\mathsf{functor} : (X \to Y) \to (\neg \neg X \to \neg \neg Y)$. Да би то постигли, конструишимо прво елемент $\neg$-$\mathsf{inv}$-$\mathsf{functor} : (X \to Y) \to (\neg Y \to \neg X)$. Искористићемо празнине и интерактивно својство језика \textsc{Agda}:
\begin{code}
¬-inv-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (¬ Y → ¬ X)
¬-inv-functor f ny x = {!   !}
\end{code}   
Тренутно треба конструисати елемент тип $\0$, а у контексту се налази $x : X, ny : \neg Y$ и $f : X \to Y$. Због тога примењујемо функцију $ny : \neg Y :\equiv Y → \0$.
\begin{code}
¬-inv-functor f ny x = ny {!   !}
\end{code}
Тренутни циљ постаје конструисање елемента типа $Y$, за исти контекст. Због тога, примењујемо функцију $f : X \to Y$.
\begin{code}
¬-inv-functor f ny x = ny (f {!   !})
\end{code}
На крају, треба конструисати елемент типа $X$, за исти контекст. Како се у контексту налази одговарајућа конструкција, тј. $x : X$ је у контексту, конструкцију тривијално завршавамо:
\begin{code}
¬-inv-functor f ny x = ny (f x)
\end{code}
Тражену конструкцију о функториалности дупле негације извршавамо интерактивно на сличан начин.
\begin{code}
¬¬-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (¬¬ X → ¬¬ Y)
¬¬-functor f nnx ny = nnx (¬-inv-functor f ny)
\end{code}

\subsection{Jединични тип}

На основу правила $\1$-form jединични тип можемо формирати из празног контекста, односно $\1 : \mathcal{U}_0$. Поред тога, на основу правила $\1$-intro$_\star$ jединични тип има један конструктор $\star : \1$. У језику \textsc{Agda} то записујемо као:
\begin{code}
data 𝟙 : 𝓤₀ ̇ where
    ⋆ : 𝟙
\end{code}

Правило индукције $\1$-ind заједно са правилом израчунавања $\1$-comp, као и правило рекурзије $\1$-rec у језику \textsc{Agda} записујемо као:
\begin{code}
𝟙-induction : (P : 𝟙 → 𝓤 ̇ ) → P ⋆ → (x : 𝟙) → P x 
𝟙-induction P p ⋆ = p

𝟙-recursion : (A : 𝓤 ̇ ) → A → 𝟙 → A
𝟙-recursion A = 𝟙-induction (λ _ → A)
\end{code}

Дефиницију јединствене функције~\ref{def:unifun} у језику \textsc{Agda} записујемо као:
\begin{code}
!𝟙 : {A : 𝓤 ̇ } → A → 𝟙
!𝟙 a = ⋆
\end{code}

\subsection{Тип копроизвода}

На основу правила $+$-form тип копроизвода можемо формирати из контекста у коме су $X$ и $Y$ типови. Oдносно, ако $X : \mathcal{U}$ и $Y : \mathcal{V}$, онда $X + Y : \mathcal{U} \sqcup \mathcal{V}$. Поред тога, на основу правила $+$-intro$_\inl$ и $+$-intro$_\inr$ јединични тип има два конструктора $\inl : X \to X + Y$ и $\inr : Y \to X + Y$. У језику \textsc{Agda} то записујемо као:
\begin{code}
data _+_ (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
    inl : X → X + Y 
    inr : Y → X + Y 
\end{code}

Правило индукције $+$-ind заједно са правилима израчунавања $+$-comp$_{\inl}$ и $+$-comp$_{\inr}$, као и правило рекурзије $+$-rec у језику \textsc{Agda} записујемо као:
\begin{code}
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
\end{code}

За функције $f : A \to X$ и $g : B \to Y$ можемо конструисати елемент функције копроизвод $A + B \to X + Y$. У језику \textsc{Agda} то записујемо као:
\begin{code}
_+→_ : {A X : 𝓤 ̇ } {B Y : 𝓤 ̇ } (f : A → X) (g : B → Y) 
     → (A + B) → (X + Y)
(f +→ g) (inl x) = inl (f x)
(f +→ g) (inr x) = inr (g x)
\end{code}

Даље су приказана својства о празном типу и типу копроизвода:
\begin{code}
+-empty : {A : 𝓤 ̇ } {B : 𝓥 ̇ } 
        → ¬ A → ¬ B → ¬ (A + B)
+-empty f g (inl a) = f a
+-empty f g (inr b) = g b

+-left-empty : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
             → ¬ X → X + Y → Y
+-left-empty {𝓤} {X} {Y} ex = +-recursion Y (!𝟘 ∘ ex) id 

+-right-empty : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
              → ¬ Y → X + Y → X 
+-right-empty {𝓤} {X} {Y} ey = +-recursion X id (!𝟘 ∘ ey)
\end{code}

\subsection{Тип зависних парова}

На основу правила $\sum$-form тип зависних парова можемо формирати из контекста у коме је $X$ тип и $Y$ фамилија типови над типом $X$. Oдносно, ако $X : \mathcal{U}$ и $Y : X \to \mathcal{V}$, онда $\sum_{(x : X)} Y (x) : \mathcal{U} \sqcup \mathcal{V}$. Поред тога, на основу правила $\sum$-intro тип зависних парова има један конструктора $(x , y(x)) : \sum_{(x : X)} Y (x)$. У језику \textsc{Agda} то записујемо као:
\begin{code}
record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
    constructor
        _,_
    field
        x : X
        y : Y x
\end{code}

Дефиницију пројекција на први и други елемент~\ref{def:proj} у језику \textsc{Agda} записујемо као:
\begin{code}
fst : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } 
    → Σ Y → X
fst (x , y) = x

snd : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } 
    → (z : Σ Y) → Y (fst z)
snd (x , y) = y
\end{code}

Правило индукције $\sum$-ind заједно са правилима израчунавања $\sum$-comp, као и поступак каријевања и инверзног каријевања у језику \textsc{Agda} записујемо као:
\begin{code}
Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → P (x , y))
            → ((x , y) : Σ Y) → P (x , y)
Σ-induction f (x , y) = f x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → P (x , y))
      → ((x : X) (y : Y x) → P (x , y))
curry f x y = f (x , y)

uncurry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {P : Σ Y → 𝓦 ̇ }
        → ((x : X) (y : Y x) → P (x , y))
        → ((x , y) : Σ Y) → P (x , y)
uncurry f (x , y) = Σ-induction f (x , y)
\end{code}

Слично као и за тип зависних функција, за тип зависних парова можемо увести синтаксу на коју смо навикли:
\begin{code}
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y
\end{code}

На основу типа зависних парова, можемо дефинисати тип (независних) парова или Декартов производ $X \times Y$. Његово правило индукције $\times$-ind и правило израчунавања $\times$-comp, директно следи из правила индукције и правила израчунавања типа зависних парова. У језику \textsc{Agda} то записујемо као:
\begin{code}
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

×-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {P : X × Y → 𝓦 ̇ }
            → ((x : X) (y : Y) → P (x , y))
            → ((x , y) : X × Y) → P (x , y)
×-induction f (x , y) = f x y 
\end{code}

Корисно је увести и следећи пар функција:
\begin{code}
_↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↔ Y = (X → Y) × (Y → X)
\end{code}

\subsection{Типови идентитета}

На основу правила $=$-form тип идентитета можемо формирати из контекста у коме је $X$ тип и у коме су $x : X$ и $y : X$ неки елементи. Oдносно, ако $X : \mathcal{U}$, онда $\Id{X} : X \to X \to \mathcal{U}$. Поред тога, на основу правила $=$-intro тип зависних парова има један конструктора $\refl{X} : X \to \Id{X}$. У језику \textsc{Agda} то записујемо као:

\begin{code}
data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇ where
    refl : (x : X) → Id X x x
\end{code}

Такође, уводимо и синтаксу $x =_X y$ за тип идентитета $\Id{X}(x, y)$ у којој се тип $X$ закључује имплицитно. 
\begin{code}
infixl 10 _==_

_==_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x == y = Id _ x y
\end{code}

Индукцију путање $=$-ind заједно са правилом израчунавања $=$-comp у језику \textsc{Agda} записујемо као:
\begin{code}
𝕁 : (X : 𝓤 ̇ ) (P : (x y : X) → x == y → 𝓥 ̇ )
  → ((x : X) → P x x (refl x))
  → ((x y : X) (p : x == y) → P x y p)
𝕁 X P f x y (refl x) = f x
\end{code}
Индукцију путање традиционално називамо и $\mathbb{J}$ правило. Поред индукције путање можемо дефинисати и базну индукцију путање, коју традиционално називамо $\mathbb{H}$ правило, и у језику \textsc{Agda} записујемо као:
\begin{code}
ℍ : {X : 𝓤 ̇ } (x : X) (P : (y : X) → x == y → 𝓥 ̇ )
  → P x (refl x) → (y : X) (p : x == y) → P y p 
ℍ x P p-refl y (refl x) = p-refl
\end{code}

У наставку текста биће описане формализације лема о особинама типова индентитета које су наведене и доказане у поглављу~\ref{sec:id}.

Лему~\ref{lmm:inv} (о инверзу) и лему~\ref{lmm:comp} (о надовизивању) у језику \textsc{Agda} формализујемо као:
\begin{code}
_⁻¹ : {X : 𝓤 ̇ } {x y : X} 
    → x == y → y == x 
(refl x) ⁻¹ = refl x

infixr 11 _·_

_·_ : {X : 𝓤 ̇ } {x y z : X} 
    → x == y → y == z → x == z
refl _ · q = q
\end{code}
Често надовезујемо и више од две путање, те тако добијамо ланац надовезаних путањи. Због тога, згодно је на сваком кораку пратити тренутни елемент ланца, као и последњи елемент ланца. То нам омогућава следећа синтакса:
\begin{code}
_==⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} 
        → x == y → y == z → x == z
x ==⟨ p ⟩ q = p · q

_∎ : {X : 𝓤 ̇ } (x : X) 
    → x == x
x ∎ = refl x
\end{code}

Резултат леме~\ref{lmm:inftygrupoid}, односно да тип идентитета на датом нивоу има својства слабог $\infty$-групоида, у језику \textsc{Agda} формализујемо као:
\begin{code}
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

assoc : {X : 𝓤 ̇ } {x y z w : X} 
        (p : x == y) (q : y == z) (r : z == w)
      → (p · q) · r == p · (q · r)
assoc (refl _) q r = refl (q · r)
\end{code}

Лему~\ref{lmm:ap}, односно акцију путање формализујемо као:
\begin{code}
ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} 
   → x == y → f x == f y 
ap f (refl x) = refl (f x)
\end{code}

Резултат леме~\ref{lmm:app}, односно особине акције путање формализујемо као:
\begin{code}
ap-id : {X : 𝓤 ̇ } {x y : X} (p : x == y) 
      → p == ap id p
ap-id (refl x) = refl (refl x)

ap-comp : {X : 𝓤 ̇ } (f g : X → X) 
          {x y z : X} (p : x == y)
        → ap g (ap f p) == ap (g ∘ f) p
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X) 
        → ap f (refl x) == refl (f x)
ap-refl f x = refl (refl (f x))

ap-inv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) 
         {x y : X} (p : x == y) 
       → ap f (p ⁻¹) == (ap f p) ⁻¹
ap-inv f (refl x) = refl (ap f (refl x))

ap-concat : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) 
            {x y z : X} (p : x == y) (q : y == z)
          → ap f (p · q) == ap f p · ap f q 
ap-concat f (refl x) q = refl (ap f q)
\end{code}

Резултат леме~\ref{lmm:tr}, односно транспорт, у језику \textsc{Agda} формализујемо као:
\begin{code}
tr : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {x y : A}
   → x == y → B x → B y
tr B (refl x) = id
\end{code}

\subsection{Природни бројеви}

Природни бројеви $0, 1, 2, \ldots$ представљају основне математичке конструкције. Тип природних бројева $\N$ у језику \textsc{Agda} је већ детаљно уведен у поглављу~\ref{sec:ex} као:
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
\end{code}

Правило рекурзије $\N$-rec дефинишемо као специјалан случај правила индукције $\N$-ind када тип $P$ не зависи од $\N$. У језику \text{Agda} то записујемо као:
\begin{code}
ℕ-recursion : (A : 𝓤 ̇ )
            → A 
            → (ℕ → A → A)
            → ℕ → A
ℕ-recursion A = ℕ-induction (λ _ → A)
\end{code}

Над типом природних бројева $\N$ можемо дефинисати разне операције, као што су сабирање, множење, степеновање и израчунавање факторијела.
\begin{code}
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
\end{code}

Ове операције имају одређена својства која можемо доказати. На пример, за природне бројеве и операцију сабирања природно је да важи $\zeroN +_\N n =_\N n$, као и $n +_\N \zeroN =_\N n$. Већ је дискутовано зашто је овде неопходно користити исказну једнакост (за детаље видети поглавље~\ref{sec:id}). У наставку су приказана нека својства природних бројева и операције сабирања, као и њихове конструкције:
\begin{code}
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
right-succ-law-+ℕ 0 n = refl (succ n)
right-succ-law-+ℕ (succ m) n = ap succ (right-succ-law-+ℕ m n)

associative-+ℕ : (m n k : ℕ) → (m +ℕ n) +ℕ k == m +ℕ (n +ℕ k) 
associative-+ℕ 0 n k = refl (n +ℕ k)
associative-+ℕ (succ m) n k = ap succ (associative-+ℕ m n k)

commutative-+ℕ : (m n : ℕ) → m +ℕ n == n +ℕ m 
commutative-+ℕ 0 n = right-zero-law-+ℕ n ⁻¹
commutative-+ℕ (succ m) n = (succ (m +ℕ n))  ==⟨ 
                                ap succ (commutative-+ℕ m n) 
                            ⟩ ((succ (n +ℕ m)) ==⟨ 
                                right-succ-law-+ℕ n m ⁻¹ 
                            ⟩ ((n +ℕ succ m)   ∎))
\end{code}
Приметимо да се за конструисање доказа ових својстава користе особине путање. Прецизније, често користимо акције над путањама, инверз путање, као и надовезивање путања. Поред тога, приметимо и да у доказу о комутативности, користимо синтаксу за ланац путања. 

Простор кодова над типом природних бројева, односно дефиницију~\ref{def:code}, у језику \textsc{Agda} записујемо као:
\begin{code}
code-ℕ : ℕ → ℕ → 𝓤₀ ̇
code-ℕ 0 0 = 𝟙
code-ℕ 0 (succ n) = 𝟘 
code-ℕ (succ m) 0 = 𝟘 
code-ℕ (succ m) (succ n) = code-ℕ m n
\end{code}

Простор кодова је рефлексивна релација. Односно, резултат леме~\ref{lmm:reflcode} у језику \textsc{Agda} формализујемо као:
\begin{code}
relf-code-ℕ : (n : ℕ) → code-ℕ n n 
relf-code-ℕ 0        = ⋆ 
relf-code-ℕ (succ n) = relf-code-ℕ n
\end{code}

Резултат леме~\ref{lmm:encdec}, постојање функција које трансформишу једнакост у код, као и код у једнакост, у језику \textsc{Agda} формализујемо као: 
\begin{code}
encode-ℕ : {m n : ℕ} → m == n → code-ℕ m n 
encode-ℕ {m} {n} p = tr (code-ℕ m) p (relf-code-ℕ m)

decode-ℕ : (m n : ℕ) → code-ℕ m n → m == n
decode-ℕ 0 0 code = refl 0
decode-ℕ (succ m) (succ n) code = ap succ (decode-ℕ m n code)
\end{code}

На основу претходне две функције можемо показати Пеанову седму и осму аксиому. Пеанова седма аксиома тврди да уколико су одређене инстанце целих бројева једнаке, тада ће бити једнаки и њихови следбеници, као и да важи обрнуто. Док Пеанова осма аксиома тврди да нула никада није следбеник неког природног броја. У језику \textsc{Agda} то записујемо као: 
\begin{code}
injective-succ-ℕ : (m n : ℕ) → succ m == succ n → m == n
injective-succ-ℕ m n e = decode-ℕ m n (encode-ℕ e)

peano-7-axiom : (n m : ℕ) → (m == n) ↔ (succ m == succ n)
peano-7-axiom n m = ap succ , injective-succ-ℕ m n

peano-8-axiom : (n : ℕ) → ¬ (0 == succ n)
peano-8-axiom n = encode-ℕ
\end{code}

По узору на дефиницију~\ref{def:code} (простор кодова над природним бројевима), можемо дефинисати релацију поретка $\leq_\N$ над природним бројевима као:
\begin{code}
_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇ 
0 ≤ℕ n = 𝟙 
succ m ≤ℕ 0 = 𝟘 
succ m ≤ℕ succ n = m ≤ℕ n
\end{code}

\subsection{Булов тип}

Булов тип $\2$ је специјалан случај типа копроизвода $A + B$ када су и $A$ и $B$ јединични типови, тј. $\2 :\equiv \1 + \1$. Као такав, њега настањују једино $\inl(\star)$ и $\inr(\star)$, које другачије називамо $\true$ и $\false$. У језику \textsc{Agda}, Булов тип $\2$ уводимо на следећи начин: 
\begin{code}
𝟚 : 𝓤₀ ̇ 
𝟚 = 𝟙 + 𝟙

pattern true  = inl ⋆
pattern false = inr ⋆
\end{code}

Правило индукције $\2$-ind заједно са правилом израчунавања $\2$-comp, у језику \textsc{Agda} записујемо као:
\begin{code}
𝟚-induction : (P : 𝟚 → 𝓤 ̇ ) 
            → (P true)
            → (P false)
            → (b : 𝟚) → (P b)
𝟚-induction P p₀ p₁ true  = p₀
𝟚-induction P p₀ p₁ false = p₁
\end{code}

\newpage%
Уколико у правилу индукције $\2$-ind заменимо одговарајуће аргументе добијамо конструкцију коју називамо \emph{if-then-else}:   
\begin{code}
if_then_else : {P : 𝟚 → 𝓤 ̇ }
             → (b : 𝟚)
             → (P true)
             → (P false)
             → (P b)
if true  then x else y = x
if false then x else y = y
\end{code}