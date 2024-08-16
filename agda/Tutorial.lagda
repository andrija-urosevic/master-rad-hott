\textsc{Agda} програми се развијају интерактивно, што значи да је могуће верификовати ограничења типовa (енгл. \emph{type check}) иако код није комплетно написан. Код може садржати празнине које се могу допунити касније. Многи текстуални едитори подржавају интерактивни развој \textsc{Agda} програма: \textsc{Emacs}, \textsc{Vim}, \textsc{Atom}, \textsc{Visual Studio Code}.

Када се интерактивно развија \textsc{Agda} програм користе се команде које пружају информације од проверивача типова (енгл. \emph{typechecker}) (програма који извршава верификацију ограничења типова), као и начине на које можемо обрађивати празнине. Неке од корисних комадна су:

\begin{itemize}
    \item[\texttt{C-c C-l}:]{Учитава фајл и извршава верификацију ограничења типова. Свако појављивање знак \texttt{?} замењује са новом празнином.}
    \item[\texttt{C-c C-d}:]{Одређује тип датог израза.}
    \item[\texttt{C-c C-n}:]{Нормализује дати израз.}
    \item[\texttt{C-c C-f}:]{Поставља курсор на прву следећу празнину.}
    \item[\texttt{C-c C-b}:]{Поставља курсор на прву претходну празнину.}
    \item[\texttt{C-c C-,}:]{Приказује очекивани тип празнине на којој се налази курсор, као и типове свих променљивих из контекста.}
    \item[\texttt{C-c C-c}:]{Раздваја променљиву на све могуће случајеве.}
    \item[\texttt{C-c C-SPC}:]{Замењује празнину датим изразом, ако је дати израз одговарајућег типа.}
    \item[\texttt{C-c C-r}:]{Прерађује празнину тако што је замени са изразом заједно са новим одговарајућим празнинама.}
    \item[\texttt{C-c C-a}:]{Аутоматски покушава да пронађе одговарајући израз за празнину на којој се налази курсор.}
    \item[\texttt{C-x C-c}:]{Преводи програм.}
\end{itemize}

Прођимо кроз један основни пример. Како се име сваког \textsc{Agda} фајла завршава екстензијом \texttt{.agda}, нека се наш фајл зове \texttt{Tutorial.agda}.

На почетку фајла описујемо неке мета-податке:
\begin{code}
{-# OPTIONS --without-K --safe #-}
\end{code}
У овом случају то су опције \texttt{--without-K} и \texttt{--safe}, које обезбеђују сигурну аксиоматизацију унивалентности. Без ових опција дошло би до контрадикције.

\textsc{Agda} програм је стачињен од \emph{модула}. Сваки модул има своје име (које мора да се поклопи са именом фајла) као и низ декларација. Модул за наш фајл \texttt{Tutorial.agda} започињемо на следећи начин:
\begin{code}
module Tutorial where
\end{code}

Једна врста декларација је увожење других модула. Тако, на пример, можемо увести модул \texttt{Universes} на следећи начин: 
\begin{code}
open import Universes public
\end{code}

Друга врста декларација је декларисање променљивих. На пример, можемо рећи да $\mathcal{U}$, $\mathcal{V}$ и $\mathcal{W}$ представљају универзум:
\begin{code}
variable 𝓤 𝓥 𝓦 : Universe 
\end{code}

Једна од кључних декларација је декларација индуктивних типова. Декларисање индуктивних типова подразумева навођење имена тог типа, начин на који се он формира, као и начин за конструисања каноничних елемената тог типа. У теорији типова, то смо називали правило формирања типова и правила конструисања. Подсетимо се правила формирања и правила конструисања типа природних бројева $\N$. Тип природних бројева $\N$ може да се формира из празног контекста, односно $\N : \mathcal{U}_0$, као и да су му једини конструктори $\zeroN : \N$ и $\succN : \N \to \N$. У језику \textsc{Agda} то записујемо као: 
\begin{code}
data ℕ : 𝓤₀ ̇ where
    zero : ℕ
    succ : ℕ → ℕ
    
{-# BUILTIN NATURAL ℕ #-}
\end{code}

Поред правила формирања и правила конструисања, за комплетну спецификацију индуктивних типова имали смо и правило индукције и правило израчунавања. Правило индукције типа природних бројева $\N$, у језику \textsc{Agda} записујемо као:
\begin{code} 
ℕ-induction : (P : ℕ → 𝓤₀ ̇ )
            → P 0
            → ((n : ℕ) → P n → P (succ n))
            → (n : ℕ) → P n

\end{code}
Са друге стране, правила израчунавања записујемо као:
\begin{code}
ℕ-induction P p₀ pₛ zero     = p₀
ℕ-induction P p₀ pₛ (succ n) = pₛ n (ℕ-induction P p₀ pₛ n)
\end{code}

У многим случајевима \textsc{Agda} може помоћи при декларисању правила израчунавања. Како она описују начин конструисања елемента који оправдава правило индукције можемо поћи од:
\begin{code}
ℕ-induction P p₀ pₛ n = {!   !}
\end{code}
Командом \texttt{C-c C-c} раздвајамо \texttt{n} на случајеве:
\begin{code}
ℕ-induction P p₀ pₛ zero     = {!   !}
ℕ-induction P p₀ pₛ (succ n) = {!   !}
\end{code}
Командом \texttt{C-c C-а} аутоматски решавамо први случај, док на други примењујемо \texttt{C-c C-r} над изразом $p_s$:
\begin{code}
ℕ-induction P p₀ pₛ zero     = p₀
ℕ-induction P p₀ pₛ (succ n) = pₛ {!   !} {!   !}
\end{code}
На првом пољу, командом \texttt{C-c C-,}, сазнајемо да је потребно конструисати тип $\N$, као и да је у контексту $n : \N$. Због тога, једноставно, попуњавамо поље са $n$ командом \texttt{C-c C-SPC}. На другом пољу, командом \texttt{C-c C-,}, сазнајемо да је потребно конструисати тип $P(n)$ за $n : \N$. Приметимо да је \AgdaFunction{ℕ-induction} функција која враћа $P(n)$, те примењујемо команду \texttt{C-c C-r} над \AgdaFunction{ℕ-induction} $P$.
\begin{code}
ℕ-induction P p₀ pₛ zero     = p₀
ℕ-induction P p₀ pₛ (succ n) = pₛ n (ℕ-induction P {!   !} {!   !} {!   !})
\end{code}
Преостала поља можемо једноставно попунити аутоматски помоћу команде \texttt{C-c C-a}, или разматрањем траженог типа и контекста помоћу команде \texttt{C-c C-,}, а онда уписивањем одговарајућих израза помоћу команде \texttt{C-c C-SPC}.
