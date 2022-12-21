theory ex05
imports Main

begin 

text \<open>Let the following data type for propositional formulae be given:\<close>

datatype form = T | Var nat | And form form | Xor form form

text \<open>
Here @{term "T"} denotes a formula that is always true, @{term "Var n"} denotes
a propositional variable, its name given by a natural number, @{term "And f1
f2"} denotes the AND combination, and @{term "Xor f1 f2"} the XOR (exclusive or)
combination of two formulae.  A constructor @{term "F"} for a formula that is
always false is not necessary, since @{term "F"} can be expressed by @{term "Xor
T T"}.

{\bf Exercise 1:} Define a function
@{term "evalf :: (nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"}
that evaluates a formula under a given variable assignment.
\<close>

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where
    "xor x y \<equiv> (x \<and> \<not>y) \<or> (\<not> x \<and> y)"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"
  where
    "evalf v T = True"
  | "evalf v (Var n) = v n"
  | "evalf v (And fl fr) = (evalf v fl \<and> evalf v fr)"
  | "evalf v (Xor fl fr) = xor (evalf v fl) (evalf v fr)"

text \<open>
Propositional formulae can be represented by so-called {\it polynomials}.  A
polynomial is a list of lists of propositional variables, i.e.\ an element of
type @{typ "nat list list"}.  The inner lists (the so-called {\it monomials})
are interpreted as conjunctive combination of variables, whereas the outer list
is interpreted as exclusive-or combination of the inner lists.

{\bf Exercise 2:} Define two functions

@{term "evalm :: (nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool"}
@{term "evalp :: (nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool"}

for evaluation of monomials and polynomials under a given variable assignment.
In particular think about how empty lists have to be evaluated.
\<close>

primrec evalm :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "evalm v [] = True"
  | "evalm v (x#xs) = (v x \<and> evalm v xs)"

primrec evalp :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool"
  where
    "evalp v [] = False"
  | "evalp v (x#xs) = xor (evalm v x) (evalp v xs)"

text \<open>
{\bf Exercise 3:} Define a function

@{term "poly :: form \<Rightarrow> nat list list"}

that turns a formula into a polynomial.  You will need an auxiliary function

@{term "mulpp :: nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list"}

to ``multiply'' two polynomials, i.e.\ to compute
\[
((v^1_1 \mathbin{\odot} \cdots \mathbin{\odot} v^1_{m_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (v^k_1 \mathbin{\odot} \cdots \mathbin{\odot} v^k_{m_k})) \mathbin{\odot}
((w^1_1 \mathbin{\odot} \cdots \mathbin{\odot} w^1_{n_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (w^l_1 \mathbin{\odot} \cdots \mathbin{\odot} w^l_{n_l}))
\]
where $\mathbin{\oplus}$ denotes ``exclusive or'', and $\mathbin{\odot}$ denotes
``and''.  This is done using the usual calculation rules for addition and
multiplication.
\<close>

primrec mulpp :: "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list"
  where
    "mulpp [] qs = []"
  | "mulpp (m # ps) qs = map (\<lambda> x. m @ x) qs @ (mulpp ps qs)"

primrec poly :: "form \<Rightarrow> nat list list"
  where
    "poly T = [[]]"
  | "poly (Var n) = [[n]]"
  | "poly (Xor fl fr) = poly fl @ poly fr"
  | "poly (And fl fr) = mulpp (poly fl) (poly fr)"

text \<open>
{\bf Exercise 4:} Now show correctness of your function @{term "poly"}:
@{term "evalf e f = evalp e (poly f)"}
It is useful to prove a similar correctness theorem for @{term "mulpp"} first.
\<close>

value "poly (And T T)"

lemma evalp_append: "evalp v (p @ q) = (xor (evalp v p) (evalp v q))"
  by (induction p) (auto simp add: xor_def)

lemma evalm_append: "evalm v (xs @ ys) = (evalm v xs \<and> evalm v ys)"
  by (induction xs) (auto simp add: xor_def)

lemma mulmp_correct: "evalp v (map (\<lambda>x. m @ x) q) = (evalm v m \<and> evalp v q)"
  by (induction q) (auto simp add: xor_def evalm_append)

lemma mulpp_correct: "evalp v (mulpp p q) = (evalp v p \<and> evalp v q)"
  by (induction p) (auto simp add: xor_def mulmp_correct evalp_append)

theorem poly_correct: "evalf v f = evalp v (poly f)"
  by (induction f) (auto simp add: xor_def mulpp_correct evalp_append)

end