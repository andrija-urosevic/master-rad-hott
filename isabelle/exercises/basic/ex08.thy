theory ex08
  imports Main

begin

text \<open>
\begin{description}
\item[\bf (a)] Define a primitive recursive function @{term ListSum} that
computes the sum of all elements of a list of natural numbers.

Prove the following equations.  Note that @{term  "[0..n]"} and @{term
"replicate n a"} are already defined in a theory {\tt List.thy}.
\end{description}
\<close>

primrec ListSum :: "nat list \<Rightarrow> nat" where
  "ListSum [] = 0"
| "ListSum (x # xs) = x + ListSum xs"

lemma ListSum_append: "ListSum (xs @ ys) = ListSum xs + ListSum ys"
  by (induction xs) auto

theorem "2 * ListSum [0..<n+1] = n * (n + 1)"
  by (induction n) (auto simp add: ListSum_append)

theorem "ListSum (replicate n a) = n * a"
  by (induction n) auto

text \<open> 
\begin{description}
\item[\bf (b)] Define an equivalent function @{term ListSumT} using a
tail-recursive function @{term ListSumTAux}.  Prove that @{term ListSum}
and @{term ListSumT} are in fact equivalent.
\end{description}
\<close>

primrec ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "ListSumTAux [] acc = acc"
| "ListSumTAux (x # xs) acc = ListSumTAux xs (x + acc)"

definition ListSumT :: "nat list \<Rightarrow> nat" where
  "ListSumT xs = ListSumTAux xs 0"

lemma ListSumTAux_acc [rule_format]: "\<forall>x y. ListSumTAux xs (x + y) = x + ListSumTAux xs y"
  by (induction xs) auto

theorem "ListSum xs = ListSumT xs"
  using ListSumT_def
  by (induction xs) (auto simp add: ListSumTAux_acc[THEN sym])

end