theory ex07
  imports Main

begin

text \<open>Finite sets can obviously be implemented by lists.  In the
following, you will be asked to implement the set operations union,
intersection and difference and to show that these implementations are
correct.  Thus, for a function \<close>

primrec list_union :: "['a list, 'a list] \<Rightarrow> 'a list" where
  "list_union xs [] = xs"
| "list_union xs (y # ys) = (if y \<in> set xs then list_union xs ys else y # list_union xs ys)"

text \<open>to be defined by you it has to be shown that\<close>

lemma set_list_union: "set (list_union xs ys) = set xs \<union> set ys"
  by (induction ys) auto

text \<open>In addition, the functions should be space efficient in the
sense that one obtains lists without duplicates (@{text "distinct"})
whenever the parameters of the functions are duplicate-free.  Thus, for
example,\<close>

lemma [rule_format]: 
  "distinct xs \<longrightarrow> distinct ys \<longrightarrow> (distinct (list_union xs ys))"
  by (induction ys) (auto simp add: set_list_union)

text \<open>\emph{Hint:} @{text "distinct"} is defined in @{text List.thy}.\<close>

subsubsection \<open>Quantification over Sets\<close>

text \<open>Define a (non-trivial) set @{text S} such that the following proposition holds:\<close>

lemma "((\<forall> x \<in> A. P x) \<and> (\<forall> x \<in> B. P x)) \<longrightarrow> (\<forall> x \<in> A \<union> B. P x)"
  by auto

text \<open>Define a (non-trivial) predicate @{text P} such that\<close>

lemma "\<forall> x \<in> A. Q (f x) \<Longrightarrow>  \<forall> y \<in> f ` A. Q y"
  by auto

end