theory ex01
  imports Main

begin

text \<open>In classical propositional logic, the connectives @{text "=, \<or>,
\<not>"} can be replaced by @{text "\<longrightarrow>, \<and>, False"}.  Define
corresponding simplification rules as lemmas and prove their correctness.  (You
may use automated proof tactics.)\<close>

lemma eq_elim: "(A = B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))"
  by auto

lemma or_elim: "(A \<or> B) = (\<not> (\<not> A \<and> \<not> B))"
  by auto

lemma not_elim: "(\<not> A) = (A \<longrightarrow> False)"
  by auto

text \<open>What is the result of your translation for the formula @{text "A \<or>
(B \<and> C) = A"}?  (You can use Isabelle's simplifier to compute the result
by using the simplifier's @{text "only"} option.)\<close>

lemma "A \<or> (B \<and> C) = A"
  apply (simp only: eq_elim or_elim not_elim)
  sorry

end