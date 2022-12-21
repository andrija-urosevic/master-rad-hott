theory ex03
  imports Main

begin

text \<open>We are again talking about proofs in the calculus of Natural Deduction.  In
addition to the rules given in the exercise ``Propositional Logic'', you may
now also use

  @{text "exI:"}~@{thm exI[no_vars]}\\
  @{text "exE:"}~@{thm exE[no_vars]}\\
  @{text "allI:"}~@{thm allI[no_vars]}\\
  @{text "allE:"}~@{thm allE[no_vars]}\\

Give a proof of the following propositions or an argument why the formula is
not valid:
\<close>

lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
  apply (rule impI)
  apply (rule allI)
  apply (erule exE)
  apply (rule_tac x=\<open>x\<close> in exI)
  apply (erule_tac x=\<open>y\<close> in allE)
  apply auto
  done

lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
  apply (rule iffI)
   apply (rule impI)
   apply (erule exE)
   apply (erule_tac x=\<open>x\<close> in allE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   apply (rule_tac x=\<open>x\<close> in exI)
   apply assumption
  apply assumption
  done

lemma "((\<forall> x. P x) \<and> (\<forall> x. Q x)) = (\<forall> x. (P x \<and> Q x))"
  apply (rule iffI)
   apply (erule conjE)
   apply (rule allI)
   apply (erule_tac x=\<open>x\<close> in allE)
   apply (erule_tac x=\<open>x\<close> in allE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule conjI)
   apply (rule allI)
   apply (erule_tac x=\<open>x\<close> in allE)
   apply (erule conjE)
   apply assumption
  apply (rule allI)
  apply (erule_tac x=\<open>x\<close> in allE)
  apply (erule conjE)
  apply assumption
  done

lemma "((\<forall> x. P x) \<or> (\<forall> x. Q x)) = (\<forall> x. (P x \<or> Q x))"
  oops

lemma "((\<exists> x. P x) \<or> (\<exists> x. Q x)) = (\<exists> x. (P x \<or> Q x))"
  apply (rule iffI)
   apply (erule disjE)
    apply (erule exE)
    apply (rule_tac x=\<open>x\<close> in exI)
    apply (rule disjI1)
    apply assumption
   apply (erule exE)
   apply (rule_tac x=\<open>x\<close> in exI)
   apply (rule disjI2)
   apply assumption
  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule_tac x=\<open>x\<close> in exI)
   apply assumption
  apply (rule disjI2)
  apply (rule_tac x=\<open>x\<close> in exI)
  apply assumption
  done

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
  oops

lemma "(\<not> (\<forall> x. P x)) = (\<exists> x. \<not> P x)"
  apply (rule iffI)
   apply (rule classical)
   apply (erule notE)
   apply (rule allI)
   apply (rule classical)
   apply (erule notE)
   apply (rule_tac x=\<open>x\<close> in exI)
   apply assumption
  apply (erule exE)
  apply (rule notI)
  apply (erule_tac x=\<open>x\<close> in allE)
  apply (erule notE)
  apply assumption
  done

end