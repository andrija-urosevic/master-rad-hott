theory ex04
  imports Main

begin

text \<open>
  First prove the following formula, which is valid in classical predicate
  logic, informally with pen and paper.  Use case distinctions and/or proof by
  contradiction.

  {\it  If every poor man has a rich father,\\
   then there is a rich man who has a rich grandfather.}
\<close>

theorem
  "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow>
  \<exists>x. rich (father (father x)) \<and> rich x"
  apply (rule classical)
  apply (rule exI)
  apply (rule conjI)  
   apply (rule classical)
   apply (rule allE)
    apply assumption
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply (rule exI)
   apply (rule conjI) 
    apply assumption
   apply (rule classical)
   apply (erule allE)
   apply (erule notE)
   apply (erule impE) 
    apply assumption
   apply assumption
  apply (rule classical)
  apply (rule allE) 
   apply assumption
  apply (erule impE) 
   apply assumption
  apply (erule notE)
  apply (rule exI)
  apply (rule conjI) 
   apply assumption
  apply (rule classical)
  apply (erule allE)
  apply (erule notE)
  apply (erule impE) 
   apply assumption
  apply assumption
  done

text \<open>
  Now prove the formula in Isabelle using a sequence of rule applications (i.e.\
  only using the methods @{term rule}, @{term erule} and @{term assumption}).
\<close>

end