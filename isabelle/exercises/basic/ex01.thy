theory ex01
  imports Main

begin

text\<open>Define a primitive recursive function @{text snoc} that appends an element 
at the \emph{right} end of a list. Do not use @{text"@"} itself.\<close>

primrec snoc :: "'a list => 'a => 'a list" where
  "snoc [] a = [a]"
| "snoc (x # xs) a = x # snoc xs a"

lemma snoc_append: "snoc xs x = xs @ [x]"
  by (induction xs) auto

text\<open>Prove the following theorem:\<close>
theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
  by (induction xs) (auto simp: snoc_append)

text\<open>Hint: you need to prove a suitable lemma first.\<close>

end