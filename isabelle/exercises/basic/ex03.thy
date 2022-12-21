theory ex03
  imports Main

begin 

text \<open>Define a universal and an existential quantifier on lists
using primitive recursion.  Expression @{term "alls P xs"} should
be true iff @{term "P x"} holds for every element @{term x} of
@{term xs}, and @{term "exs P xs"} should be true iff @{term "P x"}
holds for some element @{term x} of @{term xs}.\<close>

primrec alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "alls P [] = True"
| "alls P (x # xs) = (if P x then alls P xs else False)"

primrec exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "exs P [] = False"
| "exs P (x # xs) = (if P x then True else exs P xs)"

text \<open>Prove or disprove (by counterexample) the following theorems.
You may have to prove some lemmas first.

Use the @{text "[simp]"}-attribute only if the equation is truly a
simplification and is necessary for some later proof.
\<close>

lemma "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
  by (induction xs) auto

lemma alls_append[simp]: "alls P (xs @ ys) = (alls P xs \<and> alls P ys)"
  by (induction xs) auto

lemma "alls P (rev xs) = alls P xs"
  by (induction xs) auto

lemma "exs (\<lambda>x. P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
  oops

lemma "exs P (map f xs) = exs (P \<circ> f) xs"
  by (induction xs) auto

lemma exs_append[simp]: "exs P (xs @ ys) = (exs P xs \<or> exs P ys)"
  by (induction xs) auto

lemma "exs P (rev xs) = exs P xs"
  by (induction xs) auto


text \<open>Find a (non-trivial) term @{text Z} such that the following equation holds: \<close>

lemma "exs (\<lambda>x. P x \<or> Q x) xs = Z"
  oops

lemma "exs (\<lambda>x. P x \<or> Q x) xs = (exs P xs \<or> exs Q xs)"
  by (induction xs) auto

text \<open>Express the existential via the universal quantifier --
@{text exs} should not occur on the right-hand side:\<close>

lemma "exs P xs = Z"
  oops

lemma "exs P xs = (\<not>(alls (\<lambda>x. \<not>(P x)) xs))"
  by (induction xs) auto

text \<open>Define a primitive-recursive function @{term "is_in x xs"} that
checks if @{term x} occurs in @{term xs}. Now express @{text is_in} via @{term exs}:\<close>

primrec is_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_in a [] = False"
| "is_in a (x # xs) = (if a = x then True else is_in a xs)"

lemma "is_in a xs = exs (\<lambda>x. x = a) xs"
  by (induction xs) auto

text \<open>Define a primitive-recursive function @{term "nodups xs"}
that is true iff @{term xs} does not contain duplicates, and a
function @{term "deldups xs"} that removes all duplicates.  Note
that @{term "deldups[x,y,x]"} (where @{term x} and @{term y} are
distinct) can be either @{term "[x,y]"} or @{term "[y,x]"}.

Prove or disprove (by counterexample) the following theorems.
\<close>

primrec nodups :: "'a list \<Rightarrow> bool" where
  "nodups [] = True"
| "nodups (x # xs) = (\<not> is_in x xs \<and> nodups xs)"

primrec deldups :: "'a list \<Rightarrow> 'a list" where
  "deldups [] = []"
| "deldups (x # xs) = (if is_in x xs then deldups xs else x # deldups xs)"

lemma "length (deldups xs) <= length xs"
  by (induction xs) auto

lemma is_in_deldups: "is_in a (deldups xs) = is_in a xs"
  by (induction xs) auto

lemma "nodups (deldups xs)"
  by (induction xs) (auto simp add: is_in_deldups)

lemma "deldups (rev xs) = rev (deldups xs)"
  oops

end