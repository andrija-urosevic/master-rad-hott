theory ex02
  imports Main

begin

text\<open>Define a function @{term replace}, such that @{term"replace x y zs"}
yields @{term zs} with every occurrence of @{term x} replaced by @{term y}.\<close>

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace x y [] = []"
| "replace x y (z # zs) = (if z = x then y # replace x y zs else z # replace x y zs)"

text\<open>Prove or disprove (by counterexample) the following theorems.
You may have to prove some lemmas first.\<close>
lemma replace_append: "replace x y (xs @ ys) = replace x y xs @ replace x y ys"
  by (induction xs) auto

theorem "rev (replace x y zs) = replace x y (rev zs)"
  by (induction zs) (auto simp add: replace_append)

theorem "replace x y (replace u v zs) = replace u v (replace x y zs)"
  oops

theorem "replace y z (replace x y zs) = replace x z zs"
  oops

text\<open>Define two functions for removing elements from a list:
@{term"del1 x xs"} deletes the first occurrence (from the left) of
@{term x} in @{term xs}, @{term"delall x xs"} all of them.\<close>
primrec del1   :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "del1 a [] = []"
| "del1 a (x # xs) = (if a = x then xs else x # del1 a xs)"

primrec delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "delall a [] = []"
| "delall a (x # xs) = (if a = x then delall a xs else x # delall a xs)"

text\<open>Prove or disprove (by counterexample) the following theorems.\<close>

theorem del1_delall: "del1 x (delall x xs) = delall x xs"
  by (induction xs) auto

theorem "delall x (delall x xs) = delall x xs"
  by (induction xs) auto

theorem "delall x (del1 x xs) = delall x xs"
  by (induction xs) auto

theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
  by (induction zs) auto

theorem "delall x (del1 y zs) = del1 y (delall x zs)"
  by (induction zs) (auto simp add: del1_delall)

theorem "delall x (delall y zs) = delall y (delall x zs)"
  by (induction zs) auto

theorem "del1 y (replace x y xs) = del1 x xs"
  oops

theorem "delall y (replace x y xs) = delall x xs"
  oops

theorem "replace x y (delall x zs) = delall x zs"
  by (induction zs) auto

theorem "replace x y (delall z zs) = delall z (replace x y zs)"
  oops

theorem "rev (del1 x xs) = del1 x (rev xs)"
  oops

lemma delall_append:
  shows "delall a (xs @ ys) = delall a xs @ delall a ys"
  by (induction xs) auto

theorem "rev (delall x xs) = delall x (rev xs)"
  by (induction xs) (auto simp add: delall_append)

end