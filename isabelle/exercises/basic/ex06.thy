theory ex06
  imports Main

begin

text \<open>Define a function @{text sum}, which computes the sum of
elements of a list of natural numbers.\<close>

primrec sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

text \<open>Then, define a function @{text flatten} which flattens a list
of lists by appending the member lists.\<close>

primrec flatten :: "'a list list \<Rightarrow> 'a list" where
  "flatten [] = []"
| "flatten (x # xs) = x @ flatten xs"

text \<open>Test your functions by applying them to the following example lists:\<close>

lemma "sum [2::nat, 4, 8] = 14"
  by auto

lemma "flatten [[2::nat, 3], [4, 5], [7, 9]] = [2, 3, 4, 5, 7, 9]"
  by auto

text \<open>Prove the following statements, or give a counterexample:\<close>

lemma "length (flatten xs) = sum (map length xs)"
  by (induction xs) auto

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
  by (induction xs) auto

lemma flatten_append: "flatten (xs @ ys) = flatten xs @ flatten ys"
  by (induction xs) auto

lemma "flatten (map rev (rev xs)) = rev (flatten xs)"
  by (induction xs) (auto simp add: flatten_append)

lemma "flatten (rev (map rev xs)) = rev (flatten xs)"
  by (induction xs) (auto simp add: flatten_append)

lemma "list_all (list_all P) xs = list_all P (flatten xs)"
  by (induction xs) auto

lemma "flatten (rev xs) = flatten xs"
  oops

lemma "sum (rev xs) = sum xs"
  by (induction xs) (auto simp add: sum_append)

text \<open>Find a (non-trivial) predicate @{text P} which satisfies\<close>

lemma "list_all (\<lambda> x. x \<ge> 1) xs \<longrightarrow> length xs \<le> sum xs"
  by (induction xs) auto

text \<open>Define, by means of primitive recursion, a function @{text
list_exists} which checks whether an element satisfying a given property
is contained in the list:\<close>

primrec list_exists :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)" where
  "list_exists P [] = False"
| "list_exists P (x # xs) = (P x \<or> list_exists P xs)"

text \<open>Test your function on the following examples:\<close>

lemma "list_exists (\<lambda> n. n < 3) [4::nat, 3, 7] = False"
  by auto

lemma "list_exists (\<lambda> n. n < 4) [4::nat, 3, 7] = True"
  by auto

text \<open>Prove the following statements:\<close>

lemma list_exists_append: 
  "list_exists P (xs @ ys) = (list_exists P xs \<or> list_exists P ys)"
  by (induction xs) auto

lemma "list_exists (list_exists P) xs = list_exists P (flatten xs)"
  by (induction xs) (auto simp add: list_exists_append)

text \<open>You could have defined @{text list_exists} only with the aid of
@{text list_all}.  Do this now, i.e. define a function @{text
list_exists2} and show that it is equivalent to @{text list_exists}.\<close>

definition list_exists2 :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)" where
  "list_exists2 P xs = (\<not> list_all (\<lambda>x. \<not> P x) xs)"

lemma "list_exists P xs = list_exists2 P xs"
  by (induction xs) (auto simp add: list_exists2_def)

end