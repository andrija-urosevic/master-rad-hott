theory Ex01
    imports Main

begin

value "2 + (2::nat)"
value "(2::nat) * (5 + 3)"
value "(3::nat) * 4 - 2 * (7 - 1)"

lemma "(x::nat) + y = y + x"
  by auto

lemma "((x::nat) + y) + z = x + (y + z)"
  by auto

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] a = 0"
| "count (x # xs) a = (if x = a then 1 + count xs a else count xs a)"

value "count [] (0::nat)"
value "count [1, 1, 2, 2] (2::nat)"
value "count [1, 1, 1, 1] (2::nat)"

theorem "count xs a \<le> length xs"
  by (induction xs) auto

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = [a]"
| "snoc (x # xs) a = x # snoc xs a"

value "snoc [] c"

lemma "snoc [] c = [c]"
  by auto

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"

value "reverse [a, b, c]"

lemma "reverse [a, b, c] = [c, b, a]"
  by auto

lemma [simp]: "reverse (snoc xs x) = x # reverse xs"
  by (induction xs) auto

theorem "reverse (reverse xs) = xs"
  by (induction xs) auto

fun fold_right :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold_right f [] a = a"
| "fold_right f (x # xs) a = f x (fold_right f xs a)"

value "fold_right (+) [1::nat, 2, 3, 4] 0"
value "fold_right (#) [a, b, c] []"

lemma "fold_right f (map g xs) a = fold_right (f \<circ> g) xs a"
  by (induction xs) auto

theorem fold_plus_append: 
  "fold_right (+) (xs @ ys) (0::nat) = fold_right (+) xs 0 + fold_right (+) ys 0"
  by (induction xs arbitrary: ys) auto

lemma fold_snoc[simp]: "fold_right f (snoc xs x) a = fold_right f xs (f x a)"
  by (induction xs) auto

lemma [simp]: "fold_right (+) xs (x + a) = x + fold_right (+) xs (a::nat)"
  by (induction xs) (auto simp add: algebra_simps)
    
theorem fold_reverse: "fold_right (+) (reverse xs) (x::nat) = fold_right (+) xs x"
  by (induction xs) auto

end