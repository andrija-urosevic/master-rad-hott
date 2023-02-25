theory Ex04
  imports "HOL-Library.Tree"
begin

declare Let_def[simp]

fun in_range :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list"  where
  "in_range Leaf _ _ = []"
| "in_range (Node l a r) u v = (if a < u then [] else in_range l u v) 
                             @ (if u \<le> a \<and> a \<le> v then [a] else []) 
                             @ (if v < a then [] else in_range r u v)"

thm in_range.induct

lemma "bst t \<Longrightarrow> set (in_range t u v) = {x \<in> set_tree t. u \<le> x \<and> x \<le> v}"
  by (induction t) auto

thm filter_empty_conv
thm filter_empty_conv[symmetric]

lemma filter_empty_commutative: "[] = filter P xs \<longleftrightarrow> filter P xs = []"
  by auto

lemma "bst t \<Longrightarrow> in_range t u v = filter (\<lambda> x. u \<le> x \<and> x \<le> v) (inorder t)"
  by (induction t) (auto simp add: filter_empty_conv filter_empty_commutative)

theorem 
  assumes "x \<ge> (1 :: nat)"
  shows "(x + x^2)^2 \<le> 4 * x^4"
proof -
  have "x \<le> x^2" using assms by (simp add: self_le_power)
  then have 1: "(x + x^2)^2 \<le> (x^2 + x^2)^2" by simp
  have 2: "(x^2 + x^2)^2 = 4 * x^4" by algebra
  from 1 2 show "(x + x\<^sup>2)\<^sup>2 \<le> 4 * x ^ 4" by auto
qed


fun enum :: "nat \<Rightarrow> unit tree set" where
  "enum 0 = {Leaf}"
| "enum (Suc n) = (let ns = enum n in
                  ns \<union> {Node l () r | l r. l \<in> ns \<and> r \<in> ns})"

lemma enum_sound: "t \<in> enum n \<Longrightarrow> height t \<le> n"
  by (induction n arbitrary: t) (auto simp add: le_SucI)

lemma enum_complete: "height t \<le> n \<Longrightarrow> t \<in> enum n"
  apply (induction n arbitrary: t)
   apply auto
  apply (case_tac t)
   apply auto
  done

lemma enum_correct: "enum h = {t. height t \<le> h}"
  by (auto simp: enum_complete enum_sound)

end