theory Hw05
  imports Complex_Main "HOL-Library.Tree"

begin

section \<open>Landau Notation\<close>

text \<open>We define a (slightly simplified) version of the landau symbol @{text "\<O>"}:\<close>

text \<open>@{text "\<O> g = {f .\<exists> c > 0. \<exists> x0. \<forall> x \<ge> x0. f x \<le> c \<^emph> g x}"}\<close>

definition \<O> :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "\<O> g = {f . \<exists> c::nat > 0. \<exists> x0::nat. \<forall> x::nat \<ge> x0. f x \<le> c * g x}"

text \<open>Show that @{text "2n \<in> O(n²)"}. 
      Use Isar proof patterns, and make sure that your types are correct.\<close>

value "(0::nat) < 2"

thm exE[of "(<) 0"]

lemma lin_in_square: "(\<lambda> n. (2::nat) * n) \<in> \<O> (\<lambda> n. n ^ 2)"
  unfolding \<O>_def
proof
  have "\<forall>x::nat \<ge> 1. x \<le> x ^ 2"
    by (simp add: self_le_power)
  then have "\<forall>x::nat \<ge> 1. 2 * x \<le> 2 * x ^ 2" 
    by simp
  then have "\<exists>x0::nat. \<forall>x::nat \<ge> x0. 2 * x \<le> 2 * x ^ 2"
    by (rule_tac x = "1" in exI)
  then show "\<exists>c::nat>0. \<exists>x0::nat. \<forall>x::nat\<ge>x0. 2 * x \<le> c * x ^ 2"
    using pos2 by blast
qed

text \<open>Show that the other direction does not hold, i.e., n^2 \<notin> 2*n\<close>
text \<open>Hint: to simplify quadratic formulae, give @{text "power2_eq_square"} 
      and @{text "algebra_simps"} to the simplifier.\<close>

lemma square_notin_lin: "(\<lambda> n. n ^ 2) \<notin> \<O> (\<lambda> n. 2 * n)"
proof
  assume "power2 \<in> \<O> (\<lambda> n. 2 * n)"
  then have "power2 \<in> {f . \<exists> c::nat > 0. \<exists> x0::nat. \<forall> x::nat \<ge> x0. f x \<le> c * (2 * x)}" 
    using \<O>_def[of "(*) 2"] by simp
  then have "\<exists> c::nat > 0. \<exists> x0::nat. \<forall> x::nat \<ge> x0. power2 x \<le> c * (2 * x)" by simp
  then obtain c where "\<exists> x0::nat. \<forall> x::nat \<ge> x0. power2 x \<le> c * (2 * x)" by blast
  then obtain x0 where "\<forall> x::nat \<ge> x0. power2 x \<le> c * (2 * x)" by blast
  then have "\<forall> x::nat \<ge> x0. x * x \<le> c * (2 * x)" by (simp add: power2_eq_square)
  then have "\<forall> x::nat \<ge> x0. x \<le> c * 2" by (auto simp add: algebra_simps)
  then show False
    by (meson Suc_n_not_le_n dual_order.refl le_SucI)
qed

section \<open>Interleave Lists\<close>

text \<open>The function @{text "splice"} takes two lists and interleaves them. 
      Check its recursion equations:\<close>

thm splice.simps

text \<open>Show that, using the splice function, every list can be constructed from two lists, 
      where each of which is at least as long as half the length of the constructed list.\<close>

lemma split_splice:
  "\<exists> ys zs. xs = splice ys zs \<and> length ys \<ge> (length xs) div 2 \<and> length zs \<ge> (length xs) div 2"
proof (induction xs rule: induct_list012)
  case 1
  have a: "[] = splice [] []" by simp
  have b: "length [] div 2 \<le> length []" by simp
  from a b show ?case by blast
next
  case (2 x)
  have a: "[x] = splice [] [x]" by simp
  have b: "length [x] div 2 \<le> length []" by simp
  have c: "length [x] div 2 \<le> length [x]" by simp
  from a b c show ?case by blast
next
  case (3 x y xs)
  then obtain ys zs where 
     "xs = splice ys zs"
     "length xs div 2 \<le> length ys"
     "length xs div 2 \<le> length zs" by blast
  have a: "x # y # xs = splice (x # ys) (y # zs)"
    by (simp add: \<open>xs = splice ys zs\<close>)
  have b: "length (x # y # xs) div 2 \<le> length (x # ys)"
    by (simp add: \<open>length xs div 2 \<le> length ys\<close>)
  have c: "length (x # y # xs) div 2 \<le> length (y # zs)"
    by (simp add: \<open>length xs div 2 \<le> length zs\<close>)
  from a b c show ?case by blast
qed

text \<open>Hint: To prove that theorem, you will need a stronger induction hypothesis than that
            which you get by using structural induction on lists. To get such a stronger 
            hypothesis, you will need to use a different induction principle, like the one below\<close>

text \<open>@{text "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P zs \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"}\<close>

text \<open>In particular, your proof should begin by @{text "proof (induction xs rule: induct_pcpl)"}.\<close>

end