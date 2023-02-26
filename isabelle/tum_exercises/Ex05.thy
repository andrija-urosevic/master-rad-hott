theory Ex05
  imports Complex_Main "HOL-Library.Tree"
begin

lemma exp_fact_estimate: "n > 3 \<Longrightarrow> (2::nat)^n < fact n"
proof (induction n)
  case 0 then show ?case by auto
next
  case (Suc n)
  then have "n = 3 \<or> n > 3" by auto
  then show ?case 
  proof
    assume \<open>n = 3\<close>
    then show ?thesis 
      by (auto simp: eval_nat_numeral)
  next 
    assume \<open>n > 3\<close>
    have "(2::nat) ^ (Suc n) = 2 * 2 ^ n" by simp
    also have "... < 2 * fact n" using Suc.IH[OF \<open>n > 3\<close>] by simp
    also have "... < (Suc n) * fact n" using \<open>n > 3\<close> by simp
    also have "... = fact (Suc n)" by simp
    finally show ?thesis .
  qed
qed

lemma "2 ^ n \<le> 2 ^ Suc n"
  apply auto 
  oops 
text \<open>Leaves the subgoal \<open>2 ^ n \<le> 2 * 2 ^ n\<close>\<close>

lemma "(2::nat) ^ n \<le> 2 ^ Suc n" by simp

fun sumto :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"  where
  "sumto f 0 = f 0"
| "sumto f (Suc n) = sumto f n + f (Suc n)"

lemma sum_of_naturals: "2 * sumto (\<lambda>x. x) n = n * (n + 1)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "2 * sumto (\<lambda>x. x) (Suc (n::nat)) = 2 * (sumto (\<lambda>x. x) n + (Suc n))" using sumto.simps(2) by simp
  also have "... = 2 * (sumto (\<lambda>x. x) n) + 2 * (Suc n)" by simp
  also have "... = n * (n + 1) + 2 * (Suc n)" using Suc.IH by simp
  also have "... = n * (n + 1) + 2 * (n + 1)" by simp
  also have "... = (n + 2) * (n + 1)" by simp
  also have "... = (n + 1) * (n + 2)" by simp
  also have "... = (Suc n) * (Suc n + 1)" by simp
  finally show ?case .
qed

lemma "sumto (\<lambda>x. x) n ^ 2 = sumto (\<lambda>x. x ^ 3) n"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  assume IH: "(sumto (\<lambda>x. x) n)\<^sup>2 = sumto (\<lambda>x. x ^ 3) n"
  note [simp] = algebra_simps \<comment>\<open>Extend the simpset only in this block\<close>
  have "(sumto (\<lambda>x. x) (Suc n)) ^ 2 = (sumto (\<lambda>x. x) n + (Suc n)) ^ 2" by simp
  also have "... = (sumto (\<lambda>x. x) n) ^ 2 
                 + 2 * (sumto (\<lambda>x. x) n) * (Suc n) 
                 + (Suc n) ^ 2" by algebra
  also have "... = sumto (\<lambda>x. x ^ 3) n
                 +  2 * (sumto (\<lambda>x. x) n) * (Suc n) 
                 + (Suc n) ^ 2" using IH by simp
  also have "... = sumto (\<lambda>x. x ^ 3) n
                 + n * (n + 1) * (Suc n)
                 + (Suc n) ^ 2" using sum_of_naturals by simp
  also have "... = sumto (\<lambda>x. x ^ 3) n
                 + n * (Suc n) * (Suc n)
                 + (Suc n) ^ 2" by simp
  also have "... = sumto (\<lambda>x. x ^ 3) n
                 + n * (Suc n) ^ 2
                 + (Suc n) ^ 2" by algebra
  also have "... = sumto (\<lambda>x. x ^ 3) n + (n + 1) * (Suc n) ^ 2" by simp
  also have "... = sumto (\<lambda>x. x ^ 3) n + (Suc n) * (Suc n) ^ 2" by simp
  also have "... = sumto (\<lambda>x. x ^ 3) n + (Suc n) ^ 3" by algebra
  also have "... = sumto (\<lambda>x. x ^ 3) (Suc n)" by simp
  finally show "(sumto (\<lambda>x. x) (Suc n)) ^ 2 = sumto (\<lambda>x. x ^ 3) (Suc n)" .
qed

datatype 'a tchar = L | N 'a

fun pretty :: "'a tree \<Rightarrow> 'a tchar list"  where
  "pretty Leaf = [L]"
| "pretty (Node l x r) = [N x] @ pretty l @ pretty r"

value "pretty (Node (Node Leaf 0 Leaf) (1::nat) (Node Leaf 2 Leaf)) = [N 1, N 0, L, L, N 2, L, L]"

lemma pretty_unique_aux: "pretty t @ xs = pretty t' @ xs' \<Longrightarrow> t = t'"
proof (induction t arbitrary: t' xs xs')
  case Leaf
  then show ?case
  proof (cases t')
    case Leaf
    then show ?thesis by simp
  next
    case (Node l a r)
    with Leaf have False by simp
    then show ?thesis by simp
  qed
next
  case (Node l a r)
  then show ?case 
  proof (cases t')
    case Leaf
    with Node have False by simp
    then show ?thesis by simp
  next
    fix l' a' r' 
    assume [simp]: "t' = Node l' a' r'"
    with Node have "l = l'" by auto
    with Node have "r = r'" by auto
    with Node show ?thesis by auto
  qed
qed

lemma pretty_unique: "pretty t = pretty t' \<Longrightarrow> t = t'"
  using pretty_unique_aux[where xs = "[]" and xs' = "[]"] 
  by auto

fun bin_tree2 :: "'a tree \<Rightarrow> 'b tree \<Rightarrow> bool"  where
  "bin_tree2 Leaf Leaf                     \<longleftrightarrow> True"
| "bin_tree2 (Node _ _ _) Leaf             \<longleftrightarrow> False"
| "bin_tree2 Leaf (Node _ _ _)             \<longleftrightarrow> False"
| "bin_tree2 (Node l1 _ r1) (Node l2 _ r2) \<longleftrightarrow> (bin_tree2 l1 l2 \<and> bin_tree2 r1 r2)"

print_statement bin_tree2.induct

lemma pretty_unique_aux': "pretty t @ xs = pretty t' @ xs' \<Longrightarrow> t = t'"
  apply (induction t t' arbitrary: xs xs' rule: bin_tree2.induct)
     apply auto
  apply blast
  done

end