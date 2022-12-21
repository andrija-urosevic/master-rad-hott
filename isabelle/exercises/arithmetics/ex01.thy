theory ex01
  imports Main

begin

subsubsection \<open>Power\<close>

text \<open>Define a primitive recursive function $pow~x~n$ that
computes $x^n$ on natural numbers.\<close>

primrec pow :: "nat => nat => nat"
  where
    "pow x 0 = 1"
  | "pow x (Suc n) = x * pow x n"

text \<open>Prove the well known equation $x^{m \cdot n} = (x^m)^n$:\<close>

lemma pow_plus: "pow x (m + n) = pow x m * pow x n"
  by (induction n) auto

theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
  by (induction n) (auto simp add: pow_plus)

text \<open>Hint: prove a suitable lemma first.  If you need to appeal to
associativity and commutativity of multiplication: the corresponding
simplification rules are named @{text mult_ac}.\<close>

subsubsection \<open>Summation\<close>

text \<open>Define a (primitive recursive) function $sum~ns$ that sums a list
of natural numbers: $sum [n_1, \dots, n_k] = n_1 + \cdots + n_k$.\<close>


primrec sum :: "nat list => nat"
  where
    "sum [] = 0"
  | "sum (n # ns) = n + sum ns"


text \<open>Show that $sum$ is compatible with $rev$. You may need a lemma.\<close>

lemma sum_append: "sum (ns @ ms) = sum ns + sum ms"
  by (induction ns) auto
    
theorem sum_rev: "sum (rev ns) = sum ns"
  by (induction ns) (auto simp add: sum_append)

text \<open>Define a function $Sum~f~k$ that sums $f$ from $0$ up to $k-1$:
$Sum~f~k = f~0 + \cdots + f(k - 1)$.\<close>

value "map (\<lambda>x. x + 2) [0..k]"

primrec Sum :: "(nat => nat) => nat => nat"
  where
    "Sum f 0 = 0"
  | "Sum f (Suc k) = Sum f k + f k"

text \<open>Show the following equations for the pointwise summation of functions.
Determine first what the expression @{text whatever} should be.\<close>

theorem "Sum (\<lambda>i. f i + g i) k = Sum f k + Sum g k"
  by (induction k) auto

theorem "Sum f (k + l) = Sum f k + Sum (\<lambda>i. f (k +i)) l"
  by (induction l) auto

text \<open>What is the relationship between @{term sum} and @{text Sum}?
Prove the following equation, suitably instantiated.\<close>

theorem "Sum f k = sum (map f [0..<k])"
  by (induction k) (auto simp add: sum_append)

text \<open>Hint: familiarize yourself with the predefined functions @{term map}
and @{text"[i..<j]"} on lists in theory List.\<close>

end