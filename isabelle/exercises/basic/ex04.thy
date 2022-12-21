theory ex04
  imports Main

begin

text \<open>Define a function @{text first_pos} that computes the index
of the first element in a list that satisfies a given predicate:

  @{text "first_pos :: ('a => bool) => 'a list => nat"}

text The smallest index is @{text 0}.  If no element in the
list satisfies the predicate, the behaviour of @{text first_pos} should
be as described below.\<close>

primrec first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "first_pos P [] = 0"
| "first_pos P (x # xs) = (if P x then 0 else Suc (first_pos P xs))"


text \<open>Verify your definition by computing
\begin{itemize}
\item the index of the first number equal to @{text 3} in the list
  @{text "[1::nat, 3, 5, 3, 1]"},
\item the index of the first number greater than @{text 4} in the list
  @{text "[1::nat, 3, 5, 7]"},
\item the index of  the first list with more than one element in the list
  @{text "[[], [1, 2], [3]]"}.
\end{itemize}
\emph{Note:} Isabelle does not know the operators @{text ">"} and @{text
"\<ge>"}.  Use @{text "<"} and @{text "\<le>"} instead.\<close>

lemma "first_pos (\<lambda>x. x=3) [1::nat, 3, 5, 3, 1] = 1"
  by auto

lemma "first_pos (\<lambda>x. x>4) [1::nat, 3, 5, 7] = 2"
  by auto

lemma "first_pos (\<lambda>xs. xs \<noteq> []) [[], [1,2], [3]] = 1"
  by auto

text \<open>Prove that @{text first_pos} returns the length of the list if
and only if no element in the list satisfies the given predicate.\<close>

lemma "first_pos P xs = length xs \<longleftrightarrow> \<not> (\<exists>x \<in> set xs. P x)"
  by (induction xs) auto

text \<open>Now prove:\<close>

lemma "list_all (\<lambda> x. \<not> P x) (take (first_pos P xs) xs)"
  by (induction xs) auto

text \<open>How can @{text "first_pos (\<lambda> x. P x \<or> Q x) xs"} be computed from
@{text "first_pos P xs"} and @{text "first_pos Q xs"}?  Can something
similar be said for the conjunction of @{text P} and @{text Q}?  Prove
your statement(s).\<close>

lemma "first_pos (\<lambda> x. P x \<or> Q x) xs = min (first_pos P xs) (first_pos Q xs)"
  by (induction xs) auto

lemma "first_pos (\<lambda> x. P x \<and> Q x) xs \<ge> max (first_pos P xs) (first_pos Q xs)"
  by (induction xs) auto

text \<open>Suppose @{text P} implies @{text Q}. What can be said about the
relation between @{text "first_pos P xs"} and @{text "first_pos Q xs"}?
Prove your statement.\<close>

lemma first_pos_imp_geq:
  assumes "\<forall> x. P x \<longrightarrow> Q x"
  shows "first_pos P xs \<ge> first_pos Q xs"
  using assms
  by (induction xs) auto

text \<open>Define a function @{text count} that counts the number of
elements in a list that satisfy a given predicate.\<close>

primrec count :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count P [] = 0"
| "count P (x # xs) = (if P x then 1 + count P xs else count P xs)"


text \<open>Show: The number of elements with a given property stays the
same when one reverses a list with @{text rev}.  The proof will require
a lemma.\<close>

lemma count_append: "count P (xs @ ys) = count P xs + count P ys"
  by (induction xs) auto

lemma "count P xs = count P (rev xs)"
  by (induction xs) (auto simp add: count_append)

text \<open>Find and prove a connection between the two functions @{text filter}
and @{text count}.\<close>

lemma "count P xs = length (filter P xs)"
  by (induction xs) auto

end