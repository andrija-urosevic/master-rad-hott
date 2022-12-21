theory ex09
  imports Main

begin

text \<open>Read the chapter about total recursive functions in the 
``Tutorial on Isabelle/HOL'' (@{text fun}, Chapter 3.5).\<close>

text \<open>
In this exercise you will define a function @{text Zip} that merges two lists
by interleaving.
 Examples:
@{text "Zip [a1, a2, a3]  [b1, b2, b3] = [a1, b1, a2, b2, a3, b3]"} 
 and
@{text "Zip [a1] [b1, b2, b3] = [a1, b1, b2, b3]"}.

Use three different approaches to define @{text Zip}:
\begin{enumerate}
\item by primitive recursion on the first list,
\item by primitive recursion on the second list,
\item by total recursion (using @{text fun}).
\end{enumerate}
\<close>

primrec zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zip1 [] ys = ys"
| "zip1 (x # xs) ys = 
      (case ys of 
            [] \<Rightarrow> x # xs 
      | z # zs \<Rightarrow> x # z # zip1 xs zs)"


primrec zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zip2 xs [] = xs"
| "zip2 xs (y # ys) =
      (case xs of
            [] \<Rightarrow> y # ys
      | x # xs \<Rightarrow> x # y # zip2 xs ys)"

fun zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zipr [] ys = ys"
| "zipr xs [] = xs"
| "zipr (x # xs) (y # ys) = x # y # zipr xs ys"

text \<open>Show that all three versions of @{text Zip} are equivalent.\<close>

lemma "zip1 xs ys = zip2 xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case 
    by (case_tac ys) auto
next
  case (Cons a xs)
  then show ?case
    by (case_tac ys) auto
qed

text \<open>Show that @{text zipr} distributes over @{text append}.\<close>

lemma "\<lbrakk>length p = length u; length q = length v\<rbrakk> \<Longrightarrow> 
  zipr (p @ q) (u @ v) = zipr p u @ zipr q v"
proof (induction p arbitrary: q u v)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a p)
  then show ?case 
    by (case_tac u) auto
qed


text \<open>
{\bf Note:} For @{text fun}, the order of your equations is relevant.
If equations overlap, they will be disambiguated before they are added
to the logic.  You can have a look at these equations using @{text
"thm zipr.simps"}.
\<close>

thm zipr.simps

end