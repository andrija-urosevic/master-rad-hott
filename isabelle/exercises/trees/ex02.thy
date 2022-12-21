theory ex02
  imports Main

begin

text \<open>Recall the summation function\<close>

primrec sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

text \<open>In the Isabelle library, you will find (in the theory {\tt List.thy})
the functions @{text foldr} and @{text foldl}, which allow you to define some
list functions, among them @{text sum} and @{text length}.  Show the following:\<close>

lemma sum_foldr: "sum xs = foldr (+) xs 0"
  by (induction xs) auto

lemma length_foldr: "length xs = foldr (\<lambda> x res. 1 + res) xs 0"
  by (induction xs) auto

text \<open>Repeated application of @{text foldr} and @{text map} has the
disadvantage that a list is traversed several times.  A single traversal is
sufficient, as illustrated by the following example:\<close>

lemma "sum (map (\<lambda> x. x + 3) xs) = foldr h xs b"
  oops

text \<open>Find terms @{text h} and @{text b} which solve this equation.\<close>
lemma "sum (map (\<lambda> x. x + 3) xs) = foldr (\<lambda> x acc. x + 3 + acc) xs 0"
  by (induction xs) auto

text \<open>Generalize this result, i.e.\ show for appropriate @{text h} and @{text
b}:\<close>

lemma "foldr g (map f xs) a = foldr (g \<circ> f) xs a"
  by (induction xs) auto

text \<open>Hint: Isabelle can help you find the solution if you use the equalities
arising during a proof attempt.\<close>

text \<open>The following function @{text rev_acc} reverses a list in linear time:\<close>

primrec rev_acc :: "['a list, 'a list] \<Rightarrow> 'a list" where
  "rev_acc [] ys = ys"
| "rev_acc (x#xs) ys = (rev_acc xs (x#ys))"

text \<open>Show that @{text rev_acc} can be defined by means of @{text foldl}.\<close>

lemma rev_acc_foldl: "rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
  by (induction xs arbitrary: a) auto


text \<open>Prove the following distributivity property for @{text sum}:\<close>

lemma sum_append [simp]: "sum (xs @ ys) = sum xs + sum ys"
  by (induction xs arbitrary: ys) auto


text \<open>Prove a similar property for @{text foldr}, i.e.\ something like @{text
"foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"}.  However, you will
have to strengthen the premises by taking into account algebraic properties of
@{text f} and @{text a}.\<close>

definition left_neutral :: "['a \<Rightarrow> 'b \<Rightarrow> 'b, 'a] \<Rightarrow> bool"
  where
    "left_neutral f a \<equiv> \<forall>x. f a x = x"

definition assoc_left :: "['a \<Rightarrow> 'a \<Rightarrow> 'a] \<Rightarrow> bool"
  where
    "assoc_left f \<equiv> \<forall>x y z. f (f x y) z = f x (f y z)"

lemma foldr_append:
  assumes "left_neutral f a"
      and "assoc_left f"
  shows "foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"
  using assms
  by (induction xs) (auto simp add: left_neutral_def assoc_left_def)


text \<open>Now, define the function @{text prod}, which computes the product of
all list elements\<close>

definition prod :: "nat list \<Rightarrow> nat"
  where
    "prod xs = foldr (*) xs 1"

text \<open>directly with the aid of a fold and prove the following:\<close>

lemma "prod (xs @ ys) = prod xs * prod ys"
  by (induction xs) (auto simp add: prod_def)

text \<open>Consider the following type of binary trees:\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text \<open>Define functions which convert a tree into a list by traversing it in
pre-, resp.\ postorder:\<close>


primrec preorder :: "'a tree \<Rightarrow> 'a list"
  where
    "preorder Tip = []"
  | "preorder (Node lt x rt) = x # preorder lt @ preorder rt"

primrec  postorder :: "'a tree \<Rightarrow> 'a list"
  where
    "postorder Tip = []"
  | "postorder (Node lt x rt) = postorder lt @ postorder rt @ [x]"

text \<open>You have certainly realized that computation of postorder traversal can
be efficiently realized with an accumulator, in analogy to @{text rev_acc}:\<close>

primrec postorder_acc :: "['a tree, 'a list] \<Rightarrow> 'a list"
  where
    "postorder_acc Tip xs = xs"
  | "postorder_acc (Node lt x rt) xs = postorder_acc lt (postorder_acc rt (x # xs))"

text \<open>Define this function and show:\<close>

lemma "postorder_acc t xs = (postorder t) @ xs"
  by (induction t arbitrary: xs) auto

text \<open>@{text postorder_acc} is the instance of a function @{text foldl_tree},
which is similar to @{text foldl}.\<close>

primrec foldl_tree :: "('b => 'a => 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b"
  where
    "foldl_tree f acc Tip = acc"
  | "foldl_tree f acc (Node lt x rt) = foldl_tree f (foldl_tree f (f acc x) rt) lt"

text \<open>Show the following:\<close>

lemma "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x. Cons x xs) a t"
  by (induction t) auto

text \<open>Define a function @{text tree_sum} that computes the sum of the
elements of a tree of natural numbers:\<close>

primrec tree_sum :: "nat tree \<Rightarrow> nat"
  where
    "tree_sum Tip = 0"
  | "tree_sum (Node lt x rt) = tree_sum lt + x + tree_sum rt"

text \<open>and show that this function satisfies\<close>

lemma "tree_sum t = sum (preorder t)"
  by (induction t) auto

end