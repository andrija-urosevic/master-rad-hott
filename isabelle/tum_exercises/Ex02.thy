theory Ex02
  imports Main "HOL-Library.Tree"
begin

thm fold.simps

fun listsum :: "nat list \<Rightarrow> nat" where
  "listsum [] = 0"
| "listsum (x # xs) = x + listsum xs"

definition listsum' :: "nat list \<Rightarrow> nat" where
  "listsum' xs = fold (+) xs 0"

thm listsum'_def

lemma fold_acc_listsum: "fold (+) xs a = a + listsum xs"
  by (induction xs arbitrary: a) auto

lemma "listsum xs = listsum' xs"
  unfolding listsum'_def
  by (simp add: fold_acc_listsum)

datatype 'a ltree = Leaf 'a
                  | Node "'a ltree" "'a ltree"

fun inorder :: "'a ltree \<Rightarrow> 'a list" where
  "inorder (Leaf x) = [x]"
| "inorder (Node l r) = inorder l @ inorder r"

fun fold_ltree :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a ltree \<Rightarrow> 's \<Rightarrow> 's" where
  "fold_ltree f (Leaf x) a = f x a"
| "fold_ltree f (Node l r) a = fold_ltree f r (fold_ltree f l a)"

lemma "fold f (inorder t) s = fold_ltree f t s"
  by (induction t arbitrary: s) auto

fun mirror :: "'a ltree \<Rightarrow> 'a ltree" where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l r) = Node (mirror r) (mirror l)"

lemma "inorder (mirror t) = rev (inorder t)"
  by (induction t) auto

fun shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "shuffles [] ys = [ys]"
| "shuffles xs [] = [xs]"
| "shuffles (x # xs) (y # ys) = (map (Cons x) (shuffles xs (y # ys))) 
                              @ (map (Cons y) (shuffles (x # xs) ys))"

thm list.induct
thm shuffles.induct

lemma "zs \<in> set (shuffles xs ys) \<Longrightarrow> length zs = length xs + length ys"
  by (induction xs ys arbitrary: zs rule: shuffles.induct) auto

fun replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace a b [] = []"
| "replace a b (x # xs) = 
        (if a = x then b # replace a b xs else x # replace a b xs)"

lemma replace_len: "length (replace a b xs) = length xs"
  by (induction xs) auto

lemma replace_set: "a \<noteq> b \<Longrightarrow> a \<notin> set (replace a b xs)"
  by (induction xs) auto

lemma replace_set2: "b \<in> set xs \<Longrightarrow> b \<in> set (replace a b xs)"
  by (induction xs) auto

fun replace_tr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace_tr _ _ acc [] = rev acc"
| "replace_tr a b acc (x # xs) = 
    (if a = x then replace_tr a b (b # acc) xs else replace_tr a b (x # acc) xs)"

lemma replace_tr_len_gen: "length (replace_tr a b ys xs) = length ys + length xs"
  by (induction xs arbitrary: ys) auto

lemma replace_tr_len: "length (replace_tr a b [] xs) = length xs"
  by (induction xs) (auto simp add: replace_tr_len_gen)

lemma replace_tr_set_gen: "(a \<noteq> b \<and> a \<notin> set ys) \<Longrightarrow> a \<notin> set (replace_tr a b ys xs)"
  by (induction xs arbitrary: ys b) auto

lemma replace_tr_set: "a \<noteq> b \<Longrightarrow> a \<notin> set (replace_tr a b [] xs)"
  by (induction xs) (auto simp add: replace_tr_set_gen)

lemma replace_tr_set2_gen: "(b \<in> set xs \<or> b \<in> set ys) \<Longrightarrow> b \<in> set (replace_tr a b ys xs)"
  by (induction xs arbitrary: ys) auto

lemma replace_tr_set2: "b \<in> set xs \<Longrightarrow> b \<in> set (replace_tr a b [] xs)"
  by (induction xs) (auto simp add: replace_tr_set2_gen)

fun to_tree :: "'a tree \<Rightarrow> 'a ltree" where
  "to_tree \<langle>\<rangle>         = undefined"
| "to_tree \<langle>\<langle>\<rangle>, v, \<langle>\<rangle>\<rangle> = Leaf v"
| "to_tree \<langle>l, v, \<langle>\<rangle>\<rangle>  = Node (to_tree l) (Leaf v)"
| "to_tree \<langle>\<langle>\<rangle>, v, r\<rangle>  = Node (Leaf v) (to_tree r)"
| "to_tree \<langle>l, v, r\<rangle>  = Node (to_tree l) (Node (Leaf v) (to_tree r))"

thm to_tree.induct

lemma to_tree_inorder: "t \<noteq> \<langle>\<rangle> \<Longrightarrow> Tree.inorder t = inorder (to_tree t)"
  by (induction t rule: to_tree.induct) auto



end