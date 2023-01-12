theory Ex03
  imports "HOL-Library.Tree"
begin

fun isin :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin Leaf x = False"
| "isin (Node l a r) x = 
    (if x < a then isin l x 
     else if x > a then isin r x
     else True)"

fun isin2 :: "('a::linorder) tree \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> bool" where
  \<comment> \<open>The second parameter stores the value for the deferred comparison\<close>
  "isin2 Leaf None x = False" 
| "isin2 Leaf (Some a) x = (a = x)"
| "isin2 (Node l a r) acc x = 
    (if x < a then isin2 l acc x 
     else isin2 r (Some a) x)"

lemma isin2_Some:
  "bst t \<Longrightarrow> (\<forall>y \<in> set_tree t. a < y) \<Longrightarrow> isin2 t (Some a) x = (isin t x \<or> x = a)"
  by (induction t arbitrary: a) auto

lemma isin2_None: 
  "bst t \<Longrightarrow> isin2 t None x = isin t x"
  by (induction t) (auto simp add: isin2_Some)

fun join :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"  where
  "join Leaf r = r"
| "join l Leaf = l"
| "join (Node l1 a1 r1) (Node l2 a2 r2) = 
    (case join r1 l2 of
       Leaf \<Rightarrow> Node l1 a1 (Node Leaf a2 r2)
    | (Node l a r) \<Rightarrow> Node (Node l1 a1 l) a (Node r a2 r2))"

lemma join_inorder[simp]: "inorder(join t1 t2) = inorder t1 @ inorder t2"
  by (induction t1 t2 rule: join.induct) (auto split: tree.split)

lemma "height(join t1 t2) \<le> max (height t1) (height t2) + 1"
  by (induction t1 t2 rule: join.induct) (auto split: tree.split)

declare join.simps[simp del]

thm set_inorder[symmetric] bst_iff_sorted_wrt_less

thm bst_wrt.simps
thm sorted_wrt_append

lemma join_set[simp]: "set_tree (join t1 t2) = set_tree t1 \<union> set_tree t2"
  by (simp del: set_inorder add: set_inorder[symmetric])

lemma bst_pres[simp]: "bst (Node l (x::_::linorder) r) \<Longrightarrow> bst (join l r)"
  by (force simp add: bst_iff_sorted_wrt_less sorted_wrt_append)

fun delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree"  where
  "delete x Leaf = Leaf"
| "delete x (Node l a r) = 
    (if x < a then Node (delete x l) a r
     else if x > a then Node l a (delete x r)
     else join l r)"

lemma bst_set_delete[simp]: "bst t \<Longrightarrow> set_tree (delete x t) = (set_tree t) - {x}"
  by (induction t) auto

lemma bst_del_pres: "bst t \<Longrightarrow> bst (delete x t)"
  by (induction t) auto

end