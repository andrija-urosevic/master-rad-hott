theory Hw04
  imports Main "HOL-Library.Tree"
begin

section \<open>Popularity Annotated Trees\<close>

text \<open>We define @{text "ptrees"}, which are trees that store the popularity of each element, 
      i.e. the number of times it was searched for, as @{text "(nat \<^emph> \<Zprime>a) tree"}.\<close>

type_synonym 'a ptree = "(nat * 'a) tree"

definition test_ptree :: "nat ptree" where
  "test_ptree \<equiv> \<langle>\<langle>\<langle>\<rangle>, (1, 2), \<langle>\<rangle>\<rangle>, (2, 5) ,\<langle>\<langle>\<langle>\<rangle>, (1, 6) ,\<langle>\<rangle>\<rangle>, (3, 7), \<langle>\<langle>\<rangle>, (3, 8),\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"

text \<open>Define the set of elements of that tree as a recursive function, then show it 
      correct w.r.t. to the normal @{text "set_tree"} (` is the set @{text "image"}):\<close> 

fun set_ptree :: "('a::linorder) ptree \<Rightarrow> 'a set" where
  "set_ptree Leaf         = {}"
| "set_ptree (Node l a r) = (set_ptree l)
                          \<union> {snd a}
                          \<union> (set_ptree r)"

value "set_ptree test_ptree"
value "snd ` set_tree test_ptree"

lemma set_ptree: "set_ptree t = snd ` set_tree t"
  by (induction t) auto

text \<open>Define the binary search tree predicate as well as insert function for those trees 
     (they should be quite similar to the formulations for normal trees).\<close>

text \<open>If a node is already present, overwrite the old popularity value\<close>

fun pbst :: "'a::linorder ptree \<Rightarrow> bool" where
  "pbst Leaf         \<longleftrightarrow> True"
| "pbst (Node l a r) \<longleftrightarrow> (\<forall> x \<in> set_ptree l. x < snd a) 
                       \<and> (\<forall> x \<in> set_ptree r. snd a < x) 
                       \<and> pbst l \<and> pbst r"

value "pbst test_ptree"

fun pins :: "(nat * 'a::linorder) \<Rightarrow> 'a ptree \<Rightarrow> 'a ptree" where
  "pins x Leaf         = Node Leaf x Leaf"
| "pins x (Node l a r) = (if snd x < snd a then Node (pins x l) a r else
                          if snd a < snd x then Node l a (pins x r) else
                          Node l (fst x, snd a) r) "

value "pins (2, 9) test_ptree"

text \<open>Show the most interesting property, namely that insert preserves the invariant:\<close>

lemma pins_invar: "pbst t \<Longrightarrow> pbst (pins x t)"
  apply (induction x t rule: pins.induct)
   apply (auto split: prod.split)
  sorry

text \<open>Now define the @{text "pisin"} function, which should return the updated @{text "ptree"} 
      and the number of times it was searched for (i.e., zero for elements not in the tree and 
      at least one for everything in the tree):\<close>

fun pisin :: "'a :: linorder \<Rightarrow> 'a ptree \<Rightarrow> ('a ptree * nat)" where
  "pisin x Leaf = Pair Leaf 0"
| "pisin x (Node l a r) = 
    (let (lt, lc) = pisin x l;
         (rt, rc) = pisin x r;
            count = fst a
      in (if x < snd a then (Node lt a r, lc) else
          if snd a < x then (Node l a rt, rc) else
          ((Node l (count + 1, snd a) r), count)))"

value "test_ptree"
value "pisin 2 test_ptree"

text \<open>Show the correctness of your function:\<close>

lemma pisin_set: "pbst t \<Longrightarrow> set_ptree (fst (pisin x t)) = set_ptree t"
  by (induction x t rule: pisin.induct) (auto split: prod.split if_split_asm)

lemma pisin_invar: "pbst t \<Longrightarrow> pbst (fst (pisin x t))"
  apply (induction x t rule: pisin.induct)
   apply (auto split: prod.split)
   apply (metis fst_eqD pisin_set)+
  done

lemma pisin_inc: "pbst t \<Longrightarrow> (n,x) \<in> set_tree t \<Longrightarrow> (Suc n,x) \<in> set_tree (fst (pisin x t))"
  apply (induction x t arbitrary: n rule: pisin.induct)
   apply (auto split: prod.split)
  sorry

text \<open>Knowing the popularity of element queries, we can re-order the tree from time to time to
      optimize query time (assuming that the distribution of searched nodes stays the same).\<close>

text \<open>Implement such a re-ordering — it does not need to be optimal, but the most popular
      element should be at the root, and the least popular elements should be on the bottom.\<close>

text \<open>Hint: Sorting might be useful. Have a look at the pre-defined sort function and its
      implementation.\<close>

term "sort_key (\<lambda> x. fst x) (inorder (t::'a ptree))"
term "sort \<circ> inorder"
term pins

definition reorder :: "('a :: linorder) ptree \<Rightarrow> 'a ptree" where
  "reorder t = foldr pins (sort_key fst (inorder t)) Leaf"

value "reorder test_ptree"

value "sort_key fst [(1::nat, 2::nat), (3, 2)]"

text \<open>Show that your re-ordering preserves the invariant:\<close>

theorem reorder_pbst: "pbst t \<Longrightarrow> pbst (reorder t)"
  apply (induction t)
   apply auto
  sorry

section \<open>Popularity Annotated Trees (II)\<close>


text \<open>Show that in the @{text "reorder"} function, the set of elements stays unchanged. 
      Start by proving that the @{text "set_ptree"} stays unchanged — 
      this should give you an idea how the proof should work.\<close>

theorem reorder_pset: "pbst t \<Longrightarrow> set_ptree (reorder t) = set_ptree t"
  sorry

theorem reorder_set: "pbst t \<Longrightarrow> set_tree (reorder t) = set_tree t"
  sorry

end