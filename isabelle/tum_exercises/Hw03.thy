theory Hw03
  imports Main "HOL-Library.Tree" "HOL-Data_Structures.AList_Upd_Del"

begin

section \<open>Path\<close>

text \<open>A position in a tree can be given as a list of navigation instructions from the root, i.e.
whether to go to the left or right subtree. We call such a list a path.\<close>

datatype direction = L | R

type_synonym path = "direction list"

text \<open>Define when a path is valid.\<close>

fun valid :: "'a tree \<Rightarrow> path \<Rightarrow> bool" where
  "valid t [] = True"
| "valid Leaf xs = False"
| "valid (Node l a r) (x # xs) = 
    (case x of L \<Rightarrow> valid l xs 
             | R \<Rightarrow> valid r xs)"

text \<open>Define a function @{text "delete_subtree t p"}, that returns @{text "t"}, 
      with the subtree at @{text "p"} replaced with a leaf.\<close>

fun delete_subtree :: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree" where
  "delete_subtree t [] = Leaf"
| "delete_subtree Leaf (x # xs) = Leaf"
| "delete_subtree (Node l a r) (x # xs) = 
    (case x of L \<Rightarrow> Node (delete_subtree l xs) a r
             | R \<Rightarrow> Node l a (delete_subtree r xs))"

text \<open>Define the function such that nothing happens if an invalid path is given. 
      Prove the following for delete_subtree:\<close>

lemma delete_subtree_invalid: 
  shows "\<not> valid t p \<Longrightarrow> delete_subtree t p = t"
  by (induct t p rule: delete_subtree.induct) (auto split: direction.splits)

text \<open>Similarly define two functions, the first @{text "get t p"} to return 
      the subtree of @{text "t"} addressed by a given path, and a second one 
      @{text "put t p s"}, that returns @{text "t"}, with the subtree at @{text "p"}
      replaced by @{text "s"}. The function @{text "get"} should return @{text "undefined"}
      if the path is not valid and @{text "put"} should do nothing if the path 
      is not valid.\<close>

fun get :: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree" where
  "get t [] = t"
| "get Leaf (x # xs) = undefined"
| "get (Node l _ r) (x # xs) = 
    (case x of L \<Rightarrow> get l xs
             | R \<Rightarrow> get r xs)"

fun put :: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "put t [] s = s"
| "put Leaf (x # xs) s = Leaf"
| "put (Node l a r) (x # xs) s = 
    (case x of L \<Rightarrow> Node (put l xs s) a r
             | R \<Rightarrow> Node l a (put r xs s))"

text \<open>Prove the following algebraic laws on @{text "delete"}, 
      @{text "put"}, and @{text "get"}.\<close>

lemma put_in_delete: 
  shows "put (delete_subtree t p) p (get t p) = t"
  by (induct t p rule: delete_subtree.induct) (auto split: direction.split)

lemma delete_delete:
  shows "valid t p \<Longrightarrow> delete_subtree (delete_subtree t p) p = delete_subtree t p"
  by (induction t p rule: delete_subtree.induct) (auto split: direction.split)

lemma delete_replaces_with_leaf [simp]:
  shows "valid t p \<Longrightarrow> get (delete_subtree t p) p = Leaf"
  by (induction t p rule: delete_subtree.induct) (auto split: direction.split)

lemma valid_delete: "valid t p \<Longrightarrow> valid (delete_subtree t p) p"
  by (induction t p rule: delete_subtree.induct) (auto split: direction.split)

text \<open>Show the following lemmas about appending two paths:\<close>

lemma valid_append: 
  shows "valid t (p @ q) \<longleftrightarrow> valid t p \<and> valid (get t p) q"
  by (induction t p rule: valid.induct) (auto split: direction.split)

lemma put_delete_get_append:
  shows "valid t (p @ q) \<Longrightarrow> delete_subtree t (p @ q) = put t p (delete_subtree (get t p) q)"
  by (induction t p rule: valid.induct) (auto split: direction.split)

lemma put_get_append:
  shows "valid t (p @ q) \<Longrightarrow> get (put t (p @ q) s) p = put (get t p) q s"
  by (induction t p rule: valid.induct) (auto split: direction.split)

section \<open>Map\<close>

text \<open>A map is a collection of @{text "(key, value)"} pairs, where each possible key 
      appears at most once. For this @{text "datatype"}, one should be able 
      @{text "add"}/@{text "update"} a @{text "(key,value)"} pair, 
      @{text "delete"} a pair, and
      @{text "lookup"} a @{text "value"} associated with a particular @{text "key"}.\<close>

text \<open>A straightforward implementation of maps can be done using association lists. 
      An existing such implementation uses the functions @{text "upd_list"}, 
      @{text "del_list"}, and @{text "AList_Upd_Del.map_of"} 
      for @{text "add"}/@{text "update"} a @{text "(key,value)"} 
      pair, @{text "delete"} a pair, and @{text "lookup"} values, respectively.\<close>

thm map_of.simps upd_list.simps del_list.simps

text \<open>HINT: to prove facts concerning @{text "del_list"}, @{text "upd_list"}, 
      or @{text "AList_Upd_Del.map_of"} you might find it useful to use 
      @{text "del_list_simps"}, @{text "upd_list_simps"}, or 
      @{text "map_of_simps"} as simp rules. Each one of those is a set of 
      lemmas proven about the respective functions.\<close>

thm del_list_simps
thm upd_list_simps
thm map_of_simps

text \<open>For linearly ordered keys, it is more efficient to implement maps using 
      binary trees. Using binary search trees, implement the three main map 
      functionalities @{text "add"}/@{text "update"} a @{text "(key,value)"} pair, 
      @{text "delete"} a pair, and @{text "lookup"} values. Then you should prove 
      their equivalence to the corresponding association list implementation of maps.\<close>

text \<open>The first one of those functionalities is map @{text "lookup"}. It should return 
      an option type, i.e. for a key @{text "k"} it should return @{text "Some v"} if 
      the map has an entry for @{text "k"}, and @{text "None"} otherwise\<close>

fun map_lookup :: "('a::linorder \<times> 'b) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "map_lookup Leaf key = None"
| "map_lookup (Node l (k, a) r) key = 
    (if k > key then map_lookup l key
     else if k < key then map_lookup r key
     else Some a)"

text \<open>Prove it is equivalent to @{text "AList_Upd_Del.map_of"}, 
      if the tree is well-formed 
      (i.e an inorder traversal of its elements returns a sorted list).
      
      HINT: for proving facts about objects of type @{text "option"}, it is 
      useful to use @{text "option.split"} as a split rule for @{text "auto"} 
      (check the usage of @{text "split: tree.split"} in the exercise).\<close>

lemma lookup_map_of:
  shows "sorted1 (inorder t) \<Longrightarrow> map_lookup t k = map_of (inorder t) k"
  by (induction t k rule: map_lookup.induct) (auto simp add: map_of_simps split: option.split)

text \<open>The second functionality is map update.\<close>

fun map_update :: "'a :: linorder \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) tree \<Rightarrow> ('a \<times> 'b) tree" where
  "map_update key v Leaf = Node Leaf (key, v) Leaf"
| "map_update key v (Node l (k, a) r) = 
    (if key < k then Node (map_update key v l) (k, a) r
     else if key > k then Node l (k, a) (map_update key v r)
     else Node l (k, v) r)"

text \<open>Prove it is equivalent to @{text "upd_list"}.\<close>

lemma inorder_update:
  shows "sorted1 (inorder t) \<Longrightarrow> inorder (map_update k v t) = upd_list k v (inorder t)"
  by (induction k v t rule: map_update.induct) (auto simp add: upd_list_simps)

text \<open>Lastly, define a function that, given a key @{text "k"}, deletes key-value pair 
      @{text "(k, v)"} from a map represented as a tree, if @{text "(k, v)"} exists.
      HINT: You can use the function split_min defined in the lecture demonstration 
      of trees.\<close>

fun split_min :: "'a tree \<Rightarrow> 'a * 'a tree" where
  "split_min (Node l a r) =
    (if l = Leaf then (a,r)
     else let (x,l') = split_min l
           in (x, Node l' a r))"

fun map_delete :: "'a :: linorder \<Rightarrow> ('a \<times> 'b) tree \<Rightarrow> ('a \<times> 'b) tree" where
  "map_delete key Leaf = Leaf"
| "map_delete key (Node l (k, a) r) = 
    (if key < k then Node (map_delete key l) (k, a) r
     else if key > k then Node l (k, a) (map_delete key r)
     else if r = Leaf then l else let (a', r') = split_min r in Node l a' r')"

text \<open>Prove that it works as intended.
      HINT: you will need to prove a lemma about split_min\<close>

lemma split_min_set_tree:
  assumes "split_min t = (x, t')"
      and "bst t"
      and "t \<noteq> Leaf"
    shows "set_tree t' = set_tree t - {x} \<and> x \<in> set_tree t"
  using assms
  apply (induction t arbitrary: x t' rule: split_min.induct)
   apply (force split: if_split_asm prod.splits)
  apply simp
  done

lemma split_min_inorder:
  shows "split_min r = (a, r') \<Longrightarrow> r \<noteq> Leaf \<Longrightarrow> a # inorder r' = inorder r"
  by (induction r arbitrary: a r' rule: split_min.induct) (auto split: if_split_asm prod.splits)

lemma inorder_delete:
  shows "sorted1 (inorder t) \<Longrightarrow> inorder (map_delete x t) = del_list x (inorder t)"
  by (induction x t rule: map_delete.induct) (auto simp add: del_list_simps split_min_inorder split: prod.split)

end