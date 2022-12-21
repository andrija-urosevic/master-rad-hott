theory ex01
  imports Main

begin

text \<open>Define a datatype @{text"'a tree"} for binary trees. Both leaf and
internal nodes store information.\<close>

datatype 'a tree = Tip "'a" 
                 | Node "'a" "'a tree" "'a tree"

text \<open>Define the functions @{term preOrder}, @{term postOrder}, and @{term
inOrder} that traverse an @{text"'a tree"} in the respective order.\<close>

definition test_tree :: "nat tree" where
  "test_tree = Node 1 (Node 2 (Tip 3) (Tip 4)) (Node 5 (Tip 6) (Tip 7))"

primrec preOrder :: "'a tree \<Rightarrow> 'a list" where
  "preOrder (Tip x) = [x]"
| "preOrder (Node x lt rt) = x # preOrder lt @ preOrder rt"

primrec postOrder :: "'a tree \<Rightarrow> 'a list" where
  "postOrder (Tip x) = [x]"
| "postOrder (Node x lt rt) = postOrder lt @ postOrder rt @ [x]"

primrec inOrder :: "'a tree \<Rightarrow> 'a list" where
  "inOrder (Tip x) = [x]"
| "inOrder (Node x lt rt) = inOrder lt @ [x] @ inOrder rt"

value "preOrder test_tree"
value "postOrder test_tree"
value "inOrder test_tree"

text \<open>Define a function @{term mirror} that returns the mirror image of an@{text "'a tree"}.\<close>

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror (Tip x) = (Tip x)"
| "mirror (Node x lt rt) = (Node x (mirror rt) (mirror lt))"

text \<open>Suppose that @{term xOrder} and @{term yOrder} are tree traversal
functions chosen from @{term preOrder}, @{term postOrder}, and @{term inOrder}.
Formulate and prove all valid properties of the form \mbox{@{text "xOrder
(mirror xt) = rev (yOrder xt)"}}.\<close>

lemma "preOrder (mirror xt) = rev (preOrder xt)"
  oops

lemma "preOrder (mirror xt) = rev (inOrder xt)"
  oops

lemma "preOrder (mirror xt) = rev (postOrder xt)"
  by (induction xt) auto

lemma "inOrder (mirror xt) = rev (preOrder xt)"
  oops

lemma "inOrder (mirror xt) = rev (inOrder xt)"
  by (induction xt) auto

lemma "inOrder (mirror xt) = rev (postOrder xt)"
  oops

lemma "postOrder (mirror xt) = rev (preOrder xt)"
  by (induction xt) auto

lemma "postOrder (mirror xt) = rev (inOrder xt)"
  oops

lemma "postOrder (mirror xt) = rev (postOrder xt)"
  oops

text \<open>Define the functions @{term root}, @{term leftmost} and @{term
rightmost}, that return the root, leftmost, and rightmost element respectively.\<close>

primrec root :: "'a tree \<Rightarrow> 'a" where
  "root (Tip x) = x"
| "root (Node x lt rt) = x"

primrec leftmost :: "'a tree \<Rightarrow> 'a" where
  "leftmost (Tip x) = x"
| "leftmost (Node x lt rt) = leftmost lt"

primrec rightmost :: "'a tree \<Rightarrow> 'a" where
  "rightmost (Tip x) = x"
| "rightmost (Node x lt rt) = rightmost rt"


text \<open>Prove (or let Isabelle disprove) the theorems that follow.
You may have to prove some lemmas first.\<close>

lemma [simp]: "inOrder xt \<noteq> []"
  by (induction xt) auto

theorem "last (inOrder xt) = rightmost xt"
  by (induction xt) auto

theorem "hd (inOrder xt) = leftmost xt"
  by (induction xt) auto

theorem "hd (preOrder xt) = last (postOrder xt)"
  by (induction xt) auto

theorem "hd (preOrder xt) = root xt"
  by (induction xt) auto

theorem "hd (inOrder xt) = root xt"
  oops

theorem "last (postOrder xt) = root xt"
  by (induction xt) auto

end