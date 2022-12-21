theory ex01
  imports Main

begin

text \<open>For simplicity we sort natural numbers.\<close>

text \<open>The task is to define insertion sort and prove its correctness. 
      The following functions are required:\<close>
 
primrec insort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  where
    "insort a [] = [a]"
  | "insort a (x # xs) = (if a \<le> x then a # x # xs else x # insort a xs)"

primrec sort :: "nat list \<Rightarrow> nat list"
  where
    "sort [] = []"
  | "sort (x # xs) = insort x (sort xs)"

primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "le n [] = True"
  | "le n (x # xs) = (n \<le> x \<and> le n xs)"

primrec ge :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "ge n [] = True"
  | "ge n (x # xs) = (n \<ge> x \<and> ge n xs)"

primrec sorted :: "nat list \<Rightarrow> bool"
  where
    "sorted [] = True"
  | "sorted (x # xs) = (le x xs \<and> sorted xs)"

text \<open>
  In your definition, @{term "insort x xs"} should insert a number @{term x}
  into an already sorted list @{text xs}, and @{term "sort ys"} should build on
  @{text insort} to produce the sorted version of @{text ys}.

  To show that the resulting list is indeed sorted we need a predicate @{term
  sorted} that checks if each element in the list is less or equal to the
  following ones; @{term "le n xs"} should be true iff @{term n} is less or
  equal to all elements of @{text xs}.
\<close>

text \<open>
  Start out by showing a monotonicity property of @{term le}.  For technical
  reasons the lemma should be phrased as follows:
\<close>

lemma [simp]: "x \<le> y \<Longrightarrow> le y xs \<longrightarrow> le x xs"
  by (induction xs) auto

text \<open>
  Now show the following correctness theorem:
\<close>

lemma [simp]: "le x (insort a xs) = (x \<le> a \<and> le x xs)"
  by (induction xs) auto

lemma [simp]: "sorted (insort a xs) = sorted xs"
  by (induction xs) auto

theorem "sorted (sort xs)"
  by (induction xs) auto

text \<open>
  This theorem alone is too weak.  It does not guarantee that the sorted list
  contains the same elements as the input.  In the worst case, @{term sort}
  might always return @{term"[]"}~-- surely an undesirable implementation of
  sorting.

  Define a function @{term "count xs x"} that counts how often @{term x} occurs
  in @{term xs}.
\<close>

primrec count :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "count [] a = 0"
  | "count (x # xs) a = (if a = x then Suc (count xs a) else count xs a)"

text \<open>Show that\<close>

lemma [simp]: "count (insort y xs) x = (if x = y then Suc (count xs x) else count xs x)"
  by (induction xs) auto

theorem "count (sort xs) x = count xs x"
  by (induction xs) auto

text \<open>
  Our second sorting algorithm uses trees.  Thus you should first define a data
  type @{text bintree} of binary trees that are either empty or consist of a
  node carrying a natural number and two subtrees.
\<close>

datatype bintree = Empty
                 | Node nat bintree bintree

text \<open>
  Define a function @{text tsorted} that checks if a binary tree is sorted.  It
  is convenient to employ two auxiliary functions @{text tge}/@{text tle} that
  test whether a number is greater-or-equal/less-or-equal to all elements of a
  tree.

  Finally define a function @{text tree_of} that turns a list into a sorted
  tree.  It is helpful to base @{text tree_of} on a function @{term "ins n b"}
  that inserts a number @{term n} into a sorted tree @{term b}.
\<close>

primrec tge :: "bintree \<Rightarrow> nat \<Rightarrow> bool"
  where
    "tge Empty a = True"
  | "tge (Node x lt rt) a = (a \<ge> x \<and> tge lt a \<and> tge rt a)"

primrec tle :: "bintree \<Rightarrow> nat \<Rightarrow> bool"
  where
    "tle Empty a = True"
  | "tle (Node x lt rt) a = (a \<le> x \<and> tle lt a \<and> tle rt a)"

primrec tsorted :: "bintree \<Rightarrow> bool"
  where
    "tsorted Empty = True"
  | "tsorted (Node x lt rt) = (tsorted lt \<and> tsorted rt \<and> tge lt x \<and> tle rt x)"

primrec ins :: "nat \<Rightarrow> bintree \<Rightarrow> bintree"
  where
    "ins a Empty = (Node a Empty Empty)"
  | "ins a (Node x lt rt) = (if a \<le> x then (Node x (ins a lt) rt) else (Node x lt (ins a rt)))" 

primrec tree_of :: "nat list \<Rightarrow> bintree"
  where
    "tree_of [] = Empty"
  | "tree_of (x # xs) = ins x (tree_of xs)"

text \<open>Show\<close>

lemma [simp]: "tge (ins a t) x = (a \<le> x \<and> tge t x)"
  by (induction t) auto

lemma [simp]: "tle (ins a t) x = (a \<ge> x \<and> tle t x)"
  by (induction t) auto

lemma [simp]: "tsorted (ins a t) = tsorted t"
  by (induction t) auto

theorem [simp]: "tsorted (tree_of xs)"
  by (induction xs) auto

text \<open>
  Again we have to show that no elements are lost (or added).  As for lists,
  define a function @{term "tcount x b"} that counts the number of occurrences
  of the number @{term x} in the tree @{term b}.
\<close>

primrec tcount :: "bintree \<Rightarrow> nat \<Rightarrow> nat"
  where
    "tcount Empty a = 0"
  | "tcount(Node x lt rt) a = (if a = x then Suc (tcount lt a + tcount rt a) else tcount lt a + tcount rt a)"

text \<open>
  Show
\<close>

lemma [simp]: "tcount (ins y t) x = (if x = y then Suc (tcount t x) else tcount t x)"
  by (induction t) auto

theorem "tcount (tree_of xs) x = count xs x"
  by (induction xs) auto

text \<open>
  Now we are ready to sort lists.  We know how to produce an ordered tree from
  a list.  Thus we merely need a function @{text list_of} that turns an
  (ordered) tree into an (ordered) list.  Define this function and prove
\<close>

primrec list_of :: "bintree \<Rightarrow> nat list"
  where
    "list_of Empty = []"
  | "list_of (Node x lt rt) = list_of lt @ [x] @ list_of rt"

lemma [simp]: "le a (xs @ ys) = (le a xs \<and> le a ys)"
  by (induction xs) auto

lemma [simp]: "ge a (xs @ ys) = (ge a xs \<and> ge a ys)"
  by (induction xs) auto

lemma [simp]: "sorted (xs @ a # ys) = (sorted xs \<and> sorted ys \<and> ge a xs \<and> le a ys)"
  by (induction xs) auto

lemma [simp]: "ge x (list_of t) = tge t x"
  by (induction t) auto

lemma [simp]: "le x (list_of t) = tle t x"
  by (induction t) auto

lemma [simp]: "sorted (list_of t) = tsorted t"
  by (induction t) auto

theorem "sorted (list_of (tree_of xs))"
  by auto

lemma [simp]: "count (xs @ ys) n = count xs n + count ys n"
  by (induction xs) auto

lemma [simp]: "count (list_of t) n = tcount t n"
  by (induction t) auto

theorem "count (list_of (tree_of xs)) n = count xs n"
  by (induction xs) auto

text \<open>
  Hints:
  \begin{itemize}
  \item
  Try to formulate all your lemmas as equations rather than implications
  because that often simplifies their proof.  Make sure that the right-hand
  side is (in some sense) simpler than the left-hand side.
  \item
  Eventually you need to relate @{text sorted} and @{text tsorted}.  This is
  facilitated by a function @{text ge} on lists (analogously to @{text tge} on
  trees) and the following lemma (that you will need to prove):\\
  @{term[display] "sorted (a@x#b) = (sorted a \<and> sorted b \<and> ge x a
  \<and> le x b)"}
  \end{itemize}
\<close>

end