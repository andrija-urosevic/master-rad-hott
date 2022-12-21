theory ex05
  imports Main

begin


text \<open>Define a function @{term occurs}, such that @{term"occurs x xs"} is
the number of occurrences of the element @{term x} in the list @{term xs}.\<close>

primrec occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "occurs a [] = 0"
| "occurs a (x # xs) = (if x = a then 1 else 0) + occurs a xs"


text \<open>Prove (or let Isabelle disprove) the lemmas that follow. You may have
to prove additional lemmas first.  Use the @{text "[simp]"}-attribute
only if the equation is truly a simplification and is necessary for
some later proof.\<close>

lemma occurs_append [simp]: "occurs a (xs @ ys) = occurs a xs + occurs a ys"
  by (induction xs) auto

lemma "occurs a xs = occurs a (rev xs)"
  by (induction xs) auto

lemma "occurs a xs <= length xs"
  by (induction xs) auto

text \<open>Function @{text map} applies a function to all elements of a list:
@{text"map f [x\<^isub>1,\<dots>,x\<^isub>n] = [f x\<^isub>1,\<dots>,f x\<^isub>n]"}.\<close>

lemma "occurs a (map f xs) = occurs (f a) xs"
  oops

text \<open>Function @{text"filter :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"} is defined
by @{thm[display]filter.simps[no_vars]} Find an expression @{text e}
not containing @{text filter} such that the following becomes a true
lemma, and prove it:\<close>

lemma "occurs a (filter P xs) = (if P a then occurs a xs else 0)"
  by (induction xs) auto

text\<open>With the help of @{term occurs}, define a function @{term remDups}
that removes all duplicates from a list.\<close>

primrec remDups :: "'a list \<Rightarrow> 'a list" where
  "remDups [] = []"
| "remDups (x # xs) = (if occurs x xs > 0 then remDups xs else x # remDups xs)"


text\<open>Find an expression @{text e} not containing @{text remDups} such that
the following becomes a true lemma, and prove it:\<close>

lemma occurs_remDups: "occurs x (remDups xs) = min 1 (occurs x xs)"
  by (induction xs) auto

text\<open>
With the help of @{term occurs} define a function @{term unique}, such
that @{term "unique xs"} is true iff every element in @{term xs}
occurs only once.\<close>

primrec unique :: "'a list \<Rightarrow> bool" where
  "unique [] = True"
| "unique (x # xs) = (occurs x xs = 0 \<and> unique xs)"


text \<open>Show that the result of @{term remDups} is @{term unique}.\<close>

lemma "unique (remDups xs)"
  by (induction xs) (auto simp add: occurs_remDups)

end