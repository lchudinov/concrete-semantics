(* 2.3.1 Data Types *)

theory Datatypes
  imports Main
begin

declare [[names_short]]

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror(mirror t) = t"
  apply (induction t)
  apply (auto)
  done

datatype 'a option = None | Some 'a

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a, b) # ps) x = (if a = x then Some b else lookup ps x)"

(* Exercise 2.6. *)

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = a # (contents l) @ (contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + (sum_tree l) + (sum_tree r)"

fun sum_list :: "nat list \<Rightarrow> nat" where
"sum_list [] = 0" |
"sum_list (x # xs) = x + sum_list xs"

lemma [simp]: "sum_list t1 + sum_list t2 = sum_list (t1 @ t2)"
  apply (induction t1)
  apply (auto)
  done

lemma "sum_tree t = sum_list (contents t)"
  apply (induction t)
  apply (auto)
  done

(* Exercise 2.7. *)

fun pre_order :: "'a tree \<Rightarrow> 'a list " where
"pre_order Tip = []" |
"pre_order (Node l a r) = a # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list " where
"post_order Tip = []" |
"post_order (Node l a r) = (post_order l) @ (post_order r) @ [a]"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  apply (auto)
  done

end