theory MyList
  imports Main
begin

declare [[names_short]]

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"
value "rev (Cons a (Cons b Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
  apply (auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply (auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  apply (auto)
  done

theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply (induction xs)
  apply (auto)
  done

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"map f Nil = Nil" |
"map f (Cons x xs) = Cons (f x) (map f xs)"

(* Exercise 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.3 *)
(*
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = 0" |
"count x (Cons x xs) = if (x  x0) then 1 + (count x xs)" else count x xs"
*)

end

