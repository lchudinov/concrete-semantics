theory InductionHeuristics
imports Main
begin

declare [[names_short]]

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x # xs) = (rev xs) @ [x]"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev []       ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"


lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
  apply (auto)
  done

(* Exercise 2.9. *)
fun add :: "nat => nat => nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)" 

lemma add_succ [simp] : "add n (Suc m) = Suc (add n m)"
  apply (induction n)
  apply (auto)
  done

lemma "itadd m n = add m n"
  apply (induction m arbitrary: n)
  apply (auto)
  done

end
