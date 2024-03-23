theory add
imports Main
begin

fun add :: "nat => nat => nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02 [simp] : "add m 0 = m"
apply (induction m)
apply (auto)
done

thm add_02

(* Exercise 2.2 *)

lemma add_succ [simp] : "add n (Suc m) = Suc (add n m)"
  apply (induction n)
  apply (auto)
  done

theorem add_comm [simp] : "add m n = add n m"
  apply (induction m)
  apply (auto)
  done
  
theorem add_assoc [simp] : "add (add m n) k = add m (add n k)"
  apply (induction m)
  apply (auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc x) = Suc (Suc (double x))"

theorem double_correct [simp] : "double m = add m m"
  apply (induction m)
  apply (auto)
  done

(* Exercise 2.5 *)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = n + 1 + sum_upto n"

value "sum_upto 5"

theorem sum_upto_n : "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
  apply (auto)
  done

end