theory AExp
imports Main
begin
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 0)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) = 
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N (n1 + n2) |
    (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply (auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto simp add: aval_plus)
  done

(* Exercise 3.1. *)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus a1 a2) = 
  (case (optimal a1, optimal a2) of
    (True, True) \<Rightarrow> True |
    (b1, b2) \<Rightarrow> False)"

lemma "optimal (asimp_const a)"
  apply (induction a)
  apply (auto split: aexp.split)
  done

(* Exercise 3.2. *)

fun sum_const :: "aexp \<Rightarrow>  int" where
"sum_const (N n) = n" |
"sum_const (V x) = 0" |
"sum_const (Plus a1 a2) = sum_const a1 + sum_const a2"

fun zero_const :: "aexp \<Rightarrow> aexp" where
"zero_const (N n) = (N 0)" |
"zero_const (V x) = (V x)" |
"zero_const (Plus a1 a2) = (Plus (zero_const a1) (zero_const a2))"

fun full_asimp :: "aexp => aexp" where
"full_asimp a = asimp (Plus (N (sum_const a)) (zero_const a))"

lemma "aval (full_asimp a) s = aval a s"
  apply (induction a)
  apply (auto simp add: aval_plus)
  done

end