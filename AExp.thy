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

text \<open>A little syntax magic to write larger states compactly:\<close>

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

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

lemma aval_asimp[simp]: "aval (asimp a) s = aval a s"
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

(* Exercise 3.3. *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = (N n)" |
"subst x a (V v) = (if x = v then a else (V v))" |
"subst x a (Plus a1 a2) = (Plus (subst x a a1) (subst x a a2))"

value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))"

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  apply (auto simp add: aval_plus)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (induction a1)
  apply (auto simp add: subst_lemma)
  done

(* Exercise 3.4. in file AExp3.4 *)

(* Exercise 3.5. *)
datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | Inc2 vname

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
"aval2 (N2 n) s =  (n, s)" |
"aval2 (V2 x) s = (s x, s)" |
"aval2 (Inc2 x) s = (s x, s(x := s x + 1))" |
"aval2 (Plus2 a1 a2) s = (case aval2 a1 s of
                         (n1, s1) \<Rightarrow> (case aval2 a2 s1 of
                                     (n2, s2) \<Rightarrow> (n1 + n2, s2)))"

datatype aexp3 = N3 int | V3 vname | Plus3 aexp3 aexp3 | Inc3 vname | Div3 aexp3 aexp3

fun aval3 :: "aexp3 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval3 (N3 n) s =  Some (n, s)" |
"aval3 (V3 x) s = Some (s x, s)" |
"aval3 (Inc3 x) s = Some (s x, s(x := s x + 1))" |
"aval3 (Plus3 a1 a2) s = (case aval3 a1 s of
                         Some (n1, s1) \<Rightarrow> (case aval3 a2 s1 of
                                          Some (n2, s2) \<Rightarrow> Some (n1 + n2, s2) |
                                          None \<Rightarrow> None)|
                         None \<Rightarrow> None)" |
"aval3 (Div3 a1 a2) s = (case aval3 a1 s of
                         Some (n1, s1) \<Rightarrow> (case aval3 a2 s1 of
                                          Some (n2, s2) \<Rightarrow> (if n2 = 0 then None else Some (n1 div n2, s2)) |
                                          None \<Rightarrow> None)|
                         None \<Rightarrow> None)"

value "aval3 (Div3 (N3 6) (N3 3)) (\<lambda>x. 0)"

(* Exercise 3.6. *)
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl n) s =  n" |
"lval (Vl x) s = s x" |
"lval (Plusl a1 a2) s = lval a1 s + lval a2 s" |
"lval (LET x e1 e2) s = lval e2 (s(x := lval e1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = N n" |
"inline (Vl x) = V x" |
"inline (Plusl a1 a2) = Plus (inline a1) (inline a2)" |
"inline (LET x e1 e2) = subst x (inline e1) (inline e2)"

lemma "lval l s = aval (inline l) s"
  apply (induction l arbitrary: s rule: inline.induct)
  apply (auto simp add: subst_lemma)
  done

end
