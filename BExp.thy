theory BExp
imports AExp
begin
declare [[names_short]]

datatype bexp = Bc bool | Not bexp | Andb bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (Andb b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" | 
"and b1 b2 = Andb b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)" |
"less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (Andb b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

(* Exercise 3.7. *)
fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 = (Andb (Not (Less a1 a2)) (Not (Less a2 a1)))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = (Not (Less a2 a1))"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply (induction a1)
  apply (auto)
  done

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply (induction a1)
  apply (auto)
  done

(* Exercise 3.8. *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b)s = b" |
"ifval (If i1 i2 i3) s = (if (ifval i1 s) then (ifval i2 s) else (ifval i3 s))" |
"ifval (Less2 a1 a2) s = ((aval a1 s) < (aval a2 s))"

fun orB :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"orB p q = Not (Andb (Not p) (Not q))"

fun impliesB :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"impliesB p q = orB (Not p) q"

fun IfB :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"IfB a b c = Andb (impliesB a b) (impliesB (Not a) c)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b) = (Bc2 b)" |
"b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))" |
"b2ifexp (Andb b1 b2) = (If (b2ifexp b1) (b2ifexp b2) (Bc2 False))" |
"b2ifexp (Less a1 a2) = (Less2 a1 a2)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = Bc b" |
"if2bexp (If i1 i2 i3) = IfB (if2bexp i1) (if2bexp i2) (if2bexp i3)" |
"if2bexp (Less2 a1 a2) = (Less a1 a2)"

value "if2bexp (If (Bc2 True) (Bc2 True) (Bc2 True))"

lemma b2if_correct : "bval b s = ifval (b2ifexp b) s"
  apply (induction b)
  apply (auto)
  done

lemma if2bexp_correct : "ifval b s = bval (if2bexp b) s"
  apply (induction b)
  apply (auto)
  done

(* Exercise 3.9 *)
datatype pbexp = VAR vname | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NEG b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NEG (VAR x)) = True" |
"is_nnf (NEG b) = False" |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (NEG (VAR x)) = (NEG (VAR x))" |
"nnf (NEG (NEG b)) = nnf b" |
"nnf (NEG (AND b1 b2)) = (OR (nnf (NEG b1)) (nnf (NEG b2)))" |
"nnf (NEG (OR b1 b2)) = (AND (nnf (NEG b1)) (nnf (NEG b2)))" |
"nnf (VAR x) = (VAR x)" |
"nnf (AND b1 b2) = (AND (nnf b1) (nnf b2))" | 
"nnf (OR b1 b2) = (OR (nnf b1) (nnf b2))"

lemma "pbval (nnf b) s = pbval b s"
  apply (induction b rule: nnf.induct)
  apply (auto)
  done

lemma "pbval (nnf b) s = pbval b s"
  apply (induction b rule: nnf.induct)
  apply (auto)
  done

lemma "is_nnf (nnf b)"
  apply (induction b rule: nnf.induct)
  apply (auto)
  done

fun andb :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"andb b1 (OR b2 b3) = OR (andb b1 b2) (andb b1 b3)" |
"andb (OR b1 b2) b3 = OR (andb b1 b3) (andb b2 b3)" |
"andb b1 b2 = AND b1 b2"

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = (VAR x)" |
"dnf_of_nnf (NEG b) = (NEG b)" |
"dnf_of_nnf (OR b1 b2) = (OR (dnf_of_nnf b1) (dnf_of_nnf b2))" |
"dnf_of_nnf (AND b1 b2) = andb (dnf_of_nnf b1) (dnf_of_nnf b2)"

fun no_or :: "pbexp \<Rightarrow> bool" where
"no_or (VAR x) = True" |
"no_or (NEG b) = True" |
"no_or (OR b1 b2) = False" |
"no_or (AND b1 b2) = (no_or b1 \<and> no_or b2)"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NEG b) = True" |
"is_dnf (AND b1 b2) = (no_or b1 \<and> no_or b2)" |
"is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)"

lemma [simp] : "pbval (andb b1 b2) s = pbval (AND b1 b2) s"
  apply (induction b1 b2 rule: andb.induct)
  apply (auto)
  done

lemma "(pbval (dnf_of_nnf b) s = pbval b s)"
  apply (induction b)
  apply (auto)
  done

lemma [simp] : "is_nnf (NEG b) \<Longrightarrow> no_or b"
  apply (induction b)
  apply (auto)
  done

lemma [simp] : "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (andb b1 b2)"
  apply (induction b1 b2 rule: andb.induct)
  apply (auto)
  done

lemma "(is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b))"
  apply (induction b rule: dnf_of_nnf.induct)
  apply (auto)
  done

end

