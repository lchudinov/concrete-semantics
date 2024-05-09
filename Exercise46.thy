theory Exercise46 imports AExp
begin

declare [[names_short]]

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
aval_rel_const: "aval_rel (N n) s n" |
aval_rel_var: "aval_rel (V x) s (s x)" |
aval_rel_plus: "aval_rel a1 s v1 \<Longrightarrow> aval_rel a2 s v2 \<Longrightarrow> aval_rel (Plus a1 a2) s (v1 + v2)"

lemma aval_rel_is_aval [simp]: "aval_rel a s v \<Longrightarrow> aval a s = v"
  apply (induction rule: aval_rel.induct)
  apply (auto)
  done

lemma aval_is_aval_rel [simp]: "aval a s = v \<Longrightarrow> aval_rel a s v"
  apply (induction a arbitrary: v)
  apply (simp)
  apply (rule aval_rel_const)
  apply (simp)
  apply (rule aval_rel_var)
  apply (metis AExp.aval.simps(3) aval_rel_plus)
  done

thm "AExp.aval.simps"


lemma "aval_rel a s v \<longleftrightarrow> aval a s = v"
  apply (metis aval_is_aval_rel aval_rel_is_aval)
  done
 