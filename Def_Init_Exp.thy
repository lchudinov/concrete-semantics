theory Def_Init_Exp imports Vars
begin

subsection "Initialization-Sensitive Expressions Evaluation"

type_synonym state = "vname \<Rightarrow> val option"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val option" where
"aval (N i) s = Some i" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = 
(case (aval a1 s, aval a2 s) of
  (Some i1, Some i2) \<Rightarrow> Some(i1+i2)| _ \<Rightarrow> None)"

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool option" where
"bval (Bc v) s = Some v" |
"bval (Not b) s = (case bval b s of None \<Rightarrow> None | Some bv \<Rightarrow> Some(\<not> bv))" |
"bval (Andb b1 b2) s = (case (bval b1 s, bval b2 s) of (Some bv1, Some bv2) \<Rightarrow> Some (bv1 & bv2) | _ \<Rightarrow> None)" |
"bval (Less a1 a2) s = (case (aval a1 s, aval a2 s) of (Some i1, Some i2) \<Rightarrow> Some (i1 < i2) | _ \<Rightarrow> None)"

lemma aval_Some: "vars a \<subseteq> dom s \<Longrightarrow> \<exists> i. aval a s = Some i"
by (induct a) auto

lemma bval_Some: "vars b \<subseteq> dom s \<Longrightarrow> \<exists> bv. bval b s = Some bv"
by (induct b) (auto dest!: aval_Some)

end
