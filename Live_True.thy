subsection "True Liveness Analysis"

theory Live_True
imports "HOL-Library.While_Combinator" Vars Big_Step
begin

subsubsection "Analysis"

fun L :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"L SKIP X = X" |
"L (x ::= a) X = (if x \<in> X then vars a \<union> (X - {x}) else X)" |
"L (c1;;c2) X = L c1 (L c2 X)" |
"L (IF b THEN c1 ELSE c2) X = vars b \<union> L c1 X \<union> L c2 X" |
"L (WHILE b DO c) X = lfp(\<lambda>Y. vars b \<union> X \<union> L c Y)"

lemma L_mono: "mono (L c)"
proof-
  have "X \<subseteq> Y \<Longrightarrow> L c X \<subseteq> L c Y" for X Y
  proof(induction c arbitrary: X Y)
    case (While b c)
    show ?case
    proof(simp, rule lfp_mono)
      fix Z show "vars b \<union> X \<union> L c Z \<subseteq> vars b \<union> Y \<union> L c Z"
        using While by auto
    qed
  next
    case If thus ?case by(auto simp: subset_iff)
  qed auto
  thus ?thesis by(rule monoI)
qed

lemma mono_union_L:
  "mono (\<lambda>Y. X \<union> L c Y)"
by (metis (no_types) L_mono mono_def order_eq_iff set_eq_subset sup_mono)

lemma L_While_unfold:
  "L (WHILE b DO c) X = vars b \<union> X \<union> L c (L (WHILE b DO c) X)"
by(metis lfp_unfold[OF mono_union_L] L.simps(5))

lemma L_While_pfp: "L c (L (WHILE b DO c) X) \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

lemma L_While_vars: "vars b \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

lemma L_While_X: "X \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

text\<open>Disable \<open>L WHILE\<close> equation and reason only with \<open>L WHILE\<close> constraints:\<close>
declare L.simps(5)[simp del]


subsubsection "Correctness"

theorem L_correct:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> s = t on L c X \<Longrightarrow>
  \<exists> t'. (c,t) \<Rightarrow> t' & s' = t' on X"
proof (induction arbitrary: X t rule: big_step_induct)
  case Skip then show ?case by auto
next
  case Assign then show ?case
    by (auto simp: ball_Un)
next
  case (Seq c1 s1 s2 c2 s3 X t1)
  from Seq.IH(1) Seq.prems obtain t2 where
    t12: "(c1, t1) \<Rightarrow> t2" and s2t2: "s2 = t2 on L c2 X"
    by simp blast
  from Seq.IH(2)[OF s2t2] obtain t3 where
    t23: "(c2, t2) \<Rightarrow> t3" and s3t3: "s3 = t3 on X"
    by auto
  show ?case using t12 t23 s3t3 by auto
next
  case (IfTrue b s c1 s' c2)
  hence "s = t on vars b" and "s = t on L c1 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfTrue(1) have "bval b t" by simp
  from IfTrue.IH[OF \<open>s = t on L c1 X\<close>] obtain t' where
    "(c1, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using \<open>bval b t\<close> by auto
next
  case (IfFalse b s c2 s' c1)
  hence "s = t on vars b" "s = t on L c2 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfFalse(1) have "~bval b t" by simp
  from IfFalse.IH[OF \<open>s = t on L c2 X\<close>] obtain t' where
    "(c2, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using \<open>~bval b t\<close> by auto
next
  case (WhileFalse b s c)
  hence "~ bval b t"
    by (metis L_While_vars bval_eq_if_eq_on_vars subsetD)
  thus ?case using WhileFalse.prems L_While_X[of X b c] by auto
next
  case (WhileTrue b s1 c s2 s3 X t1)
  let ?w = "WHILE b DO c"
  from \<open>bval b s1\<close> WhileTrue.prems have "bval b t1"
    by (metis L_While_vars bval_eq_if_eq_on_vars subsetD)
  have "s1 = t1 on L c (L ?w X)" using  L_While_pfp WhileTrue.prems
    by (blast)
  from WhileTrue.IH(1)[OF this] obtain t2 where
    "(c, t1) \<Rightarrow> t2" "s2 = t2 on L ?w X" by auto
  from WhileTrue.IH(2)[OF this(2)] obtain t3 where "(?w,t2) \<Rightarrow> t3" "s3 = t3 on X"
    by auto
  with \<open>bval b t1\<close> \<open>(c, t1) \<Rightarrow> t2\<close> show ?case by auto
qed
