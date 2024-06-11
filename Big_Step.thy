theory Big_Step imports Com begin

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow> s2; (c2,s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> s3" |
IfTrue: "\<lbrakk> bval b s; (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not> bval b s; (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
WhileFalse: "\<not> bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue: "\<lbrakk> bval b s1; (c,s1) \<Rightarrow> s2; (WHILE b DO c, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow> s3"

schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
  apply (rule Seq)
  apply (rule Assign)
  apply (simp)
  apply (rule Assign)
  done

thm ex[simplified]

code_pred big_step .

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"

values "{map t[''x'', ''y''] |t. (''x'' ::= N 2, \<lambda>_. 0) \<Rightarrow> t}"

declare big_step.intros [intro]

thm big_step.induct

lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm SkipE

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
  by blast

thm IfTrue

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t" shows "t = s"
proof -
  from assms show ?thesis
  proof cases
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

lemma assign_simp: "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

lemma Seq_assoc: "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
  c1: "(c1, s) \<Rightarrow> s1" and
  c2: "(c2, s1) \<Rightarrow> s2" and
  c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed

abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall> s t. (c,s) \<Rightarrow> t = (c',s) \<Rightarrow> t)"
  
lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
  by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
  by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
  by blast

lemma sim_while_cong[simp]: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
  by blast

lemma sim_relf: "c \<sim> c" by simp
lemma sim_sym: "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto


theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+

theorem "(c,s) \<Rightarrow> t  \<Longrightarrow>  (c,s) \<Rightarrow> t'  \<Longrightarrow>  t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  fix b c s s1 t t'
  assume "bval b s" and "(c,s) \<Rightarrow> s1" and "(WHILE b DO c,s1) \<Rightarrow> t"
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s1"
  assume IHw: "\<And>t'. (WHILE b DO c,s1) \<Rightarrow> t' \<Longrightarrow> t' = t"
  assume "(WHILE b DO c,s) \<Rightarrow> t'"
  with \<open>bval b s\<close> obtain s1' where
      c: "(c,s) \<Rightarrow> s1'" and
      w: "(WHILE b DO c,s1') \<Rightarrow> t'"
    by auto
  from c IHc have "s1' = s1" by blast
  with w IHw show "t' = t" by blast
qed blast+

end