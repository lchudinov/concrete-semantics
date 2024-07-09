theory Exercise78 imports BExp Star
begin

datatype
  com = SKIP
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Repeat com  bexp        ("(REPEAT _/ UNTIL _)"  [61, 0] 61)

value "''x'' ::= Plus (V ''y'') (N 1);; ''y'' ::= N 2"

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow> s2; (c2,s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> s3" |
IfTrue: "\<lbrakk> bval b s; (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not> bval b s; (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
WhileFalse: "\<not> bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue: "\<lbrakk> bval b s1; (c,s1) \<Rightarrow> s2; (WHILE b DO c, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow> s3" |
RepeatFalse:  "\<lbrakk> (c, s) \<Rightarrow> t; \<not> bval b t \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> t" |
RepeatTrue: "\<lbrakk> (c, s) \<Rightarrow> t; bval b t; (REPEAT c UNTIL b, t) \<Rightarrow> t1\<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> t1"

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

inductive_cases RepeatE[elim]: "(REPEAT c UNTIL b,s) \<Rightarrow> t"
thm RepeatE

inductive
  small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c2,s) \<rightarrow> (c2,s)" |
Seq2:    "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "\<not> bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |

Repeat: "(REPEAT c UNTIL b,s) \<rightarrow> (c;; IF b THEN REPEAT c UNTIL b ELSE SKIP,s)"

abbreviation
  small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y" 

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t.
  (''x'' ::= V ''z'';; ''y'' ::= V ''x'',
   <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsubsection\<open>Proof automation\<close>

declare small_step.intros[simp,intro]

text\<open>Rule inversion:\<close>

inductive_cases SkipSE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipSE
inductive_cases AssignSE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignSE
inductive_cases SeqSE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqSE
inductive_cases IfSE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileSE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"
inductive_cases RepeatSE[elim]: "(REPEAT c UNTIL b, s) \<rightarrow> ct"

lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
  done

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
by (blast intro: star.step star_seq2 star_trans)

lemma big_to_small: "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
proof (induction arbitrary: s rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next 
  case Seq show ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue
  thus ?case
    by(metis While seq_comp small_step.IfTrue star.step[of small_step])
next
  case RepeatFalse
  thus ?case
    by (metis Repeat seq_comp star.step[of small_step])
next
  case RepeatTrue
  thus ?case
    by (metis Repeat seq_comp star.step[of small_step])
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_to_big:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
apply (induction cs "(SKIP,t)" rule: star.induct)
apply (auto intro: small1_big_continue)
done

theorem big_iff_small:  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
  by(metis big_to_small small_to_big)

end