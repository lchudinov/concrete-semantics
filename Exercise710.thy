theory Exercise710 imports BExp Star
begin

datatype
  com = SKIP
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | THROW
      | Try    com  com         ("(TRY _/ CATCH _)"  [60, 61] 61)

value "''x'' ::= Plus (V ''y'') (N 1);; ''y'' ::= N 2"

inductive
  big_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> (SKIP, s)" |
Assign: "(x ::= a,s) \<Rightarrow> (SKIP, s(x := aval a s))" |
SeqOk: "\<lbrakk> (c1,s1) \<Rightarrow> (SKIP,s2); (c2,s2) \<Rightarrow> (c2',s3) \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> (c2',s3)" |
SeqFail: "(c1,s1) \<Rightarrow> (THROW,s2) \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> (THROW,s2)" |
IfTrue: "\<lbrakk> bval b s; (c1,s) \<Rightarrow> (c1', t) \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> (c1', t)" |
IfFalse: "\<lbrakk> \<not> bval b s; (c2,s) \<Rightarrow> (c2',t) \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> (c2',t)" |
WhileFalse: "\<not> bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> (SKIP,s)" |
WhileTrueOk: "\<lbrakk> bval b s1; (c,s1) \<Rightarrow> (SKIP,s2); (WHILE b DO c, s2) \<Rightarrow> (c'',s3) \<rbrakk> \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow> (c'',s3)" |
WhileTrueFail: "\<lbrakk> bval b s1; (c,s1) \<Rightarrow> (THROW,s2) \<rbrakk> \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow> (THROW,s2)" |
Throw:  "(THROW,s) \<Rightarrow> (THROW, s)" |
TryOk:  "(c1, s) \<Rightarrow> (SKIP,s') \<Longrightarrow> (TRY c1 CATCH c2, s) \<Rightarrow> (SKIP,s')" |
TryFail: "\<lbrakk>(c1,s) \<Rightarrow> (THROW,s'); (c2,s') \<Rightarrow> (c2', s'')\<rbrakk> \<Longrightarrow> (TRY c1 CATCH c2, s) \<Rightarrow> (c2',s'')" 

code_pred big_step .

values "{(c', map t [''x'']) |c' t. (SKIP, \<lambda>_. 0) \<Rightarrow> (c',t)}"

values "{(c', map t [''x'']) |c' t. (SKIP, <''x'' := 42>) \<Rightarrow> (c',t)}"


values "{(c', map t [''x'']) |c' t. (SKIP, <''x'' := 42>) \<Rightarrow> (c',t)}"

values "{(c', map t [''x'']) |c' t. (''x'' ::= N 2, \<lambda>_. 0) \<Rightarrow> (c',t)}"

values "{(c', map t [''x'']) |c' t. (TRY THROW CATCH SKIP, <''x'' := 42>) \<Rightarrow> (c',t)}"

values "{(c', map t [''x'']) |c' t. (THROW;; SKIP, <''x'' := 42>) \<Rightarrow> (c',t)}"

declare big_step.intros [intro]

thm big_step.induct

lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> (SKIP,t)"
thm SkipE

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> (SKIP,t)"
thm AssignE

inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> (c2',t)"
thm SeqE

inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> (c, t)"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE

inductive_cases TryE[elim!]: "(TRY c1 CATCH c2,s) \<Rightarrow> (c, t)"
thm TryE

inductive_cases ThrowE[elim!]: "(THROW,s) \<Rightarrow> (THROW,t)"
thm ThrowE

inductive
  small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c2,s) \<rightarrow> (c2,s)" |
Seq2:    "(THROW;;c2,s) \<rightarrow> (THROW,s)" |
Seq3:    "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "\<not> bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |

TryOk:  "(TRY SKIP CATCH c2, s) \<rightarrow> (SKIP,s)" |
TryFail: "(TRY THROW CATCH c2, s) \<rightarrow> (c2,s)" | 
TryStep:  "(c1, s) \<rightarrow> (c1',s') \<Longrightarrow> (TRY c1 CATCH c2, s) \<rightarrow> (TRY c1' CATCH c2, s')" 



abbreviation
  small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y" 

subsection\<open>Executability\<close>

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t.
  (''x'' ::= V ''z'';;''y'' ::= V ''z'',
   <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"

values "{(c',map t [''x'',''y'',''z'']) |c' t.
  (''x'' ::= V ''z'';; ''y'' ::= V ''x'',
   <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"

values "{(c',map t [''x'',''y'',''z'']) |c' t.
  (''x'' ::= V ''z'';; THROW ;; ''y'' ::= V ''x'',
   <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"

values "{(c',map t [''x'',''y'',''z'']) |c' t.
  (TRY ''x'' ::= V ''z'';; THROW ;; ''y'' ::= V ''x'' CATCH  ''x'' ::= V ''y'' ,
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
thm IfSE
inductive_cases WhileSE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"
thm WhileSE
inductive_cases ThrowSE[elim!]: "(THROW, s) \<rightarrow> ct"
thm ThrowSE
inductive_cases TrySE[elim!]: "(TRY c1 CATCH c2, s) \<rightarrow> ct"
thm TrySE

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp_skip:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
  by (blast intro: star.step star_seq2 star_trans)

lemma seq_comp_throw:
  "(c1,s1) \<rightarrow>* (THROW,s2) \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (THROW,s2)"
  by (blast intro: star.step star_seq2 star_trans)

lemma star_try2: "(c1, s) \<rightarrow>* (c1', s') \<Longrightarrow> (TRY c1 CATCH c2, s) \<rightarrow>* (TRY c1' CATCH c2, s')"
   by (blast intro: star.step star_seq2 star_trans)

lemma try_comp_skip: "(c1, s1) \<rightarrow>* (SKIP, s2) \<Longrightarrow> (TRY c1 CATCH c2, s1) \<rightarrow>* (SKIP, s2)"
  by (blast intro: star.step star_try2 star_trans)

lemma try_comp_throw: "\<lbrakk>(c1, s1) \<rightarrow>* (THROW, s2); (c2, s2) \<rightarrow>* (x, s3)\<rbrakk>
  \<Longrightarrow> (TRY c1 CATCH c2, s1) \<rightarrow>* (x, s3)"
  by (blast intro: star.step star_try2 star_trans)

lemma big_to_small: "cs \<Rightarrow> (SKIP, t) \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
proof (induction arbitrary: s rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next 
  case SeqOk show ?case by (blast intro: seq_comp_skip seq_comp_throw star.step)
next 
  case SeqFail show ?case by (blast intro: seq_comp_skip seq_comp_throw)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrueOk
  thus ?case
    by(metis While seq_comp_skip small_step.IfTrue star.step[of small_step])
next
  case WhileTrueFail
  thus ?case
    by(metis While seq_comp_skip small_step.IfTrue star.step[of small_step])
next
  case TryOk
  thus ?case
    by (metis small_step.TryOk small_step.TryStep star.step[of small_step])
next
  case TryFail
  thus ?case
    by (metis small_step.TryFail  star.step[of small_step])
next
  case Throw
  thus ?case 
    (*by (metis small_step.Throw star.step[of small_step])*)
    sorry
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_to_big_skip:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> (SKIP,t)"
apply (induction cs "(SKIP,t)" rule: star.induct)
apply (auto intro: small1_big_continue)
  done

lemma small_to_big_throw:
  "cs \<rightarrow>* (THROW,t) \<Longrightarrow> cs \<Rightarrow> t"
apply (induction cs "(SKIP,t)" rule: star.induct)
apply (auto intro: small1_big_continue)
done

theorem big_iff_small:  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
  by(metis big_to_small small_to_big)


