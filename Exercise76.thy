theory Exercise76 imports Big_Step
begin

abbreviation "DoWhile" :: "com \<Rightarrow> bexp \<Rightarrow> com"  ("(DO _/ WHILE _)"  [0, 61] 61) where
"DoWhile c b  \<equiv>  c ;; WHILE b DO c"

fun dewhile :: "com \<Rightarrow> com" where
"dewhile SKIP = SKIP" |
"dewhile (c1;; c2) = ((dewhile c1);; (dewhile c2))" |
"dewhile (v ::= a) = (v ::= a)" |
"dewhile (IF b THEN c1 ELSE c2) = (IF b THEN (dewhile c1) ELSE (dewhile c2))" |
"dewhile (WHILE b DO c) = (IF b THEN (DO c WHILE b) ELSE SKIP)"

lemma "dewhile c \<sim> c"
proof (induction rule: dewhile.induct)
qed auto+

end