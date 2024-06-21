theory Exercise73 imports Big_Step begin

fun deskip :: "com \<Rightarrow> com" where
"deskip (c1;;c2) = (case (deskip c1, deskip c2) of
  (SKIP, SKIP) \<Rightarrow> SKIP |
  (a, SKIP) \<Rightarrow> a |
  (SKIP, b) \<Rightarrow> b |
  (a, b) \<Rightarrow> (a;;b)
  )" |
"deskip (IF b THEN c1 ELSE c2) = (IF b THEN deskip c1 ELSE deskip c2)" |
"deskip (WHILE b DO c) = (WHILE b DO deskip c)" |
"deskip c = c"

value "deskip (SKIP;; WHILE b DO (x ::= a;; SKIP))"

lemma "deskip c \<sim> c"
proof (induction c)
  case SKIP show ?case by auto
next
  case (Seq c1 c2)
  then show "deskip (c1;;c2) \<sim> (c1;;c2)" by blast
next
  case (Assign x a)
  
  
qed auto+ 

end