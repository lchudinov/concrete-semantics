theory Exercise72 imports Big_Step begin

fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True" |
"skip (x ::= a) = False" |
"skip (c1;;c2) = (skip c1 \<and> skip c2)" |
"skip (IF b THEN c1 ELSE c2) = (skip c1 \<and> skip c2)" |
"skip (WHILE b DO c) = False"

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
proof (induction c)
  case SKIP show ?case by auto
next
  case (Seq c1 c2)
  then have "c1 \<sim> SKIP" and "c2 \<sim> SKIP" by auto
  then have "(c1;;c2) \<sim> (SKIP;;SKIP)" by blast
  then show "(c1;;c2) \<sim> SKIP" by blast
next
  case (If b c1 c2)
  then have "c1 \<sim> SKIP" and "c2 \<sim> SKIP" by auto
  then have "(IF b THEN c1 ELSE c2) \<sim> (IF b THEN SKIP ELSE SKIP)" by blast
  then show "(IF b THEN c1 ELSE c2) \<sim> SKIP" by blast
qed auto+ 

end