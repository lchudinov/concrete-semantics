theory Exercise95 imports Sec_Typing
begin

fun ok :: "level \<Rightarrow> com \<Rightarrow> bool" where
"ok l SKIP = True" |
"ok l (Assign x a) = ((sec x \<ge> sec a) \<and>  (sec x \<ge> l))" |
"ok l (Seq c1 c2) = ((ok l c1) \<and> (ok l c2))" |
"ok l (If b c1 c2) = ((ok (max (sec b) l) c1) \<and> (ok (max (sec b) l) c2))" |
"ok l (While b c) = ok (max (sec b) l) c"

lemma sec_type_ok: "l \<turnstile> c \<Longrightarrow> ok l c"
proof (induction rule: sec_type.induct)
  case (Skip l)
  then show ?case by simp
next
  case (Assign x a l)
  then show ?case by auto
next
  case (Seq l c\<^sub>1 c\<^sub>2)
  then show ?case by auto
next
  case (If b l c\<^sub>1 c\<^sub>2)
  then show ?case by auto
next
  case (While b l c)
  then show ?case by auto
qed

lemma ok_sec_type: "ok l c \<Longrightarrow> l \<turnstile> c"
proof (induction rule: ok.induct)
  case (1 l)
  then show ?case by simp
next
  case (2 l x a)
  then show ?case by auto
next
  case (3 l c1 c2)
  then show ?case by auto
next
  case (4 l b c1 c2)
  then show ?case by auto
next
  case (5 l b c)
  then show ?case by metis
qed

