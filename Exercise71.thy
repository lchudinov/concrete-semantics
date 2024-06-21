theory Exercise71 imports Big_Step begin

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (x ::= a) = {x}" |
"assigned (c1;;c2) = (assigned c1) \<union> (assigned c2)" |
"assigned (IF b THEN c1 ELSE c2) = (assigned c1) \<union> (assigned c2)" |
"assigned (WHILE b DO c) = assigned c"

lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"
apply (induction rule: big_step_induct)
apply (auto)
done

end