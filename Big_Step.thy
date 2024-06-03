theory Big_Step imports Com begin

inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
Skip: "(Skip,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow> s2; (c2,s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> s3" |
IfTrue: "\<lbrakk> bval b s; (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not> bval b s; (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
WhileFalse: "\<not> bval b s \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s" |
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

end