theory Exercise74 imports Big_Step Small_Step begin

inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x, s) \<leadsto> N (s x)" |
"(Plus (N i) (N j), s) \<leadsto> N (i + j)" |
"(a1, s) \<leadsto> a1' \<Longrightarrow> ((Plus a1 a2), s) \<leadsto> (Plus a1' a2)" |
"(a2, s) \<leadsto> a2' \<Longrightarrow> ((Plus (N i) a2), s) \<leadsto> (Plus (N i) a2')"

code_pred astep .

values "{c' | c'. ((Plus (N 42) (N 42)), <''x'' := 42>) \<leadsto> c'}"

values "{c' | c'. ((V ''x''), <''x'' := 42>) \<leadsto> c'}"

values "{c' | c'. (Plus (V ''x'') (V ''x''), <''x'' := 42>) \<leadsto> c'}"

values "{c' | c'. (Plus (N 42) (V ''x''), <''x'' := 42>) \<leadsto> c'}"

lemmas astep_induct = astep.induct[split_format(complete)]

declare astep.intros[simp,intro]

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep_induct)
qed auto+

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep_induct)
  fix s x
  show "aval (V x) s = aval (N (s x)) s" by simp
next
  fix i j s
  show "aval (Plus (N i) (N j)) s = aval (N (i + j))s" by simp
next
  fix a1 s a1' a2
  assume H1: "(a1, s) \<leadsto> a1'"
  assume H2: "aval a1 s = aval a1' s"
  show "aval (Plus a1 a2) s = aval (Plus a1' a2) s" using H1 H2 by simp
next
  fix a2 s a2' i
  assume H1: "(a2, s) \<leadsto> a2'"
  assume H2: " aval a2 s = aval a2' s"
  show "aval (Plus (N i) a2) s = aval (Plus (N i) a2') s" using H1 H2 by simp
qed






end