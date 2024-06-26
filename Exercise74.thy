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





end