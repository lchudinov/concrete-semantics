theory ASM imports AExp begin

declare [[names_short]]

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD x) s stk = s(x) # stk" |
"exec1 ADD _ ( j # i # stk) = (i + j) # stk"

value "exec1 (LOAD x) (\<lambda>x. 0) []"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_append [simp] : "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply (induction is1 arbitrary: stk)
  apply (auto)
  done

lemma "exec (comp a) s stk = aval a s # stk"
  apply (induction a arbitrary: stk)
  apply (auto)
  done

end