theory ASM311 imports AExp begin

(* Exercise 3.11. *)

declare [[names_short]]
type_synonym reg = int

datatype instr = LDI int reg | LD vname reg | ADD reg reg

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec1 (LDI i r) _ regs = regs (r:=i)" |
"exec1 (LD x r) s regs = regs (r:=(s x))" |
"exec1 (ADD r1 r2) _ regs = regs(r1 := (regs r1) + (regs r2))"

value "exec1 (LDI 5 1) (\<lambda>x. 0) (\<lambda>x. 0)"
value "exec1 (LD ''a'' 1) (\<lambda>x. 0) (\<lambda>x. 0)"


fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
"comp (N n) r = [LDI n r]" |
"comp (V x) r = [LD  x r]" |
"comp (Plus e1 e2) r = comp e1 r @ comp e2 (r + 1) @ [ADD r (r + 1)]"

value "comp (Plus (N 1) (Plus (N 2) (N 3))) 0"

lemma exec_append [simp] : "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply (induction is1 arbitrary: stk)
  apply (auto)
  done

lemma [simp] : "r1 < r2 \<Longrightarrow> exec (comp a r2) s rs r1 = rs r1"
  apply (induction a arbitrary: r2 rs)
  apply (auto)
  done

lemma "exec (comp a r) s rs r = aval a s"
  apply (induction a arbitrary: r rs)
  apply (auto)
  done

end