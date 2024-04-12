theory ASM312 imports AExp begin

(* Exercise 3.12. *)

declare [[names_short]]
type_synonym reg = int

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

type_synonym stack = "val list"

fun exec1 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec1 (LDI0 i) _ regs = regs (0 := i)" |
"exec1 (LD0 x) s regs = regs  (0 := s x)" |
"exec1 (MV0 r) _ regs = regs  (r := regs 0)" |
"exec1 (ADD0 r) _ regs = regs(0 := regs 0 + regs r)"

value "exec1 (LDI0 5) (\<lambda>x. 0) (\<lambda>x. 0)"
value "exec1 (LD0 ''a'') (\<lambda>x. 0) (\<lambda>x. 0)"


fun exec :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp (N n) r = [LDI0 n]" |
"comp (V x) r = [LD0  x] @ [MV0 r]" |
"comp (Plus e1 e2) r = comp e1 (r + 1) @ [MV0 (r + 1)] @ comp e2 (r + 2) @ [ADD0 (r + 1)]"

value "comp (Plus (N 1) (N 2)) 0"
value "exec (comp (Plus (N 1) (N 2)) 0) (\<lambda>x. 0) (\<lambda>x. 0) (0)"

value "comp (Plus (N 1) (Plus (N 2) (N 3))) 1"

lemma exec_append [simp] : "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply (induction is1 arbitrary: stk)
  apply (auto)
  done


lemma [simp] : "(r1 > 0) \<and> (r1 < r2) \<Longrightarrow> exec (comp a r2) s rs r1 = rs r1"
  apply (induction a arbitrary: r2 rs)
  apply (auto)
  done

lemma "r > 0 \<Longrightarrow> exec (comp a r) s rs 0 = aval a s"
  apply (induction a arbitrary: r rs)
  apply (auto)
  done

end