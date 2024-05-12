theory Exercise47 imports ASM
begin

declare [[names_short]]

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
ok_empty: "ok n [] n" |
ok_loadi: "ok n is n' \<Longrightarrow> ok n (is @ [LOADI k]) (Suc n')" |
ok_load : "ok n is n' \<Longrightarrow> ok n (is @ [LOAD x]) (Suc n')" | 
ok_add : "ok n is (Suc (Suc n')) \<Longrightarrow> ok n (is @ [ADD]) (Suc n')"

lemma exec_append: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
apply (induction is1 arbitrary:stk)
apply (auto split:option.split)
done

lemma "\<lbrakk>ok n is n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec is s stk ) = n'"
  apply (induction arbitrary: stk rule: ok.induct)
  apply (simp_all)
  sorry

end
  