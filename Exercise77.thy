theory Exercise77 imports Small_Step
begin

lemma
 "\<lbrakk> C 0 = c;;d ; \<forall>n. (C n, S n) \<rightarrow> (C (Suc n), S (Suc n))\<rbrakk> \<Longrightarrow> (\<forall>n. \<exists> c1 c2. C n = c1;;d \<and> C (Suc n) = c2;;d \<and> (c1, S n) \<rightarrow> (c2, S (Suc n))) \<or> (\<exists>k. C k = SKIP;;d)"
apply (induction c)
sorry

  
end