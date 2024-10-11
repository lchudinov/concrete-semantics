theory Hoare_Examples imports Hoare
begin

hide_const (open) sum

text\<open>Summing up the first \<open>x\<close> natural numbers in variable \<open>y\<close>.\<close>

fun sum :: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1) + i)"

lemma sum_simps[simp]:
  "0 < i \<Longrightarrow> sum i = sum (i - 1) + i"
  "i \<le> 0 \<Longrightarrow> sum i = 0"
  by(simp_all)

declare sum.simps[simp del]

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
      ''x'' ::= Plus (V ''x'') (N (- 1)))"

subsubsection\<open>Proof by Operational Semantics\<close>

text\<open>The behaviour of the loop is proved by induction:\<close>

lemma while_sum:
  "(wsum, s) \<Rightarrow> t \<Longrightarrow> t ''y'' = s ''y'' + sum(s ''x'')"
apply(induction wsum s t rule: big_step_induct)
apply(auto)
  done

lemma sum_via_bigstep:
  assumes "(''y'' ::= N 0;; wsum, s) \<Rightarrow> t"
  shows "t ''y'' = sum (s ''x'')"
proof -
  from assms have "(wsum,s(''y'':=0)) \<Rightarrow> t" by auto
  from while_sum[OF this] show ?thesis by simp
qed

subsubsection\<open>Proof by Hoare Logic\<close>

text\<open>Note that we deal with sequences of commands from right to left,
pulling back the postcondition towards the precondition.\<close>

lemma "\<turnstile> {\<lambda>s. s ''x'' = n} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = sum n}"
  apply (rule Seq)
  prefer 2
  apply(rule While' [where P = "\<lambda>s. (s ''y'' = sum n - sum(s ''x''))"])
  apply(rule Seq)
  prefer 2
  apply(rule Assign)
  apply(rule Assign')
  apply simp
  apply simp
  apply(rule Assign')
  apply simp
done



