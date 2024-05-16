theory Exercise51 imports Main
begin

lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof -
  show ?thesis using assms by blast
qed


lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume Z: "\<not> T x y"
  from this and T have "T y x" by auto
  from this and TA have "A y x" by auto
  from this and assms(4) and A have "x = y" by auto
  from this and T have "T x y" by auto
  from this and Z show "False" by auto
qed


  



