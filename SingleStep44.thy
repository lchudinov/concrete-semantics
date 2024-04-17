theory SingleStep44 imports Main
begin

thm conjI
thm conjI[of "a=b" "False"]
thm conjI[of _ "False"]

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
  by (blast intro: le_trans)

thm conjI[OF refl[of "a"] refl[of "b"]]

thm Suc_leD

lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (blast dest: Suc_leD)

end