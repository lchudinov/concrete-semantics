theory InductiveDefinitions45 imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0:  "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

thm ev.induct
thm evSS[OF evSS[OF evSS[OF ev0]]]

lemma "ev(Suc(Suc(Suc(Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

lemma "ev m \<Longrightarrow> evn m"
  apply (induction rule: ev.induct)
  by (simp_all)

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule: evn.induct)
  by (simp_all add: ev0 evSS)

declare ev.intros[simp,intro]

end