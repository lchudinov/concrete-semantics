theory Exercise44 imports InductiveDefinitions45
begin

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_refl: "iter r 0 x x" |
iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply (induction rule: star.induct)
  apply (auto intro: iter_refl iter_step)
  done

end