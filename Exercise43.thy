theory Exercise43 imports InductiveDefinitions45
begin

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

thm "star.simps"

lemma "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  apply (rule star.refl)
  apply (metis star.simps star_trans)
  done

lemma star'_rev: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
  apply (auto intro: refl' step')
  done

lemma "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  apply (auto simp add: refl' star'_rev)
  done
  
end