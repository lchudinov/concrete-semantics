theory Exercise55 imports Exercise44
begin

lemma "iter r n x y \<Longrightarrow> star r x y "
proof (induction rule: iter.induct)
  case (iter_refl x)
  then show ?case by (rule star.refl)
next
  case (iter_step x y n z)
  then show ?case by (auto intro: star.step)
qed

end