(* Recursive Functions *)
theory RecursiveFunctions
  imports Main
begin
fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

lemma "div2 n = n div 2"
  apply (induction n rule: div2.induct)
  apply (auto)
  (*
    An application of auto finishes the proof. Had we used ordinary structural
    induction on n, the proof would have needed an additional case analysis in
    the induction step.
  *)
  done

end
