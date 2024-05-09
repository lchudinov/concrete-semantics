theory Exercise45 imports Main
begin

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S_e: "S []" |
S_aSb: "S xs \<Longrightarrow> S (y # xs @ [z])" |
S_SS: "S xs \<Longrightarrow> S ys \<Longrightarrow> S (xs @ ys)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_e: "T []" |
T_TaTb: "T xs \<Longrightarrow> T ys \<Longrightarrow> T (xs @ [x] @ ys @ [y])"

lemma [simp]: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  apply (auto intro: T_e T_TaTb S_e S_aSb S_SS)
  done


lemma [simp]: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
  apply (auto intro: T_e T_TaTb S_e S_aSb S_SS)
  sorry

end