theory Exercise42 imports Main
begin

inductive palindrome ::  "'a list \<Rightarrow> bool" where
palindrome_0: "palindrome []" |
palindrome_1: "palindrome [x]" |
palindrome_x: "palindrome xs \<Longrightarrow> palindrome ([x] @ xs @ [x])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindrome.induct)
  apply (auto)
  done
end