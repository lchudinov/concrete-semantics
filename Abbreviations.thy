(* 2.3.3 Abbreviations *)
theory Abbreviations
imports Main
begin
abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"

end