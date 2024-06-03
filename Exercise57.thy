theory Exercise57 imports Exercise45
begin

fun replicate :: "nat \<Rightarrow> alpha \<Rightarrow> alpha list" where
"replicate 0 _ = []" |
"replicate (Suc n) x = x # replicate n x"

(*
fun balanced :: "nat => alpha list => bool" where
"balanced 0 [] = True" |
"balanced (Suc _) [] = False"

sorry

*)


end