theory Exercise56 imports Main
begin

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x # xs) = {x} \<union> elems xs"

lemma fixes x :: 'a shows "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case sorry
qed


  
