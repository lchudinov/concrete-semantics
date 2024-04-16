theory Exercise41 imports Main
begin
declare [[names_short]]

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun "set" :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l v r) = (set l) \<union> {v} \<union> (set r)"

value "set (Node Tip (3::int) Tip)"

fun "ord" :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l v r) = (ord l \<and> ord r \<and> (\<forall> x \<in> (set l). (x < v)) \<and> (\<forall> x \<in> (set r). (x \<ge> v)))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l v r) = (if x < v then (Node (ins x l) v r) else (Node l v (ins x r)))"

lemma [simp] : "set (ins x t) = {x} \<union> set t"
  apply (induction t)
  apply (auto)
  done

lemma "ord t \<Longrightarrow> ord (ins i t)"
  apply (induction t arbitrary: i)
  apply (auto)
  done

end