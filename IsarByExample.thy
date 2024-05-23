theory IsarByExample imports Main
begin

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists> a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

thm "surj_def"

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists> a. {x. x \<notin> f x} = f a" by (simp add: surj_def)
  from this show "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by (simp add: surj_def)
  thus "False" by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by (simp add: surj_def)
  thus "False" by blast
qed


lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by (auto simp add: surj_def) (* hence = then have *)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast (* thus = then show *)
qed

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  have "\<exists>k'. a = b*k'" if asm: "a+b = b*k" for k
  proof
    show "a = b*(k-1)" using asm by (simp add:algebra_simps)
  qed
  then show ?thesis using assms by(auto simp add: dvd_def) 
qed

lemma "length (tl xs) = length xs -1"
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

lemma "length (tl xs) = length xs -1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n assume "\<Sum>{0..n::nat} = n*(n+1) div 2"
  thus "\<Sum>{0..Suc n} = Suc n*(Suc n+1) div 2" by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  let ?case = "?P 0"
  show ?case by simp
next
  fix n assume Suc: "?P(n)"
  let ?case = "?P(Suc n)"
  show ?case by (simp add: Suc)
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule:ev.induct)
  case ev0
  show ?case by simp
next
  case evSS
  thus ?case by simp
qed

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  case ev0 show ?case by simp
next
  case (evSS m)
  have "evn(Suc(Suc m)) = evn m" by simp
  thus ?case using `evn m` by blast
qed

lemma "ev n \<Longrightarrow> ev(n - 2)"
proof -
  assume "ev n"
  from this have "ev(n-2)"
  proof cases
    case ev0 thus "ev(n - 2)" by (simp add: ev.ev0)
  next
    case (evSS m) thus "ev(n - 2)" by (simp add: ev.evSS)
  qed
  thus ?thesis by auto
qed

lemma "\<not> ev(Suc 0)"
proof
  assume "ev(Suc 0)" then show False by cases
qed

lemma "\<not> ev(Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  from this have "ev (Suc 0)" by cases
  from this show False by cases
qed

(*
lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof (induction "Suc m" arbitrary: m rule:ev.induct)
  fix n assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev (Suc n)"
  proof - contradiction
    assume "ev(Suc n)"
    thus False
*)

end



