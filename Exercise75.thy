theory Exercise75 imports Big_Step
begin

abbreviation "Orb" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Orb b1 b2  \<equiv>  Not (Andb (Not b1) (Not b2))"

lemma "(IF Andb b1 b2 THEN c1 ELSE c2) \<sim> (IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2)"
  by blast

lemma "\<not> (\<forall> b1 b2 c. WHILE Andb b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)" (is "\<not> ?P")
sorry

lemma "\<not> (WHILE Orb b1 b2 DO c) \<sim> (WHILE Or b1 b2 DO c;; WHILE b1 DO c)"
  by blast

end