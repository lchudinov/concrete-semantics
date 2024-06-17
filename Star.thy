theory Star imports Main
begin

inductive
  star :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool"
for r where
refl:  "star r x x" |
step:  "r x y ⟹ star r y z ⟹ star r x z"

hide_fact (open) refl step  ― ‹names too generic›

lemma star_trans:
  "star r x y ⟹ star r y z ⟹ star r x z"
proof(induction rule: star.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis star.step)
qed

lemmas star_induct =
  star.induct[of "r:: 'a*'b ⇒ 'a*'b ⇒ bool", split_format(complete)]

declare star.refl[simp,intro]

lemma star_step1[simp, intro]: "r x y ⟹ star r x y"
by(metis star.refl star.step)

code_pred star .

end