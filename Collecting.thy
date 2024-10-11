subsection "Collecting Semantics of Commands"

theory Collecting imports Complete_Lattice Big_Step ACom
begin

subsubsection "The generic Step function"

notation
  sup (infixl "\<squnion>" 65) and
  inf (infixl "\<sqinter>" 70) and
  bot ("\<bottom>") and
  top ("\<top>")

context
  fixes asem :: "vname \<Rightarrow> aexp \<Rightarrow> 'a \<Rightarrow> 'a::sup"
  fixes bsem :: "bexp \<Rightarrow> 'a \<Rightarrow> 'a"
begin
fun Step :: "'a \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"Step S (SKIP {Q}) = (SKIP {S})" |
"Step S (x ::= e {Q}) = x ::= e {asem x e S}" |
"Step S (C1;;C2) = Step S C1;; Step (post C1) C2" |
"Step S (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) = 
  IF b THEN {bsem b S} Step P1 C1 ELSE {bsem (Not b) S} Step P2 C2 {post C1 \<squnion> post C2 }" |
"Step S ({I} WHILE b DO {P} C {Q}) =
  {S \<squnion> post C} WHILE b DO {bsem b I} Step P C {bsem (Not b) I}"
end

lemma strip_Step[simp]: "strip(Step asem bsem S C) = strip C"
by(induct C arbitrary: S) auto




end