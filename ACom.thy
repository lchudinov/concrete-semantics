subsection "Annotated Commands"

theory ACom imports Com
begin

datatype 'a acom =
  SKIP 'a                           ("SKIP {_}" 61) |
  Assign vname aexp 'a              ("(_ ::= _/ {_})" [1000, 61, 0] 61) |
  Seq "('a acom)" "('a acom)"       ("_;;//_"  [60, 61] 60) |
  If bexp 'a "('a acom)" 'a "('a acom)" 'a
    ("(IF _/ THEN ({_}/ _)/ ELSE ({_}/ _)//{_})"  [0, 0, 0, 61, 0, 0] 61) |
  While 'a bexp 'a "('a acom)" 'a
    ("({_}//WHILE _//DO ({_}//_)//{_})"  [0, 0, 0, 61, 0] 61)

notation com.SKIP ("SKIP")

fun strip :: "'a acom \<Rightarrow> com" where
"strip (SKIP {P}) = SKIP" |
"strip (x ::= e {P}) = x ::= e" |
"strip (C1;;C2) = strip C1;; strip C2" |
"strip (IF b THEN {P1} C1 ELSE {P2} C2 {P}) = IF b THEN strip C1 ELSE strip C2" |
"strip ({I} WHILE b DO {P} C {Q}) = WHILE b DO strip C"

fun asize :: "com \<Rightarrow> nat" where
"asize SKIP = 1" |
"asize (x ::= e) = 1" |
"asize (C1;;C2) = asize C1 + asize C2" |
"asize (IF b THEN C1 ELSE C2) = asize C1 + asize C2 + 3" |
"asize (WHILE b DO C) = asize C + 3"

definition shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
"shift f n = (\<lambda>p. f(p+n))"

fun annotate :: "(nat \<Rightarrow> 'a) \<Rightarrow> com \<Rightarrow> 'a acom" where
"annotate f SKIP = SKIP {f 0}" |
"annotate f (x ::= e) = x ::= e {f 0}" |
"annotate f (c1;;c2) = annotate f c1 ;; annotate (shift f (asize c1)) c2" |
"annotate f (IF b THEN c1 ELSE c2) = 
  IF b THEN {f 0} annotate (shift f 1) c1
  ELSE {f(asize c1 + 1)} annotate (shift f (asize c1 + 2)) c2
  {f(asize c1 + asize c2 +2)}" |
"annotate f (WHILE b DO c) =
  {f 0} WHILE b DO {f 1} annotate (shift f 2) c {f(asize c + 2)}"

fun annos :: "'a acom \<Rightarrow> 'a list" where
"annos (SKIP {P}) = [P]" |
"annos (x ::= e {P}) = [P]" |
"annos (C1;;C2) = annos C1 @ annos C2" |
"annos (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) =
  P1 # annos C1 @ P2 # annos C2 @ [Q]" |
"annos ({I} WHILE b DO {P} C {Q}) = I # P # annos C @ [Q]"

definition anno :: "'a acom \<Rightarrow> nat \<Rightarrow> 'a" where
"anno C p = annos C ! p"

definition post :: "'a acom \<Rightarrow>'a" where
"post C = last(annos C)"

fun map_acom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a acom \<Rightarrow> 'b acom" where
"map_acom f (SKIP {P}) = SKIP {f P}" |
"map_acom f (x ::= e {P}) = x ::= e {f P}" |
"map_acom f (C1;;C2) = map_acom f C1;; map_acom f C2" |
"map_acom f (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) = 
  (IF b THEN {f P1} map_acom f C1 ELSE {f P2} map_acom f C2 {f Q})" |
"map_acom f ({I} WHILE b DO {P} c {Q}) =
  ({f I} WHILE b DO {f P} map_acom f c {f Q})"

lemma annos_ne: "annos C \<noteq> []"
by(induction C) auto

lemma strip_annotate[simp]: "strip(annotate f c) = c"
by(induction c arbitrary: f) auto

lemma length_annos_annotate[simp]: "length (annos (annotate f c)) = asize c"
by(induction c arbitrary: f) auto

lemma size_annos: "size(annos C) = asize(strip C)"
by(induction C)(auto)

lemma size_annos_same: "strip C1 = strip C2 \<Longrightarrow> size(annos C1) = size(annos C2)"
apply(induct C2 arbitrary: C1)
apply(case_tac C1, simp_all)+
done

lemmas size_annos_same2 = eqTrueI[OF size_annos_same]

lemma anno_annotate[simp]: "p < asize c \<Longrightarrow> anno (annotate f c) p = f p"
apply(induction c arbitrary: f p)
apply (auto simp: anno_def nth_append nth_Cons numeral_eq_Suc shift_def
            split: nat.split)
  apply (metis add_Suc_right add_diff_inverse add.commute)
 apply(rule_tac f=f in arg_cong)
 apply arith
apply (metis less_Suc_eq)
done

lemma eq_acom_iff_strip_annos:
  "C1 = C2 \<longleftrightarrow> strip C1 = strip C2 \<and> annos C1 = annos C2"
apply(induction C1 arbitrary: C2)
apply(case_tac C2, auto simp: size_annos_same2)+
done

lemma eq_acom_iff_strip_anno:
  "C1=C2 \<longleftrightarrow> strip C1 = strip C2 \<and> (\<forall>p<size(annos C1). anno C1 p = anno C2 p)"
by(auto simp add: eq_acom_iff_strip_annos anno_def
     list_eq_iff_nth_eq size_annos_same2)

lemma post_map_acom[simp]: "post(map_acom f C) = f(post C)"
by (induction C) (auto simp: post_def last_append annos_ne)

lemma strip_map_acom[simp]: "strip (map_acom f C) = strip C"
by (induction C) auto

lemma anno_map_acom: "p < size(annos C) \<Longrightarrow> anno (map_acom f C) p = f(anno C p)"
apply(induction C arbitrary: p)
apply(auto simp: anno_def nth_append nth_Cons' size_annos)
done

lemma strip_eq_SKIP:
  "strip C = SKIP \<longleftrightarrow> (\<exists>P. C = SKIP {P})"
by (cases C) simp_all

lemma strip_eq_Assign:
  "strip C = x::=e \<longleftrightarrow> (\<exists>P. C = x::=e {P})"
by (cases C) simp_all

lemma strip_eq_Seq:
  "strip C = c1;;c2 \<longleftrightarrow> (\<exists>C1 C2. C = C1;;C2 & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_If:
  "strip C = IF b THEN c1 ELSE c2 \<longleftrightarrow>
  (\<exists>P1 P2 C1 C2 Q. C = IF b THEN {P1} C1 ELSE {P2} C2 {Q} & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_While:
  "strip C = WHILE b DO c1 \<longleftrightarrow>
  (\<exists>I P C1 Q. C = {I} WHILE b DO {P} C1 {Q} & strip C1 = c1)"
by (cases C) simp_all

lemma [simp]: "shift (\<lambda>p. a) n = (\<lambda>p. a)"
by(simp add:shift_def)

lemma set_annos_anno[simp]: "set (annos (annotate (\<lambda>p. a) c)) = {a}"
by(induction c) simp_all

lemma post_in_annos: "post C \<in> set(annos C)"
by(auto simp: post_def annos_ne)

lemma post_anno_asize: "post C = anno C (size(annos C) - 1)"
by(simp add: post_def last_conv_nth[OF annos_ne] anno_def)

end