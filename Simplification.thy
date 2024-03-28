theory Simplification
imports Main
begin
declare [[names_short]]

(* Exercise 2.10. *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

value "nodes (Node (Node Tip Tip) Tip)"
value "nodes (explode 0 (Node (Node Tip Tip) Tip))" 
value "nodes (explode 3 Tip)" 

lemma "nodes (explode n t) = 2 ^ n * (nodes t) + 2 ^ n - 1"
  apply (induction n arbitrary: t)
  apply (auto simp add: algebra_simps)
  done

(* Exercise 2.11. *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

value "eval (Add Var (Const 6)) 10"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] v = 0" |
"evalp (x # xs) v = x + v * evalp xs v"

value "evalp [1, 2, 3] 1"

fun add_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_coeffs [] xs = xs" |
"add_coeffs xs [] = xs" |
"add_coeffs (x # xs) (y # ys) = (x + y) # add_coeffs xs ys"

value "add_coeffs [1,2,3,4,4] [1,2,3,4]"

fun mult_coeff :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeff n [] = []" |
"mult_coeff n (x # xs) = n * x # (mult_coeff n xs)"

value "mult_coeff 2 [1,2,3]"

fun mult_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeffs [] l = []" |
"mult_coeffs (x # xs) ys = add_coeffs (mult_coeff x ys) (0 # mult_coeffs xs ys)"

value "mult_coeffs [1, 2, 3] [1, 1, 1]"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const c) = [c]" |
"coeffs (Add e1 e2) = add_coeffs (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = mult_coeffs (coeffs e1) (coeffs e2)"

value "coeffs (Add (Mult (Const 3) (Const 1)) (Mult (Const 2) Var))"

lemma evalp_additive [simp]: "evalp (add_coeffs xs ys) x = evalp xs x + evalp ys x"
  apply (induction rule: add_coeffs.induct)
  apply (auto simp add: algebra_simps)
  done

lemma evalp_coeff [simp]: "evalp (mult_coeff c xs) x = c * evalp xs x"
  apply (induction xs)
  apply (auto simp add:algebra_simps)
  done

lemma evalp_miltiplicative [simp]: "evalp (mult_coeffs xs ys) x = (evalp xs x) * (evalp ys x)"
  apply (induction xs)
  apply (auto simp add: algebra_simps)
  done
  
lemma "evalp (coeffs e) x = eval e x"
  apply (induction e)
  apply (auto)
  done

end