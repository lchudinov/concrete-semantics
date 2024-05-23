theory Exercise52 imports Main
begin

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
  then obtain a where "length xs = 2*a" by blast 
  let ?ys = "take a xs"
  let ?zs = "drop a xs"
  have "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs)" by (simp add: \<open>length xs = 2 * a\<close>) 
  hence "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by blast 
  thus ?thesis by blast
next
  assume "odd (length xs)"
  then obtain a where "length xs = 2 * a + 1" using oddE by blast
  let ?ys = "take (a + 1) xs"
  let ?zs = "drop (a + 1) xs"
  have "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs + 1)" by (simp add: \<open>length xs = 2 * a + 1\<close>)
  hence "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by blast 
  thus ?thesis by blast
qed
    
end