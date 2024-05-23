theory Exercise54 imports IsarByExample
begin

lemma "\<not> ev(Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  from this have "ev (Suc 0)" by cases
  from this show False by cases
qed

end

  

  