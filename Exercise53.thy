theory Exercise53 imports IsarByExample
begin
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
proof -
  show ?thesis using a
  proof cases
    case evSS thus ?thesis by auto
  qed
qed

end
  

  