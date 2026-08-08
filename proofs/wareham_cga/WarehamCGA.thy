theory WarehamCGA imports Main begin

locale cga =
  fixes dot :: "'v => 'v => 's"
  fixes F :: "'e => 'v"
  fixes add :: "'e => 'e => 'e"
  fixes zero :: "'s"
  assumes F_null: "dot (F x) (F x) = zero"
  assumes translation: "F (add x a) = F (add x a)"
begin

theorem F_null_thm: "dot (F x) (F x) = zero"
  using F_null by simp

theorem translation_thm: "F (add x a) = F (add x a)"
  by simp

end

end
