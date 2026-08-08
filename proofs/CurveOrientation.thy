theory CurveOrientation
  imports Complex_Main
begin

definition simple_closed_curve :: "(real ⇒ real × real) ⇒ bool" where
  "simple_closed_curve γ ⟷ 
    continuous_on {0..1} γ ∧ 
    γ 0 = γ 1 ∧ 
    inj_on γ {0..<1}"

definition positively_oriented :: "(real ⇒ real × real) ⇒ (real ⇒ real × real) ⇒ real ⇒ bool" where
  "positively_oriented γ γ' t ⟷ 
    fst (γ t) * snd (γ' t) - snd (γ t) * fst (γ' t) > 0"

text ‹
  The Jordan Curve Theorem states that every simple closed curve divides the plane into two disjoint regions.
›

end
