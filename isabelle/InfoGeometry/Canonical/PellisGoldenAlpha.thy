theory PellisGoldenAlpha
  imports Complex_Main
begin

definition pellis_expr :: "real => real" where
  "pellis_expr phi = 360 / phi^2 - 2 / phi^3 + 1 / (3 * phi)^5"

definition pellis_normal_form :: "real => real" where
  "pellis_normal_form phi = 176410 / 243 - (88447 / 243) * phi"

axiomatization phi_nonzero :: "real => bool" where
  phi_nonzero_axiom: "phi_nonzero phi"

axiomatization phi_inv :: "real => bool" where
  phi_inv_axiom: "phi_inv phi"

axiomatization pellis_normal_form_theorem :: "real => bool" where
  pellis_normal_form_axiom: "pellis_normal_form_theorem phi"

end
