theory CoriolisBarrierAnomaly
  imports Complex_Main
begin

locale singular_projections =
  fixes mul :: "'a => 'a => 'a" (infixl "*" 70)
    and add :: "'a => 'a => 'a" (infixl "+" 65)
    and sub :: "'a => 'a => 'a" (infixl "-" 65)
    and smul :: "real => 'a => 'a"
    and zero :: 'a
    and PD :: 'a
    and PL :: 'a
    and PR :: 'a
    and D :: 'a
    and chi_L :: 'a
    and chi_R :: 'a
    and half :: real
  assumes dilation_def: "D = smul half (PL - PR)"
      and chi_L_def: "chi_L = PD * PL - PL * PD"
      and chi_R_def: "chi_R = PD * PR - PR * PD"
begin

end
end
