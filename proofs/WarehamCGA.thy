theory WarehamCGA
imports Main Real
begin

typedecl CGA

consts
  wedge :: "CGA ⇒ CGA ⇒ CGA" (infixl "∧" 70)
  dot :: "CGA ⇒ CGA ⇒ CGA" (infixl "⋅" 70)
  e1 :: CGA
  e2 :: CGA
  e :: CGA
  e_bar :: CGA
  scalar_mul :: "real ⇒ CGA ⇒ CGA" (infixr "*s" 75)
  add_cga :: "CGA ⇒ CGA ⇒ CGA" (infixl "+c" 65)
  sub_cga :: "CGA ⇒ CGA ⇒ CGA" (infixl "-c" 65)

definition n :: CGA where
  "n = e +c e_bar"

definition n_bar :: CGA where
  "n_bar = e -c e_bar"

definition F :: "CGA ⇒ real ⇒ CGA" where
  "F x x_sq = (0.5 *s ((x_sq *s n) +c (2.0 *s x) -c n_bar))"

definition circle_dual :: "CGA ⇒ real ⇒ CGA" where
  "circle_dual B rho = B -c (0.5 * rho * rho *s n)"

end
