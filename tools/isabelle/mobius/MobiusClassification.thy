theory MobiusClassification
  imports Complex_Main
begin

datatype mobius_class = Elliptic | Parabolic | Hyperbolic | Loxodromic

type_synonym sigma_pair = "rat * rat"

definition classify_sigma :: "sigma_pair => mobius_class" where
  "classify_sigma s =
    (if snd s = 0 then
       if fst s = 4 then Parabolic
       else if fst s < 4 then Elliptic
       else Hyperbolic
     else Loxodromic)"

definition hyper_sigma :: sigma_pair where
  "hyper_sigma = (25/4, 0)"

definition para_sigma :: sigma_pair where
  "para_sigma = (4, 0)"

definition ell_sigma :: sigma_pair where
  "ell_sigma = (0, 0)"

definition lox_sigma :: sigma_pair where
  "lox_sigma = (3, 4)"

definition gaussian_square :: "rat => rat => sigma_pair" where
  "gaussian_square a b = (a * a - b * b, 2 * a * b)"

theorem hyper_sigma_readback:
  "hyper_sigma = ((5/2) * (5/2), 0)"
  by (simp add: hyper_sigma_def)

theorem para_sigma_readback:
  "para_sigma = (2 * 2, 0)"
  by (simp add: para_sigma_def)

theorem ell_sigma_readback:
  "ell_sigma = (0, 0)"
  by (simp add: ell_sigma_def)

theorem lox_sigma_readback:
  "gaussian_square 2 1 = lox_sigma"
  by (simp add: gaussian_square_def lox_sigma_def)

theorem hyper_classification:
  "classify_sigma hyper_sigma = Hyperbolic"
  by (simp add: classify_sigma_def hyper_sigma_def)

theorem para_classification:
  "classify_sigma para_sigma = Parabolic"
  by (simp add: classify_sigma_def para_sigma_def)

theorem ell_classification:
  "classify_sigma ell_sigma = Elliptic"
  by (simp add: classify_sigma_def ell_sigma_def)

theorem lox_classification:
  "classify_sigma lox_sigma = Loxodromic"
  by (simp add: classify_sigma_def lox_sigma_def)

end
