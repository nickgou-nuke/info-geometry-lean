theory WarehamCGADilatorSL2
  imports Complex_Main
begin

datatype m2q = Mat rat rat rat rat

fun madd :: "m2q => m2q => m2q" where
  "madd (Mat a b c d) (Mat e f g h) = Mat (a+e) (b+f) (c+g) (d+h)"
fun mneg :: "m2q => m2q" where
  "mneg (Mat a b c d) = Mat (-a) (-b) (-c) (-d)"
definition msub :: "m2q => m2q => m2q" where "msub A B = madd A (mneg B)"
fun smul :: "rat => m2q => m2q" where
  "smul k (Mat a b c d) = Mat (k*a) (k*b) (k*c) (k*d)"
fun mmul :: "m2q => m2q => m2q" where
  "mmul (Mat a b c d) (Mat e f g h) = Mat (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h)"

definition I2 :: m2q where "I2 = Mat 1 0 0 1"
definition Z2 :: m2q where "Z2 = Mat 0 0 0 0"
definition e :: m2q where "e = Mat 1 0 0 (-1)"
definition ebar :: m2q where "ebar = Mat 0 1 (-1) 0"
definition S :: m2q where "S = mmul e ebar"
definition nvec :: m2q where "nvec = madd e ebar"
definition nbar :: m2q where "nbar = msub e ebar"
definition comm :: "m2q => m2q => m2q" where "comm A B = msub (mmul A B) (mmul B A)"
definition anticomm :: "m2q => m2q => m2q" where "anticomm A B = madd (mmul A B) (mmul B A)"
definition H :: m2q where "H = mneg S"
definition E :: m2q where "E = smul (1/2) nvec"
definition F :: m2q where "F = smul (1/2) nbar"
definition Casimir :: m2q where "Casimir = madd (mmul H H) (smul 2 (madd (mmul E F) (mmul F E)))"

theorem wareham_dilator_sl2_kernel:
  "mmul e e = I2 \<and> mmul ebar ebar = mneg I2 \<and> anticomm e ebar = Z2 \<and>
   mmul S S = I2 \<and> mmul S nvec = mneg nvec \<and> mmul nvec S = nvec \<and>
   mmul S nbar = nbar \<and> mmul nbar S = mneg nbar \<and>
   anticomm S nvec = Z2 \<and> anticomm S nbar = Z2 \<and> anticomm nvec nbar = smul 4 I2 \<and>
   comm S nvec = smul (-2) nvec \<and> comm S nbar = smul 2 nbar \<and> comm nvec nbar = smul (-4) S \<and>
   comm H E = smul 2 E \<and> comm H F = smul (-2) F \<and> comm E F = H \<and>
   Casimir = smul 3 I2 \<and> comm Casimir H = Z2 \<and> comm Casimir E = Z2 \<and> comm Casimir F = Z2"
  by (simp add: I2_def Z2_def e_def ebar_def S_def nvec_def nbar_def msub_def comm_def anticomm_def H_def E_def F_def Casimir_def)

datatype concept = Wareham_CGA_Dilator | Null_Basis_n_nbar | SL2R_Subalgebra | SO21_Isomorphic_Form | Quadratic_Casimir_3
datatype edge = generated_by | anticommutes_with | closes_to | has_casimir | isomorphic_to
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Wareham_CGA_Dilator generated_by Null_Basis_n_nbar = True" |
  "edgeHolds Wareham_CGA_Dilator closes_to SL2R_Subalgebra = True" |
  "edgeHolds SL2R_Subalgebra isomorphic_to SO21_Isomorphic_Form = True" |
  "edgeHolds SL2R_Subalgebra has_casimir Quadratic_Casimir_3 = True" |
  "edgeHolds Null_Basis_n_nbar anticommutes_with Wareham_CGA_Dilator = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Wareham_CGA_Dilator generated_by Null_Basis_n_nbar = True \<and>
   edgeHolds Wareham_CGA_Dilator closes_to SL2R_Subalgebra = True \<and>
   edgeHolds SL2R_Subalgebra isomorphic_to SO21_Isomorphic_Form = True \<and>
   edgeHolds SL2R_Subalgebra has_casimir Quadratic_Casimir_3 = True \<and>
   edgeHolds Null_Basis_n_nbar anticommutes_with Wareham_CGA_Dilator = True"
  by simp

end
