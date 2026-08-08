theory SarsChiralMassDilaton
  imports Main
begin

datatype m2z = M int int int int

fun madd :: "m2z => m2z => m2z" where
  "madd (M a b c d) (M e f g h) = M (a+e) (b+f) (c+g) (d+h)"

fun mmul :: "m2z => m2z => m2z" where
  "mmul (M a b c d) (M e f g h) = M (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h)"

fun smul :: "int => m2z => m2z" where
  "smul m (M a b c d) = M (m*a) (m*b) (m*c) (m*d)"

fun diagBlock :: "m2z => m2z" where
  "diagBlock (M a b c d) = M a 0 0 d"

fun offBlock :: "m2z => m2z" where
  "offBlock (M a b c d) = M 0 b c 0"

definition PR :: m2z where "PR = M 1 0 0 0"
definition PL :: m2z where "PL = M 0 0 0 1"
definition I2 :: m2z where "I2 = M 1 0 0 1"
definition Jmod :: m2z where "Jmod = M 0 1 1 0"
definition zeroM :: m2z where "zeroM = M 0 0 0 0"
definition diracMassCoupling :: "int => m2z" where "diracMassCoupling m = smul m Jmod"
definition springPotential2 :: "int => int => int" where "springPotential2 m lam = abs (m*lam)"
definition entropyQuadratic2 :: "int => int" where "entropyQuadratic2 x = x*x"

datatype concept = Left_Weyl_Sheet | Right_Weyl_Sheet | Tomita_Modular_Swap | Dirac_Mass_Coupling | Zitterbewegung | Dilaton_Weyl_Scale | Conformal_Spring | Orthogonal_Entropy_Transport
datatype edge = swapped_by | couples_to | generates | breaks_weyl_scale_by | realizes_as | drives_orthogonal_transport
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Left_Weyl_Sheet swapped_by Tomita_Modular_Swap = True" |
  "edgeHolds Left_Weyl_Sheet couples_to Right_Weyl_Sheet = True" |
  "edgeHolds Dirac_Mass_Coupling generates Zitterbewegung = True" |
  "edgeHolds Dirac_Mass_Coupling breaks_weyl_scale_by Dilaton_Weyl_Scale = True" |
  "edgeHolds Dilaton_Weyl_Scale realizes_as Conformal_Spring = True" |
  "edgeHolds Conformal_Spring drives_orthogonal_transport Orthogonal_Entropy_Transport = True" |
  "edgeHolds _ _ _ = False"

theorem matrix_kernel:
  "mmul PR PL = zeroM \<and> madd PR PL = I2 \<and> mmul (mmul Jmod PL) Jmod = PR \<and>
   (\<forall>m. diracMassCoupling m = M 0 m m 0) \<and>
   (\<forall>m. diagBlock (diracMassCoupling m) = zeroM) \<and>
   (\<forall>m. offBlock (diracMassCoupling m) = diracMassCoupling m)"
  by (simp add: PR_def PL_def I2_def Jmod_def zeroM_def diracMassCoupling_def)

theorem spring_entropy_kernel:
  "(\<forall>m lam. 0 <= springPotential2 m lam) \<and> (\<forall>m. springPotential2 m 0 = 0) \<and>
   (\<forall>x. 0 <= entropyQuadratic2 x) \<and> entropyQuadratic2 0 = 0"
  by (simp add: springPotential2_def entropyQuadratic2_def)

theorem graph_kernel:
  "edgeHolds Left_Weyl_Sheet swapped_by Tomita_Modular_Swap = True \<and>
   edgeHolds Left_Weyl_Sheet couples_to Right_Weyl_Sheet = True \<and>
   edgeHolds Dirac_Mass_Coupling generates Zitterbewegung = True \<and>
   edgeHolds Dirac_Mass_Coupling breaks_weyl_scale_by Dilaton_Weyl_Scale = True \<and>
   edgeHolds Dilaton_Weyl_Scale realizes_as Conformal_Spring = True \<and>
   edgeHolds Conformal_Spring drives_orthogonal_transport Orthogonal_Entropy_Transport = True"
  by simp

end
