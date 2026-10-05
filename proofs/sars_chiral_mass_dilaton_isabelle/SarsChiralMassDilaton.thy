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

fun det2 :: "m2z => int" where
  "det2 (M a b c d) = a*d - b*c"

definition PR :: m2z where "PR = M 1 0 0 0"
definition PL :: m2z where "PL = M 0 0 0 1"
definition I2 :: m2z where "I2 = M 1 0 0 1"
definition Jmod :: m2z where "Jmod = M 0 1 1 0"
definition zeroM :: m2z where "zeroM = M 0 0 0 0"
definition diracMassCoupling :: "int => m2z" where "diracMassCoupling m = smul m Jmod"
definition springPotential2 :: "int => int => int" where "springPotential2 m lam = abs (m*lam)"
definition entropyQuadratic2 :: "int => int" where "entropyQuadratic2 x = x*x"

theorem matrix_kernel:
  "mmul PR PL = zeroM \<and> madd PR PL = I2 \<and> mmul (mmul Jmod PL) Jmod = PR \<and>
   (\<forall>m. diracMassCoupling m = M 0 m m 0) \<and>
   (\<forall>m. diagBlock (diracMassCoupling m) = zeroM) \<and>
   (\<forall>m. offBlock (diracMassCoupling m) = diracMassCoupling m)"
  by (simp add: PR_def PL_def I2_def Jmod_def zeroM_def diracMassCoupling_def)

(* The mass matrix determines a rest-energy splitting; it does not alone
   assert time-dependent Zitterbewegung. *)
theorem dirac_mass_characteristic:
  "det2 (madd (diracMassCoupling m) (smul (-E) I2)) = (E-m)*(E+m)"
  by (simp add: det2.simps madd.simps smul.simps diracMassCoupling_def I2_def Jmod_def algebra_simps)

theorem spring_entropy_kernel:
  "(\<forall>m lam. 0 <= springPotential2 m lam) \<and> (\<forall>m. springPotential2 m 0 = 0) \<and>
   (\<forall>x. 0 <= entropyQuadratic2 x) \<and> entropyQuadratic2 0 = 0"
  by (simp add: springPotential2_def entropyQuadratic2_def)

end
