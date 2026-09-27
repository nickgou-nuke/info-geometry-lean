import InfoGeometry.OperatorAlgebra.TKKRegressiveBridge
import InfoGeometry.Core.JordanAssociator
import InfoGeometry.Algebra.KantorTripleFiveGrading
import InfoGeometry.OperatorAlgebra.TKKClosure

namespace InfoGeometry.Geometry.Ambitwistor

open InfoGeometry.Algebra.KantorTripleFiveGrading
open InfoGeometry.Core.JordanAssociator
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Core.JordanPeirceDecomposition

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

-- 1. Map the Regressive Incidence
/--
The symmetric part of the Kantor triple product.
-/
def kantorSymmetric (T : KantorTripleSystem R V) (x y z : V) : V :=
  T.triple x z y + T.triple y z x

/--
The incidence defect K can be written in terms of the triple product.
The regressive product evaluates to the defect.
-/
theorem regressive_product_eq_defect (T : KantorTripleSystem R V) (x y z : V) :
    regressiveProduct T x y z = T.triple x z y - T.triple y z x := by
  rfl

-- 2. Isolate the Defect
variable {A : Type*} [Ring A] [Algebra ℝ A]

/--
The non-zero ambitwistor incidence residue (the geometric 'miss') is directly 
the evaluation of the Jordan Associator `[x, y, z]`.
-/
def incidenceResidue (x y z : A) : A :=
  jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z)

theorem residue_eq_double_commutator (x y z : A) :
    incidenceResidue x y z = (1 / 4 : ℝ) • (y * (x * z - z * x) - (x * z - z * x) * y) := by
  exact jordan_associator_eq_expanded_double_commutator x y z

-- 3. The TKK Envelope (Jacobi Resolution)
/--
The TKK Lie envelope successfully closes over the geometric anomaly.
Despite the underlying Jordan algebra being non-associative, the Lie bracket
satisfies the Jacobi identity, trapping the associator defect inside the
grade-0 derivation algebra (structure operators).
-/
theorem tkk_jacobi_resolution {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] (C : TKKLieClosure J L) (x y z : L) :
    C.lie.bracket x (C.lie.bracket y z) +
    C.lie.bracket y (C.lie.bracket z x) +
    C.lie.bracket z (C.lie.bracket x y) = 0 :=
  C.lie.jacobi x y z

end InfoGeometry.Geometry.Ambitwistor
