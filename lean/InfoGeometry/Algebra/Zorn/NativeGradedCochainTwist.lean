import InfoGeometry.Algebra.Zorn.CochainTwistSeparation
import InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
import InfoGeometry.Clifford.Cl11Matrix

/-!
# An explicit binary twist between the native matrix and Zorn basis tables

Grades are `Fin 3 → ZMod 2`. The first two bits select the existing real
Clifford/Pauli core basis `1, Eplus, J1, Eminus`; the third selects the
complementary summand. The coefficient formulas below are certified against
BOTH native multiplication laws, rather than assumed to describe octonions.

The source exponent is bilinear. The target exponent contains cubic terms.
Their relative TWO-cochain changes the homogeneous product. Its coboundary
is the target associator, with the determinant parity in three grades.
Nontrivial pointwise values of this coboundary do not make its cohomology
class nontrivial. No change of algebra multiplication is attributed to an
ordinary nonlinear Cayley coordinate map.
-/

set_option maxHeartbeats 6000000

noncomputable section

namespace InfoGeometry.Algebra.Zorn.NativeGradedCochainTwist

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge
open InfoGeometry.Algebra.Zorn.CochainTwistSeparation
open InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
open InfoGeometry.Clifford.Cl11Matrix

/-- Four homogeneous core elements; the third bit is deliberately ignored. -/
def coreGrade (x : Z2Grade) : RealCore :=
  if x 0 = 0 then (if x 1 = 0 then 1 else J1)
  else (if x 1 = 0 then Eplus else Eminus)

/-- Homogeneous elements of the associative central-complex doubling. -/
def matrixGrade (x : Z2Grade) : ComplexMatrix :=
  if x 2 = 0 then complexDouble (coreGrade x) 0
  else complexDouble 0 (coreGrade x)

/-- Homogeneous elements of the actual native split Zorn algebra. -/
def splitGrade (x : Z2Grade) : SplitCarrier :=
  if x 2 = 0 then splitDouble (coreGrade x) 0
  else splitDouble 0 (coreGrade x)

/-- The two homogeneous frames are matched by the proved real-linear equivalence. -/
theorem matrixSplitLinearEquiv_grade (x : Z2Grade) :
    matrixSplitLinearEquiv (matrixGrade x) = splitGrade x := by
  unfold matrixGrade splitGrade
  split <;> exact matrixSplitLinearEquiv_double _ _

/-- Associative matrix coefficient: the core anticommutation and central `i²=-1`. -/
def matrixExponent (x y : Z2Grade) : ZMod 2 :=
  x 1 * y 0 + x 2 * y 2

/-- The native Zorn table has a non-bilinear parity exponent in this frame. -/
def splitExponent (x y : Z2Grade) : ZMod 2 :=
  x 1 * y 0 + x 2 * y 0 + x 2 * y 1 +
    x 2 * y 0 * y 1 + x 1 * y 0 * y 2 + x 0 * y 1 * y 2

def matrixCochain (x y : Z2Grade) : ℝˣ := signUnit (matrixExponent x y)

def splitCochain (x y : Z2Grade) : ℝˣ := signUnit (splitExponent x y)

private theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

private theorem zmod_two : (2 : ZMod 2) = 0 := by
  exact ZMod.natCast_self 2

private theorem zmod_one_add_one : (1 + 1 : ZMod 2) = 0 := by
  exact zmod_two

private theorem zorn_neg_eq (X : SplitCarrier) :
    -X =
      { a := -X.a
        v := ![-X.v 0, -X.v 1, -X.v 2]
        w := ![-X.w 0, -X.w 1, -X.w 2]
        b := -X.b } := by
  change InfoGeometry.Algebra.ZornMatrixRealModule.neg X = _
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals simp [InfoGeometry.Algebra.ZornMatrixRealModule.neg, Vec3.smul]

private theorem coreGrade_mul (x y : Z2Grade) :
    coreGrade x * coreGrade y =
      (signUnit (x 1 * y 0) : ℝ) • coreGrade (x + y) := by
  rcases bit_cases (x 0) with hx0 | hx0 <;>
    rcases bit_cases (x 1) with hx1 | hx1 <;>
    rcases bit_cases (y 0) with hy0 | hy0 <;>
    rcases bit_cases (y 1) with hy1 | hy1
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coreGrade, signUnit, Matrix.mul_apply, Fin.sum_univ_two,
        Eplus, Eminus, J1, Pi.add_apply, zmod_two, zmod_one_add_one,
        hx0, hx1, hy0, hy1]

/-- All 64 products are computed using ordinary complex matrix multiplication. -/
theorem matrixGrade_mul (x y : Z2Grade) :
    matrixGrade x * matrixGrade y = (matrixCochain x y : ℝ) • matrixGrade (x + y) := by
  rcases bit_cases (x 0) with hx0 | hx0 <;>
    rcases bit_cases (x 1) with hx1 | hx1 <;>
    rcases bit_cases (x 2) with hx2 | hx2 <;>
    rcases bit_cases (y 0) with hy0 | hy0 <;>
    rcases bit_cases (y 1) with hy1 | hy1 <;>
    rcases bit_cases (y 2) with hy2 | hy2
  all_goals
    simp [matrixGrade, matrixCochain, matrixExponent, complexDouble_mul,
      coreGrade_mul, complexDouble, signUnit, Pi.add_apply, zmod_two,
      zmod_one_add_one,
      hx0, hx1, hx2, hy0, hy1, hy2] <;>
    (ext i j <;> apply Complex.ext <;> simp [complexDouble])

/-- All 64 target products are computed using native Zorn multiplication. -/
theorem splitGrade_mul (x y : Z2Grade) :
    splitGrade x * splitGrade y = (splitCochain x y : ℝ) • splitGrade (x + y) := by
  rcases bit_cases (x 0) with hx0 | hx0 <;>
    rcases bit_cases (x 1) with hx1 | hx1 <;>
    rcases bit_cases (x 2) with hx2 | hx2 <;>
    rcases bit_cases (y 0) with hy0 | hy0 <;>
    rcases bit_cases (y 1) with hy1 | hy1 <;>
    rcases bit_cases (y 2) with hy2 | hy2
  all_goals
    simp [splitGrade, splitDouble_mul, splitDouble_coordinates,
      coreGrade, splitCochain, splitExponent, coreConj, Eplus, Eminus, J1,
      signUnit, ZornMatrix.mul, ZornMatrix.smul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul, Pi.add_apply, zmod_two,
      zmod_one_add_one, zorn_neg_eq, hx0, hx1, hx2, hy0, hy1, hy2] <;>
    apply ZornMatrix.ext <;>
      first | (funext i; fin_cases i) | skip <;>
      simp [InfoGeometry.Algebra.ZornMatrixRealModule.neg,
        ZornMatrix.smul, Vec3.smul, Vec3.add, Vec3.sub]

/-- The associative coefficient table satisfies the binary cocycle equation. -/
theorem matrixExponent_cocycle (x y z : Z2Grade) :
    matrixExponent x y + matrixExponent (x + y) z =
      matrixExponent y z + matrixExponent x (y + z) := by
  simp only [matrixExponent, Pi.add_apply]
  ring

/-- The associator of the actual matrix table is trivial. -/
theorem matrixCochain_associator_one (x y z : Z2Grade) :
    associatorCochain matrixCochain x y z = 1 := by
  apply (associator_eq_one_iff _ x y z).2
  have h := congrArg signUnit (matrixExponent_cocycle x y z)
  simpa only [signUnit_add, matrixCochain] using h

/-- Determinant parity: signs disappear in characteristic two, not the six monomials. -/
def associatorParity (x y z : Z2Grade) : ZMod 2 :=
  x 0 * y 1 * z 2 + x 0 * y 2 * z 1 +
    x 1 * y 0 * z 2 + x 1 * y 2 * z 0 +
    x 2 * y 0 * z 1 + x 2 * y 1 * z 0

/-- Explicit coboundary calculation of the native split coefficient exponent. -/
theorem splitExponent_coboundary (x y z : Z2Grade) :
    splitExponent x y + splitExponent (x + y) z =
      associatorParity x y z + splitExponent y z + splitExponent x (y + z) := by
  simp only [splitExponent, associatorParity, Pi.add_apply]
  ring_nf
  simp [zmod_two]

/-- The actual split multiplication table has the stated three-variable associator. -/
theorem splitCochain_associator (x y z : Z2Grade) :
    associatorCochain splitCochain x y z = signUnit (associatorParity x y z) := by
  have h : splitCochain x y * splitCochain (x + y) z =
      signUnit (associatorParity x y z) * splitCochain y z * splitCochain x (y + z) := by
    simpa only [signUnit_add, splitCochain] using
      congrArg signUnit (splitExponent_coboundary x y z)
  rw [associatorCochain, h]
  simp [mul_assoc]

/-- Concrete nontrivial value; no nontrivial cohomology class is asserted. -/
theorem splitCochain_associator_basis :
    associatorCochain splitCochain ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] = -1 := by
  rw [splitCochain_associator]
  norm_num [associatorParity, signUnit, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- Relative binary multiplier between the certified matrix and Zorn tables. -/
def nativeTwist : Z2Grade → Z2Grade → ℝˣ :=
  relativeTwist matrixCochain splitCochain

/-- This is an actual identity between native products on homogeneous elements. -/
theorem nativeTwist_product (x y : Z2Grade) :
    splitGrade x * splitGrade y =
      (nativeTwist x y : ℝ) • matrixSplitLinearEquiv (matrixGrade x * matrixGrade y) := by
  rw [splitGrade_mul, matrixGrade_mul, map_smul, matrixSplitLinearEquiv_grade,
    smul_smul]
  have h := congrArg (fun u : ℝˣ => (u : ℝ))
    (relativeTwist_mul matrixCochain splitCochain x y)
  have hc : (nativeTwist x y : ℝ) * (matrixCochain x y : ℝ) =
      (splitCochain x y : ℝ) := h
  rw [hc]

/-- The target associator is precisely the relative TWO-cochain coboundary. -/
theorem nativeTwist_coboundary (x y z : Z2Grade) :
    associatorCochain nativeTwist x y z = associatorCochain splitCochain x y z := by
  exact (target_associator_is_relative_coboundary matrixCochain splitCochain
    matrixCochain_associator_one x y z).symm

/-- The native twist satisfies the pentagon equation inherited from a coboundary. -/
theorem nativeTwist_pentagon (x y z w : Z2Grade) :
    associatorCochain nativeTwist x y z * associatorCochain nativeTwist x (y + z) w *
        associatorCochain nativeTwist y z w =
      associatorCochain nativeTwist (x + y) z w *
        associatorCochain nativeTwist x y (z + w) :=
  associatorCochain_cocycle nativeTwist x y z w

/-- No bilinear exponent can equal this native split coefficient table. -/
theorem splitCochain_not_bilinear :
    ¬ ∃ β : Z2Grade →+ (Z2Grade →+ ZMod 2),
      ∀ x y, splitCochain x y = signUnit (β x y) := by
  rintro ⟨β, hβ⟩
  have hfun : splitCochain = fun x y => signUnit (β x y) := funext fun x => funext (hβ x)
  have h := splitCochain_associator_basis
  rw [hfun, bilinear_sign_associator_one] at h
  have hv := congrArg (fun u : ℝˣ => (u : ℝ)) h
  norm_num at hv

end InfoGeometry.Algebra.Zorn.NativeGradedCochainTwist
