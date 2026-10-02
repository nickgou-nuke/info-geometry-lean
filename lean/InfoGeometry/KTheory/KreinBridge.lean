import InfoGeometry.Krein.Clifford
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The real matrix space is identified with an existing doubled Hilbert carrier.
Its fundamental symmetry is left multiplication by `diag(1,-1)`, not by a
square-minus-one complex structure. No new Krein typeclass is introduced.
-/

noncomputable section

namespace InfoGeometry.KTheory.KreinBridge

open InfoGeometry.Krein
open InfoGeometry.Clifford.Cl11Matrix
open scoped InnerProductSpace

abbrev Carrier := HilbertDoubled (EuclideanSpace ℝ (Fin 2))

def matrixToHilbert : Mat2 ≃ₗ[ℝ] Carrier where
  toFun matrix := HilbertDoubled.toLp
    (WithLp.toLp 2 (matrix 0), WithLp.toLp 2 (matrix 1))
  invFun vector := ![WithLp.ofLp (HilbertDoubled.ofLp vector).1,
    WithLp.ofLp (HilbertDoubled.ofLp vector).2]
  left_inv matrix := by
    ext row column
    fin_cases row <;> rfl
  right_inv vector := by
    apply HilbertDoubled.ext
    rfl
  map_add' first second := rfl
  map_smul' scalar vector := rfl

def matrixMetric : Module.End ℝ Mat2 :=
  matrixToHilbert.symm.toLinearMap.comp
    ((KreinSpace.J (H := Carrier)).toLinearEquiv.toLinearMap.comp matrixToHilbert.toLinearMap)

theorem matrixMetric_apply (matrix : Mat2) : matrixMetric matrix = Eplus * matrix := by
  ext row column
  fin_cases row <;>
    simp [matrixMetric, matrixToHilbert, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

theorem metric_transport (matrix : Mat2) :
    matrixToHilbert (matrixMetric matrix) = KreinSpace.J (matrixToHilbert matrix) := by
  simp [matrixMetric]

theorem matrixMetric_involutive : matrixMetric.comp matrixMetric = LinearMap.id := by
  apply LinearMap.ext
  intro matrix
  apply matrixToHilbert.injective
  simp only [LinearMap.comp_apply, LinearMap.id_apply, metric_transport, KreinSpace.J_invol]

def matrixForm : LinearMap.BilinForm ℝ Mat2 where
  toFun first :=
    { toFun second := KreinSpace.kreinInner (matrixToHilbert first) (matrixToHilbert second)
      map_add' second third := by simp only [map_add, KreinSpace.kreinInner_add_right]
      map_smul' scalar second := by
        simp only [map_smul, KreinSpace.kreinInner_smul_right, smul_eq_mul, RingHom.id_apply] }
  map_add' first second := by
    ext third
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add,
      KreinSpace.kreinInner_add_left, LinearMap.add_apply]
  map_smul' scalar first := by
    ext second
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul,
      KreinSpace.kreinInner_smul_left, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem matrixForm_symmetric (first second : Mat2) :
    matrixForm first second = matrixForm second first := by
  change KreinSpace.kreinInner (matrixToHilbert first) (matrixToHilbert second) =
    KreinSpace.kreinInner (matrixToHilbert second) (matrixToHilbert first)
  exact KreinSpace.kreinInner_symm (H := Carrier) _ _

theorem matrixForm_twist (first second : Mat2) :
    matrixForm first (matrixMetric second) = ⟪matrixToHilbert first, matrixToHilbert second⟫_ℝ := by
  change KreinSpace.kreinInner (matrixToHilbert first)
    (matrixToHilbert (matrixMetric second)) = _
  rw [metric_transport, KreinSpace.kreinInner_def]
  exact (KreinSpace.J (H := Carrier)).inner_map_map _ _

theorem matrixForm_twist_positive (matrix : Mat2) (hnonzero : matrix ≠ 0) :
    0 < matrixForm matrix (matrixMetric matrix) := by
  rw [matrixForm_twist]
  apply real_inner_self_pos.mpr
  exact fun hzero => hnonzero (matrixToHilbert.injective (by simpa using hzero))

theorem matrixForm_nondegenerate (matrix : Mat2)
    (hzero : ∀ other, matrixForm matrix other = 0) : matrix = 0 := by
  by_contra hnonzero
  have hpositive := matrixForm_twist_positive matrix hnonzero
  rw [hzero] at hpositive
  exact (lt_irrefl 0) hpositive

theorem elliptic_left_square (matrix : Mat2) : Eminus * (Eminus * matrix) = -matrix := by
  rw [← mul_assoc, Eminus_sq]
  simp

theorem elliptic_left_not_involutive : ¬ Function.Involutive (fun matrix : Mat2 => Eminus * matrix) := by
  intro hinvolution
  have hequal := hinvolution 1
  change Eminus * (Eminus * (1 : Mat2)) = 1 at hequal
  rw [elliptic_left_square] at hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 0 0) hequal
  norm_num at hentry

end InfoGeometry.KTheory.KreinBridge
