import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import InfoGeometry.SuperGrassmannian.SatoColimitTriality

noncomputable section

open scoped Matrix

namespace InfoGeometry.SuperGrassmannian.MajoranaCAR

/-- The carrier used for the concrete, noncommutative split-cell model. -/
abbrev WitnessMat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- A real matrix with square one. -/
def witnessE : WitnessMat2R := !![1, 0; 0, -1]

/-- A real matrix with square minus one, anticommuting with `witnessE`. -/
def witnessF : WitnessMat2R := !![0, -1; 1, 0]

/-- The central half-unit in the real matrix carrier. -/
def witnessHalf : WitnessMat2R := (1 / 2 : ℝ) • (1 : WitnessMat2R)

/-- A concrete matrix model inhabiting the abstract split Clifford cell. -/
def matrixSplitCliffordCell : SplitCliffordCell WitnessMat2R where
  e := witnessE
  f := witnessF
  half := witnessHalf
  e_sq := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessE, Matrix.mul_apply, Fin.sum_univ_two]
  f_sq := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessF, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]
  anticomm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessE, witnessF, Matrix.add_apply]
  two_half := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessHalf, Matrix.smul_apply, Matrix.add_apply] <;>
      norm_num
  half_comm := fun X => by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessHalf, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.one_apply] <;>
      ring

/-- The exhibited split-cell carrier is inhabited. -/
theorem matrixSplitCliffordCell_nonempty :
    Nonempty (SplitCliffordCell WitnessMat2R) :=
  ⟨matrixSplitCliffordCell⟩

/-- The two chosen generators do not commute, so this model is noncommutative. -/
theorem matrixSplitCliffordCell_generators_noncommute :
    witnessE * witnessF ≠ witnessF * witnessE := by
  intro h
  have h01 := congrArg (fun M : WitnessMat2R => M 0 1) h
  norm_num [witnessE, witnessF, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- CAR nilpotency and anticommutation hold in the explicit matrix model. -/
theorem matrix_model_majorana_car :
    (SplitCliffordCell.a matrixSplitCliffordCell) ^ 2 = 0 ∧
      (SplitCliffordCell.a_star matrixSplitCliffordCell) ^ 2 = 0 ∧
      (SplitCliffordCell.a matrixSplitCliffordCell) *
          (SplitCliffordCell.a_star matrixSplitCliffordCell) +
          (SplitCliffordCell.a_star matrixSplitCliffordCell) *
            (SplitCliffordCell.a matrixSplitCliffordCell) = 1 := by
  exact ⟨matrixSplitCliffordCell.a_sq_zero,
    matrixSplitCliffordCell.a_star_sq_zero,
    matrixSplitCliffordCell.car_anticommutator⟩

end InfoGeometry.SuperGrassmannian.MajoranaCAR

namespace InfoGeometry.SuperGrassmannian.SatoColimitTriality

open InfoGeometry.SuperGrassmannian.MajoranaCAR

/-- Matrix realization of the split-cell carrier used by the Sato operator owner. -/
def matrixSplitCliffordCell : SplitCliffordCell WitnessMat2R where
  e := witnessE
  f := witnessF
  half := witnessHalf
  e_sq := InfoGeometry.SuperGrassmannian.MajoranaCAR.matrixSplitCliffordCell.e_sq
  f_sq := InfoGeometry.SuperGrassmannian.MajoranaCAR.matrixSplitCliffordCell.f_sq
  anticomm := InfoGeometry.SuperGrassmannian.MajoranaCAR.matrixSplitCliffordCell.anticomm
  two_half := InfoGeometry.SuperGrassmannian.MajoranaCAR.matrixSplitCliffordCell.two_half
  half_comm := InfoGeometry.SuperGrassmannian.MajoranaCAR.matrixSplitCliffordCell.half_comm

/-- The second owner-specific split-cell carrier is explicitly inhabited. -/
theorem matrixSplitCliffordCell_nonempty :
    Nonempty (SplitCliffordCell WitnessMat2R) :=
  ⟨matrixSplitCliffordCell⟩

/-- Both Sato lightcone modes are nilpotent in this concrete matrix model. -/
theorem matrix_model_lightcone_nilpotent :
    matrixSplitCliffordCell.a ^ 2 = 0 ∧
      matrixSplitCliffordCell.a_star ^ 2 = 0 :=
  ⟨matrixSplitCliffordCell.a_sq_zero, matrixSplitCliffordCell.a_star_sq_zero⟩

end InfoGeometry.SuperGrassmannian.SatoColimitTriality
