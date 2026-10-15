import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import InfoGeometry.SuperGrassmannian.SatoColimitTriality

/-!
# Native `Cl(1,1)` carrier for the two repository CAR structures

This scratch bridge instantiates the `MajoranaCAR` and `SatoColimitTriality`
split-cell structures on Mathlib's `CliffordAlgebra Cl11Matrix.q11`.  The
existing `Cl11Matrix.cl11EquivMat` records the corresponding concrete
`M₂(ℝ)` model and fixes the negative generator sign as `Eminus`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11MajoranaCARNativeWitness

open InfoGeometry.Clifford.Cl11Matrix

abbrev Cl11 := CliffordAlgebra q11

/-- The positive generator in the repository's native real `Cl(1,1)`. -/
def positiveGenerator : Cl11 := CliffordAlgebra.ι q11 (1, 0)

/-- The negative generator in the repository's native real `Cl(1,1)`. -/
def negativeGenerator : Cl11 := CliffordAlgebra.ι q11 (0, 1)

/-- The scalar half in the native Clifford algebra. -/
def scalarHalf : Cl11 := algebraMap ℝ Cl11 (1 / 2 : ℝ)

@[simp] theorem cl11EquivMat_positiveGenerator :
    cl11EquivMat positiveGenerator = Eplus := by
  simpa [positiveGenerator] using cl11EquivMat_iota_pos

@[simp] theorem cl11EquivMat_negativeGenerator :
    cl11EquivMat negativeGenerator = Eminus := by
  simpa [negativeGenerator] using cl11EquivMat_iota_neg

@[simp] theorem cl11EquivMat_scalarHalf :
    cl11EquivMat scalarHalf = (1 / 2 : ℝ) • (1 : Mat2) := by
  simp [scalarHalf, Algebra.smul_def]

/-- The half scalar satisfies the normalization required by both CAR cells. -/
theorem scalarHalf_add_scalarHalf : scalarHalf + scalarHalf = 1 := by
  calc
    scalarHalf + scalarHalf =
        algebraMap ℝ Cl11 ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
          rw [← map_add]
          rfl
    _ = 1 := by
      rw [show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num, map_one]

theorem scalarHalf_commutes (x : Cl11) : scalarHalf * x = x * scalarHalf :=
  Algebra.commutes (1 / 2 : ℝ) x

/-- The native Clifford generators and central half form the existing CAR cell. -/
def nativeCARCell : InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell Cl11 where
  e := positiveGenerator
  f := negativeGenerator
  half := scalarHalf
  e_sq := by
    apply cl11EquivMat.injective
    simp only [map_pow, cl11EquivMat_positiveGenerator, Eplus_sq, map_one]
  f_sq := by
    apply cl11EquivMat.injective
    calc
      cl11EquivMat (negativeGenerator ^ 2) = Eminus * Eminus := by simp
      _ = -1 := by simpa using Eminus_sq
      _ = cl11EquivMat (-1) := by simp
  anticomm := by
    apply cl11EquivMat.injective
    simpa only [map_add, map_mul, cl11EquivMat_positiveGenerator,
      cl11EquivMat_negativeGenerator, map_zero] using
      cl11EquivMat_iota_pos_neg_anticomm
  two_half := scalarHalf_add_scalarHalf
  half_comm := scalarHalf_commutes

theorem nativeCARCell_positive_generator_exact :
    nativeCARCell.e = CliffordAlgebra.ι q11 (1, 0) := rfl

theorem nativeCARCell_negative_generator_exact :
    nativeCARCell.f = CliffordAlgebra.ι q11 (0, 1) := rfl

theorem nativeCARCell_half_exact :
    nativeCARCell.half = algebraMap ℝ Cl11 (1 / 2 : ℝ) := rfl

/-- The positive and negative generators are distinct in the native carrier. -/
theorem positive_ne_negative : positiveGenerator ≠ negativeGenerator := by
  intro h
  have h' := congrArg cl11EquivMat h
  norm_num [positiveGenerator, negativeGenerator, cl11EquivMat_iota_pos,
    cl11EquivMat_iota_neg, Eplus, Eminus] at h'

/-- The generators do not commute; this witnesses a noncommutative carrier. -/
theorem generators_noncommute :
    positiveGenerator * negativeGenerator ≠
      negativeGenerator * positiveGenerator := by
  intro h
  have h' := congrArg cl11EquivMat h
  have hmatrix : Eplus * Eminus = Eminus * Eplus := by
    simpa only [map_mul, cl11EquivMat_positiveGenerator,
      cl11EquivMat_negativeGenerator] using h'
  have h01 := congrArg (fun M : Mat2 => M 0 1) hmatrix
  norm_num [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ### Theorems instantiated on the native carrier -/

theorem native_annihilation_nilpotent :
    (InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a
      nativeCARCell) ^ 2 = 0 :=
  InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a_sq_zero
    nativeCARCell

theorem native_creation_nilpotent :
    (InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a_star
      nativeCARCell) ^ 2 = 0 :=
  InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a_star_sq_zero
    nativeCARCell

theorem native_CAR :
    InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a nativeCARCell *
        InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a_star nativeCARCell +
      InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a_star nativeCARCell *
        InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.a nativeCARCell = 1 :=
  InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.car_anticommutator
    nativeCARCell

theorem native_chirality_involution :
    (InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.Gamma
      nativeCARCell) ^ 2 = 1 :=
  InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.Gamma_sq
    nativeCARCell

theorem native_number_idempotent :
    (InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.N
      nativeCARCell) ^ 2 =
      InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.N nativeCARCell :=
  InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell.N_sq
    nativeCARCell

/-! ### Explicit `M₂(ℝ)` realization and sign-preserving equations -/

theorem matrix_positive_generator_square :
    (cl11EquivMat positiveGenerator) * (cl11EquivMat positiveGenerator) = 1 := by
  rw [cl11EquivMat_positiveGenerator]
  exact Eplus_sq

theorem matrix_negative_generator_square :
    (cl11EquivMat negativeGenerator) * (cl11EquivMat negativeGenerator) = -1 := by
  rw [cl11EquivMat_negativeGenerator]
  simpa using Eminus_sq

theorem matrix_half_normalization :
    cl11EquivMat scalarHalf + cl11EquivMat scalarHalf = (1 : Mat2) := by
  rw [cl11EquivMat_scalarHalf]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply] <;> norm_num

/-! ### Sato's similarly shaped cell is a separate structure declaration -/

/-- Sato's cell, instantiated on the same native Clifford carrier. -/
def nativeSatoCell :
    InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell Cl11 where
  e := nativeCARCell.e
  f := nativeCARCell.f
  half := nativeCARCell.half
  e_sq := nativeCARCell.e_sq
  f_sq := nativeCARCell.f_sq
  anticomm := nativeCARCell.anticomm
  two_half := nativeCARCell.two_half
  half_comm := nativeCARCell.half_comm

theorem satoCell_positive_generator_exact :
    nativeSatoCell.e = CliffordAlgebra.ι q11 (1, 0) := rfl

theorem satoCell_negative_generator_exact :
    nativeSatoCell.f = CliffordAlgebra.ι q11 (0, 1) := rfl

theorem satoCell_half_exact :
    nativeSatoCell.half = algebraMap ℝ Cl11 (1 / 2 : ℝ) := rfl

theorem sato_native_annihilation_nilpotent :
    (InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.a
      nativeSatoCell) ^ 2 = 0 :=
  InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.a_sq_zero
    nativeSatoCell

theorem sato_native_CAR :
    InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.a nativeSatoCell *
        InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.a_star nativeSatoCell +
      InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.a_star nativeSatoCell *
        InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.a nativeSatoCell = 1 :=
  InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.car_anticomm
    nativeSatoCell

theorem sato_native_chirality_involution :
    (InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.gamma
      nativeSatoCell) ^ 2 = 1 :=
  InfoGeometry.SuperGrassmannian.SatoColimitTriality.SplitCliffordCell.gamma_sq_one
    nativeSatoCell

end InfoGeometry.Clifford.Cl11MajoranaCARNativeWitness
