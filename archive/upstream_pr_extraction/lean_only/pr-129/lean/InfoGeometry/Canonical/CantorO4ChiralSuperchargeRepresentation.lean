import InfoGeometry.Topology.CantorBoundaryCuntzFamily
import InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation
import InfoGeometry.Physics.SuperPoincareOperatorCharges

noncomputable section

/-!
# Projected chiral supercharge datum on the concrete O₄ Cantor carrier

The four-branch Cantor carrier is already a concrete O₄ representation.  This
file does not assert that a unital binary O₂ family is obtained automatically
from the four branches.  Instead it records the projected-sector datum needed
to transport the chiral supercharge relations onto that carrier.
-/

namespace InfoGeometry.Canonical.CantorO4ChiralSuperchargeRepresentation

open InfoGeometry.Topology.CantorBoundaryCuntzFamily
open InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation
open InfoGeometry.Physics.SuperPoincareOperatorCharges

abbrev CantorOperator := ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ)

/-! ## The grouped two-branch projected sector inside the four-branch carrier -/

def groupedS1 : CantorOperator :=
  cuntzS (0 : Fin 4) + cuntzS (1 : Fin 4)

def groupedS2 : CantorOperator :=
  cuntzS (2 : Fin 4) + cuntzS (3 : Fin 4)

def groupedS1star : CantorOperator :=
  (1 / 2 : ℂ) • (cuntzT (0 : Fin 4) + cuntzT (1 : Fin 4))

def groupedS2star : CantorOperator :=
  (1 / 2 : ℂ) • (cuntzT (2 : Fin 4) + cuntzT (3 : Fin 4))

def groupedGenerators : CuntzO2Generators CantorOperator where
  S1 := groupedS1
  S2 := groupedS2
  S1star := groupedS1star
  S2star := groupedS2star

theorem groupedS1star_S1 : groupedS1star * groupedS1 = 1 := by
  dsimp [groupedS1star, groupedS1]
  simp only [smul_mul_assoc, add_mul, mul_add]
  rw [cuntz_ortho, cuntz_ortho, cuntz_ortho, cuntz_ortho]
  simp <;> norm_num [div_eq_mul_inv] <;> module

theorem groupedS2star_S2 : groupedS2star * groupedS2 = 1 := by
  dsimp [groupedS2star, groupedS2]
  simp only [smul_mul_assoc, add_mul, mul_add]
  rw [cuntz_ortho, cuntz_ortho, cuntz_ortho, cuntz_ortho]
  simp <;> norm_num [div_eq_mul_inv] <;> module

theorem groupedS1star_S2 : groupedS1star * groupedS2 = 0 := by
  dsimp [groupedS1star, groupedS2]
  simp only [smul_mul_assoc, add_mul, mul_add]
  rw [cuntz_ortho, cuntz_ortho, cuntz_ortho, cuntz_ortho]
  simp <;> norm_num [div_eq_mul_inv] <;> module

theorem groupedS2star_S1 : groupedS2star * groupedS1 = 0 := by
  dsimp [groupedS2star, groupedS1]
  simp only [smul_mul_assoc, add_mul, mul_add]
  rw [cuntz_ortho, cuntz_ortho, cuntz_ortho, cuntz_ortho]
  simp <;> norm_num [div_eq_mul_inv] <;> module

/-! The grouped family is complete only on a projection sector, not on the full
    O₄ carrier. -/
def groupedProjection : CantorOperator :=
  groupedS1 * groupedS1star + groupedS2 * groupedS2star

/-- The complementary sector of the grouped chiral projection. -/
def groupedComplement : CantorOperator :=
  1 - groupedProjection

theorem grouped_completeness :
    groupedS1 * groupedS1star + groupedS2 * groupedS2star =
      groupedProjection := by
  rfl

theorem groupedProjection_idempotent :
    groupedProjection * groupedProjection = groupedProjection := by
  dsimp [groupedProjection]
  calc
    (groupedS1 * groupedS1star + groupedS2 * groupedS2star) *
        (groupedS1 * groupedS1star + groupedS2 * groupedS2star) =
        groupedS1 * groupedS1star * (groupedS1 * groupedS1star) +
          groupedS1 * groupedS1star * (groupedS2 * groupedS2star) +
          groupedS2 * groupedS2star * (groupedS1 * groupedS1star) +
          groupedS2 * groupedS2star * (groupedS2 * groupedS2star) := by
            noncomm_ring
    _ = groupedS1 * groupedS1star + groupedS2 * groupedS2star := by
      rw [mul_assoc, ← mul_assoc groupedS1star, groupedS1star_S1, one_mul,
        mul_assoc, ← mul_assoc groupedS1star, groupedS1star_S2, zero_mul,
        mul_zero, mul_assoc, ← mul_assoc groupedS2star, groupedS2star_S1,
        zero_mul, mul_zero, mul_assoc, ← mul_assoc groupedS2star,
        groupedS2star_S2, one_mul]
      simp

@[simp] theorem groupedProjection_add_complement :
    groupedProjection + groupedComplement = 1 := by
  dsimp [groupedComplement]
  noncomm_ring

@[simp] theorem groupedProjection_mul_complement :
    groupedProjection * groupedComplement = 0 := by
  dsimp [groupedComplement]
  rw [mul_sub, mul_one, groupedProjection_idempotent]
  noncomm_ring

@[simp] theorem groupedComplement_mul_projection :
    groupedComplement * groupedProjection = 0 := by
  dsimp [groupedComplement]
  rw [sub_mul, one_mul, groupedProjection_idempotent]
  noncomm_ring

theorem groupedComplement_idempotent :
    groupedComplement * groupedComplement = groupedComplement := by
  calc
    groupedComplement * groupedComplement =
        groupedComplement * (1 - groupedProjection) := by
          rfl
    _ = groupedComplement * 1 -
        groupedComplement * groupedProjection := by
          rw [mul_sub]
    _ = groupedComplement - groupedComplement * groupedProjection := by
          rw [mul_one]
    _ = groupedComplement := by
          rw [groupedComplement_mul_projection]
          simp

theorem groupedProjection_apply_branch_two :
    groupedProjection
        (fun w : ℕ → Fin 4 =>
          if headN w = (2 : Fin 4) then (1 : ℂ) else 0)
        (fun _ : ℕ => (2 : Fin 4)) = (1 / 2 : ℂ) := by
  have hdecomp : groupedProjection =
      (1 / 2 : ℂ) •
        (matrixUnit (0 : Fin 4) 0 + matrixUnit 0 1 +
          matrixUnit 1 0 + matrixUnit 1 1 +
          matrixUnit 2 2 + matrixUnit 2 3 +
          matrixUnit 3 2 + matrixUnit 3 3) := by
    dsimp [groupedProjection, groupedS1, groupedS2, groupedS1star,
      groupedS2star, matrixUnit]
    simp only [mul_smul_comm, add_mul, mul_add, smul_add]
    abel
  rw [hdecomp]
  simp [matrixUnit_apply, headN, tailN, prependN]

theorem groupedComplement_ne_zero : groupedComplement ≠ 0 := by
  intro h
  have h_eval := congrArg
    (fun T : CantorOperator =>
      T
        (fun w : ℕ → Fin 4 =>
          if headN w = (2 : Fin 4) then (1 : ℂ) else 0)
        (fun _ : ℕ => (2 : Fin 4))) h
  change ((1 : CantorOperator)
      (fun w : ℕ → Fin 4 =>
        if headN w = (2 : Fin 4) then (1 : ℂ) else 0)
      (fun _ : ℕ => (2 : Fin 4)) -
      groupedProjection
        (fun w : ℕ → Fin 4 =>
          if headN w = (2 : Fin 4) then (1 : ℂ) else 0)
        (fun _ : ℕ => (2 : Fin 4))) = 0 at h_eval
  rw [groupedProjection_apply_branch_two] at h_eval
  norm_num [headN] at h_eval

/-- A chiral projected-sector datum on the concrete O₄ Cantor carrier. -/
structure Datum where
  generators : CuntzO2Generators CantorOperator
  S1star_S1 : generators.S1star * generators.S1 = 1
  S2star_S2 : generators.S2star * generators.S2 = 1
  S1star_S2 : generators.S1star * generators.S2 = 0
  S2star_S1 : generators.S2star * generators.S1 = 0
  projection : CantorOperator
  completeness :
    generators.S1 * generators.S1star +
        generators.S2 * generators.S2star = projection
  dirac : CantorOperator
  dirac_eq_chiral :
    dirac = QPlus generators + QMinus generators

/-! The concrete grouped O₄ datum.  Its completeness field is the projection
    `groupedProjection`, not the identity of the full carrier. -/
def groupedDatum : Datum where
  generators := groupedGenerators
  S1star_S1 := groupedS1star_S1
  S2star_S2 := groupedS2star_S2
  S1star_S2 := groupedS1star_S2
  S2star_S1 := groupedS2star_S1
  projection := groupedProjection
  completeness := grouped_completeness
  dirac := QPlus groupedGenerators + QMinus groupedGenerators
  dirac_eq_chiral := rfl

namespace Datum

variable (D : Datum)

/-- The represented positive chiral supercharge. -/
abbrev qPlus : CantorOperator := QPlus D.generators

/-- The represented negative chiral supercharge. -/
abbrev qMinus : CantorOperator := QMinus D.generators

/-- The represented chiral Dirac operator. -/
abbrev chiralDirac : CantorOperator := D.qPlus + D.qMinus

theorem qPlus_sq_zero : D.qPlus * D.qPlus = 0 :=
  qplus_nilpotent D.generators D.S2star_S1

theorem qMinus_sq_zero : D.qMinus * D.qMinus = 0 :=
  qminus_nilpotent D.generators D.S1star_S2

theorem chiral_anticommutator_eq_projection :
    D.qPlus * D.qMinus + D.qMinus * D.qPlus = D.projection := by
  rw [qplus_qminus_product D.generators D.S2star_S2,
    qminus_qplus_product D.generators D.S1star_S1,
    D.completeness]

theorem projection_mul_qPlus : D.projection * D.qPlus = D.qPlus := by
  rw [← D.chiral_anticommutator_eq_projection]
  calc
    (D.qPlus * D.qMinus + D.qMinus * D.qPlus) * D.qPlus =
        D.qPlus * D.qMinus * D.qPlus + D.qMinus * D.qPlus * D.qPlus := by
          noncomm_ring
    _ = D.qPlus := by
      have htriple : D.qPlus * D.qMinus * D.qPlus = D.qPlus := by
        change QPlus D.generators * QMinus D.generators * QPlus D.generators =
          QPlus D.generators
        exact qplus_qminus_qplus D.generators D.S2star_S2 D.S1star_S1
      have hnil : D.qMinus * D.qPlus * D.qPlus = 0 := by
        rw [mul_assoc, D.qPlus_sq_zero, mul_zero]
      rw [htriple, hnil]
      simp

theorem qPlus_mul_projection : D.qPlus * D.projection = D.qPlus := by
  rw [← D.chiral_anticommutator_eq_projection]
  calc
    D.qPlus * (D.qPlus * D.qMinus + D.qMinus * D.qPlus) =
        D.qPlus * D.qPlus * D.qMinus + D.qPlus * D.qMinus * D.qPlus := by
          noncomm_ring
    _ = D.qPlus := by
      have hnil : D.qPlus * D.qPlus * D.qMinus = 0 := by
        calc
          D.qPlus * D.qPlus * D.qMinus =
              (D.qPlus * D.qPlus) * D.qMinus := rfl
          _ = 0 * D.qMinus := by rw [D.qPlus_sq_zero]
          _ = 0 := zero_mul _
      have htriple : D.qPlus * D.qMinus * D.qPlus = D.qPlus := by
        change QPlus D.generators * QMinus D.generators * QPlus D.generators =
          QPlus D.generators
        exact qplus_qminus_qplus D.generators D.S2star_S2 D.S1star_S1
      rw [hnil, htriple]
      simp

theorem projection_mul_qMinus : D.projection * D.qMinus = D.qMinus := by
  rw [← D.chiral_anticommutator_eq_projection]
  calc
    (D.qPlus * D.qMinus + D.qMinus * D.qPlus) * D.qMinus =
        D.qPlus * D.qMinus * D.qMinus + D.qMinus * D.qPlus * D.qMinus := by
          noncomm_ring
    _ = D.qMinus := by
      have hnil : D.qPlus * D.qMinus * D.qMinus = 0 := by
        rw [mul_assoc, D.qMinus_sq_zero, mul_zero]
      have htriple : D.qMinus * D.qPlus * D.qMinus = D.qMinus := by
        change QMinus D.generators * QPlus D.generators * QMinus D.generators =
          QMinus D.generators
        exact qminus_qplus_qminus D.generators D.S1star_S1 D.S2star_S2
      rw [hnil, htriple]
      simp

theorem qMinus_mul_projection : D.qMinus * D.projection = D.qMinus := by
  rw [← D.chiral_anticommutator_eq_projection]
  calc
    D.qMinus * (D.qPlus * D.qMinus + D.qMinus * D.qPlus) =
        D.qMinus * D.qPlus * D.qMinus + D.qMinus * D.qMinus * D.qPlus := by
          noncomm_ring
    _ = D.qMinus := by
      have htriple : D.qMinus * D.qPlus * D.qMinus = D.qMinus := by
        change QMinus D.generators * QPlus D.generators * QMinus D.generators =
          QMinus D.generators
        exact qminus_qplus_qminus D.generators D.S1star_S1 D.S2star_S2
      have hnil : D.qMinus * D.qMinus * D.qPlus = 0 := by
        calc
          D.qMinus * D.qMinus * D.qPlus =
              (D.qMinus * D.qMinus) * D.qPlus := rfl
          _ = 0 * D.qPlus := by rw [D.qMinus_sq_zero]
          _ = 0 := zero_mul _
      rw [htriple, hnil]
      simp

theorem chiralDirac_sq_eq_projection :
    D.chiralDirac * D.chiralDirac = D.projection := by
  simp only [chiralDirac, add_mul, mul_add, D.qPlus_sq_zero,
    D.qMinus_sq_zero, zero_add, add_zero]
  simpa [add_comm] using D.chiral_anticommutator_eq_projection

theorem chiralDirac_commutes_projection :
    D.chiralDirac * D.projection = D.projection * D.chiralDirac := by
  calc
    D.chiralDirac * D.projection =
        D.chiralDirac * (D.chiralDirac * D.chiralDirac) := by
          rw [D.chiralDirac_sq_eq_projection]
    _ = (D.chiralDirac * D.chiralDirac) * D.chiralDirac := by
          rw [mul_assoc]
    _ = D.projection * D.chiralDirac := by
          rw [D.chiralDirac_sq_eq_projection]

theorem dirac_eq_chiralDirac : D.dirac = D.chiralDirac := by
  exact D.dirac_eq_chiral

theorem grouped_chiralDirac_sq_eq_projection :
    groupedDatum.chiralDirac * groupedDatum.chiralDirac = groupedProjection := by
  exact groupedDatum.chiralDirac_sq_eq_projection

theorem grouped_dirac_eq_chiralDirac :
    groupedDatum.dirac = groupedDatum.chiralDirac := by
  exact groupedDatum.dirac_eq_chiralDirac

end Datum

end InfoGeometry.Canonical.CantorO4ChiralSuperchargeRepresentation
