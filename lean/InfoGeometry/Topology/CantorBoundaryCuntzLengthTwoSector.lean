import InfoGeometry.Topology.CantorBoundaryCuntzFamily
import InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation
noncomputable section
namespace InfoGeometry.Topology.CantorBoundaryCuntzLengthTwoSector
open InfoGeometry.Topology.CantorBoundaryCuntzFamily
open InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation
abbrev Op := C4Functions →ₗ[ℂ] C4Functions

/-- First grouped creation branch on the concrete four-ary Cantor carrier. -/
def gS0 : Op := cuntzS 0 + cuntzS 1
/-- Second grouped creation branch on the concrete four-ary Cantor carrier. -/
def gS1 : Op := cuntzS 2 + cuntzS 3
/-- Algebraic dual of the first grouped branch.  The factor `1/2` is
chosen so the grouped family has the Cuntz contraction relations. -/
def gT0 : Op := (2 : ℂ)⁻¹ • (cuntzT 0 + cuntzT 1)
/-- Algebraic dual of the second grouped branch. -/
def gT1 : Op := (2 : ℂ)⁻¹ • (cuntzT 2 + cuntzT 3)
/-- The grouped two-branch Cuntz datum. -/
def g : CuntzO2Generators Op where
  S1 := gS0
  S2 := gS1
  S1star := gT0
  S2star := gT1
/-- The normalization identity used by the grouped contractions. -/
lemma half_one : (2 : ℂ)⁻¹ • (1 : Op) + (2 : ℂ)⁻¹ • (1 : Op) = 1 := by
  rw [← add_smul]
  rw [show (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 by norm_num]
  exact one_smul ℂ (1 : Op)

/-- Grouped contraction relation `(T₀ S₀) = 1`. -/
lemma o00 : gT0*gS0=1 := by
 dsimp [gT0,gS0]
 calc
  _ = (2:ℂ)⁻¹ • ((cuntzT 0+cuntzT 1)*(cuntzS 0+cuntzS 1)) := by rw [smul_mul_assoc]
  _ = (2:ℂ)⁻¹ • (cuntzT 0*cuntzS 0+cuntzT 0*cuntzS 1+(cuntzT 1*cuntzS 0+cuntzT 1*cuntzS 1)) := by congr 1
  _ = 1 := by
      rw [cuntz_ortho,cuntz_ortho,cuntz_ortho,cuntz_ortho]
      simp
      exact half_one
/-- Mixed grouped contraction vanishes. -/
lemma o01 : gT0*gS1=0 := by
 dsimp [gT0,gS1]
 calc
  _ = (2:ℂ)⁻¹ • ((cuntzT 0+cuntzT 1)*(cuntzS 2+cuntzS 3)) := by rw [smul_mul_assoc]
  _ = (2:ℂ)⁻¹ • (cuntzT 0*cuntzS 2+cuntzT 0*cuntzS 3+(cuntzT 1*cuntzS 2+cuntzT 1*cuntzS 3)) := by congr 1
  _ = 0 := by
      rw [cuntz_ortho,cuntz_ortho,cuntz_ortho,cuntz_ortho]
      simp
/-- Mixed grouped contraction vanishes. -/
lemma o10 : gT1*gS0=0 := by
 dsimp [gT1,gS0]
 calc
  _ = (2:ℂ)⁻¹ • ((cuntzT 2+cuntzT 3)*(cuntzS 0+cuntzS 1)) := by rw [smul_mul_assoc]
  _ = (2:ℂ)⁻¹ • (cuntzT 2*cuntzS 0+cuntzT 2*cuntzS 1+(cuntzT 3*cuntzS 0+cuntzT 3*cuntzS 1)) := by congr 1
  _ = 0 := by
      rw [cuntz_ortho,cuntz_ortho,cuntz_ortho,cuntz_ortho]
      simp
/-- Grouped contraction relation `(T₁ S₁) = 1`. -/
lemma o11 : gT1*gS1=1 := by
 dsimp [gT1,gS1]
 calc
  _ = (2:ℂ)⁻¹ • ((cuntzT 2+cuntzT 3)*(cuntzS 2+cuntzS 3)) := by rw [smul_mul_assoc]
  _ = (2:ℂ)⁻¹ • (cuntzT 2*cuntzS 2+cuntzT 2*cuntzS 3+(cuntzT 3*cuntzS 2+cuntzT 3*cuntzS 3)) := by congr 1
  _ = 1 := by
      rw [cuntz_ortho,cuntz_ortho,cuntz_ortho,cuntz_ortho]
      simp
      exact half_one
/-- The projected even sector selected by the grouping. -/
def P : Op := gS0 * gT0 + gS1 * gT1
/-- The induced pair-swap involution, represented algebraically by `2P-I`. -/
def C : Op := (2 : ℂ) • P - 1

/-- The grouped even sector is an idempotent projection. -/
theorem P_sq : P * P = P := by
  dsimp [P]
  calc
    (gS0 * gT0 + gS1 * gT1) * (gS0 * gT0 + gS1 * gT1) =
      gS0 * (gT0 * gS0) * gT0 + gS0 * (gT0 * gS1) * gT1 +
        (gS1 * (gT1 * gS0) * gT0 + gS1 * (gT1 * gS1) * gT1) := by noncomm_ring
    _ = gS0 * gT0 + gS1 * gT1 := by rw [o00, o01, o10, o11]; simp

/-- The induced pair-swap operator is an involution. -/
theorem C_sq : C * C = 1 := by
  dsimp [C]
  rw [show (2 : ℂ) • P = P + P by module]
  noncomm_ring
  rw [P_sq]
  noncomm_ring

/-- The projection is the `(+1)` spectral projector of `C`. -/
lemma P_eq_half_one_add_C : P = (2 : ℂ)⁻¹ • (1 + C) := by
  dsimp [C]
  simp only [smul_add, smul_sub, smul_smul]
  norm_num

/-- The ungrouped first branch detects only half of the grouped sector. -/
lemma rawT0_P_rawS0 :
    cuntzT 0 * P * cuntzS 0 = (2 : ℂ)⁻¹ • (1 : Op) := by
  have hT0gS0 : cuntzT 0 * gS0 = 1 := by
    dsimp [gS0]
    rw [mul_add, cuntz_ortho, cuntz_ortho]
    simp
  have hT0gS1 : cuntzT 0 * gS1 = 0 := by
    dsimp [gS1]
    rw [mul_add, cuntz_ortho, cuntz_ortho]
    simp
  have hT0gT0S0 : gT0 * cuntzS 0 = (2 : ℂ)⁻¹ • (1 : Op) := by
    dsimp [gT0]
    calc
      (2 : ℂ)⁻¹ • (cuntzT 0 + cuntzT 1) * cuntzS 0 =
          (2 : ℂ)⁻¹ • ((cuntzT 0 + cuntzT 1) * cuntzS 0) := by
            rw [smul_mul_assoc]
      _ = (2 : ℂ)⁻¹ • (1 : Op) := by
        rw [add_mul, cuntz_ortho, cuntz_ortho]
        simp
  have hT0gT1S0 : gT1 * cuntzS 0 = 0 := by
    dsimp [gT1]
    calc
      (2 : ℂ)⁻¹ • (cuntzT 2 + cuntzT 3) * cuntzS 0 =
          (2 : ℂ)⁻¹ • ((cuntzT 2 + cuntzT 3) * cuntzS 0) := by
            rw [smul_mul_assoc]
      _ = 0 := by
        rw [add_mul, cuntz_ortho, cuntz_ortho]
        simp
  dsimp [P]
  calc
    cuntzT 0 * (gS0 * gT0 + gS1 * gT1) * cuntzS 0 =
        (cuntzT 0 * gS0) * (gT0 * cuntzS 0) +
          (cuntzT 0 * gS1) * (gT1 * cuntzS 0) := by noncomm_ring
    _ = (2 : ℂ)⁻¹ • (1 : Op) := by
      rw [hT0gS0, hT0gS1, hT0gT0S0, hT0gT1S0]
      simp

/-- The grouped projection is proper on the concrete O₄ carrier. -/
theorem P_ne_one : P ≠ (1 : Op) := by
  intro hP
  have hdet := congrArg (fun X : Op => cuntzT 0 * X * cuntzS 0) hP
  dsimp at hdet
  rw [rawT0_P_rawS0] at hdet
  have hfull : cuntzT 0 * (1 : Op) * cuntzS 0 = 1 := by
    simp [cuntz_ortho]
  rw [hfull] at hdet
  have heval := congrArg
    (fun X : Op => X (fun _ => (1 : ℂ)) (fun _ => (0 : Fin 4))) hdet
  have hscalar : (2 : ℂ)⁻¹ = 1 := by
    simpa using heval
  norm_num at hscalar

/-- Projected positive chiral zero mode. -/
noncomputable def qPlusC : Op := QPlus g
/-- Projected negative chiral zero mode. -/
noncomputable def qMinusC : Op := QMinus g

/-- The grouped positive charge is an explicit off-diagonal matrix-unit sum. -/
lemma qPlusC_eq_matrixUnit_sum :
    qPlusC = (2 : ℂ)⁻¹ •
      (CantorBoundaryCuntzFamily.matrixUnit 0 2 +
        CantorBoundaryCuntzFamily.matrixUnit 0 3 +
        (CantorBoundaryCuntzFamily.matrixUnit 1 2 +
          CantorBoundaryCuntzFamily.matrixUnit 1 3)) := by
  dsimp [qPlusC, QPlus, g, gS0, gT1]
  rw [mul_smul_comm, add_mul, mul_add]
  dsimp [CantorBoundaryCuntzFamily.matrixUnit]
  simp only [mul_add]

/-- The grouped negative charge is the opposite off-diagonal matrix-unit sum. -/
lemma qMinusC_eq_matrixUnit_sum :
    qMinusC = (2 : ℂ)⁻¹ •
      (CantorBoundaryCuntzFamily.matrixUnit 2 0 +
        CantorBoundaryCuntzFamily.matrixUnit 3 0 +
        (CantorBoundaryCuntzFamily.matrixUnit 2 1 +
          CantorBoundaryCuntzFamily.matrixUnit 3 1)) := by
  dsimp [qMinusC, QMinus, g, gS1, gT0]
  rw [mul_smul_comm, add_mul, mul_add]
  dsimp [CantorBoundaryCuntzFamily.matrixUnit]
  simp only [mul_add]
  module

/-- The projected positive chiral mode is nilpotent. -/
lemma qPlusC_sq : qPlusC * qPlusC = 0 := by
  exact qplus_nilpotent g o10

/-- The projected negative chiral mode is nilpotent. -/
lemma qMinusC_sq : qMinusC * qMinusC = 0 := by
  exact qminus_nilpotent g o01

/-- The odd--odd bracket closes on `P`, not on the full identity. -/
lemma qC_anticommutator : qPlusC * qMinusC + qMinusC * qPlusC = P := by
  change QPlus g * QMinus g + QMinus g * QPlus g = P
  rw [qplus_qminus_product g o11, qminus_qplus_product g o00]
  rfl

lemma P_mul_qPlusC : P * qPlusC = qPlusC := by
  rw [← qC_anticommutator]
  calc
    (qPlusC * qMinusC + qMinusC * qPlusC) * qPlusC =
        qPlusC * qMinusC * qPlusC + qMinusC * qPlusC * qPlusC := by
          noncomm_ring
    _ = qPlusC := by
      have htriple : qPlusC * qMinusC * qPlusC = qPlusC := by
        change QPlus g * QMinus g * QPlus g = QPlus g
        rw [qplus_qminus_product g o11]
        change gS0 * (gT0 * gS0) * gT1 = gS0 * gT1
        rw [o00]
        simp
      have hnil : qMinusC * qPlusC * qPlusC = 0 := by
        rw [mul_assoc, qPlusC_sq, mul_zero]
      rw [htriple, hnil]
      simp

lemma qPlusC_mul_P : qPlusC * P = qPlusC := by
  rw [← qC_anticommutator]
  calc
    qPlusC * (qPlusC * qMinusC + qMinusC * qPlusC) =
        qPlusC * qPlusC * qMinusC + qPlusC * qMinusC * qPlusC := by
          noncomm_ring
    _ = qPlusC := by
      have htriple : qPlusC * qMinusC * qPlusC = qPlusC := by
        change QPlus g * QMinus g * QPlus g = QPlus g
        rw [qplus_qminus_product g o11]
        change gS0 * (gT0 * gS0) * gT1 = gS0 * gT1
        rw [o00]
        simp
      have hnil : qPlusC * qPlusC * qMinusC = 0 := by
        rw [qPlusC_sq, zero_mul]
      rw [hnil, htriple]
      simp

lemma P_mul_qMinusC : P * qMinusC = qMinusC := by
  rw [← qC_anticommutator]
  calc
    (qPlusC * qMinusC + qMinusC * qPlusC) * qMinusC =
        qPlusC * qMinusC * qMinusC + qMinusC * qPlusC * qMinusC := by
          noncomm_ring
    _ = qMinusC := by
      have htriple : qMinusC * qPlusC * qMinusC = qMinusC := by
        change QMinus g * QPlus g * QMinus g = QMinus g
        rw [qminus_qplus_product g o00]
        change gS1 * (gT1 * gS1) * gT0 = gS1 * gT0
        rw [o11]
        simp
      have hnil : qPlusC * qMinusC * qMinusC = 0 := by
        rw [mul_assoc, qMinusC_sq, mul_zero]
      rw [hnil, htriple]
      simp

lemma qMinusC_mul_P : qMinusC * P = qMinusC := by
  rw [← qC_anticommutator]
  calc
    qMinusC * (qPlusC * qMinusC + qMinusC * qPlusC) =
        qMinusC * qPlusC * qMinusC + qMinusC * qMinusC * qPlusC := by
          noncomm_ring
    _ = qMinusC := by
      have htriple : qMinusC * qPlusC * qMinusC = qMinusC := by
        change QMinus g * QPlus g * QMinus g = QMinus g
        rw [qminus_qplus_product g o00]
        change gS1 * (gT1 * gS1) * gT0 = gS1 * gT0
        rw [o11]
        simp
      have hnil : qMinusC * qMinusC * qPlusC = 0 := by
        rw [qMinusC_sq, zero_mul]
      rw [htriple, hnil]
      simp

/-- The projected chiral Dirac square is the sector projector. -/
lemma qC_dirac_square : (qPlusC + qMinusC) * (qPlusC + qMinusC) = P := by
  calc
    (qPlusC + qMinusC) * (qPlusC + qMinusC) =
        qPlusC * qPlusC + qPlusC * qMinusC +
          (qMinusC * qPlusC + qMinusC * qMinusC) := by noncomm_ring
    _ = P := by rw [qPlusC_sq, qMinusC_sq]; simp [qC_anticommutator]

noncomputable def projectedCantorDirac : Op := qPlusC + qMinusC

@[simp] theorem projectedCantorDirac_square :
    projectedCantorDirac * projectedCantorDirac = P := by
  exact qC_dirac_square

@[simp] theorem P_mul_projectedCantorDirac :
    P * projectedCantorDirac = projectedCantorDirac := by
  dsimp [projectedCantorDirac]
  rw [mul_add, P_mul_qPlusC, P_mul_qMinusC]

@[simp] theorem projectedCantorDirac_mul_P :
    projectedCantorDirac * P = projectedCantorDirac := by
  dsimp [projectedCantorDirac]
  rw [add_mul, qPlusC_mul_P, qMinusC_mul_P]

@[simp] theorem projectedCantorDirac_mul_projectedCantorDirac_mul_P :
    projectedCantorDirac * projectedCantorDirac * P = P := by
  rw [projectedCantorDirac_square, P_sq]

@[simp] theorem P_mul_projectedCantorDirac_mul_projectedCantorDirac :
    P * projectedCantorDirac * projectedCantorDirac = P := by
  rw [P_mul_projectedCantorDirac, projectedCantorDirac_square]

@[simp] theorem dirac_agrees_sector_square
    (D : Op) (hD : D = qPlusC + qMinusC) : D * D = P := by
  rw [hD]
  exact qC_dirac_square

end InfoGeometry.Topology.CantorBoundaryCuntzLengthTwoSector
