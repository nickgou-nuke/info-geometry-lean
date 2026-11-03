/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectLevelSet
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import Mathlib.Tactic.NoncommRing

/-!
# Weyl rescaling and the Peirce defect metric

These results formalize generator rescaling, not inner conjugation. The
rescaled pair has metric `E * V` when the tetrad `E` commutes with the lower
generator. The particular choice `E = V - 1` gives the idempotency defect.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

def opComm (x y : B) : B := x * y - y * x
def opAnticomm (x y : B) : B := x * y + y * x

def defectVielbein (v : B) : B := v - 1
def rescaledPlus (e np : B) : B := e * np
def rescaledMinus (e nm : B) : B := e * nm
def rescaledPhi (e np nm : B) : B := rescaledPlus e np + nm
def rescaledJ (e np nm : B) : B := rescaledPlus e np - nm

def twoScalePhi (ep em np nm : B) : B := ep * np + em * nm
def twoScaleJ (ep em np nm : B) : B := ep * np - em * nm

/-- Exact ordered products for two independently rescaled generators. The
cross-centralizer hypotheses are only those needed to move each scale past
the opposite generator; no relation between the two scale factors is assumed. -/
theorem two_scale_ordered_products (ep em np nm : B)
    (hNpEm : np * em = em * np) (hNmEp : nm * ep = ep * nm) :
    (ep * np) * (em * nm) = (ep * em) * (np * nm) ∧
    (em * nm) * (ep * np) = (em * ep) * (nm * np) := by
  constructor
  · calc
      (ep * np) * (em * nm) = ep * (np * em) * nm := by simp [mul_assoc]
      _ = ep * (em * np) * nm := by rw [hNpEm]
      _ = (ep * em) * (np * nm) := by simp [mul_assoc]
  · calc
      (em * nm) * (ep * np) = em * (nm * ep) * np := by simp [mul_assoc]
      _ = em * (ep * nm) * np := by rw [hNmEp]
      _ = (em * ep) * (nm * np) := by simp [mul_assoc]

/-- The two-scale metric and chirality retain the order of the scale factors.
They reduce to a common left factor only when the scale factors commute. -/
theorem two_scale_metric_and_chirality (ep em np nm : B)
    (hNpEm : np * em = em * np) (hNmEp : nm * ep = ep * nm) :
    opAnticomm (ep * np) (em * nm) =
        (ep * em) * (np * nm) + (em * ep) * (nm * np) ∧
    opComm (ep * np) (em * nm) =
        (ep * em) * (np * nm) - (em * ep) * (nm * np) := by
  have hProd := two_scale_ordered_products ep em np nm hNpEm hNmEp
  constructor
  · simp only [opAnticomm]
    rw [hProd.1, hProd.2]
  · simp only [opComm]
    rw [hProd.1, hProd.2]

/-- If the two scale factors commute, the ordered two-scale formulas combine
into the usual common Weyl factor multiplying the original metric and
commutator. -/
theorem two_scale_common_factor (ep em np nm : B)
    (hNpEm : np * em = em * np) (hNmEp : nm * ep = ep * nm)
    (hScale : ep * em = em * ep) :
    opAnticomm (ep * np) (em * nm) =
        (ep * em) * opAnticomm np nm ∧
    opComm (ep * np) (em * nm) =
        (ep * em) * opComm np nm := by
  rcases two_scale_metric_and_chirality ep em np nm hNpEm hNmEp with
    ⟨hMetric, hChiral⟩
  constructor
  · rw [hMetric, hScale]
    simp only [opAnticomm, mul_add]
  · rw [hChiral, hScale]
    simp only [opComm, mul_sub]

/-- A left rescaling transports the anticommutator by `E` if `E` commutes
with the second generator. No commutativity of the ambient ring is assumed. -/
theorem rescaled_anticommutator (e np nm : B)
    (hE : e * nm = nm * e) :
    opAnticomm (rescaledPlus e np) nm = e * opAnticomm np nm := by
  have hterm : nm * (e * np) = e * (nm * np) := by
    rw [← mul_assoc, ← hE, mul_assoc]
  simp only [opAnticomm, rescaledPlus]
  calc
    e * np * nm + nm * (e * np) = e * (np * nm) + e * (nm * np) := by
      rw [mul_assoc, hterm]
    _ = e * (np * nm + nm * np) := by rw [mul_add]

/-- The corresponding commutator transformation, with the same ordered
centralizer condition. -/
theorem rescaled_commutator (e np nm : B)
    (hE : e * nm = nm * e) :
    opComm (rescaledPlus e np) nm = e * opComm np nm := by
  have hterm : nm * (e * np) = e * (nm * np) := by
    rw [← mul_assoc, ← hE, mul_assoc]
  simp only [opComm, rescaledPlus]
  calc
    e * np * nm - nm * (e * np) = e * (np * nm) - e * (nm * np) := by
      rw [mul_assoc, hterm]
    _ = e * (np * nm - nm * np) := by rw [mul_sub]

private theorem rescaled_reverse_cross (e np nm : B)
    (hEM : e * nm = nm * e) :
    nm * (e * np) = e * (nm * np) := by
  rw [← mul_assoc, ← hEM, mul_assoc]

/-- Rescaling one member of an isotropic nilpotent pair preserves its
Tetraktys multiplication pattern, with the metric and chirality multiplied
on the left by the rescaling operator. The hypotheses state the required
centralizer relations explicitly. -/
theorem rescaled_tetraktys (e np nm : B)
    (hNp : np * np = 0) (hNm : nm * nm = 0)
    (hEN : e * np = np * e) (hEM : e * nm = nm * e) :
    rescaledPhi e np nm * rescaledPhi e np nm =
      e * opAnticomm np nm ∧
    rescaledJ e np nm * rescaledJ e np nm =
      -(e * opAnticomm np nm) ∧
    rescaledJ e np nm * rescaledPhi e np nm =
      e * opComm np nm ∧
    rescaledPhi e np nm * rescaledJ e np nm =
      -(e * opComm np nm) ∧
    opAnticomm (rescaledPhi e np nm) (rescaledJ e np nm) = 0 := by
  have hPlusSq : rescaledPlus e np * rescaledPlus e np = 0 := by
    calc
      rescaledPlus e np * rescaledPlus e np = e * (np * e) * np := by
        simp [rescaledPlus, mul_assoc]
      _ = e * (e * np) * np := by rw [← hEN]
      _ = e * e * (np * np) := by simp [mul_assoc]
      _ = 0 := by rw [hNp]; simp
  have hMinusSq : nm * nm = 0 := hNm
  have hPlusMinus : rescaledPlus e np * nm = e * (np * nm) := by
    simp [rescaledPlus, mul_assoc]
  have hMinusPlus : nm * rescaledPlus e np = e * (nm * np) := by
    exact rescaled_reverse_cross e np nm hEM
  constructor
  · dsimp [rescaledPhi]
    unfold opAnticomm
    simp only [add_mul, mul_add, hPlusSq, hMinusSq, zero_add,
      hPlusMinus, hMinusPlus]
    abel_nf
  constructor
  · dsimp [rescaledJ]
    unfold opAnticomm
    simp only [sub_mul, mul_sub, hPlusSq, hMinusSq, zero_sub,
      hPlusMinus, hMinusPlus]
    rw [mul_add]
    abel_nf
  constructor
  · dsimp [rescaledJ, rescaledPhi]
    unfold opComm
    simp only [sub_mul, mul_add, add_mul, hPlusSq, hMinusSq, zero_add,
      zero_sub, hPlusMinus, hMinusPlus]
    rw [mul_sub]
    abel_nf
  constructor
  · dsimp [rescaledPhi, rescaledJ]
    unfold opComm
    simp only [add_mul, mul_sub, hPlusSq, hMinusSq, add_zero,
      hPlusMinus, hMinusPlus]
    abel_nf
  · unfold opAnticomm rescaledPhi rescaledJ
    simp only [add_mul, mul_add, sub_mul, mul_sub, hPlusSq, hMinusSq]
    abel_nf

/-- The defect tetrad sends the metric `V` to `V² - V`. -/
theorem defect_rescaling_metric (v : B) :
    defectVielbein v * v = v * v - v := by
  rw [defectVielbein, sub_mul, one_mul]

/-- On the defect-one shell, the defect factor `v - 1` is a unit with inverse
`v`. Thus the normalization is an invertible operator rescaling on this
shell; away from it, `v - 1` is only a rescaling factor. -/
theorem defect_vielbein_is_unit_on_shell (v : B)
    (hShell : v * v - v = 1) :
    v * defectVielbein v = 1 ∧ defectVielbein v * v = 1 := by
  constructor
  · dsimp [defectVielbein]
    rw [mul_sub, mul_one]
    exact hShell
  · exact defect_rescaling_metric v ▸ hShell

/-- Under the shell equation `V² - V = 1`, the defect tetrad normalizes
the anticommutator to the unit. -/
theorem defect_rescaling_undeforms
    (np nm v : B) (hMetric : opAnticomm np nm = v)
    (hCentral : (v - 1) * nm = nm * (v - 1))
    (hShell : v * v - v = 1) :
    opAnticomm (rescaledPlus (defectVielbein v) np) nm = 1 := by
  calc
    opAnticomm (rescaledPlus (defectVielbein v) np) nm =
        defectVielbein v * opAnticomm np nm :=
      rescaled_anticommutator _ _ _ hCentral
    _ = defectVielbein v * v := by rw [hMetric]
    _ = v * v - v := defect_rescaling_metric v
    _ = 1 := hShell

/-- Peirce specialization: the defect Weyl factor `V - 1` commutes with the
lower cone, so on the defect-one level set it normalizes the Peirce metric.
This is a generator rescaling; no conjugation is asserted. -/
theorem peirce_defect_weyl_rescaling_on_unit_shell
    {P : B} (hP : P * P = P) (A C : B)
    (hShell : idempotencyDefect (genV P A C) = 1) :
    opAnticomm
      (rescaledPlus (defectVielbein (genV P A C)) (conePlus P A))
      (coneMinus P C) = 1 := by
  have hCentral :
      (genV P A C - 1) * coneMinus P C =
        coneMinus P C * (genV P A C - 1) := by
    simp only [genV, anticomm, sub_mul, mul_sub, one_mul, mul_one]
    peirce_nf hP
  exact defect_rescaling_undeforms
    (conePlus P A) (coneMinus P C) (genV P A C) rfl hCentral hShell

/-- The chiral combinations `Σ ± J` square to the idempotency defect of
`V`.  The mixed combination `Σ + Φ` instead squares to `V² + V`; this
distinction follows from `Σ² = V²`, `J² = -V`, `Φ² = V`, and the respective
anticommutation relations. -/
theorem chiral_defect_square_roots (hP : P * P = P) (A C : B) :
    (genSig P A C + genJ P A C) * (genSig P A C + genJ P A C) =
      genV P A C * genV P A C - genV P A C ∧
    (genSig P A C - genJ P A C) * (genSig P A C - genJ P A C) =
      genV P A C * genV P A C - genV P A C ∧
    (genSig P A C + genPhi P A C) * (genSig P A C + genPhi P A C) =
      genV P A C * genV P A C + genV P A C ∧
    opAnticomm (genSig P A C + genJ P A C)
      (genSig P A C - genJ P A C) =
      (2 : ℤ) • (genV P A C * genV P A C + genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · have hAlgebra (s j : B) :
        opAnticomm (s + j) (s - j) =
          (2 : ℤ) • (s * s) - (2 : ℤ) • (j * j) := by
      dsimp [opAnticomm]
      noncomm_ring
    rw [hAlgebra]
    have hSig : genSig P A C * genSig P A C =
        genV P A C * genV P A C := by
      peirce_nf hP
    have hJ : genJ P A C * genJ P A C = -genV P A C := by
      peirce_nf hP
    rw [hSig, hJ]
    abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
