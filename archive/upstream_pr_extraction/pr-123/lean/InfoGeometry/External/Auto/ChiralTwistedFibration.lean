import Mathlib.Tactic

open Matrix

/-!
# Chiral Twisted Fibration

Lean mirror of `proofs/chiral_twisted_fibration_sympy.py`.

The point is bookkeeping discipline: `S7`, `S4`, `CP2`, Klein/V4 monodromy,
and chiral braiding are not identified.  They are organized as base charts,
fiber sectors, and transport/monodromy data.
-/

noncomputable section

abbrev R2 := ℝ × ℝ

def T (p : R2) : R2 := (p.1, p.2 + 1)
def TInv (p : R2) : R2 := (p.1, p.2 - 1)
def M (p : R2) : R2 := (p.1, -p.2)
def G (p : R2) : R2 := (p.1 + 1, -p.2)
def H (p : R2) : R2 := (-p.1, -p.2)

theorem klein_relation (p : R2) : G (T p) = TInv (G p) := by
  ext
  · simp [G, T, TInv]
  · simp [G, T, TInv]
    ring

theorem glide_square (p : R2) : G (G p) = (p.1 + 2, p.2) := by
  ext
  · simp [G]
    ring
  · simp [G]

theorem mirror_involution (p : R2) : M (M p) = p := by
  ext <;> simp [M]

theorem half_turn_involution (p : R2) : H (H p) = p := by
  ext <;> simp [H]

theorem glide_translated_mirror (p : R2) : G p = ((M p).1 + 1, (M p).2) := by
  ext <;> simp [G, M]

theorem mirror_fixed_iff (p : R2) : M p = p ↔ p.2 = 0 := by
  constructor
  · intro h
    have hy : -p.2 = p.2 := congrArg Prod.snd h
    linarith
  · intro hy
    ext <;> simp [M, hy]

theorem half_turn_fixed_iff (p : R2) : H p = p ↔ p = (0, 0) := by
  constructor
  · intro h
    have hx : -p.1 = p.1 := congrArg Prod.fst h
    have hy : -p.2 = p.2 := congrArg Prod.snd h
    ext <;> linarith
  · intro h
    rw [h]
    simp [H]

def ePlus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def eMinus : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
def pseudo : Matrix (Fin 2) (Fin 2) ℝ := ePlus * eMinus

/-- Sheet swap (Tomita swap operator) on two sheets. -/
def sheetSwap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Sheet grading/grade operator (even vs odd sheet sector). -/
def sheetGrading : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Emergent complex structure on the doubled space: `K = J ε`. -/
def emergentComplex : Matrix (Fin 2) (Fin 2) ℝ := sheetSwap * sheetGrading

theorem ePlus_sq : ePlus * ePlus = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ePlus]

theorem eMinus_sq : eMinus * eMinus = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eMinus]

/-- Sheet swap is an involution: `J² = I`. -/
theorem sheetSwap_sq : sheetSwap * sheetSwap = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sheetSwap]

/-- Sheet grading is an involution: `ε² = I`. -/
theorem sheetGrading_sq : sheetGrading * sheetGrading = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sheetGrading]

/-- The sheet swap and grading anticommute: `J ε = - ε J`. -/
theorem sheetSwap_grading_anticomm : sheetSwap * sheetGrading = -(sheetGrading * sheetSwap) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sheetSwap, sheetGrading]

/-- Emergent complex structure from two-sheeted composition: `K = J ε`. -/
theorem emergentComplex_eq_eMinus : emergentComplex = eMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emergentComplex, eMinus, sheetSwap, sheetGrading]

/-- `K² = -I`, so `K` is an honest complex structure on the doubled real sheets. -/
theorem emergentComplex_sq : emergentComplex * emergentComplex = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [emergentComplex_eq_eMinus]
  simp [eMinus_sq]


theorem clifford_anticomm : ePlus * eMinus + eMinus * ePlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ePlus, eMinus]

theorem det_ePlus : ePlus.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [ePlus]

theorem det_eMinus : eMinus.det = 1 := by
  rw [Matrix.det_fin_two]
  norm_num [eMinus]

theorem det_pseudo : pseudo.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [pseudo, ePlus, eMinus, Matrix.mul_apply, Fin.sum_univ_two]

inductive DetSector where
  | positive
  | negative
  | null
  deriving DecidableEq, Repr

def detSector (A : Matrix (Fin 2) (Fin 2) ℝ) : DetSector :=
  if 0 < A.det then DetSector.positive
  else if A.det < 0 then DetSector.negative
  else DetSector.null

def nullProjector : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

theorem sector_eMinus : detSector eMinus = DetSector.positive := by
  simp [detSector, det_eMinus]

theorem sector_ePlus : detSector ePlus = DetSector.negative := by
  simp [detSector, det_ePlus]

theorem sector_nullProjector : detSector nullProjector = DetSector.null := by
  rw [detSector]
  rw [Matrix.det_fin_two]
  norm_num [nullProjector]

/-- Homogeneous coordinate carrier for the `CP¹` twistor fiber, before quotienting
by nonzero complex scale. -/
abbrev TwistorFiberCoord : Type := Fin 2 → ℂ

/-- Left chiral projector on the two homogeneous twistor-fiber coordinates. -/
def chiralProjectorL : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- Right chiral projector on the two homogeneous twistor-fiber coordinates. -/
def chiralProjectorR : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- Apply a chiral projector to a twistor-fiber coordinate vector. -/
def applyTwistorProjector
    (P : Matrix (Fin 2) (Fin 2) ℂ) (z : TwistorFiberCoord) : TwistorFiberCoord :=
  P.mulVec z

theorem chiralProjectorL_idempotent :
    chiralProjectorL * chiralProjectorL = chiralProjectorL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjectorL, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralProjectorR_idempotent :
    chiralProjectorR * chiralProjectorR = chiralProjectorR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjectorR, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralProjector_orthogonal :
    chiralProjectorL * chiralProjectorR = 0 ∧
      chiralProjectorR * chiralProjectorL = 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralProjectorL, chiralProjectorR, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralProjectorL, chiralProjectorR, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralProjector_partition :
    chiralProjectorL + chiralProjectorR = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralProjectorL, chiralProjectorR]

theorem chiralProjectorL_apply (z : TwistorFiberCoord) :
    applyTwistorProjector chiralProjectorL z = fun i => if i = 0 then z 0 else 0 := by
  funext i
  fin_cases i <;>
    simp [applyTwistorProjector, chiralProjectorL, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail]

theorem chiralProjectorR_apply (z : TwistorFiberCoord) :
    applyTwistorProjector chiralProjectorR z = fun i => if i = 1 then z 1 else 0 := by
  funext i
  fin_cases i <;>
    simp [applyTwistorProjector, chiralProjectorR, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail]

def RLeft (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![q, 0; 0, q ^ 4]
def RRight (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![q ^ 4, 0; 0, q]

theorem det_RLeft (q : ℂ) (hq : q ^ 5 = 1) : (RLeft q).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [RLeft]
  calc
    q * q ^ 4 = q ^ 5 := by ring
    _ = 1 := hq

theorem det_RRight (q : ℂ) (hq : q ^ 5 = 1) : (RRight q).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [RRight]
  calc
    q ^ 4 * q = q ^ 5 := by ring
    _ = 1 := hq

theorem chiral_braid_inverse (q : ℂ) (hq : q ^ 5 = 1) :
    RLeft q * RRight q = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RLeft, RRight, Matrix.mul_apply, Fin.sum_univ_two]
  · calc
      q * q ^ 4 = q ^ 5 := by ring
      _ = 1 := hq
  · calc
      q ^ 4 * q = q ^ 5 := by ring
      _ = 1 := hq

inductive BaseChart where
  | S4
  | CP2
  | kleinOrbifold
  deriving DecidableEq, Repr

inductive FiberSector where
  | S7
  | splitOctonion
  deriving DecidableEq, Repr

/-- Named spaces used only for dimension bookkeeping of the Hopf/twistor chain. -/
inductive SpaceLabel where
  | S1
  | S3
  | S4
  | S7
  | CP1
  | CP2
  | CP3
  deriving DecidableEq, Repr

/-- Real dimensions of the named spaces. -/
def realDim : SpaceLabel → ℕ
  | SpaceLabel.S1 => 1
  | SpaceLabel.S3 => 3
  | SpaceLabel.S4 => 4
  | SpaceLabel.S7 => 7
  | SpaceLabel.CP1 => 2
  | SpaceLabel.CP2 => 4
  | SpaceLabel.CP3 => 6

/-- Quaternionic Hopf fibration dimension check: `S³ → S⁷ → S⁴`. -/
theorem quaternionic_hopf_dimension :
    realDim SpaceLabel.S3 + realDim SpaceLabel.S4 = realDim SpaceLabel.S7 := by
  native_decide

/-- Complex Hopf fibration dimension check: `S¹ → S⁷ → CP³`. -/
theorem complex_hopf_dimension :
    realDim SpaceLabel.S1 + realDim SpaceLabel.CP3 = realDim SpaceLabel.S7 := by
  native_decide

/-- Twistor fibration dimension check: `CP¹ → CP³ → S⁴`. -/
theorem twistor_dimension :
    realDim SpaceLabel.CP1 + realDim SpaceLabel.S4 = realDim SpaceLabel.CP3 := by
  native_decide

/-- Dimension obstruction to the informal claim `CP² → S⁷ → S⁴`.

As a smooth fiber-bundle slogan this cannot be right: `dim CP² + dim S⁴ = 8`,
not `dim S⁷ = 7`. -/
theorem not_cp2_fiber_over_s4_with_total_s7 :
    realDim SpaceLabel.CP2 + realDim SpaceLabel.S4 ≠ realDim SpaceLabel.S7 := by
  native_decide

inductive TransportKind where
  | glideMonodromy
  | pentagonChiralBraid
  deriving DecidableEq, Repr

def orientationSign : TransportKind → ℤ
  | TransportKind.glideMonodromy => -1
  | TransportKind.pentagonChiralBraid => 1

structure Transport where
  kind : TransportKind
  source : BaseChart
  target : BaseChart

namespace Transport

/-- The orientation sign determined by the transport kind. -/
abbrev sign (T : Transport) : ℤ := orientationSign T.kind

/-- The transport sign is its canonical orientation sign. -/
theorem sign_eq (T : Transport) : T.sign = orientationSign T.kind := by
  rfl

end Transport

def glideTransport : Transport where
  kind := TransportKind.glideMonodromy
  source := BaseChart.S4
  target := BaseChart.kleinOrbifold

def chiralTransport : Transport where
  kind := TransportKind.pentagonChiralBraid
  source := BaseChart.CP2
  target := BaseChart.CP2

/-- Chiral twisted fibration theorem: base charts and fiber sectors remain typed
    separately, while glide monodromy reverses orientation and chiral transport
    preserves it. -/
theorem chiral_twisted_fibration_theorem :
    glideTransport.source = BaseChart.S4 ∧
    glideTransport.target = BaseChart.kleinOrbifold ∧
    chiralTransport.source = BaseChart.CP2 ∧
    chiralTransport.target = BaseChart.CP2 ∧
    glideTransport.sign = -1 ∧
    chiralTransport.sign = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two-sheeted complex polarization package:
    sheet swap `J`, grading `ε`, and emergent `K = J ε`, with `K² = -I`. -/
theorem two_sheeted_complex_emergence :
    sheetSwap * sheetSwap = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    sheetGrading * sheetGrading = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    sheetSwap * sheetGrading = -(sheetGrading * sheetSwap) ∧
    emergentComplex = eMinus ∧
    emergentComplex * emergentComplex = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact ⟨sheetSwap_sq, sheetGrading_sq, sheetSwap_grading_anticomm,
    emergentComplex_eq_eMinus, emergentComplex_sq⟩
