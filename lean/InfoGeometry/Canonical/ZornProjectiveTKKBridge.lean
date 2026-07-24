import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Canonical.ZornTrialityTKKBridge
import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure
import InfoGeometry.Canonical.TKKJordanPairData

noncomputable section

namespace InfoGeometry.Canonical.ZornProjectiveTKKBridge

open ProjectiveAffineConformalClosure55
open ZornTrialityTKKBridge
open TKKJordanPairData
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure

/-! ## Real split coordinates and the real Zorn carrier -/

/-- The standard split-coordinate map from `ℝ^(4,4)` into real Zorn coordinates. -/
def pac44ToZorn (x : PACSplit44) : ZornMatrix ℝ where
  a := x.x0 + x.y0
  b := x.x0 - x.y0
  x := ![x.x1 + x.y1, x.x2 + x.y2, x.x3 + x.y3]
  y := ![x.y1 - x.x1, x.y2 - x.x2, x.y3 - x.x3]

/-- Inverse coordinate map from a real Zorn matrix to diagonal split coordinates. -/
def zornToPAC44 (Z : ZornMatrix ℝ) : PACSplit44 where
  x0 := (Z.a + Z.b) / 2
  x1 := (Z.x 0 - Z.y 0) / 2
  x2 := (Z.x 1 - Z.y 1) / 2
  x3 := (Z.x 2 - Z.y 2) / 2
  y0 := (Z.a - Z.b) / 2
  y1 := (Z.x 0 + Z.y 0) / 2
  y2 := (Z.x 1 + Z.y 1) / 2
  y3 := (Z.x 2 + Z.y 2) / 2

theorem zornToPAC44_pac44ToZorn (x : PACSplit44) :
    zornToPAC44 (pac44ToZorn x) = x := by
  cases x
  simp [zornToPAC44, pac44ToZorn]
  all_goals ring_nf
  all_goals simp

theorem pac44ToZorn_zornToPAC44 (Z : ZornMatrix ℝ) :
    pac44ToZorn (zornToPAC44 Z) = Z := by
  apply ZornMatrix.ext
  · simp [pac44ToZorn, zornToPAC44]; ring
  · simp [pac44ToZorn, zornToPAC44]; ring
  · ext i; fin_cases i <;> simp [pac44ToZorn, zornToPAC44] <;> ring
  · ext i; fin_cases i <;> simp [pac44ToZorn, zornToPAC44] <;> ring

/-- Real Zorn matrices and the diagonal `ℝ^(4,4)` carrier are equivalent. -/
def pac44ZornEquiv : PACSplit44 ≃ ZornMatrix ℝ where
  toFun := pac44ToZorn
  invFun := zornToPAC44
  left_inv := zornToPAC44_pac44ToZorn
  right_inv := pac44ToZorn_zornToPAC44

/-- The real Zorn norm is exactly the diagonal split quadratic form. -/
theorem pac44ToZorn_norm (x : PACSplit44) :
    zornNormFun (pac44ToZorn x) = Q44 x := by
  simp [zornNormFun, ZornMatrix.dot, pac44ToZorn, Q44]
  ring

/-! ## Embedding the real Zorn algebra into the canonical complex carrier -/

/-- Coordinatewise complexification into the canonical complex Zorn carrier. -/
def realToComplex (Z : ZornMatrix ℝ) : ZornMatrix ℂ where
  a := Z.a
  b := Z.b
  x := fun i => Z.x i
  y := fun i => Z.y i

theorem realToComplex_injective : Function.Injective realToComplex := by
  intro Z W h
  apply ZornMatrix.ext
  · apply Complex.ofReal_injective
    simpa [realToComplex] using congrArg (fun Z : ZornMatrix ℂ => Z.a) h
  · apply Complex.ofReal_injective
    simpa [realToComplex] using congrArg (fun Z : ZornMatrix ℂ => Z.b) h
  · ext i; apply Complex.ofReal_injective
    simpa [realToComplex] using congrArg (fun (Z : ZornMatrix ℂ) => Z.x i) h
  · ext i; apply Complex.ofReal_injective
    simpa [realToComplex] using congrArg (fun (Z : ZornMatrix ℂ) => Z.y i) h

/-- Complexification preserves the full nonassociative Zorn product. -/
theorem realToComplex_mul (X Y : ZornMatrix ℝ) :
    realToComplex (X * Y) = realToComplex X * realToComplex Y := by
  apply ZornMatrix.ext
  · dsimp [realToComplex, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, Matrix.vecHead, Matrix.vecTail]
    push_cast; ring
  · dsimp [realToComplex, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, Matrix.vecHead, Matrix.vecTail]
    push_cast; ring
  · ext i; fin_cases i <;> dsimp [realToComplex, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, Pi.add_apply, Pi.sub_apply] <;> push_cast <;> ring
  · ext i; fin_cases i <;> dsimp [realToComplex, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, Pi.add_apply, Pi.sub_apply] <;> push_cast <;> ring

/-- Complexification sends the real norm to the complex Zorn norm. -/
theorem realToComplex_norm (Z : ZornMatrix ℝ) :
    zornNormFun (realToComplex Z) = Complex.ofReal (zornNormFun Z) := by
  dsimp [realToComplex, zornNormFun, ZornMatrix.dot]
  push_cast
  ring

/-- Direct map from the split affine carrier into the complex Zorn algebra. -/
def pac44ToComplexZorn (x : PACSplit44) : ZornMatrix ℂ :=
  realToComplex (pac44ToZorn x)

theorem pac44ToComplexZorn_norm (x : PACSplit44) :
    zornNormFun (pac44ToComplexZorn x) = Complex.ofReal (Q44 x) := by
  rw [pac44ToComplexZorn, realToComplex_norm, pac44ToZorn_norm]

/-! ## Triality transported to the canonical carrier -/

/-- The real and complex triality actions commute with complexification. -/
theorem realToComplex_triality (Z : ZornMatrix ℝ) :
    realToComplex (zornTriality Z) = zornTriality (realToComplex Z) := by
  apply ZornMatrix.ext
  · rfl
  · rfl
  · ext i; fin_cases i <;> rfl
  · ext i; fin_cases i <;> rfl

/-! ## Projective conformal closure and five-grade routing -/

/-- The affine conformal closure of the same eight real Zorn coordinates. -/
def zornConformalEmbed (Z : ZornMatrix ℝ) : PACSplit55 :=
  conformalEmbed44to55 (zornToPAC44 Z)

theorem zornConformalEmbed_null (Z : ZornMatrix ℝ) :
    Q55 (zornConformalEmbed Z) = 0 := by
  exact conformalEmbed44to55_null (zornToPAC44 Z)

/-- The affine quadratic coordinate recovered from a real Zorn element is its norm. -/
theorem zornToPAC44_Q44 (Z : ZornMatrix ℝ) :
    Q44 (zornToPAC44 Z) = zornNormFun Z := by
  rw [← pac44ToZorn_norm, pac44ToZorn_zornToPAC44]

/-- Canonical elements occupying the named Peirce, nilpotent, and defect lanes. -/
def canonicalLaneElement : SplitOctonionLane → ZornMatrix ℂ
  | .diagonalProjector => { a := 1, b := 0, x := 0, y := 0 }
  | .upperNilpotent => { a := 0, b := 0, x := fun i => if i = 0 then 1 else 0, y := 0 }
  | .lowerNilpotent => { a := 0, b := 0, x := 0, y := fun i => if i = 0 then 1 else 0 }
  | .associatorWitness =>
      let e0 : ZornMatrix ℂ := { a := 0, b := 0, x := fun i => if i = 0 then 1 else 0, y := 0 }
      let f0 : ZornMatrix ℂ := { a := 0, b := 0, x := 0, y := fun i => if i = 0 then 1 else 0 }
      let e1 : ZornMatrix ℂ := { a := 0, b := 0, x := fun i => if i = 1 then 1 else 0, y := 0 }
      ((e0 * f0) * e1) - (e0 * (f0 * e1))

theorem canonicalLaneElement_upper_sq :
    canonicalLaneElement .upperNilpotent * canonicalLaneElement .upperNilpotent = 0 := by
  apply ZornMatrix.ext
  · simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]
  · simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]
  · ext i; fin_cases i <;> simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross]
  · ext i; fin_cases i <;> simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross]

theorem canonicalLaneElement_lower_sq :
    canonicalLaneElement .lowerNilpotent * canonicalLaneElement .lowerNilpotent = 0 := by
  apply ZornMatrix.ext
  · simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]
  · simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]
  · ext i; fin_cases i <;> simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross]
  · ext i; fin_cases i <;> simp [canonicalLaneElement, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross]

/-- The concrete canonical elements carry the already-proved five-grade routing. -/
def canonicalGradedLane (s : SplitOctonionLane) :=
  (canonicalLaneElement s, canonicalRouting s)

theorem canonicalGradedLane_grade (s : SplitOctonionLane) :
    (canonicalGradedLane s).2.grade = laneGrade s := by
  exact canonicalRouting_grade s

theorem canonical_triality_projective_five_grade_bridge (Z : ZornMatrix ℝ) :
    zornNormFun (realToComplex Z) = Complex.ofReal (zornNormFun Z) ∧
    Q55 (zornConformalEmbed Z) = 0 ∧
    realToComplex (zornTriality Z) = zornTriality (realToComplex Z) ∧
    (canonicalGradedLane .upperNilpotent).2.grade = TKKGrade.p1 ∧
    (canonicalGradedLane .lowerNilpotent).2.grade = TKKGrade.m1 := by
  exact ⟨realToComplex_norm Z, zornConformalEmbed_null Z,
    realToComplex_triality Z, canonicalGradedLane_grade _,
    canonicalGradedLane_grade _⟩

end InfoGeometry.Canonical.ZornProjectiveTKKBridge
