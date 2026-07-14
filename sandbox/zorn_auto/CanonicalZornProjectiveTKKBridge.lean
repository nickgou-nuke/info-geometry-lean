import SplitOctonionBraidSU3
import ZornCore
import ZornTrialityTKKBridge
import ProjectiveAffineConformalClosure55

/-!
# Canonical Zorn, triality, five-grade, and projective closure bridge

This module supplies carrier maps which were previously missing between four
existing branches:

* the real Zorn carrier with its order-three coordinate triality;
* the canonical complex Zorn algebra used by the braid representation;
* the split affine quadratic carrier `PACSplit44` and its conformal embedding
  into the `Q55` null cone;
* the existing routing of Peirce/nilpotent lanes into the five TKK grades.

No lattice, spin representation, or physical compactification is asserted.
-/

noncomputable section

namespace CanonicalZornProjectiveTKKBridge

open SplitOctonionBraidSU3
open ProjectiveAffineConformalClosure55
open ZornTrialityTKKBridge
open GrandUnifiedTKK

/-! ## Real split coordinates and the real Zorn carrier -/

/-- The standard split-coordinate map from `ℝ^(4,4)` into real Zorn coordinates. -/
def pac44ToCoreZorn (x : PACSplit44) : ZornCore.Zorn where
  a := x.x0 + x.y0
  b := x.x0 - x.y0
  u := ![x.x1 + x.y1, x.x2 + x.y2, x.x3 + x.y3]
  v := ![x.y1 - x.x1, x.y2 - x.x2, x.y3 - x.x3]

/-- Inverse coordinate map from a real Zorn matrix to diagonal split coordinates. -/
def coreZornToPAC44 (X : ZornCore.Zorn) : PACSplit44 where
  x0 := (X.a + X.b) / 2
  x1 := (X.u 0 - X.v 0) / 2
  x2 := (X.u 1 - X.v 1) / 2
  x3 := (X.u 2 - X.v 2) / 2
  y0 := (X.a - X.b) / 2
  y1 := (X.u 0 + X.v 0) / 2
  y2 := (X.u 1 + X.v 1) / 2
  y3 := (X.u 2 + X.v 2) / 2

theorem coreZornToPAC44_pac44ToCoreZorn (x : PACSplit44) :
    coreZornToPAC44 (pac44ToCoreZorn x) = x := by
  cases x
  simp [coreZornToPAC44, pac44ToCoreZorn]
  all_goals ring_nf
  all_goals simp

theorem pac44ToCoreZorn_coreZornToPAC44 (X : ZornCore.Zorn) :
    pac44ToCoreZorn (coreZornToPAC44 X) = X := by
  apply ZornCore.Zorn.ext'
  · simp [pac44ToCoreZorn, coreZornToPAC44]
    ring
  · funext i
    fin_cases i <;> simp [pac44ToCoreZorn, coreZornToPAC44] <;> ring
  · funext i
    fin_cases i <;> simp [pac44ToCoreZorn, coreZornToPAC44] <;> ring
  · simp [pac44ToCoreZorn, coreZornToPAC44]
    ring

/-- Real Zorn matrices and the diagonal `ℝ^(4,4)` carrier are equivalent. -/
def pac44CoreZornEquiv : PACSplit44 ≃ ZornCore.Zorn where
  toFun := pac44ToCoreZorn
  invFun := coreZornToPAC44
  left_inv := coreZornToPAC44_pac44ToCoreZorn
  right_inv := pac44ToCoreZorn_coreZornToPAC44

/-- The real Zorn determinant is exactly the diagonal split quadratic form. -/
theorem pac44ToCoreZorn_det (x : PACSplit44) :
    ZornCore.det (pac44ToCoreZorn x) = Q44 x := by
  simp [ZornCore.det, ZornCore.dot, pac44ToCoreZorn, Q44,
    Fin.sum_univ_three]
  ring

/-! ## Embedding the real Zorn algebra into the canonical complex carrier -/

/-- Coordinatewise complexification into the canonical Zorn carrier. -/
def coreToCanonical (X : ZornCore.Zorn) : SplitOctonionBraidSU3.Zorn where
  a := X.a
  u := fun i => X.u i
  v := fun i => X.v i
  b := X.b

theorem coreToCanonical_injective : Function.Injective coreToCanonical := by
  intro X Y h
  apply ZornCore.Zorn.ext'
  · apply Complex.ofReal_injective
    simpa [coreToCanonical] using
      congrArg SplitOctonionBraidSU3.Zorn.a h
  · funext i
    apply Complex.ofReal_injective
    simpa [coreToCanonical] using congrArg (fun Z => Z.u i) h
  · funext i
    apply Complex.ofReal_injective
    simpa [coreToCanonical] using congrArg (fun Z => Z.v i) h
  · apply Complex.ofReal_injective
    simpa [coreToCanonical] using
      congrArg SplitOctonionBraidSU3.Zorn.b h

/-- Complexification preserves the full nonassociative Zorn product. -/
theorem coreToCanonical_mul (X Y : ZornCore.Zorn) :
    coreToCanonical (X * Y) =
      zornMul (coreToCanonical X) (coreToCanonical Y) := by
  apply zorn_ext
  · simp [coreToCanonical, zornMul, ZornCore.dot, dot3, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [coreToCanonical, zornMul, ZornCore.cross, cross3,
        ZornCore.dot, dot3, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [coreToCanonical, zornMul, ZornCore.cross, cross3,
        ZornCore.dot, dot3, Fin.sum_univ_three]
  · simp [coreToCanonical, zornMul, ZornCore.dot, dot3, Fin.sum_univ_three]

/-- Complexification sends the real determinant to the canonical Zorn norm. -/
theorem coreToCanonical_norm (X : ZornCore.Zorn) :
    zornNorm (coreToCanonical X) = (ZornCore.det X : ℂ) := by
  simp [coreToCanonical, zornNorm, ZornCore.det, dot3, ZornCore.dot,
    Fin.sum_univ_three]

/-- Direct map from the split affine carrier into the canonical Zorn algebra. -/
def pac44ToCanonicalZorn (x : PACSplit44) : SplitOctonionBraidSU3.Zorn :=
  coreToCanonical (pac44ToCoreZorn x)

theorem pac44ToCanonicalZorn_norm (x : PACSplit44) :
    zornNorm (pac44ToCanonicalZorn x) = (Q44 x : ℂ) := by
  rw [pac44ToCanonicalZorn, coreToCanonical_norm, pac44ToCoreZorn_det]

/-! ## Triality transported to the canonical carrier -/

/-- Cyclic coordinate triality on the canonical complex Zorn carrier. -/
def canonicalTriality (X : SplitOctonionBraidSU3.Zorn) :
    SplitOctonionBraidSU3.Zorn where
  a := X.a
  u := ![X.u 1, X.u 2, X.u 0]
  v := ![X.v 1, X.v 2, X.v 0]
  b := X.b

theorem canonicalTriality_order_three (X : SplitOctonionBraidSU3.Zorn) :
    canonicalTriality (canonicalTriality (canonicalTriality X)) = X := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem canonicalTriality_norm (X : SplitOctonionBraidSU3.Zorn) :
    zornNorm (canonicalTriality X) = zornNorm X := by
  simp [canonicalTriality, zornNorm, dot3]
  ring

/-- The real and canonical triality actions commute with complexification. -/
theorem coreToCanonical_triality (X : ZornCore.Zorn) :
    coreToCanonical (ZornCore.triality X) =
      canonicalTriality (coreToCanonical X) := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

/-- Cyclic triality is an automorphism of the canonical Zorn multiplication. -/
theorem canonicalTriality_mul (X Y : SplitOctonionBraidSU3.Zorn) :
    canonicalTriality (zornMul X Y) =
      zornMul (canonicalTriality X) (canonicalTriality Y) := by
  apply zorn_ext
  · simp [canonicalTriality, zornMul, dot3]
    ring
  · funext i
    fin_cases i <;> simp [canonicalTriality, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [canonicalTriality, zornMul, cross3]
  · simp [canonicalTriality, zornMul, dot3]
    ring

/-! ## Projective conformal closure and five-grade routing -/

/-- The affine conformal closure of the same eight real Zorn coordinates. -/
def zornConformalEmbed (X : ZornCore.Zorn) : PACSplit55 :=
  conformalEmbed44to55 (coreZornToPAC44 X)

theorem zornConformalEmbed_null (X : ZornCore.Zorn) :
    Q55 (zornConformalEmbed X) = 0 := by
  exact conformalEmbed44to55_null (coreZornToPAC44 X)

/-- The affine quadratic coordinate recovered from a real Zorn element is its determinant. -/
theorem coreZornToPAC44_Q44 (X : ZornCore.Zorn) :
    Q44 (coreZornToPAC44 X) = ZornCore.det X := by
  rw [← pac44ToCoreZorn_det]
  simp [pac44ToCoreZorn_coreZornToPAC44]

/-- Canonical elements occupying the named Peirce, nilpotent, and defect lanes. -/
def canonicalLaneElement : SplitOctonionLane → SplitOctonionBraidSU3.Zorn
  | .diagonalProjector =>
      { a := 1, u := fun _ => 0, v := fun _ => 0, b := 0 }
  | .upperNilpotent => E_k 0
  | .lowerNilpotent => F_k 0
  | .associatorWitness =>
      zornSub
        (zornMul (zornMul (E_k 0) (F_k 0)) (E_k 1))
        (zornMul (E_k 0) (zornMul (F_k 0) (E_k 1)))

theorem canonicalLaneElement_upper_sq :
    zornMul (canonicalLaneElement .upperNilpotent)
      (canonicalLaneElement .upperNilpotent) = zornZero := by
  apply zorn_ext
  · simp [canonicalLaneElement, E_k, e_k, zornMul, zornZero, dot3, cross3]
  · funext i
    fin_cases i <;>
      simp [canonicalLaneElement, E_k, e_k, zornMul, zornZero, dot3, cross3]
  · funext i
    fin_cases i <;>
      simp [canonicalLaneElement, E_k, e_k, zornMul, zornZero, dot3, cross3]
  · simp [canonicalLaneElement, E_k, e_k, zornMul, zornZero, dot3, cross3]

theorem canonicalLaneElement_lower_sq :
    zornMul (canonicalLaneElement .lowerNilpotent)
      (canonicalLaneElement .lowerNilpotent) = zornZero := by
  apply zorn_ext
  · simp [canonicalLaneElement, F_k, e_k, zornMul, zornZero, dot3, cross3]
  · funext i
    fin_cases i <;>
      simp [canonicalLaneElement, F_k, e_k, zornMul, zornZero, dot3, cross3]
  · funext i
    fin_cases i <;>
      simp [canonicalLaneElement, F_k, e_k, zornMul, zornZero, dot3, cross3]
  · simp [canonicalLaneElement, F_k, e_k, zornMul, zornZero, dot3, cross3]

/-- The concrete canonical elements carry the already-proved five-grade routing. -/
def canonicalGradedLane (s : SplitOctonionLane) :=
  (canonicalLaneElement s, canonicalRouting s)

theorem canonicalGradedLane_grade (s : SplitOctonionLane) :
    (canonicalGradedLane s).2.grade = laneGrade s := by
  exact canonicalRouting_grade s

theorem canonical_triality_projective_five_grade_bridge (X : ZornCore.Zorn) :
    zornNorm (coreToCanonical X) = (ZornCore.det X : ℂ) ∧
    Q55 (zornConformalEmbed X) = 0 ∧
    coreToCanonical (ZornCore.triality X) =
      canonicalTriality (coreToCanonical X) ∧
    (canonicalGradedLane .upperNilpotent).2.grade = TKK_Grade.g_1 ∧
    (canonicalGradedLane .lowerNilpotent).2.grade = TKK_Grade.g_neg1 := by
  exact ⟨coreToCanonical_norm X, zornConformalEmbed_null X,
    coreToCanonical_triality X, canonicalGradedLane_grade _,
    canonicalGradedLane_grade _⟩

end CanonicalZornProjectiveTKKBridge

end noncomputable section
