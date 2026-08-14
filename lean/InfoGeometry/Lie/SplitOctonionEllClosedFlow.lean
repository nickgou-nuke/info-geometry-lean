import InfoGeometry.Lie.SplitOctonionEllTrifactor
import InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
import InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
import InfoGeometry.Lie.SplitOctonionEllPolarization
import InfoGeometry.Algebra.Zorn.Incidence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Closed flow of the split-octonion ell tripotent

The diagonal ell grading `diagEllGrading = (1/2) ad_(zornPlus - zornMinus)` has
three native polynomial projectors `ellFlowPZero`, `ellFlowPPlus`, and
`ellFlowPMinus`. This owner defines its closed hyperbolic flow directly from
those projectors:

`Φ(t) = P₀^ℓ + exp(t) P₊^ℓ + exp(-t) P₋^ℓ`.

The group law and the three sector actions are proved on the actual canonical
Zorn coordinates. This is a linear flow; no claim that the uniform weights
preserve the nonassociative Zorn multiplication is made here.

We also define the associated operator triad:

- `Q_ℓ = diagEllGrading²` — the active-support operator,
- `Γ_ℓ = 2·diagEllGrading² - I` — the active/defect involution,
- `activityPartitionTrace(t)` — the trace of `Φ(t)`, not yet identified with
  a physical KMS partition function.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllClosedFlow

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionEllTrifactor
open InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Canonical.ZornMatrix
open Real

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

attribute [local simp] Pi.smul_apply Pi.add_apply Pi.neg_apply

/-
#-- Projector-derived closed flow of the ell tripotent. -/
noncomputable def ellFlowPhi (t : ℝ) : EndCZ :=
  ellFlowPZero + (exp t : ℝ) • ellFlowPPlus +
    (exp (-t) : ℝ) • ellFlowPMinus

@[simp] theorem ellFlowPhi_apply (t : ℝ) (Z : CZ) :
    ellFlowPhi t Z =
      ellFlowPZero Z + (exp t : ℝ) • ellFlowPPlus Z +
        (exp (-t) : ℝ) • ellFlowPMinus Z := rfl

/-
#-- Coordinate form of the closed flow: diagonal coordinates are stationary,
#-- upper/color coordinates have weight `exp t`, and lower/anticolor coordinates
#-- have weight `exp (-t)`. -/
theorem ellFlowPhi_coord (t : ℝ) (Z : CZ) :
    ellFlowPhi t Z =
      { a := Z.a
        b := Z.b
        x := (exp t : ℝ) • Z.x
        y := (exp (-t) : ℝ) • Z.y } := by
  -- Expand using the coordinate actions of the three projectors
  have h₁ : ellFlowPZero Z = { a := Z.a, b := Z.b, x := 0, y := 0 } :=
    ellFlowPZero_coord Z
  have h₂ : ellFlowPPlus Z = { a := 0, b := 0, x := Z.x, y := 0 } :=
    ellFlowPPlus_coord Z
  have h₃ : ellFlowPMinus Z = { a := 0, b := 0, x := 0, y := Z.y } :=
    ellFlowPMinus_coord Z
  -- Compute the sum with weights
  rw [ellFlowPhi_apply, h₁, h₂, h₃]
  -- The result is:
  -- {a:=Z.a, b:=Z.b, x:=0, y:=0} + (exp t)•{a:=0,b:=0,x:=Z.x,y:=0} + (exp(-t))•{a:=0,b:=0,x:=0,y:=Z.y}
  -- = {a:=Z.a + 0 + 0, b:=Z.b + 0 + 0, x:=0 + (exp t)•Z.x + 0, y:=0 + 0 + (exp(-t))•Z.y}
  -- = {a:=Z.a, b:=Z.b, x:=(exp t)•Z.x, y:=(exp(-t))•Z.y}
  ext i <;> simp [Equiv.smul_def, coordEquiv]

/-- The uniform tripotent flow is an isometry of the native split Zorn
quadratic form.  This is a norm-preservation statement, not a claim that the
uniform flow preserves the full nonassociative multiplication. -/
theorem ellFlowPhi_preserves_det (t : ℝ) (Z : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (ellFlowPhi t Z) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Z := by
  rw [ellFlowPhi_coord]
  simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    dot, Equiv.smul_def, coordEquiv,
    Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Polarization of the native Zorn determinant is preserved by the closed flow.

This is stated directly from determinant preservation, so it records the
quadratic-form isometry without introducing a second bilinear-form wrapper. -/
theorem ellFlowPhi_preserves_det_polarization (t : ℝ) (X Y : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (ellFlowPhi t (X + Y)) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (ellFlowPhi t X) -
            InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (ellFlowPhi t Y) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (X + Y) -
            InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X -
            InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Y := by
  have h_add : ellFlowPhi t (X + Y) = ellFlowPhi t X + ellFlowPhi t Y :=
    map_add (ellFlowPhi t) X Y
  have h_sum :
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          (ellFlowPhi t X + ellFlowPhi t Y) =
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (X + Y) := by
    rw [← h_add, ellFlowPhi_preserves_det]
  rw [h_add, h_sum, ellFlowPhi_preserves_det, ellFlowPhi_preserves_det]

theorem ellFlowPhi_preserves_det_eq_zero_iff (t : ℝ) (Z : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (ellFlowPhi t Z) = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Z = 0 := by
  rw [ellFlowPhi_preserves_det]

/-
#-- At parameter zero the closed flow is the identity. -/
@[simp] theorem ellFlowPhi_zero : ellFlowPhi 0 = 1 := by
  apply LinearMap.ext
  intro Z
  rw [ellFlowPhi_coord]
  ext i <;> simp

/-
#-- The projector-derived flow is a one-parameter representation of the
#-- additive real group. -/
theorem ellFlowPhi_add (s t : ℝ) :
    ellFlowPhi (s + t) = ellFlowPhi s * ellFlowPhi t := by
  apply LinearMap.ext
  intro Z
  change ellFlowPhi (s + t) Z = ellFlowPhi s (ellFlowPhi t Z)
  rw [ellFlowPhi_coord, ellFlowPhi_coord, ellFlowPhi_coord]
  ext i <;> simp [Equiv.smul_def, coordEquiv, exp_add] <;> ring

/-
#-- Reversing the parameter gives a two-sided inverse. -/
theorem ellFlowPhi_mul_neg (t : ℝ) :
    ellFlowPhi t * ellFlowPhi (-t) = 1 := by
  rw [← ellFlowPhi_add]
  simp

theorem ellFlowPhi_neg_mul (t : ℝ) :
    ellFlowPhi (-t) * ellFlowPhi t = 1 := by
  rw [← ellFlowPhi_add]
  simp

noncomputable def ellQ : EndCZ := diagEllGrading ^ 2

theorem ellQ_coord (Z : CZ) :
    ellQ Z = { a := 0, b := 0, x := Z.x, y := Z.y } := by
  change diagEllGrading (diagEllGrading Z) = _
  exact diagEllGrading_sq_coord Z

theorem ellQ_eq_Plus_Plus_minus : ellQ = ellFlowPPlus + ellFlowPMinus := by
  apply LinearMap.ext
  intro Z
  change ellQ Z = ellFlowPPlus Z + ellFlowPMinus Z
  rw [ellQ_coord, ellFlowPPlus_coord, ellFlowPMinus_coord]
  ext <;> simp

theorem ellQ_idempotent : ellQ * ellQ = ellQ := by
  apply LinearMap.ext
  intro Z
  change ellQ (ellQ Z) = ellQ Z
  rw [ellQ_coord, ellQ_coord]

theorem ellQ_range_eq_active :
    LinearMap.range ellQ = LinearMap.range ellFlowPPlus ⊔ LinearMap.range ellFlowPMinus := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rw [ellQ_coord]
    refine Submodule.mem_sup.mpr ⟨
      { a := 0, b := 0, x := y.x, y := 0 }, ?_,
      { a := 0, b := 0, x := 0, y := y.y }, ?_, ?_⟩
    · rw [LinearMap.mem_range]
      exact ⟨{ a := 0, b := 0, x := y.x, y := 0 }, by
        rw [ellFlowPPlus_coord]⟩
    · rw [LinearMap.mem_range]
      exact ⟨{ a := 0, b := 0, x := 0, y := y.y }, by
        rw [ellFlowPMinus_coord]⟩
    · ext <;> simp
  · intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hsum⟩
    rcases LinearMap.mem_range.mp hy with ⟨y₀, hy₀⟩
    rcases LinearMap.mem_range.mp hz with ⟨z₀, hz₀⟩
    rw [LinearMap.mem_range]
    refine ⟨y + z, ?_⟩
    have hP : ellQ (ellFlowPPlus y₀) = ellFlowPPlus y₀ := by
      rw [ellFlowPPlus_coord, ellQ_coord]
    have hM : ellQ (ellFlowPMinus z₀) = ellFlowPMinus z₀ := by
      rw [ellFlowPMinus_coord, ellQ_coord]
    calc
      ellQ (y + z) = ellQ y + ellQ z := map_add _ _ _
      _ = ellQ (ellFlowPPlus y₀) + ellQ (ellFlowPMinus z₀) := by
        rw [hy₀, hz₀]
      _ = ellFlowPPlus y₀ + ellFlowPMinus z₀ := by rw [hP, hM]
      _ = y + z := by rw [hy₀, hz₀]
      _ = x := hsum

noncomputable def ellGamma : EndCZ := (2 : ℝ) • ellQ - 1

theorem ellGamma_coord (Z : CZ) :
    ellGamma Z = { a := -Z.a, b := -Z.b, x := Z.x, y := Z.y } := by
  unfold ellGamma
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [ellQ_coord]
  ext <;>
    simp [InfoGeometry.Canonical.ZornMatrix.coordEquiv, Equiv.smul_def,
      smul_eq_mul] <;> ring

theorem ellGamma_idempotent : ellGamma * ellGamma = 1 := by
  apply LinearMap.ext
  intro Z
  change ellGamma (ellGamma Z) = Z
  rw [ellGamma_coord, ellGamma_coord]
  ext <;> simp

noncomputable def activityPartitionTrace (t : ℝ) : ℝ :=
  2 + 3 * Real.exp t + 3 * Real.exp (-t)

theorem activityPartitionTrace_eq_cosh_form (t : ℝ) :
    activityPartitionTrace t = 2 + 6 * Real.cosh t := by
  unfold activityPartitionTrace
  rw [Real.cosh_eq]
  ring

def ellFlowPhiEquiv (t : ℝ) : CZ ≃ₗ[ℝ] CZ where
  toLinearMap := ellFlowPhi t
  invFun := ellFlowPhi (-t)
  left_inv X := by
    have h := congrArg (fun F : EndCZ => F X) (ellFlowPhi_neg_mul t)
    simpa [Module.End.mul_apply] using h
  right_inv X := by
    have h := congrArg (fun F : EndCZ => F X) (ellFlowPhi_mul_neg t)
    simpa [Module.End.mul_apply] using h

@[simp] theorem ellFlowPhiEquiv_apply (t : ℝ) (Z : CZ) :
    ellFlowPhiEquiv t Z = ellFlowPhi t Z :=
  rfl

@[simp] theorem ellFlowPhiEquiv_symm_apply (t : ℝ) (Z : CZ) :
    (ellFlowPhiEquiv t).symm Z = ellFlowPhi (-t) Z :=
  rfl

/-
#-- The stationary/Drazin-defect sector is fixed pointwise. -/
theorem ellFlowPhi_on_PZero (t : ℝ) (Z : CZ) :
    ellFlowPhi t (ellFlowPZero Z) = ellFlowPZero Z := by
  rw [ellFlowPZero_coord, ellFlowPhi_coord]
  ext i <;> simp

/-
#-- The positive Peirce sector has weight `exp t`. -/
theorem ellFlowPhi_on_PPlus (t : ℝ) (Z : CZ) :
    ellFlowPhi t (ellFlowPPlus Z) =
      (exp t : ℝ) • ellFlowPPlus Z := by
  rw [ellFlowPPlus_coord, ellFlowPhi_coord]
  ext i <;> simp [Equiv.smul_def, coordEquiv]

/-
#-- The negative Peirce sector has weight `exp (-t)`. -/
theorem ellFlowPhi_on_PMinus (t : ℝ) (Z : CZ) :
    ellFlowPhi t (ellFlowPMinus Z) =
      (exp (-t) : ℝ) • ellFlowPMinus Z := by
  rw [ellFlowPMinus_coord, ellFlowPhi_coord]
  ext i <;> simp [Equiv.smul_def, coordEquiv]

theorem ellGrading_ellWeightBasisReal_native (i : Fin 8) :
    InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor.ellGrading
        (ellWeightBasisReal i) =
      ellWeight i • ellWeightBasisReal i := by
  exact InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellGrading_ellWeightBasisReal i

end InfoGeometry.Lie.SplitOctonionEllClosedFlow
