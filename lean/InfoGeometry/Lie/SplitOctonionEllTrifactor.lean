import InfoGeometry.Lie.SplitOctonionEllFlowOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors
import InfoGeometry.Physics.Algebra.LinearTripotentTrifactor

/-!
# Split-octonion ell trifactor: specialization to the diagonal `ℓ`

This owner proves the concrete equalities between the ell-flow projectors
and the native Zorn Peirce projectors:

- `P_+^ℓ = colorProject`,
- `P_-^ℓ = anticolorProject`,
- `P_0^ℓ = peircePlusPlus + peirceMinusMinus`.

It also proves `range(P₀^ℓ) = ker(T_ℓ)`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllTrifactor

open InfoGeometry.Lie.SplitOctonionEllFlowOperator
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Physics.Algebra

export InfoGeometry.Lie.SplitOctonionEllFlowOperator
  (diagEll diagEllCommutator diagEllGrading diagEllGrading_apply
    diagEllCommutator_apply diagEllCommutator_coord diagEllGrading_coord
    diagEllGrading_sq_coord diagEllGrading_tripotent)

abbrev CZ := InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-
The ell-flow projectors, expressed as endomorphisms.
These are exactly `P_±^ℓ` and `P_0^ℓ` from the prompt.
-/

def ellFlowPPlus : EndCZ := (1 / 2 : ℝ) • (diagEllGrading ^ 2 + diagEllGrading)

def ellFlowPMinus : EndCZ := (1 / 2 : ℝ) • (diagEllGrading ^ 2 - diagEllGrading)

def ellFlowPZero : EndCZ := 1 - diagEllGrading ^ 2

@[simp] theorem ellFlowPPlus_apply (Z : CZ) :
    ellFlowPPlus Z = (1 / 2 : ℝ) • (diagEllGrading (diagEllGrading Z) + diagEllGrading Z) :=
  rfl

@[simp] theorem ellFlowPMinus_apply (Z : CZ) :
    ellFlowPMinus Z = (1 / 2 : ℝ) • (diagEllGrading (diagEllGrading Z) - diagEllGrading Z) :=
  rfl

@[simp] theorem ellFlowPZero_apply (Z : CZ) :
    ellFlowPZero Z = Z - diagEllGrading (diagEllGrading Z) := by
  change Z - diagEllGrading (diagEllGrading Z) = _
  rfl

/--
Coordinate action of `P_+^ℓ`:
`P_+^ℓ(a, b, x, y) = (0, 0, x, 0)`.

This is exactly the color Peirce projector.
-/
theorem ellFlowPPlus_coord (Z : CZ) :
    ellFlowPPlus Z = { a := 0, b := 0, x := Z.x, y := 0 } := by
  rw [ellFlowPPlus_apply, diagEllGrading_sq_coord, diagEllGrading_coord]
  ext <;> simp [smul_eq_mul, Equiv.smul_def, coordEquiv]
  <;> try ring
  all_goals try { rename_i i; fin_cases i <;>
    simp [smul_eq_mul, Equiv.smul_def, coordEquiv] }

/--
Coordinate action of `P_-^ℓ`:
`P_-^ℓ(a, b, x, y) = (0, 0, 0, y)`.

This is exactly the anticolor Peirce projector.
-/
theorem ellFlowPMinus_coord (Z : CZ) :
    ellFlowPMinus Z = { a := 0, b := 0, x := 0, y := Z.y } := by
  rw [ellFlowPMinus_apply, diagEllGrading_sq_coord, diagEllGrading_coord]
  ext <;> simp [smul_eq_mul, Equiv.smul_def, coordEquiv]
  <;> try ring
  all_goals try { rename_i i; fin_cases i <;>
    simp [smul_eq_mul, Equiv.smul_def, coordEquiv] }

/--
Coordinate action of `P_0^ℓ`:
`P_0^ℓ(a, b, x, y) = (a, b, 0, 0)`.

This is the sum of the two diagonal Peirce components.
-/
theorem ellFlowPZero_coord (Z : CZ) :
    ellFlowPZero Z = { a := Z.a, b := Z.b, x := 0, y := 0 } := by
  rw [ellFlowPZero_apply, diagEllGrading_sq_coord]
  ext <;> simp

/-- `P_+^ℓ` equals the color Peirce projector. -/
theorem ellFlowPPlus_eq_colorProject :
    ⇑ellFlowPPlus = colorProject := by
  funext Z
  rw [ellFlowPPlus_coord, colorProject_apply]

/-- `P_-^ℓ` equals the anticolor Peirce projector. -/
theorem ellFlowPMinus_eq_anticolorProject :
    ⇑ellFlowPMinus = anticolorProject := by
  funext Z
  rw [ellFlowPMinus_coord, anticolorProject_apply]

/--
`P_0^ℓ` equals the sum of the two diagonal Peirce components:
`peircePlusPlus + peirceMinusMinus`.
-/
theorem ellFlowPZero_eq_diagPeirceSum :
    ⇑ellFlowPZero = (fun Z =>
      peirceComponent (zornPlus : CZ) (zornPlus : CZ) Z +
      peirceComponent (zornMinus : CZ) (zornMinus : CZ) Z) := by
  funext Z
  rw [ellFlowPZero_coord,
    peirce_plus_plus_apply, peirce_minus_minus_apply]
  ext <;> simp

/-- The three ell-flow projectors are pairwise orthogonal. -/
theorem ellFlow_projectors_orthogonal :
    (ellFlowPPlus.comp ellFlowPMinus = 0) ∧
    (ellFlowPMinus.comp ellFlowPZero = 0) ∧
    (ellFlowPZero.comp ellFlowPPlus = 0) := by
  constructor
  · -- P_+ ∘ P_- = 0
    apply LinearMap.ext
    intro Z
    rw [LinearMap.comp_apply, ellFlowPMinus_coord, ellFlowPPlus_coord]
    rfl
  · constructor
    · -- P_- ∘ P_0 = 0
      apply LinearMap.ext
      intro Z
      rw [LinearMap.comp_apply, ellFlowPZero_coord, ellFlowPMinus_coord]
      rfl
    · -- P_0 ∘ P_+ = 0
      apply LinearMap.ext
      intro Z
      rw [LinearMap.comp_apply, ellFlowPPlus_coord, ellFlowPZero_coord]
      rfl

/--
`range(P_0^ℓ) = ker(T_ℓ)`.

This is the concrete version of `endProjZero_range_eq_ker` for our
specific `diagEllGrading`.
-/
theorem ellFlow_zero_range_eq_ker :
    LinearMap.range ellFlowPZero = LinearMap.ker diagEllGrading := by
  simpa [ellFlowPZero, endProjZero, projZero, pow_two] using
    (endProjZero_range_eq_ker diagEllGrading diagEllGrading_tripotent)

/--
Kernel membership criterion: `T_ℓ(Z) = 0` iff `Z.x = 0` and `Z.y = 0`.

This characterizes the defect/stationary sector as exactly the diagonal
Zorn matrices (a, b, 0, 0).
-/
theorem ellFlow_ker_iff_diag (Z : CZ) :
    diagEllGrading Z = 0 ↔ Z.x = 0 ∧ Z.y = 0 := by
  rw [diagEllGrading_coord]
  constructor
  · intro h
    have hx := congrArg (fun z : CZ => z.x) h
    have hy := congrArg (fun z : CZ => z.y) h
    exact ⟨by simpa using hx, by simpa using hy⟩
  · rintro ⟨hx, hy⟩
    ext i <;> simp [hx, hy]

/-- Membership in the kernel is exactly the diagonal-coordinate condition. -/
theorem ellFlow_mem_ker_iff_diag (Z : CZ) :
    Z ∈ LinearMap.ker diagEllGrading ↔ Z.x = 0 ∧ Z.y = 0 := by
  rw [LinearMap.mem_ker]
  exact ellFlow_ker_iff_diag Z

end InfoGeometry.Lie.SplitOctonionEllTrifactor
