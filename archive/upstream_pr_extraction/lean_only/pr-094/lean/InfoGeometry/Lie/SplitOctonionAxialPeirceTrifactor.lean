import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Diagonal split-octonion axis and native Peirce trifactor

The paper-style pseudoscalar axis is the diagonal Zorn element
`zornPlus - zornMinus = (1,-1,0,0)`.  It is distinct from the existing
off-diagonal `SplitQuaternionCore.lUnit`.

This file proves directly on `CanonicalZorn` that one half of its commutator
is the signed upper/lower coordinate projection.  Its tripotent projectors are
then identified pointwise with the native Zorn Peirce components.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Physics.Algebra

attribute [local simp] Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ
  Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply

abbrev CZ := ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- The diagonal pseudoscalar/oriented-volume axis `(1,-1,0,0)`. -/
def axialI : CZ := zornPlus - zornMinus

@[simp] theorem axialI_apply :
    axialI = { a := 1, b := -1, x := 0, y := 0 } := by
  ext i <;> simp [axialI, zornPlus, zornMinus]

/-- Signed upper/lower coordinate projection associated with `axialI`. -/
def axialGrading : EndCZ where
  toFun X := { a := 0, b := 0, x := X.x, y := -X.y }
  map_add' X Y := by
    ext i <;> simp [ZornMatrix.add_def] <;> abel
  map_smul' r X := by
    ext i <;>
      simp [Equiv.smul_def, coordEquiv]

@[simp] theorem axialGrading_apply (X : CZ) :
    axialGrading X = { a := 0, b := 0, x := X.x, y := -X.y } :=
  rfl

/-- The coordinate grading is exactly one half of the native commutator with
the diagonal pseudoscalar axis. -/
theorem axialGrading_eq_half_commutator (X : CZ) :
    axialGrading X = (1 / 2 : ℝ) • (axialI * X - X * axialI) := by
  ext i <;>
    simp [axialGrading, axialI, zornPlus, zornMinus, ZornMatrix.mul_def,
      ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
      Equiv.smul_def, coordEquiv]
  all_goals (try fin_cases i) <;> simp <;> ring

/-- The diagonal axial grading is tripotent on the full canonical carrier. -/
theorem axialGrading_tripotent : axialGrading ^ 3 = axialGrading := by
  apply LinearMap.ext
  intro X
  ext i <;>
    simp [pow_succ, Module.End.mul_apply, axialGrading]

/-- Positive, stationary, and negative polynomial projectors. -/
def axialPPlus : EndCZ := projPos axialGrading
def axialPZero : EndCZ := projZero axialGrading
def axialPMinus : EndCZ := projNeg axialGrading

/-- The positive tripotent projector is the native upper/color Peirce block. -/
theorem axialPPlus_apply (X : CZ) : axialPPlus X = colorProject X := by
  rw [colorProject_apply]
  ext i <;>
    simp [axialPPlus, projPos, axialGrading, Module.End.mul_apply,
      Equiv.smul_def, coordEquiv]
  all_goals (try fin_cases i) <;> ring

/-- The negative tripotent projector is the native lower/anticolor Peirce
block. -/
theorem axialPMinus_apply (X : CZ) : axialPMinus X = anticolorProject X := by
  rw [anticolorProject_apply]
  ext i <;>
    simp [axialPMinus, projNeg, axialGrading, Module.End.mul_apply,
      Equiv.smul_def, coordEquiv]
  all_goals (try fin_cases i) <;> ring

/-- The stationary projector extracts exactly the two diagonal coordinates. -/
theorem axialPZero_apply (X : CZ) :
    axialPZero X = { a := X.a, b := X.b, x := 0, y := 0 } := by
  ext i <;>
    simp [axialPZero, projZero, axialGrading, Module.End.mul_apply,
      Equiv.smul_def, coordEquiv]
  all_goals (try fin_cases i) <;> ring

/-- The zero sector is the sum of the two diagonal Peirce components. -/
theorem axialPZero_apply_eq_diagonal_peirce (X : CZ) :
    axialPZero X =
      peirceComponent zornPlus zornPlus X +
        peirceComponent zornMinus zornMinus X := by
  rw [axialPZero_apply, peirce_plus_plus_apply, peirce_minus_minus_apply]
  ext i <;> simp [ZornMatrix.add_def]

private theorem axialGrading_mul_three :
    axialGrading * axialGrading * axialGrading = axialGrading := by
  simpa [pow_three] using axialGrading_tripotent

/-- The stationary projector has range exactly the kernel of the diagonal
axial grading. -/
theorem axialPZero_range_eq_ker :
    LinearMap.range axialPZero = LinearMap.ker axialGrading := by
  apply le_antisymm
  · rw [LinearMap.range_le_ker_iff]
    change axialGrading * axialPZero = 0
    exact mul_projZero axialGrading_mul_three
  · intro X hX
    rw [LinearMap.mem_ker] at hX
    rw [LinearMap.mem_range]
    refine ⟨X, ?_⟩
    have hx : X.x = 0 := by
      funext i
      have hi := congrArg (fun Z : CZ => Z.x i) hX
      simpa [axialGrading] using hi
    have hy : X.y = 0 := by
      funext i
      have hi := congrArg (fun Z : CZ => Z.y i) hX
      change -X.y i = 0 at hi
      simpa using (neg_eq_zero.mp hi)
    rw [axialPZero_apply]
    ext i <;> simp [hx, hy]

/-- The positive projector range is exactly the `+1` eigenspace. -/
theorem axialPPlus_range_eq_eigenspace :
    LinearMap.range axialPPlus = Module.End.eigenspace axialGrading 1 := by
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := congrArg (fun F : EndCZ => F Y)
      (mul_projPos axialGrading_mul_three)
    simpa [Module.End.mul_apply] using h
  · intro X hX
    rw [Module.End.mem_eigenspace_iff] at hX
    have hX' : axialGrading X = X := by simpa using hX
    rw [LinearMap.mem_range]
    refine ⟨X, ?_⟩
    have hXX : axialGrading (axialGrading X) = X := by
      rw [hX', hX']
    change (1 / 2 : ℝ) •
      (axialGrading (axialGrading X) + axialGrading X) = X
    rw [hXX, hX']
    module

/-- The negative projector range is exactly the `-1` eigenspace. -/
theorem axialPMinus_range_eq_eigenspace :
    LinearMap.range axialPMinus = Module.End.eigenspace axialGrading (-1) := by
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := congrArg (fun F : EndCZ => F Y)
      (mul_projNeg axialGrading_mul_three)
    simpa [Module.End.mul_apply] using h
  · intro X hX
    rw [Module.End.mem_eigenspace_iff] at hX
    have hX' : axialGrading X = -X := by simpa using hX
    rw [LinearMap.mem_range]
    refine ⟨X, ?_⟩
    have hXX : axialGrading (axialGrading X) = X := by
      calc
        axialGrading (axialGrading X) = axialGrading (-X) := by rw [hX']
        _ = -axialGrading X := map_neg axialGrading X
        _ = -(-X) := by rw [hX']
        _ = X := neg_neg X
    change (1 / 2 : ℝ) •
      (axialGrading (axialGrading X) - axialGrading X) = X
    rw [hXX, hX']
    module

end InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
