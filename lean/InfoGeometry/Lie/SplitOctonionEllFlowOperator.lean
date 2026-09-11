import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.SplitQuaternionCore
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors
import InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor

/-!
# Split-octonion ell flow operator

The diagonal element `ell = zornPlus - zornMinus` acts by commutator on the
native Zorn carrier.  This owner records the coordinate action as a genuine
linear endomorphism and derives the normalized tripotent grading operator.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllFlowOperator

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

noncomputable def diagEll : CZ := zornPlus - zornMinus

/-- The flow-owner name for the diagonal axis is definitionally the native
Peirce-owner axis.  Keeping this equality explicit prevents downstream
consumers from treating the two names as independent distinguished elements.
-/
theorem diagEll_eq_axialI : diagEll = axialI := rfl

noncomputable def diagEllCommutator : EndCZ where
  toFun Z := zMul diagEll Z - zMul Z diagEll
  map_add' X Y := by
    rw [zMul_add_right, zMul_add_left]
    abel
  map_smul' r X := by
    rw [zMul_smul_right, zMul_smul_left, smul_sub]
    rfl

@[simp] theorem diagEllCommutator_apply (Z : CZ) :
    diagEllCommutator Z = zMul diagEll Z - zMul Z diagEll := rfl

theorem diagEllCommutator_coord (Z : CZ) :
    diagEllCommutator Z = { a := 0, b := 0, x := 2 • Z.x, y := -2 • Z.y } := by
  ext <;>
    simp [diagEll, diagEllCommutator, zornPlus, zornMinus, zMul, dot, cross]
  all_goals try { rename_i i; fin_cases i <;>
    simp [diagEll, diagEllCommutator, zornPlus, zornMinus, zMul, dot, cross] <;>
    ring_nf }

noncomputable def diagEllGrading : EndCZ := (1 / 2 : ℝ) • diagEllCommutator

@[simp] theorem diagEllGrading_apply (Z : CZ) :
    diagEllGrading Z = (1 / 2 : ℝ) • diagEllCommutator Z := rfl

theorem diagEllGrading_coord (Z : CZ) :
    diagEllGrading Z = { a := 0, b := 0, x := Z.x, y := -Z.y } := by
  rw [diagEllGrading_apply, diagEllCommutator_coord]
  ext <;> simp [smul_eq_mul, Equiv.smul_def, coordEquiv]

theorem diagEllGrading_sq_coord (Z : CZ) :
    diagEllGrading (diagEllGrading Z) = { a := 0, b := 0, x := Z.x, y := Z.y } := by
  rw [diagEllGrading_coord, diagEllGrading_coord]
  ext <;> simp

/-! The coordinate grading and the native Peirce axial grading are the same
linear endomorphism.  This is the canonical name-level bridge for consumers
that previously used `diagEllGrading` or `axialGrading` separately. -/
theorem diagEllGrading_eq_axialGrading :
    diagEllGrading = axialGrading := by
  apply LinearMap.ext
  intro Z
  rw [diagEllGrading_coord, axialGrading_apply]

theorem diagEllGrading_tripotent :
    diagEllGrading ^ 3 = diagEllGrading := by
  apply LinearMap.ext
  intro Z
  change diagEllGrading (diagEllGrading (diagEllGrading Z)) = diagEllGrading Z
  rw [diagEllGrading_sq_coord, diagEllGrading_coord]

end InfoGeometry.Lie.SplitOctonionEllFlowOperator
