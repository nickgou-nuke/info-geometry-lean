import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.G2TwistedBraiding

/-!
# Raw finite-order twist audit

`G2TwistedSystem` is only a matrix seed satisfying `Ω ^ 3 = 1`.  This owner
records the inverse consequences of that relation.  It intentionally does
not define a tensor flip, a categorical braiding, Yang--Baxter data, or a
monodromy verdict: those require a concrete tensor realization.
-/

namespace InfoGeometry.Categorical.G2TwistCategoricalBraidingBridge

open InfoGeometry.Algebra.G2

variable {BlockType : Type} [DecidableEq BlockType] [Fintype BlockType]

noncomputable def twistInverseCandidate
    (D : G2TwistedSystem BlockType) : Matrix BlockType BlockType ℂ :=
  D.omega_twist ^ 2

theorem twist_power_three (D : G2TwistedSystem BlockType) :
    D.omega_twist ^ 3 = 1 :=
  D.h_cubic_center

theorem twist_sq_mul (D : G2TwistedSystem BlockType) :
    twistInverseCandidate D * D.omega_twist = 1 := by
  unfold twistInverseCandidate
  rw [← pow_succ]
  simpa using D.h_cubic_center

theorem twist_mul_sq (D : G2TwistedSystem BlockType) :
    D.omega_twist * twistInverseCandidate D = 1 := by
  unfold twistInverseCandidate
  rw [← pow_succ']
  simpa using D.h_cubic_center

end InfoGeometry.Categorical.G2TwistCategoricalBraidingBridge
