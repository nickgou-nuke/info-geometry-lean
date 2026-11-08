import InfoGeometry.Arithmetic.Grothendieck
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Analysis.RotorCocycleBregmanBridge
import DAG.AffineProjectiveClosure

namespace InfoGeometry.Arithmetic.GrothendieckMotive

open InfoGeometry.Arithmetic
open InfoGeometry.Analysis.RotorCocycleBregmanBridge

/-- The arithmetic vacuum has trivial Liouville grading. -/
@[simp] theorem liouville_one :
    BostConnesSystem.liouville 1 = 1 :=
  BostConnesSystem.liouville_one

/-- The arithmetic parity squares to `1`. -/
theorem liouville_sq (n : ℕ+) :
    BostConnesSystem.liouville n * BostConnesSystem.liouville n = 1 :=
  BostConnesSystem.liouville_sq n n.property

/-- The modular remainder packet is exact at time `0`. -/
@[simp] theorem exponentialRemainder_zero {n : ℕ}
    (K : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n) :
    InfoGeometry.Analysis.BregmanAnalyticBound.exponentialRemainder K 0 = 0 :=
  InfoGeometry.Analysis.RotorCocycleBregmanBridge.exponentialRemainder_zero K

theorem finite_motive_inputs {n : ℕ}
    (p : ℕ+) (hp : Nat.Prime p.val)
    (K : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n) :
    BostConnesSystem.liouville 1 = 1 ∧
      BostConnesSystem.liouville p = -1 ∧
      BostConnesSystem.liouville p * BostConnesSystem.liouville p = 1 ∧
      (InfoGeometry.Analysis.BregmanAnalyticBound.exponentialRemainder K 0 = 0) := by
  constructor
  · exact liouville_one
  constructor
  · exact BostConnesSystem.liouville_prime p hp
  constructor
  · exact liouville_sq p
  · exact exponentialRemainder_zero K

/-!
The arithmetic motive layer uses the actual additive Grothendieck completion,
not a string-valued certificate.  The universal property below is the native
owner-level statement available without adding unsupported cohomological or
Weil hypotheses.
-/
theorem grothendieck_motive_completion_unique
    {M A : Type*} [AddCommMonoid M] [AddCommGroup A]
    (f : M →+ A) (g : Grothendieck M →+ A)
    (h_comp : ∀ m, g (grothendieckMap M m) = f m) (x : Grothendieck M) :
    g x = grothendieckLift f x :=
  grothendieckLift_unique f g h_comp x

end InfoGeometry.Arithmetic.GrothendieckMotive
