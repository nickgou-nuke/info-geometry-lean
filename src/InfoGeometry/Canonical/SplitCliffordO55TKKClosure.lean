import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroFiniteWindow
import InfoGeometry.Canonical.CliffordO55ProjectiveReconciliation

open InfoGeometry.Canonical.SuperVirasoroFiniteWindow
open InfoGeometry.Canonical
open Matrix

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-!
# The split `O(5,5)` form and infinitesimal carrier

BUCKET 1: The diagonal split form and its skew-adjoint matrix predicate are
definitions over the stated coefficient ring.

BUCKET 2: The relation to a real Lie subalgebra is established by the separate
`O55OrthogonalLieCarrier` owner. This file does not construct a Pin group,
Klein-bottle topology, a Weyl group, or a Virasoro representation.

BUCKET 3: Chiral anomaly cancellation and nonzero-fermion finite-window
closure remain open here. The imported finite-window source proves the
zero-`ψ` specialization; that specialization is not an `O(5,5)` anomaly result.
-/

namespace InfoGeometry.Canonical

namespace O55Representation

section Ring

variable {𝕜 V : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- O(5,5) split signature quadratic form matrix. -/
def O55Form : Matrix (Fin 10) (Fin 10) 𝕜 :=
  diagonal (fun i => if i.val < 5 then 1 else -1)

/-- The split form is an involution, since each diagonal entry is `1` or `-1`. -/
theorem O55Form_mul_self : O55Form (𝕜 := 𝕜) * O55Form = 1 := by
  rw [O55Form, Matrix.diagonal_mul_diagonal]
  have hdiag : (fun i : Fin 10 =>
      (if i.val < 5 then (1 : 𝕜) else -1) * (if i.val < 5 then 1 else -1)) =
      fun _ => (1 : 𝕜) := by
    funext i
    split_ifs <;> simp
  rw [hdiag]
  exact Matrix.diagonal_one

end Ring

end O55Representation
end InfoGeometry.Canonical
