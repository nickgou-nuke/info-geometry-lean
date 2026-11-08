import InfoGeometry.Canonical.FilteredHestenesGlobalOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredHestenesGlobalOperator
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

namespace InfoGeometry.Canonical.FilteredHestenesGlobalOperator.LinearFamily

variable {C : HestenesKreinCone} (F : LinearFamily C)

/-- Pointwise arbitrary-length operator/bonding compatibility. -/
theorem op_bondIterate_apply
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    (C.toFilteredPhaseCone).bondIterate n m (F.op n x) =
      F.op (n + m) ((C.toFilteredPhaseCone).bondIterate n m x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hbond := DFunLike.congr_fun (F.op_bond (n + m)) ((C.toFilteredPhaseCone).bondIterate n m x)
      show C.bond (n + m) ((C.toFilteredPhaseCone).bondIterate n m (F.op n x)) =
        F.op (n + m + 1) (C.bond (n + m) ((C.toFilteredPhaseCone).bondIterate n m x))
      rw [ih]
      exact hbond

/-- A compatible operator family intertwines every finite composite bonding
map, not only one-step transitions. -/
theorem op_bondIterate (n : ℕ) :
    ∀ m : ℕ,
      ((C.toFilteredPhaseCone).bondIterate n m).comp (F.op n) =
        (F.op (n + m)).comp
          ((C.toFilteredPhaseCone).bondIterate n m) := fun m => by
  ext x
  exact F.op_bondIterate_apply n m x

/-- The colimit image of an operated state is independent of the later-stage
representative used to compute it. -/
theorem ι_op_bondIterate
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    C.ι (n + m)
        (F.op (n + m)
          ((C.toFilteredPhaseCone).bondIterate n m x)) =
      C.ι n (F.op n x) := by
  rw [← F.op_bondIterate_apply n m x]
  exact (C.toFilteredPhaseCone).ι_bondIterate_apply n m (F.op n x)

/-- A global descent agrees with every iterated representative. -/
theorem globalDescent_iterated
    (T : DoubledSpace C.LimitBase →L[ℝ] DoubledSpace C.LimitBase)
    (hT : F.IsGlobalDescent T)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    T (C.ι (n + m)
        ((C.toFilteredPhaseCone).bondIterate n m x)) =
      C.ι (n + m)
        (F.op (n + m)
          ((C.toFilteredPhaseCone).bondIterate n m x)) := by
  exact hT (n + m) _

end InfoGeometry.Canonical.FilteredHestenesGlobalOperator.LinearFamily
