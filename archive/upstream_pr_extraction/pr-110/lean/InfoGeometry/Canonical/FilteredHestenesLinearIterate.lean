import InfoGeometry.Canonical.FilteredHestenesGlobalOperator
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredHestenesGlobalOperator
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

namespace InfoGeometry.Canonical.FilteredHestenesGlobalOperator.LinearFamily

variable {C : HestenesKreinCone} (F : LinearFamily C)

/-- A compatible operator family intertwines every finite composite bonding
map, not only one-step transitions. -/
theorem op_bondIterate (n : ℕ) :
    ∀ m : ℕ,
      ((C.toFilteredPhaseCone).bondIterate n m).comp (F.op n) =
        (F.op (n + m)).comp
          ((C.toFilteredPhaseCone).bondIterate n m)
  | 0 => by
      simp
  | m + 1 => by
      change
        ((C.bond (n + m)).comp
          ((C.toFilteredPhaseCone).bondIterate n m)).comp (F.op n) =
        (F.op ((n + m) + 1)).comp
          ((C.bond (n + m)).comp
            ((C.toFilteredPhaseCone).bondIterate n m))
      calc
        ((C.bond (n + m)).comp
            ((C.toFilteredPhaseCone).bondIterate n m)).comp (F.op n)
            =
          (C.bond (n + m)).comp
            (((C.toFilteredPhaseCone).bondIterate n m).comp (F.op n)) := by
              simp [ContinuousLinearMap.comp_assoc]
        _ =
          (C.bond (n + m)).comp
            ((F.op (n + m)).comp
              ((C.toFilteredPhaseCone).bondIterate n m)) := by
                rw [op_bondIterate n m]
        _ =
          ((C.bond (n + m)).comp (F.op (n + m))).comp
            ((C.toFilteredPhaseCone).bondIterate n m) := by
              simp [ContinuousLinearMap.comp_assoc]
        _ =
          ((F.op ((n + m) + 1)).comp (C.bond (n + m))).comp
            ((C.toFilteredPhaseCone).bondIterate n m) := by
              rw [F.op_bond (n + m)]
        _ =
          (F.op ((n + m) + 1)).comp
            ((C.bond (n + m)).comp
              ((C.toFilteredPhaseCone).bondIterate n m)) := by
              simp [ContinuousLinearMap.comp_assoc]

/-- Pointwise arbitrary-length operator/bonding compatibility. -/
theorem op_bondIterate_apply
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    (C.toFilteredPhaseCone).bondIterate n m (F.op n x) =
      F.op (n + m) ((C.toFilteredPhaseCone).bondIterate n m x) := by
  have h := congrArg
    (fun L :
      DoubledSpace (C.Base n) →L[ℝ] DoubledSpace (C.Base (n + m)) => L x)
    (F.op_bondIterate n m)
  simpa [ContinuousLinearMap.comp_apply] using h

/-- The colimit image of an operated state is independent of the later-stage
representative used to compute it. -/
theorem ι_op_bondIterate
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    C.ι (n + m)
        (F.op (n + m)
          ((C.toFilteredPhaseCone).bondIterate n m x)) =
      C.ι n (F.op n x) := by
  rw [← F.op_bondIterate_apply n m x]
  have h :=
    (C.toFilteredPhaseCone).ι_bondIterate_apply n m (F.op n x)
  simpa [HestenesKreinCone.toFilteredPhaseCone] using h

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
