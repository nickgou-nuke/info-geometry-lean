import InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat

/-!
# Separation of the CAR and CCR parameter fibres

The q-coordinate is part of the ambient noncommutative parameter space.  Thus
the fermionic (`q = -1`) and bosonic (`q = 1`) zero fibres are disjoint before
any representation or completion is chosen.  This is a small but useful
topological readout of the CAR/CCR distinction.
-/

namespace InfoGeometry.Canonical.CARCCRParameterFiberSeparation

open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat

variable {A : Type*} [CStarAlgebra A]

theorem qCcrParameterZeroLocusFiber_disjoint
    (q₁ q₂ : A) (h : q₁ ≠ q₂) :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) q₁)
      (qCcrParameterZeroLocusFiber (A := A) q₂) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  exact h (hp₁.2.symm.trans hp₂.2)

theorem car_ccr_parameter_fibres_disjoint
    [CharZero A] :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) (-1))
      (qCcrParameterZeroLocusFiber (A := A) 1) := by
  apply qCcrParameterZeroLocusFiber_disjoint
  intro h
  have htwo : (2 : A) = 0 := by
    calc
      (2 : A) = 1 + 1 := by norm_num
      _ = 1 + (-1) := by rw [h]
      _ = 0 := by simp
  have htwoNat : (2 : ℕ) = 0 := by exact_mod_cast htwo
  omega

theorem cuntz_car_parameter_fibres_disjoint
    [CharZero A] :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) 0)
      (qCcrParameterZeroLocusFiber (A := A) (-1)) := by
  apply qCcrParameterZeroLocusFiber_disjoint
  norm_num

theorem cuntz_ccr_parameter_fibres_disjoint
    [CharZero A] :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) 0)
      (qCcrParameterZeroLocusFiber (A := A) 1) := by
  apply qCcrParameterZeroLocusFiber_disjoint
  norm_num

theorem qCcrParameterZeroLocusFiber_closed
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q : A) :
    IsClosed (qCcrParameterZeroLocusFiber (A := A) q) := by
  rw [show qCcrParameterZeroLocusFiber (A := A) q =
      qCcrParameterZeroLocus (A := A) ∩
        (fun p : QCCRParameterSpace A => p.2.2) ⁻¹' ({q} : Set A) by
    ext p
    rfl]
  exact (qCcrParameterZeroLocus_closed (A := A)).inter
    (isClosed_singleton.preimage
      (continuous_snd.comp continuous_snd))

end InfoGeometry.Canonical.CARCCRParameterFiberSeparation
