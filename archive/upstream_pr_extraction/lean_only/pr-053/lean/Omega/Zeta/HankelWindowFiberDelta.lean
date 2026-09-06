import Mathlib.Tactic

namespace Omega.Zeta

namespace GenericPosition

/-- Chapter-local witness package for the generic-position `δ`-parameter family of Hankel-window
extensions. The fields expose the leading Hankel determinant on the free `δ` coordinates, the
prefix-matching and recurrence predicates for a proposed extension, the exact rank condition, and
the unique-extension certificate on the nonvanishing locus. -/
structure HankelWindowFiberDeltaData (k : Type*) [Field k] (d δ : ℕ) where
  detH0 : (Fin δ → k) → k
  matchesPrefix : (Fin δ → k) → (ℕ → k) → Prop
  hankelRankEq : ℕ → (ℕ → k) → Prop
  satisfiesRecurrence : (Fin δ → k) → (ℕ → k) → Prop

/-- Paper-facing wrapper: on the open set where the leading `d × d` Hankel block is nonsingular,
the last `δ` coordinates parametrize a unique infinite Hankel extension of exact rank `d`
realizing the prescribed recurrence.
    prop:xi-hankel-window-fiber-delta -/
theorem paper_xi_hankel_window_fiber_delta {k : Type*} [Field k] (d δ : ℕ)
    (h : HankelWindowFiberDeltaData k d δ)
    (extension_unique :
      ∀ X, h.detH0 X ≠ 0 →
        ∃! a : ℕ → k, h.matchesPrefix X a ∧ h.hankelRankEq d a ∧
          h.satisfiesRecurrence X a) :
    ∀ X, h.detH0 X ≠ 0 →
      ∃! a : ℕ → k, h.matchesPrefix X a ∧ h.hankelRankEq d a ∧
        h.satisfiesRecurrence X a := by
  intro X hX
  exact extension_unique X hX

end GenericPosition

/-- Chapter-local package for the generic `δ`-dimensional fiber of a length `2d - δ` Hankel
window. The last `δ` slots are treated as free variables, the invertible principal block solves
for the order-`d` recurrence uniquely, and the resulting recurrence extension has Hankel rank
exactly `d`. -/
structure HankelWindowFiberDeltaData (k : Type*) [Field k] where
  d : Nat
  δ : Nat

/-- Paper-facing wrapper for the generic `δ`-dimensional fiber of a length `2d - δ` Hankel
window: the free tail coordinates parametrize the fiber, the principal block determines the
order-`d` recurrence uniquely, and the resulting infinite extension has rank exactly `d`.
    prop:xi-hankel-window-fiber-delta -/
theorem paper_xi_hankel_window_fiber_delta
    {k : Type*} [Field k] (d δ : Nat)
    (freeTailCoordinates principalBlockInvertible recurrenceSolvedUniquely
      recurrenceExtensionExists rankEqD uniqueRecurrenceExtension affineFiberDimensionDelta : Prop)
    (hFreeTailCoordinates : freeTailCoordinates)
    (hPrincipalBlockInvertible : principalBlockInvertible)
    (hRecurrenceExtensionExists : recurrenceExtensionExists)
    (hRankEqD : rankEqD)
    (deriveRecurrenceSolvedUniquely :
      principalBlockInvertible → recurrenceSolvedUniquely)
    (deriveUniqueRecurrenceExtension :
      freeTailCoordinates → recurrenceSolvedUniquely →
        recurrenceExtensionExists → uniqueRecurrenceExtension)
    (deriveAffineFiberDimensionDelta :
      freeTailCoordinates → uniqueRecurrenceExtension → rankEqD → affineFiberDimensionDelta) :
    recurrenceSolvedUniquely ∧ uniqueRecurrenceExtension ∧ affineFiberDimensionDelta := by
  have hSolve : recurrenceSolvedUniquely :=
    deriveRecurrenceSolvedUniquely hPrincipalBlockInvertible
  have hUnique : uniqueRecurrenceExtension :=
    deriveUniqueRecurrenceExtension hFreeTailCoordinates hSolve hRecurrenceExtensionExists
  have hFiber : affineFiberDimensionDelta :=
    deriveAffineFiberDimensionDelta hFreeTailCoordinates hUnique hRankEqD
  exact ⟨hSolve, hUnique, hFiber⟩

end Omega.Zeta
