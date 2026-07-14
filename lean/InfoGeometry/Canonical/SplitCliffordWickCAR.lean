import InfoGeometry.Canonical.BosonizationConstructiveCurrent

/-!
# InfoGeometry.Canonical.SplitCliffordWickCAR

Proof-bearing CAR → Wick kernel theorems for split-current closure.

This file adds no new interfaces. It extracts the two algebraic commutator
lemmas needed for the Heisenberg current debt from the existing owner theorem
surface in `BosonizationConstructiveCurrent`.
-/

namespace SplitCliffordWickCAR

open InfoGeometry.Canonical.BosonizationConstructiveCurrent

/--
Raw CAR bilinears satisfy the matrix-unit commutator:

`[Eᵢⱼ, Eₖₗ] = δⱼₖ Eᵢₗ - δᵢₗ Eₖⱼ`.
-/
theorem car_bilinear_commutator
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (C : RawCARModeCompletion (V →ₗ[𝕜] V))
    (i j k l : Int) :
    comm (C.rawMatrixUnit i j) (C.rawMatrixUnit k l) =
      (if j = k then C.rawMatrixUnit i l else 0) -
        (if i = l then C.rawMatrixUnit k j else 0) :=
  C.raw_matrixUnit_commutator_from_rawCAR i j k l

/--
Normal-ordered CAR bilinears satisfy the Wick/Schwinger commutator:

`[Nᵢⱼ, Nₖₗ] = δⱼₖ Nᵢₗ - δᵢₗ Nₖⱼ + central`.
-/
theorem normalOrdered_bilinear_commutator
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (C : RawCARModeCompletion (V →ₗ[𝕜] V))
    (i j k l : Int) :
    comm (C.matrixUnit i j) (C.matrixUnit k l) =
      (if j = k then C.matrixUnit i l else 0) -
        (if i = l then C.matrixUnit k j else 0) +
        (if j = k ∧ i = l
          then (occ i - occ j) • C.central
          else 0) :=
  C.normalOrdered_matrixUnit_commutator_from_rawCAR i j k l

/--
Dirac-sea crossing-count theorem:
the signed polarization crossing number equals the mode shift.
-/
theorem diracSea_cocycle_sum
    (m : Int) :
    signedCrossingNumber m = m :=
  crossingNumber_eq_mode m

/--
Finite-window Dirac-sea crossing count stabilizes at the exact threshold
`N ≥ |m|`, and equals the mode shift `m`.
-/
theorem cutoff_crossing_sum_eq_mode_of_large_cutoff
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N) :
    cutoffCrossingSum N m = m :=
  crossingNumber_cutoff_eq_mode_of_large_cutoff N m hN

/--
Eventual form of the finite-window crossing-count stabilization.
-/
theorem cutoff_crossing_sum_eventually_eq_mode
    (m : Int) :
    ∀ᶠ N : Nat in Filter.atTop, cutoffCrossingSum N m = m :=
by
  rcases crossingNumber_cutoff_eventually_eq_mode m with ⟨N0, hN0⟩
  exact Filter.eventually_atTop.2 ⟨N0, hN0⟩

/--
Completed-current off-diagonal Heisenberg coefficient vanishes.
-/
theorem completedCurrent_commutator_eq_zero_of_add_ne_zero
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (C : RawCARModeCompletion (V →ₗ[𝕜] V))
    {m n : Int} (hmn : m + n ≠ 0) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) = 0 := by
  rw [normalOrderedCurrent_heisenberg_from_matrixUnit]
  simp [hmn]

/--
Completed-current diagonal Heisenberg coefficient.
-/
theorem completedCurrent_commutator_eq_central_of_add_eq_zero
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (C : RawCARModeCompletion (V →ₗ[𝕜] V))
    {m n : Int} (hmn : m + n = 0) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      m • completedCentral C := by
  rw [normalOrderedCurrent_heisenberg_from_matrixUnit]
  simp [hmn]

end SplitCliffordWickCAR
