import InfoGeometry.Canonical.BosonizationConstructiveCurrent

/-!
# InfoGeometry.Canonical.SplitCliffordWickDiracSea

Finite-window Dirac-sea crossing identities for the split-Clifford Wick branch.

This file exports concrete central-term lemmas in the `m + n = 0` interface
shape consumed by downstream Heisenberg/Sugawara packaging.
-/

noncomputable section

namespace SplitCliffordWickDiracSea

open InfoGeometry.Canonical.BosonizationConstructiveCurrent

namespace RawCARModeCompletion

variable {A : Type*} [Ring A]
variable (C : RawCARModeCompletion A)

/--
Finite-window Dirac-sea crossing coefficient.

Once the cutoff window contains the full crossing strip (`|m| ≤ N`), the
finite crossing sum is exactly the mode shift `m`.
-/
theorem diracSea_crossing_cutoff_eq_mode_of_natAbs_le
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N) :
    (∑ a ∈ cutoffWindow N, (polarizationIndicator a - polarizationIndicator (a + m))) = m :=
  InfoGeometry.Canonical.BosonizationConstructiveCurrent.crossingNumber_cutoff_eq_mode_of_large_cutoff N m hN

/--
Finite-window central coefficient in Heisenberg shape.

For cutoff `N` with `|m| ≤ N`, the explicit crossing term is already
`m δ_{m+n,0}` against the central carrier.
-/
theorem cutoffWindowCrossingTerm_eq_heisenberg_of_natAbs_le
    (N : Nat) (m n : Int) (hN : m.natAbs ≤ N) :
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffWindowCrossingTerm C N m n =
      if m + n = 0 then m • C.central else 0 :=
  InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffWindowCrossingTerm_eq_heisenberg_of_natAbs_le C N m n hN

/--
Finite-cutoff current commutator in downstream interface shape.

For cutoff `N` with `|m| ≤ N`:

`[J_m^(N), J_n^(N)] = boundary + (if m+n=0 then m • K else 0)`,

where `K = C.central` and `boundary` is the explicit finite-cutoff boundary term.
-/
theorem cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le
    (N : Nat) (m n : Int) (hN : m.natAbs ≤ N) :
    comm
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffCurrent C N m)
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffCurrent C N n)
      =
      InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffBoundaryTerm C N m n +
        (if m + n = 0 then m • C.central else 0) :=
      InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le C N m n hN

/--
Diagonal/base-case commutator specialization (`n = -m`) in downstream form.

For cutoff `N` with `|m| ≤ N`:

`[J_m^(N), J_{-m}^(N)] = boundary + m • K`,

where `K = C.central`.
-/
theorem cutoffCurrent_commutator_eq_boundary_add_mode_of_natAbs_le
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N) :
    comm
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffCurrent C N m)
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffCurrent C N (-m))
      =
      InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffBoundaryTerm C N m (-m) +
        m • C.central := by
  simpa using
    (cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le
      (C := C) N m (-m) hN)

/--
Vacuum-readout base case on the scalar carrier:

if the explicit finite-cutoff boundary term vanishes, then
`[J_m^(N), J_{-m}^(N)] = m • K`.
-/
theorem cutoffCurrent_commutator_eq_mode_of_boundary_zero
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hBoundary :
      InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffBoundaryTerm C N m (-m) = 0) :
    comm
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffCurrent C N m)
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion.cutoffCurrent C N (-m))
      =
      m • C.central := by
  have hdiag :=
    cutoffCurrent_commutator_eq_boundary_add_mode_of_natAbs_le (C := C) N m hN
  simpa [hBoundary] using hdiag

end RawCARModeCompletion

end SplitCliffordWickDiracSea
