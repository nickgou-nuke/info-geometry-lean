import InfoGeometry.Canonical.WeakValueKreinGeometry
import InfoGeometry.External.Auto.SarsModularWeakValue
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The existing guarded weak value on the doubled L² boundary

This is the explicit map from the repository's two-component state functions
to the native doubled Hilbert carrier. The denominator guard is exactly the
simultaneous vanishing of the two overlap quadratics, not diagonal isotropy.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeakValueKreinBoundary

open SarsModularWeakValue InfoGeometry.Krein WeakValueKreinGeometry

abbrev Base := EuclideanSpace ℂ (Fin 2)

def boundaryState (psi phi : State2) : DoubledSpace Base :=
  to_doubled (WithLp.toLp 2 phi) (WithLp.toLp 2 psi)

theorem overlap_boundaryState (psi phi : State2) :
    overlap (boundaryState psi phi) = weakDenominator psi phi := by
  simp [overlap, boundaryState, weakDenominator, cinner, PiLp.inner_apply,
    Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

/-- Exact identification of the native Option guard with the doubled geometry. -/
theorem weakValue_none_iff_two_quadratics (A : M2C) (psi phi : State2) :
    weakValue? A psi phi = none ↔
      swapQuadratic (boundaryState psi phi) = 0 ∧
      phaseSwapQuadratic (boundaryState psi phi) = 0 := by
  rw [← overlap_eq_zero_iff_two_swap_quadratics, overlap_boundaryState]
  simp [weakValue?]

/-- The identity preparation is diagonal-null but has a defined weak value. -/
theorem identity_boundary_null_and_regular :
    diagonalQuadratic (boundaryState ket0 ket0) = 0 ∧
      weakValue? identityWeakOperator ket0 ket0 = some 1 := by
  refine ⟨?_, identity_weak_value_ket0_ket0⟩
  rw [diagonalQuadratic_eq_norm_difference]
  simp [boundaryState]

end InfoGeometry.Canonical.WeakValueKreinBoundary
