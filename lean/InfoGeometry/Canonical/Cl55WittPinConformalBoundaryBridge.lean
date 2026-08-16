import InfoGeometry.Clifford.Cl55WittPinProjectiveNullAction
import InfoGeometry.Clifford.Cl55WittCartanDieudonneReduction
import InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge

namespace InfoGeometry.Canonical.Cl55WittPinConformalBoundaryBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.ProjectiveFoundation
open PACSplit55Cl55CoordinateBridge
open scoped LinearAlgebra.Projectivization

noncomputable def pinInfinityStabilizer : Subgroup Pin55 where
  carrier := {g | pinNativeOrthogonalAction g nativeInfinityVector = nativeInfinityVector}
  one_mem' := by
    change pinConjAction (1 : Pin55) nativeInfinityVector =
      nativeInfinityVector
    rw [pinConjAction_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change pinNativeOrthogonalAction g nativeInfinityVector =
      nativeInfinityVector at hg
    change pinNativeOrthogonalAction h nativeInfinityVector =
      nativeInfinityVector at hh
    change pinNativeOrthogonalAction (g * h) nativeInfinityVector =
      nativeInfinityVector
    rw [pinNativeOrthogonalAction_mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change pinNativeOrthogonalAction g nativeInfinityVector =
      nativeInfinityVector at hg
    change pinNativeOrthogonalAction g⁻¹ nativeInfinityVector =
      nativeInfinityVector
    rw [← hg, ← pinNativeOrthogonalAction_mul_apply, inv_mul_cancel]
    rw [pinNativeOrthogonalAction_apply_vector, pinConjAction_one]
    exact hg.symm

/-!
The full native `Pin(5,5)` action preserves the projective null cone.  The
chosen conformal boundary is a polar hyperplane, so its preservation requires
the expected stabilizer condition on the distinguished infinity vector.
-/

theorem pinProjectivization_preserves_nativeConformalBoundary_of_fixing_infinity
    (g : Pin55)
    (hg : pinNativeOrthogonalAction g nativeInfinityVector = nativeInfinityVector)
    (p : ℙ ℝ V55)
    (hp : nativeConformalBoundary55 p) :
    nativeConformalBoundary55
      (pinProjectiveRepresentation.projectivizationMap g p) := by
  rw [nativeConformalBoundary55_iff_projectiveBoundary] at hp ⊢
  induction p using Projectivization.ind with
  | h v hv =>
      rw [ProjectiveRepresentation.projectivizationMap_mk]
      change QuadraticMap.polar Q55 (pinConjActionEquiv g v)
        nativeInfinityVector = 0
      change QuadraticMap.polar Q55 (pinNativeOrthogonalAction g v)
        nativeInfinityVector = 0
      rw [← hg, Q55_isometry_preserves_polar]
      exact hp

theorem pinInfinityStabilizer_preserves_nativeConformalBoundary
    (g : pinInfinityStabilizer)
    (p : ℙ ℝ V55)
    (hp : nativeConformalBoundary55 p) :
    nativeConformalBoundary55
      (pinProjectiveRepresentation.projectivizationMap g.1 p) := by
  exact pinProjectivization_preserves_nativeConformalBoundary_of_fixing_infinity
    g.1 g.2 p hp

/-! ## Hom-level native boundary symmetry

The preceding theorem is pointwise.  This packages the same native
`Pin(5,5)` action as the actual group hom carried by the infinity stabilizer.
No matrix surrogate or new projective carrier is introduced.
-/

noncomputable def pinInfinityStabilizerProjectivizationAction :
    pinInfinityStabilizer →* Function.End (ℙ ℝ V55) :=
  pinProjectivizationAction.comp pinInfinityStabilizer.subtype

@[simp] theorem pinInfinityStabilizerProjectivizationAction_apply
    (g : pinInfinityStabilizer) (p : ℙ ℝ V55) :
    pinInfinityStabilizerProjectivizationAction g p =
      pinProjectivizationAction (g : Pin55) p := rfl

theorem pinInfinityStabilizerProjectivizationAction_preserves_boundary
    (g : pinInfinityStabilizer) (p : ℙ ℝ V55)
    (hp : nativeConformalBoundary55 p) :
    nativeConformalBoundary55
      (pinInfinityStabilizerProjectivizationAction g p) := by
  rw [pinInfinityStabilizerProjectivizationAction_apply]
  exact pinInfinityStabilizer_preserves_nativeConformalBoundary g p hp

end InfoGeometry.Canonical.Cl55WittPinConformalBoundaryBridge
