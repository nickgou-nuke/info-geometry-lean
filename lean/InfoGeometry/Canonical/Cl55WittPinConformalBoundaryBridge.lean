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

/-! The complementary affine chart is preserved by the same native action. -/
theorem pinInfinityStabilizer_preserves_nativeAffineChart
    (g : pinInfinityStabilizer)
    (p : ℙ ℝ V55)
    (hp : nativeAffineChart55 p) :
    nativeAffineChart55
      (pinProjectiveRepresentation.projectivizationMap g.1 p) := by
  apply (nativeAffineChart55_iff_not_nativeConformalBoundary55
    (pinProjectiveRepresentation.projectivizationMap g.1 p)).2
  intro hboundary
  have hp' : ¬ nativeConformalBoundary55 p :=
    (nativeAffineChart55_iff_not_nativeConformalBoundary55 p).1 hp
  have hboundary' :=
    pinInfinityStabilizer_preserves_nativeConformalBoundary
      (g := g⁻¹)
      (p := pinProjectiveRepresentation.projectivizationMap g.1 p)
      hboundary
  have hcomp :=
    congrFun
      (pinProjectiveRepresentation.projectivizationMap_mul
        (g.1)⁻¹ g.1) p
  have hcomp' :
      pinProjectiveRepresentation.projectivizationMap (g.1)⁻¹
          (pinProjectiveRepresentation.projectivizationMap g.1 p) = p := by
    rw [inv_mul_cancel,
      pinProjectiveRepresentation.projectivizationMap_one] at hcomp
    simpa [Function.comp_def] using hcomp.symm
  have hboundary'' :
      nativeConformalBoundary55
        (pinProjectiveRepresentation.projectivizationMap (g.1)⁻¹
          (pinProjectiveRepresentation.projectivizationMap g.1 p)) := by
    simpa using hboundary'
  rw [hcomp'] at hboundary''
  exact hp' hboundary''

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

/-! ## Restricted action on the native null affine chart -/

abbrev nativeNullAffineChart55Carrier : Type :=
  {p : ℙ ℝ V55 // nativeNullAffineChart55 p}

noncomputable def pinInfinityStabilizerNativeNullAffineChartAction
    (g : pinInfinityStabilizer) :
    nativeNullAffineChart55Carrier → nativeNullAffineChart55Carrier :=
  fun p =>
    ⟨pinProjectiveRepresentation.projectivizationMap g.1 p.1,
      ⟨pinProjectivization_preserves_null g.1 p.1 p.2.1,
        pinInfinityStabilizer_preserves_nativeAffineChart g p.1 p.2.2⟩⟩

noncomputable def pinInfinityStabilizerNativeNullAffineChartActionHom :
    pinInfinityStabilizer →*
      Function.End nativeNullAffineChart55Carrier where
  toFun := pinInfinityStabilizerNativeNullAffineChartAction
  map_one' := by
    funext p
    apply Subtype.ext
    change pinProjectiveRepresentation.projectivizationMap
      (1 : Pin55) p.1 = p.1
    rw [pinProjectiveRepresentation.projectivizationMap_one]
    rfl
  map_mul' := by
    intro g h
    funext p
    apply Subtype.ext
    have hmul :=
      congrFun
        (pinProjectiveRepresentation.projectivizationMap_mul
          (g.1) (h.1)) p.1
    simpa [pinInfinityStabilizerNativeNullAffineChartAction,
      Function.comp_def] using hmul

@[simp] theorem pinInfinityStabilizerNativeNullAffineChartActionHom_apply
    (g : pinInfinityStabilizer)
    (p : nativeNullAffineChart55Carrier) :
    pinInfinityStabilizerNativeNullAffineChartActionHom g p =
      pinInfinityStabilizerNativeNullAffineChartAction g p :=
  rfl

theorem pinInfinityStabilizerNativeNullAffineChartAction_preserves_null
    (g : pinInfinityStabilizer)
    (p : nativeNullAffineChart55Carrier) :
    (pinInfinityStabilizerNativeNullAffineChartAction g p).1 =
      pinProjectiveRepresentation.projectivizationMap g.1 p.1 :=
  rfl

end InfoGeometry.Canonical.Cl55WittPinConformalBoundaryBridge
