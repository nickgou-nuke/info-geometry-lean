import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
import InfoGeometry.Canonical.Pin55NativeCover

/-!
# Pin(5,5) pure-spinor annihilator equivariance interface

This owner isolates the exact sign-free algebraic contract for transporting the
split `(5,5)` exterior-spinor annihilator under an invertible Clifford-module
symmetry.

It proves the reusable theorem

`Ann(T_spinor ψ) = T_vector(Ann ψ)`

whenever the vector and spinor transports intertwine Clifford multiplication
exactly.  It also transports the repository-native full real split `Pin(5,5)`
orthogonal action from `V55` to the exterior-spinor neutral carrier.

For the full Pin group the native vector action is the twisted adjoint, so odd
Pin elements introduce the grade-involution sign.  The concrete owner
`Pin55ExteriorSpinorNativeAction` handles that parity directly and proves the
unconditional `RealPin55` annihilator-equivariance theorem.  The
`RealPin55ExteriorSpinorLift` structure retained here is therefore a stronger,
sign-free adapter useful for realizations where exact intertwining is available;
it is not a claim that such an adapter is required for annihilator equivariance.

No identification of the two connected components of the maximal-neutral
Grassmannian, chirality sectors, matter/antimatter, or CPT is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.Pin55PureSpinorAnnihilatorEquivariance

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Clifford55

/--
An invertible transport of the neutral vector carrier and the exterior-spinor
carrier that intertwines Clifford multiplication exactly.
-/
structure CliffordSpinorTransport where
  vector : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace ≃ₗ[ℝ]
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace
  spinor : Spinor ≃ₗ[ℝ] Spinor
  intertwines : ∀ w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace,
    ∀ ψ : Spinor,
    neutralAction (vector w) (spinor ψ) =
      spinor (neutralAction w ψ)

namespace CliffordSpinorTransport

variable (T : CliffordSpinorTransport)

/-- Membership in the annihilator is preserved and reflected by an invertible
Clifford-intertwining transport. -/
theorem mem_transport_annihilator_iff
    (ψ : Spinor)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace) :
    T.vector w ∈ neutralAnnihilator (T.spinor ψ) ↔
      w ∈ neutralAnnihilator ψ := by
  rw [mem_neutralAnnihilator_iff, mem_neutralAnnihilator_iff]
  rw [T.intertwines]
  constructor
  · intro h
    apply T.spinor.injective
    simpa using h
  · intro h
    simp [h]

/--
Exact annihilator equivariance:

`Ann(T_spinor ψ) = T_vector(Ann ψ)`.
-/
theorem annihilator_equivariant (ψ : Spinor) :
    neutralAnnihilator (T.spinor ψ) =
      Submodule.map T.vector.toLinearMap (neutralAnnihilator ψ) := by
  ext z
  constructor
  · intro hz
    refine ⟨T.vector.symm z, ?_, by simp⟩
    have hmem :
        T.vector (T.vector.symm z) ∈
          neutralAnnihilator (T.spinor ψ) := by
      simpa using hz
    exact (T.mem_transport_annihilator_iff ψ (T.vector.symm z)).mp hmem
  · rintro ⟨w, hw, rfl⟩
    exact (T.mem_transport_annihilator_iff ψ w).mpr hw

/-- The transported spinor is nonzero exactly when the source spinor is
nonzero. -/
theorem spinor_ne_zero_iff (ψ : Spinor) :
    T.spinor ψ ≠ 0 ↔ ψ ≠ 0 := by
  constructor
  · intro h hψ
    apply h
    simp [hψ]
  · intro h hzero
    apply h
    apply T.spinor.injective
    simpa using hzero

end CliffordSpinorTransport

/-! ## Repository-native RealPin55 vector transport -/

/--
The full real split `Pin(5,5)` orthogonal action, transported from the native
`V55` model to the exterior-spinor neutral carrier.
-/
noncomputable def realPin55NeutralTransport (g : RealPin55) :
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace ≃ₗ[ℝ]
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace :=
  neutralToV55.trans
    ((realPin55OrthogonalAction g).toLinearEquiv.trans neutralToV55.symm)

@[simp] theorem realPin55NeutralTransport_apply
    (g : RealPin55)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace) :
    realPin55NeutralTransport g w =
      neutralToV55.symm (realPin55OrthogonalAction g (neutralToV55 w)) := by
  rfl

/--
Optional exact-intertwining realization of the full real split Pin action.

The concrete native Pin action only intertwines the twisted-adjoint vector
action up to the parity sign on odd Pin elements.  Consequently this structure
is intentionally stronger than what is needed for annihilator equivariance.
-/
structure RealPin55ExteriorSpinorLift where
  spinor : RealPin55 → Spinor ≃ₗ[ℝ] Spinor
  intertwines : ∀ g : RealPin55,
    ∀ w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace,
      ∀ ψ : Spinor,
    neutralAction (realPin55NeutralTransport g w) (spinor g ψ) =
      spinor g (neutralAction w ψ)

namespace RealPin55ExteriorSpinorLift

variable (S : RealPin55ExteriorSpinorLift)

/-- The pointwise exact Clifford transport induced by a sign-free split-Pin
spinor lift. -/
noncomputable def transport (g : RealPin55) : CliffordSpinorTransport where
  vector := realPin55NeutralTransport g
  spinor := S.spinor g
  intertwines := S.intertwines g

/-- Exact-lift specialization of annihilator equivariance. -/
theorem annihilator_equivariant
    (g : RealPin55) (ψ : Spinor) :
    neutralAnnihilator (S.spinor g ψ) =
      Submodule.map (realPin55NeutralTransport g).toLinearMap
        (neutralAnnihilator ψ) := by
  exact (S.transport g).annihilator_equivariant ψ

/-- Pointwise annihilator membership version of the same exact-lift law. -/
theorem mem_annihilator_transport_iff
    (g : RealPin55) (ψ : Spinor)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace) :
    realPin55NeutralTransport g w ∈ neutralAnnihilator (S.spinor g ψ) ↔
      w ∈ neutralAnnihilator ψ := by
  exact (S.transport g).mem_transport_annihilator_iff ψ w

end RealPin55ExteriorSpinorLift

end InfoGeometry.Twistor.Pin55PureSpinorAnnihilatorEquivariance
