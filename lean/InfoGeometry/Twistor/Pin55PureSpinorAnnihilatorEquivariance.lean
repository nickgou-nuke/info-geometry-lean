import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
import InfoGeometry.Canonical.Pin55NativeCover

/-!
# Pin(5,5) pure-spinor annihilator equivariance

This owner isolates the exact algebraic contract needed to transport the
split `(5,5)` exterior-spinor annihilator under an invertible Clifford-module
symmetry.

The repository already provides the full real split `Pin(5,5)` carrier
`RealPin55` and its native orthogonal action on `V55`.  What is not yet owned
for the exterior-algebra spinor carrier is a native `RealPin55` action together
with the Clifford intertwining law.  Therefore this file does not invent such
an action.  Instead it:

* proves annihilator equivariance for any invertible vector/spinor transport
  satisfying the exact Clifford intertwining identity;
* transports the repository-native `RealPin55` orthogonal action from `V55`
  to the exterior-spinor neutral carrier;
* packages the remaining spinor-action/intertwining datum as a minimal
  `RealPin55ExteriorSpinorLift` interface;
* derives the `RealPin55` annihilator-equivariance theorem from that interface.

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
carrier that intertwines Clifford multiplication.
-/
structure CliffordSpinorTransport where
  vector : NeutralSpace ≃ₗ[ℝ] NeutralSpace
  spinor : Spinor ≃ₗ[ℝ] Spinor
  intertwines : ∀ w : NeutralSpace, ∀ ψ : Spinor,
    neutralAction (vector w) (spinor ψ) =
      spinor (neutralAction w ψ)

namespace CliffordSpinorTransport

variable (T : CliffordSpinorTransport)

/-- Membership in the annihilator is preserved and reflected by an invertible
Clifford-intertwining transport. -/
theorem mem_transport_annihilator_iff
    (ψ : Spinor) (w : NeutralSpace) :
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
    NeutralSpace ≃ₗ[ℝ] NeutralSpace :=
  neutralToV55.trans
    ((realPin55OrthogonalAction g).toLinearEquiv.trans neutralToV55.symm)

@[simp] theorem realPin55NeutralTransport_apply
    (g : RealPin55) (w : NeutralSpace) :
    realPin55NeutralTransport g w =
      neutralToV55.symm (realPin55OrthogonalAction g (neutralToV55 w)) := by
  rfl

/--
Minimal missing exterior-spinor realization of the full real split Pin action.

A concrete owner must provide an invertible spinor action and prove that it
intertwines the already constructed `RealPin55` vector transport with the
native exterior Clifford action.
-/
structure RealPin55ExteriorSpinorLift where
  spinor : RealPin55 → Spinor ≃ₗ[ℝ] Spinor
  intertwines : ∀ g : RealPin55, ∀ w : NeutralSpace, ∀ ψ : Spinor,
    neutralAction (realPin55NeutralTransport g w) (spinor g ψ) =
      spinor g (neutralAction w ψ)

namespace RealPin55ExteriorSpinorLift

variable (S : RealPin55ExteriorSpinorLift)

/-- The pointwise Clifford transport induced by a full split-Pin exterior
spinor lift. -/
noncomputable def transport (g : RealPin55) : CliffordSpinorTransport where
  vector := realPin55NeutralTransport g
  spinor := S.spinor g
  intertwines := S.intertwines g

/--
Full split `Pin(5,5)` annihilator equivariance, conditional only on the missing
native exterior-spinor lift/intertwiner:

`Ann(g · ψ) = ρ(g)(Ann ψ)`.
-/
theorem annihilator_equivariant
    (g : RealPin55) (ψ : Spinor) :
    neutralAnnihilator (S.spinor g ψ) =
      Submodule.map (realPin55NeutralTransport g).toLinearMap
        (neutralAnnihilator ψ) := by
  exact (S.transport g).annihilator_equivariant ψ

/-- Pointwise annihilator membership version of the same equivariance law. -/
theorem mem_annihilator_transport_iff
    (g : RealPin55) (ψ : Spinor) (w : NeutralSpace) :
    realPin55NeutralTransport g w ∈ neutralAnnihilator (S.spinor g ψ) ↔
      w ∈ neutralAnnihilator ψ := by
  exact (S.transport g).mem_transport_annihilator_iff ψ w

end RealPin55ExteriorSpinorLift

end InfoGeometry.Twistor.Pin55PureSpinorAnnihilatorEquivariance
