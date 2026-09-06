import InfoGeometry.Twistor.Pin55PureSpinorAnnihilatorEquivariance
import InfoGeometry.Clifford.Cl55RealSplitPinAction
import InfoGeometry.Clifford.Cl55WittPinParity

/-!
# Native exterior-spinor action of the full real split Pin(5,5)

This owner closes the remaining realization edge in
`Pin55PureSpinorAnnihilatorEquivariance` using repository-native structures
that were already present but distributed across the Clifford/Fock corridor.

The key observation is that no external matrix-spinor identification is
needed.  The repository already has

* `neutralCliffordAlgEquiv : Cl(W) ≃ₐ[ℝ] Cl55`, and
* `neutralCliffordRep : Cl(W) →ₐ[ℝ] End(Λ•V5)`.

Hence every `g : RealPin55`, being a Clifford unit, acts invertibly on the
exterior spinor carrier by the native Clifford representation itself.

The full real split Pin action on vectors is the twisted adjoint
`involute(g) * v * g⁻¹`.  On a Lipschitz/Pin unit the involution is either
`g` or `-g`.  Therefore the Clifford covariance law on spinors is exact up to
one global sign.  That sign is irrelevant to the zero-kernel defining the
pure-spinor annihilator, which yields unconditional annihilator equivariance.
-/

noncomputable section

namespace InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Twistor.Pin55PureSpinorAnnihilatorEquivariance

abbrev NeutralClifford :=
  CliffordAlgebra
    (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
      (E := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5))

/-- The native Clifford element corresponding to a full real split Pin unit. -/
noncomputable def realPin55NeutralCliffordElement (g : RealPin55) :
    NeutralClifford :=
  neutralCliffordAlgEquiv.symm (((g : Cl55ˣ) : Cl55))

/-- The full real split Pin action on the Chevalley/Fock exterior-spinor
carrier, obtained directly from the faithful neutral Clifford representation. -/
noncomputable def realPin55ExteriorSpinorEnd (g : RealPin55) : SpinorEnd :=
  neutralCliffordRep (realPin55NeutralCliffordElement g)

@[simp] theorem realPin55ExteriorSpinorEnd_one :
    realPin55ExteriorSpinorEnd (1 : RealPin55) = 1 := by
  simp [realPin55ExteriorSpinorEnd, realPin55NeutralCliffordElement]

@[simp] theorem realPin55ExteriorSpinorEnd_mul (g h : RealPin55) :
    realPin55ExteriorSpinorEnd (g * h) =
      realPin55ExteriorSpinorEnd g * realPin55ExteriorSpinorEnd h := by
  simp [realPin55ExteriorSpinorEnd, realPin55NeutralCliffordElement, map_mul]

/-- The native exterior-spinor action is invertible because the acting
Clifford element is a unit. -/
noncomputable def realPin55ExteriorSpinorLinearEquiv (g : RealPin55) :
    Spinor ≃ₗ[ℝ] Spinor :=
  LinearEquiv.ofLinear
    (realPin55ExteriorSpinorEnd g)
    (realPin55ExteriorSpinorEnd g⁻¹)
    (by
      apply LinearMap.ext
      intro ψ
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      have h := congrArg (fun T : SpinorEnd => T ψ)
        (realPin55ExteriorSpinorEnd_mul g g⁻¹)
      symm
      simpa [Module.End.mul_apply] using h)
    (by
      apply LinearMap.ext
      intro ψ
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      have h := congrArg (fun T : SpinorEnd => T ψ)
        (realPin55ExteriorSpinorEnd_mul g⁻¹ g)
      symm
      simpa [Module.End.mul_apply] using h)

@[simp] theorem realPin55ExteriorSpinorLinearEquiv_apply
    (g : RealPin55) (ψ : Spinor) :
    realPin55ExteriorSpinorLinearEquiv g ψ =
      realPin55ExteriorSpinorEnd g ψ := by
  rfl

/-- The neutral-space transport from the previous owner is exactly the native
real-split-Pin twisted action after transport through `neutralToV55`. -/
theorem neutralToV55_realPin55NeutralTransport
    (g : RealPin55)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace) :
    neutralToV55 (realPin55NeutralTransport g w) =
      realSplitPinTwistedAction g (neutralToV55 w) := by
  change neutralToV55
      (neutralToV55.symm
        (realSplitPinNativeOrthogonalAction g (neutralToV55 w))) = _
  rw [neutralToV55.apply_symm_apply]
  rfl

/-- The generator transported by the twisted Pin action, multiplied on the
right by the acting Pin unit, collapses to the involuted Pin unit times the
original generator. -/
theorem transported_generator_mul_pin
    (g : RealPin55)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace) :
    CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5))
          (realPin55NeutralTransport g w) *
        realPin55NeutralCliffordElement g =
      neutralCliffordAlgEquiv.symm
        (CliffordAlgebra.involute (((g : Cl55ˣ) : Cl55)) *
          ι55 (neutralToV55 w)) := by
  apply neutralCliffordAlgEquiv.injective
  rw [map_mul, neutralCliffordAlgEquiv_ι]
  simp only [realPin55NeutralCliffordElement,
    neutralCliffordAlgEquiv.apply_symm_apply]
  rw [neutralToV55_realPin55NeutralTransport]
  rw [realSplitPinTwistedAction_apply_ι]
  have hunit :
      (↑((g : Cl55ˣ)⁻¹) : Cl55) * ((g : Cl55ˣ) : Cl55) = 1 :=
    Units.inv_mul (g : Cl55ˣ)
  simp only [realSplitPinTwistedAdj]
  rw [mul_assoc, hunit, mul_one]

/-- Ordinary Clifford multiplication by the Pin unit on a source generator is
exactly the exterior-spinor action applied after the source Clifford action. -/
theorem pin_mul_generator_action
    (g : RealPin55)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace)
      (ψ : Spinor) :
    neutralCliffordRep
        (neutralCliffordAlgEquiv.symm
          (((g : Cl55ˣ) : Cl55) * ι55 (neutralToV55 w))) ψ =
      realPin55ExteriorSpinorEnd g (neutralAction w ψ) := by
  calc
    neutralCliffordRep
        (neutralCliffordAlgEquiv.symm
          (((g : Cl55ˣ) : Cl55) * ι55 (neutralToV55 w))) ψ =
      neutralCliffordRep
        (realPin55NeutralCliffordElement g *
          neutralCliffordAlgEquiv.symm (ι55 (neutralToV55 w))) ψ := by
            rw [map_mul]
            rfl
    _ = (realPin55ExteriorSpinorEnd g *
          neutralCliffordRep
            (neutralCliffordAlgEquiv.symm (ι55 (neutralToV55 w)))) ψ := by
            rw [map_mul]
            rfl
    _ = realPin55ExteriorSpinorEnd g (neutralAction w ψ) := by
            rw [neutralCliffordAlgEquiv_symm_ι55]
            simp only [neutralToV55.symm_apply_apply]
            rw [neutralCliffordRep_ι]
            rfl

/-- Full Pin Clifford covariance is exact up to the parity sign forced by the
twisted adjoint.  This is the correct full-Pin statement; exact sign-free
intertwining is recovered on the even/Spin sector. -/
theorem realPin55_clifford_covariance_or_neg
    (g : RealPin55)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace)
      (ψ : Spinor) :
    neutralAction (realPin55NeutralTransport g w)
        (realPin55ExteriorSpinorEnd g ψ) =
        realPin55ExteriorSpinorEnd g (neutralAction w ψ) ∨
    neutralAction (realPin55NeutralTransport g w)
        (realPin55ExteriorSpinorEnd g ψ) =
        - realPin55ExteriorSpinorEnd g (neutralAction w ψ) := by
  have hcore :
      neutralAction (realPin55NeutralTransport g w)
          (realPin55ExteriorSpinorEnd g ψ) =
        neutralCliffordRep
          (neutralCliffordAlgEquiv.symm
            (CliffordAlgebra.involute (((g : Cl55ˣ) : Cl55)) *
              ι55 (neutralToV55 w))) ψ := by
    rw [← neutralCliffordRep_ι]
    change
      neutralCliffordRep
          (CliffordAlgebra.ι
            (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
              (E := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5))
            (realPin55NeutralTransport g w))
          (neutralCliffordRep (realPin55NeutralCliffordElement g) ψ) = _
    change
      (neutralCliffordRep
          (CliffordAlgebra.ι
            (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
              (E := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5))
            (realPin55NeutralTransport g w)) *
        neutralCliffordRep (realPin55NeutralCliffordElement g)) ψ = _
    rw [← map_mul, transported_generator_mul_pin]
  have hparity :=
    lipschitzUnit_involute_eq_or_neg
      (g : Cl55ˣ)
      (realSplitPin_mem_lipschitz (g : Cl55ˣ) g.property)
  rcases hparity with hplus | hminus
  · left
    rw [hcore, hplus]
    exact pin_mul_generator_action g w ψ
  · right
    rw [hcore, hminus, neg_mul, map_neg, map_neg]
    simp only [LinearMap.neg_apply]
    exact congrArg Neg.neg (pin_mul_generator_action g w ψ)

/-- Pointwise annihilator membership is preserved and reflected by the native
full real split Pin action.  The odd-Pin sign disappears because membership is
a zero-kernel condition. -/
theorem realPin55_mem_annihilator_transport_iff
    (g : RealPin55) (ψ : Spinor)
      (w : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace) :
    realPin55NeutralTransport g w ∈
        neutralAnnihilator (realPin55ExteriorSpinorLinearEquiv g ψ) ↔
      w ∈ neutralAnnihilator ψ := by
  rw [mem_neutralAnnihilator_iff, mem_neutralAnnihilator_iff]
  rw [realPin55ExteriorSpinorLinearEquiv_apply]
  rcases realPin55_clifford_covariance_or_neg g w ψ with h | h
  · rw [h]
    constructor
    · intro hz
      apply (realPin55ExteriorSpinorLinearEquiv g).injective
      simpa using hz
    · intro hz
      simp [hz]
  · rw [h]
    constructor
    · intro hz
      have hz' : realPin55ExteriorSpinorEnd g (neutralAction w ψ) = 0 := by
        simpa using hz
      apply (realPin55ExteriorSpinorLinearEquiv g).injective
      simpa using hz'
    · intro hz
      simp [hz]

/-- Unconditional full split `Pin(5,5)` annihilator equivariance on the
repository-native exterior-spinor carrier. -/
theorem realPin55_annihilator_equivariant
    (g : RealPin55) (ψ : Spinor) :
    neutralAnnihilator (realPin55ExteriorSpinorLinearEquiv g ψ) =
      Submodule.map (realPin55NeutralTransport g).toLinearMap
        (neutralAnnihilator ψ) := by
  ext z
  constructor
  · intro hz
    refine ⟨(realPin55NeutralTransport g).symm z, ?_, by simp⟩
    have hmem :
        realPin55NeutralTransport g ((realPin55NeutralTransport g).symm z) ∈
          neutralAnnihilator (realPin55ExteriorSpinorLinearEquiv g ψ) := by
      simpa using hz
    exact (realPin55_mem_annihilator_transport_iff
      g ψ ((realPin55NeutralTransport g).symm z)).mp hmem
  · rintro ⟨w, hw, rfl⟩
    exact (realPin55_mem_annihilator_transport_iff g ψ w).mpr hw

end InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction
