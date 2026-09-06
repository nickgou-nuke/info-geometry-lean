import InfoGeometry.Clifford.SplitClifford55NeutralFormBridge

/-!
# Transport of Mathlib's native Pin subgroup across the neutral-form equivalence

This owner transports `pinGroup ChevalleyQ55` to the native `Pin55` subgroup.
It deliberately does not identify this unitary subgroup with the corrected
real split-Pin generator subgroup, since the latter also contains positive-norm
vector generators.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55PinGroupTransport

open CliffordAlgebra
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge

abbrev ChevalleyPin55 := pinGroup ChevalleyQ55

private theorem map_pinGroup_mem {g : ChevalleyPin55} :
    neutralCliffordAlgEquiv_for_chevalleyQ
        (g : CliffordAlgebra ChevalleyQ55) ∈ Clifford55.Pin55 := by
  rw [pinGroup.mem_iff]
  constructor
  · refine (Submonoid.mem_map).2 ⟨
      Units.map neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.toMonoidHom
        (pinGroup.toUnits g), ?_, ?_⟩
    · change Units.map
        neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.toMonoidHom
          (pinGroup.toUnits g) ∈ (lipschitzGroup Clifford55.Q55).toSubmonoid
      exact neutralCliffordAlgEquiv_maps_lipschitzGroup
        (pinGroup.units_mem_lipschitzGroup g.prop)
    · rfl
  · rw [Unitary.mem_iff]
    constructor
    · have h := congrArg neutralCliffordAlgEquiv_for_chevalleyQ
          (pinGroup.mem_unitary g.prop).1
      simpa only [map_mul, neutralCliffordAlgEquiv_map_star, map_one] using h
    · have h := congrArg neutralCliffordAlgEquiv_for_chevalleyQ
          (pinGroup.mem_unitary g.prop).2
      simpa only [map_mul, neutralCliffordAlgEquiv_map_star, map_one] using h

noncomputable def pinGroupTransportHom :
    ChevalleyPin55 →* Clifford55.Pin55 where
  toFun g :=
    ⟨neutralCliffordAlgEquiv_for_chevalleyQ
        (g : CliffordAlgebra ChevalleyQ55), map_pinGroup_mem⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp

theorem pinGroupTransportHom_injective :
    Function.Injective pinGroupTransportHom := by
  intro g h gh
  apply Subtype.ext
  apply neutralCliffordAlgEquiv_for_chevalleyQ.injective
  have hcoe := congrArg
      (fun z : Clifford55.Pin55 => (z : Clifford55.Cl55)) gh
  change neutralCliffordAlgEquiv_for_chevalleyQ
      (g : CliffordAlgebra ChevalleyQ55) =
    neutralCliffordAlgEquiv_for_chevalleyQ
      (h : CliffordAlgebra ChevalleyQ55) at hcoe
  exact hcoe

private theorem map_pinGroup_mem_symm {g : Clifford55.Pin55} :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm
        (g : Clifford55.Cl55) ∈ ChevalleyPin55 := by
  rw [pinGroup.mem_iff]
  constructor
  · refine (Submonoid.mem_map).2 ⟨
      Units.map neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv.toMonoidHom
        (Clifford55.pinToUnits g), ?_, ?_⟩
    · change Units.map
        neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv.toMonoidHom
          (Clifford55.pinToUnits g) ∈ (lipschitzGroup ChevalleyQ55).toSubmonoid
      exact neutralCliffordAlgEquiv_symm_maps_lipschitzGroup
        (pinGroup.units_mem_lipschitzGroup g.prop)
    · rfl
  · rw [Unitary.mem_iff]
    constructor
    · have h := congrArg neutralCliffordAlgEquiv_for_chevalleyQ.symm
          (pinGroup.mem_unitary g.prop).1
      simpa only [map_mul, neutralCliffordAlgEquiv_symm_map_star, map_one] using h
    · have h := congrArg neutralCliffordAlgEquiv_for_chevalleyQ.symm
          (pinGroup.mem_unitary g.prop).2
      simpa only [map_mul, neutralCliffordAlgEquiv_symm_map_star, map_one] using h

theorem pinGroupTransportHom_surjective :
    Function.Surjective pinGroupTransportHom := by
  intro g
  refine ⟨⟨neutralCliffordAlgEquiv_for_chevalleyQ.symm
      (g : Clifford55.Cl55), map_pinGroup_mem_symm⟩, ?_⟩
  apply Subtype.ext
  change neutralCliffordAlgEquiv_for_chevalleyQ
      (neutralCliffordAlgEquiv_for_chevalleyQ.symm (g : Clifford55.Cl55)) =
    (g : Clifford55.Cl55)
  exact neutralCliffordAlgEquiv_for_chevalleyQ.apply_symm_apply _

noncomputable def pinGroupTransportEquiv :
    ChevalleyPin55 ≃* Clifford55.Pin55 :=
  MulEquiv.ofBijective pinGroupTransportHom
    ⟨pinGroupTransportHom_injective, pinGroupTransportHom_surjective⟩

@[simp] theorem pinGroupTransportEquiv_apply (g : ChevalleyPin55) :
    pinGroupTransportEquiv g = pinGroupTransportHom g :=
  rfl

noncomputable def chevalleySpinToPin
    (g : SplitClifford55NeutralFormBridge.ChevalleySpin55) :
    ChevalleyPin55 :=
  ⟨g, spinGroup.mem_pin g.property⟩

theorem pinGroupTransportEquiv_spinGroupTransport_commutes
    (g : SplitClifford55NeutralFormBridge.ChevalleySpin55) :
    pinGroupTransportEquiv (chevalleySpinToPin g) =
      Clifford55.spinToPin
        (SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g) := by
  apply Subtype.ext
  rfl

end InfoGeometry.Clifford.SplitClifford55PinGroupTransport
