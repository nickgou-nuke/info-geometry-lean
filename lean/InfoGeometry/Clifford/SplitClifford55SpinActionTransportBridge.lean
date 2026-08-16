import InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
import InfoGeometry.Clifford.Cl55SpinOperatorAutomorphism

/-!
# Transport of the native `Spin(5,5)` action to the Chevalley carrier

The neutral-form Clifford equivalence transports the already constructed native
conjugation action and its vector readback to the `splitQ` presentation.  This
owner proves only that algebraic commuting square; it does not add a new Spin
action or assert a physical, Lie-group, or Pin/Spin covering identification.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55SpinActionTransportBridge

open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.ChiralLorentzCARLift
open CliffordAlgebra

abbrev Neutral55 := SplitClifford55NeutralFormBridge.Neutral55
abbrev ChevalleyQ55 := SplitClifford55NeutralFormBridge.ChevalleyQ55
abbrev ChevalleySpin55 := SplitClifford55NeutralFormBridge.ChevalleySpin55

noncomputable def transportedSpinAction
    (g : ChevalleySpin55) : Neutral55 ≃ₗ[ℝ] Neutral55 :=
  neutralToV55.trans
    ((spinActionIsometryEquiv
      (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)).toLinearEquiv.trans
        neutralToV55.symm)

@[simp] theorem transportedSpinAction_apply (g : ChevalleySpin55) (x : Neutral55) :
    transportedSpinAction g x =
      neutralToV55.symm (spinAction
        (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)
        (neutralToV55 x)) := by
  simp [transportedSpinAction]

/-! The transported action retains the native quadratic-isometry structure. -/

noncomputable def transportedSpinActionIsometryEquiv
    (g : ChevalleySpin55) :
    ChevalleyQ55.IsometryEquiv ChevalleyQ55 :=
  neutralToV55_isometry_for_chevalleyQ.trans
    ((spinActionIsometryEquiv
      (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)).trans
      neutralToV55_isometry_for_chevalleyQ.symm)

@[simp] theorem transportedSpinActionIsometryEquiv_apply
    (g : ChevalleySpin55) (x : Neutral55) :
    transportedSpinActionIsometryEquiv g x = transportedSpinAction g x := rfl

theorem transportedSpinAction_mul (g h : ChevalleySpin55) :
    transportedSpinAction (g * h) =
      transportedSpinAction g * transportedSpinAction h := by
  apply LinearEquiv.ext
  intro x
  simp only [transportedSpinAction_apply, LinearEquiv.mul_apply]
  have htransport :
      InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv (g * h) =
        InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g *
          InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv h := by
    change spinGroupTransportHom (g * h) =
      spinGroupTransportHom g * spinGroupTransportHom h
    exact map_mul spinGroupTransportHom g h
  rw [htransport]
  simpa only [spinActionIsometryEquiv_apply,
    neutralToV55.apply_symm_apply] using congrArg neutralToV55.symm
      (spinActionIsometryEquiv_mul_apply
        (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)
        (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv h)
        (neutralToV55 x))

noncomputable def transportedSpinActionIsometryEquivHom :
    ChevalleySpin55 →* ChevalleyQ55.IsometryEquiv ChevalleyQ55 where
  toFun := transportedSpinActionIsometryEquiv
  map_one' := by
    apply DFunLike.ext
    intro x
    change transportedSpinAction (1 : ChevalleySpin55) x = x
    change neutralToV55.symm
      (pinTwistedAction
        (spinToPin (spinGroupTransportEquiv (1 : ChevalleySpin55)))
        (neutralToV55 x)) = x
    rw [map_one spinGroupTransportEquiv]
    rw [show spinToPin (1 : Spin55) = 1 by rfl]
    rw [pinTwistedAction_one]
    exact neutralToV55.symm_apply_apply x
  map_mul' g h := by
    apply DFunLike.ext
    intro x
    change transportedSpinAction (g * h) x =
      transportedSpinAction g (transportedSpinAction h x)
    simpa only [LinearEquiv.mul_apply] using
      congrArg (fun e : Neutral55 ≃ₗ[ℝ] Neutral55 => e x)
        (transportedSpinAction_mul g h)

noncomputable def transportedSpinCliffordRingEquiv
    (g : ChevalleySpin55) :
    CliffordAlgebra ChevalleyQ55 ≃+* CliffordAlgebra ChevalleyQ55 :=
  neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.trans
    ((spinCliffordRingEquiv
      (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)).trans
      neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv)

theorem transportedSpinCliffordRingEquiv_eq_chevalley_unit_conjugation
    (g : ChevalleySpin55) (a : CliffordAlgebra ChevalleyQ55) :
    transportedSpinCliffordRingEquiv g a =
      unitConjugationRingEquiv (spinGroup.toUnits g) a := by
  have hu :
      Units.map neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.toMonoidHom
          (spinGroup.toUnits g) =
        spinGroup.toUnits
          (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g) := by
    apply Units.ext
    change neutralCliffordAlgEquiv_for_chevalleyQ
        (g : CliffordAlgebra ChevalleyQ55) =
      (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g :
        Clifford55.Cl55)
    exact spinGroupTransport_coe g
  rw [show transportedSpinCliffordRingEquiv g =
      neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.trans
        ((spinCliffordRingEquiv
          (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)).trans
            neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv) by rfl]
  simp only [RingEquiv.trans_apply, spinCliffordRingEquiv_apply]
  rw [← hu]
  simp only [Units.coe_map]

  change neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv
      (_ * _ * _) = unitConjugation (spinGroup.toUnits g) a
  rw [map_mul, map_mul]
  change _ = (spinGroup.toUnits g : CliffordAlgebra ChevalleyQ55) * a *
      (↑((spinGroup.toUnits g)⁻¹) : CliffordAlgebra ChevalleyQ55)
  change
      (neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv
        (neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv
          (g : CliffordAlgebra ChevalleyQ55))) *
        (neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv
          (neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv a)) *
        (neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv
          (neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv
            ((g⁻¹ : ChevalleySpin55) : CliffordAlgebra ChevalleyQ55))) = _
  have hsymm (x : CliffordAlgebra ChevalleyQ55) :
      neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv
          (neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv x) = x := by
    exact neutralCliffordAlgEquiv_for_chevalleyQ.symm_apply_apply x
  rw [hsymm, hsymm, hsymm]
  rfl

theorem transportedSpinCliffordRingEquiv_eq_unitConjugation
    (g : ChevalleySpin55) :
    transportedSpinCliffordRingEquiv g =
      unitConjugationRingEquiv (spinGroup.toUnits g) := by
  ext a
  exact transportedSpinCliffordRingEquiv_eq_chevalley_unit_conjugation g a

theorem transportedSpinCliffordRingEquiv_spinor_readback
    (g : ChevalleySpin55) (a : CliffordAlgebra ChevalleyQ55) :
    neutralChevalleySpinorAlgEquiv
        (transportedSpinCliffordRingEquiv g a) =
      ((matrixSpinRepresentation g : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        neutralChevalleySpinorAlgEquiv a *
        (((matrixSpinRepresentation g)⁻¹ : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  rw [transportedSpinCliffordRingEquiv_eq_chevalley_unit_conjugation]
  simp only [unitConjugationRingEquiv_apply, unitConjugation, map_mul]
  have hunit :
      neutralChevalleySpinorAlgEquiv
          (spinGroup.toUnits g : CliffordAlgebra ChevalleyQ55) =
        ((matrixSpinRepresentation g : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
    change neutralChevalleySpinorAlgEquiv
        (g : CliffordAlgebra ChevalleyQ55) = _
    exact (matrixSpinRepresentation_val g).symm
  have hinv :
      neutralChevalleySpinorAlgEquiv
          (↑((spinGroup.toUnits g)⁻¹) : CliffordAlgebra ChevalleyQ55) =
        (((matrixSpinRepresentation g)⁻¹ : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
    have h := matrixSpinRepresentation_val (g⁻¹)
    have hi := matrixSpinRepresentation_inv g
    change neutralChevalleySpinorAlgEquiv
        ((g⁻¹ : ChevalleySpin55) : CliffordAlgebra ChevalleyQ55) = _
    rw [← h, hi]
  rw [hunit, hinv]

theorem transportedSpinCliffordRingEquiv_vector_readback
    (g : ChevalleySpin55) (x : Neutral55) :
    transportedSpinCliffordRingEquiv g (CliffordAlgebra.ι ChevalleyQ55 x) =
      CliffordAlgebra.ι ChevalleyQ55 (transportedSpinAction g x) := by
  change neutralCliffordAlgEquiv_for_chevalleyQ.symm
      (spinCliffordRingEquiv
        (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)
        (neutralCliffordAlgEquiv_for_chevalleyQ
          (CliffordAlgebra.ι ChevalleyQ55 x))) =
    CliffordAlgebra.ι ChevalleyQ55 (transportedSpinAction g x)
  rw [neutralCliffordAlgEquiv_for_chevalleyQ_ι,
    spinCliffordRingEquiv_vector_readback,
    neutralCliffordAlgEquiv_for_chevalleyQ_symm_ι]
  rfl

theorem transportedSpinCliffordRingEquiv_spinor_vector_covariance
    (g : ChevalleySpin55) (x : Neutral55) :
    ((matrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        neutralChevalleySpinorAlgEquiv
          (CliffordAlgebra.ι ChevalleyQ55 x) *
        (((matrixSpinRepresentation g)⁻¹ : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      neutralChevalleySpinorAlgEquiv
        (CliffordAlgebra.ι ChevalleyQ55 (transportedSpinAction g x)) := by
  rw [← transportedSpinCliffordRingEquiv_spinor_readback]
  rw [transportedSpinCliffordRingEquiv_vector_readback]

theorem transportedSpinCliffordRingEquiv_mul
    (g h : ChevalleySpin55) (x : CliffordAlgebra ChevalleyQ55) :
    transportedSpinCliffordRingEquiv (g * h) x =
      transportedSpinCliffordRingEquiv g
        (transportedSpinCliffordRingEquiv h x) := by
  apply neutralCliffordAlgEquiv_for_chevalleyQ.injective
  change neutralCliffordAlgEquiv_for_chevalleyQ
      (neutralCliffordAlgEquiv_for_chevalleyQ.symm
        (spinCliffordRingEquiv
          (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv (g * h))
          (neutralCliffordAlgEquiv_for_chevalleyQ x))) =
    neutralCliffordAlgEquiv_for_chevalleyQ
      (neutralCliffordAlgEquiv_for_chevalleyQ.symm
        (spinCliffordRingEquiv
          (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g)
          (neutralCliffordAlgEquiv_for_chevalleyQ
            (neutralCliffordAlgEquiv_for_chevalleyQ.symm
              (spinCliffordRingEquiv
                (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv h)
                (neutralCliffordAlgEquiv_for_chevalleyQ x))))))
  have htransport :
      InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv (g * h) =
          InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv g *
          InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv h := by
    change spinGroupTransportHom (g * h) =
      spinGroupTransportHom g * spinGroupTransportHom h
    exact map_mul spinGroupTransportHom g h
  simp only [neutralCliffordAlgEquiv_for_chevalleyQ.apply_symm_apply]
  rw [htransport, spinCliffordRingEquiv_mul]

noncomputable def transportedSpinCliffordRingEquivHom :
    ChevalleySpin55 →*
      (CliffordAlgebra ChevalleyQ55 ≃+* CliffordAlgebra ChevalleyQ55) where
  toFun := transportedSpinCliffordRingEquiv
  map_one' := by
    ext x
    change neutralCliffordAlgEquiv_for_chevalleyQ.symm
        (spinCliffordRingEquiv
          (InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.spinGroupTransportEquiv 1)
          (neutralCliffordAlgEquiv_for_chevalleyQ x)) = x
    simp [spinCliffordRingEquiv]
  map_mul' g h := by
    ext x
    exact transportedSpinCliffordRingEquiv_mul g h x

end InfoGeometry.Clifford.SplitClifford55SpinActionTransportBridge
