import InfoGeometry.Clifford.Cl55RealSplitPinNullPairAction
import InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Twistor
open InfoGeometry.Twistor.ProjectiveNullIsometryIncidence
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
open scoped LinearAlgebra.Projectivization

noncomputable section

theorem n_pair_ne_zero (i : Fin 5) : n_pair i ≠ 0 := by
  intro h
  have hs := congrArg (fun x : V55 => x.2 i) h
  simp [n_pair, e_pos, f_neg] at hs

theorem nbar_pair_ne_zero (i : Fin 5) : nbar_pair i ≠ 0 := by
  intro h
  have hs := congrArg (fun x : V55 => x.2 i) h
  simp [nbar_pair, e_pos, f_neg] at hs

noncomputable def nPairProjective (i : Fin 5) : TwistorSpace Q55 :=
  twistorMk Q55 (n_pair i) (n_pair_ne_zero i) (n_pair_null i)

noncomputable def nbarPairProjective (i : Fin 5) : TwistorSpace Q55 :=
  twistorMk Q55 (nbar_pair i) (nbar_pair_ne_zero i) (nbar_pair_null i)

theorem realSplitPinNullAction_fNegRealPin_nPairProjective
    (i : Fin 5) :
    realSplitPinNullAction (fNegRealPin i) (nPairProjective i) =
      nbarPairProjective i := by
  apply Subtype.ext
  change projectiveIsometryMap
      (realSplitPinNativeOrthogonalAction (fNegRealPin i))
      (nPairProjective i).1 = (nbarPairProjective i).1
  change projectiveIsometryMap
      (realSplitPinNativeOrthogonalAction (fNegRealPin i))
      (Projectivization.mk ℝ (n_pair i) (n_pair_ne_zero i)) = _
  rw [projectiveIsometryMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  exact (realSplitPinNativeOrthogonalAction_fNegRealPin_n_pair i).symm

theorem realSplitPinNullAction_fNegRealPin_nbarPairProjective
    (i : Fin 5) :
    realSplitPinNullAction (fNegRealPin i) (nbarPairProjective i) =
      nPairProjective i := by
  apply Subtype.ext
  change projectiveIsometryMap
      (realSplitPinNativeOrthogonalAction (fNegRealPin i))
      (nbarPairProjective i).1 = (nPairProjective i).1
  change projectiveIsometryMap
      (realSplitPinNativeOrthogonalAction (fNegRealPin i))
      (Projectivization.mk ℝ (nbar_pair i) (nbar_pair_ne_zero i)) = _
  rw [projectiveIsometryMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  exact (realSplitPinNativeOrthogonalAction_fNegRealPin_nbar_pair i).symm

end

end InfoGeometry.Clifford.Clifford55
