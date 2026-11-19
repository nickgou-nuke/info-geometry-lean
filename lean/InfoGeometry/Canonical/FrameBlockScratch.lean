import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Canonical.ThermofieldWittSoldering
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.FrameBlockScratch

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame
open InfoGeometry.Canonical.ThermofieldWittSoldering
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

abbrev CanonicalZorn := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

def circularZornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4 :=
  coordinateEquiv.trans wittSolderingEquiv.symm

private lemma frameBasis_apply_eq (a b : Fin 4) :
    frameBasis a b = if b = a then 1 else 0 := by
  simp [frameBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem frame_block_negative (i : Fin 4) :
    circularZornToKreinFrame (frame (Fin.addNat i 4)) = minusFrame i := by
  apply wittSoldering_injective
  have hleft : wittSoldering (circularZornToKreinFrame (frame (Fin.addNat i 4))) =
      coordinateEquiv (frame (Fin.addNat i 4)) := by
    change wittSolderingEquiv (wittSolderingEquiv.symm
      (coordinateEquiv (frame (Fin.addNat i 4)))) = _
    exact wittSolderingEquiv.apply_symm_apply _
  rw [hleft, coordinateEquiv_apply_frame]
  change Pi.single (Fin.addNat i 4) 1 =
    wittSoldering (to_doubled 0 (frameBasis i) : DoubledSpace V4)
  funext j
  rw [wittSoldering_to_doubled_apply]
  by_cases hj : j.val < 4
  · simp only [hj, ↓reduceDIte, Pi.single_apply]
    split_ifs with h
    · exfalso
      have hv := congrArg Fin.val h
      simp only [Fin.val_addNat] at hv
      omega
    · rfl
  · have hjLower : 4 ≤ j.val := Nat.le_of_not_gt hj
    let j' : Fin 4 := ⟨j.val - 4, by omega⟩
    have hcond : j' = i ↔ j = Fin.addNat i 4 := by
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simp only [j'] at hv
        apply Fin.ext
        simp only [Fin.val_addNat]
        omega
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp only [Fin.val_addNat] at hv
        change j.val - 4 = i.val
        omega
    simp only [hj, ↓reduceDIte, frameBasis_apply_eq]
    by_cases h : (⟨j.val - 4, by omega⟩ : Fin 4) = i
    · have h' := hcond.mp h
      simp [h']
    · have h' : j ≠ Fin.addNat i 4 := fun heq => h (hcond.mpr heq)
      simp [h, h']

end InfoGeometry.Canonical.FrameBlockScratch
