import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

/-!
# Critical-line / local Lee--Yang circle equivalence

For a finite prime chain, a shifted local fugacity has squared norm one
exactly on the critical line.  This is a pointwise real/complex calculation;
it is not a statement about roots of the partition polynomial.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangCriticalCircleNative

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

theorem shiftedPrimeFugacity_onLeeYangCircle_iff_criticalLine
    {n : ℕ} (C : PrimeFerromagneticChain n) (s : ℂ) (i : Fin n) :
    OnLeeYangCircle (C.shiftedPrimeFugacity s i) ↔ OnCriticalLine s := by
  constructor
  · intro hcircle
    unfold OnLeeYangCircle at hcircle
    unfold PrimeFerromagneticChain.shiftedPrimeFugacity
      PrimeFerromagneticChain.shiftedRiemannParameter at hcircle
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp] at hcircle
    have hexp : Real.exp
        (-(s - (1 / 2 : ℂ)) * (C.siteEnergy i : ℂ)).re = 1 := by
      have hnonneg : 0 ≤ Real.exp
          (-(s - (1 / 2 : ℂ)) * (C.siteEnergy i : ℂ)).re :=
        Real.exp_nonneg _
      nlinarith
    have hre :
        (-(s - (1 / 2 : ℂ)) * (C.siteEnergy i : ℂ)).re = 0 :=
      (Real.exp_eq_one_iff _).mp hexp
    unfold OnCriticalLine
    have henergy : 0 < C.siteEnergy i := C.siteEnergy_pos i
    simp [Complex.mul_re] at hre
    rcases hre with hre | hzero
    · linarith
    · exfalso
      linarith
  · intro hs
    unfold OnLeeYangCircle
    exact C.shiftedPrimeFugacity_normSq_of_criticalLine s hs i

end InfoGeometry.Canonical.PrimeLeeYangCriticalCircleNative
