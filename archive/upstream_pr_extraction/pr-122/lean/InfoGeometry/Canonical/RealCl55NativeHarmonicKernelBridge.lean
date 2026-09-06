import Mathlib
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

/-!
# Harmonic-kernel readback for the native finite Hodge packet

The concrete master packet has `D_H² = 3 I`, hence its native Hodge
Laplacian has no nonzero harmonic vectors.  This is a finite-carrier theorem,
not a statement about a boundary, a completed complex, or an analytic index.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeHarmonicKernelBridge

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

theorem nativeHodgeLaplacian_apply_eq_zero_iff
    (x : NativeSpinorCarrier) :
    nativeHodgeLaplacian x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hdirac : nativeHodgeDirac (nativeHodgeDirac x) = 0 := by
      simpa [nativeHodgeLaplacian, ContinuousLinearMap.comp_apply] using hx
    have hinner : nativeHodgeDirac x = 0 :=
      nativeHodgeDirac_apply_eq_zero_iff _ |>.mp hdirac
    exact nativeHodgeDirac_apply_eq_zero_iff _ |>.mp hinner
  · intro hx
    simp [hx]

theorem nativeHodgeLaplacian_no_harmonic_vectors :
    ∀ x : NativeSpinorCarrier, nativeHodgeLaplacian x = 0 → x = 0 := by
  intro x hx
  exact nativeHodgeLaplacian_apply_eq_zero_iff x |>.mp hx

theorem nativeChiralLaplacianPlus_apply_eq_zero_iff
    (x : NativeSpinorCarrier) :
    nativeChiralLaplacianPlus x = 0 ↔
      nativeChiralProjectorPlus x = 0 := by
  rw [nativeChiralLaplacianPlus_eq_three_projector]
  constructor
  · intro hx
    have hsmul : (3 : ℝ) • nativeChiralProjectorPlus x = 0 := by
      simpa using hx
    rcases smul_eq_zero.mp hsmul with hzero | hzero
    · norm_num at hzero
    · exact hzero
  · intro hx
    simp [hx]

theorem nativeChiralLaplacianMinus_apply_eq_zero_iff
    (x : NativeSpinorCarrier) :
    nativeChiralLaplacianMinus x = 0 ↔
      nativeChiralProjectorMinus x = 0 := by
  rw [nativeChiralLaplacianMinus_eq_three_projector]
  constructor
  · intro hx
    have hsmul : (3 : ℝ) • nativeChiralProjectorMinus x = 0 := by
      simpa using hx
    rcases smul_eq_zero.mp hsmul with hzero | hzero
    · norm_num at hzero
    · exact hzero
  · intro hx
    simp [hx]

end InfoGeometry.Canonical.RealCl55NativeHarmonicKernelBridge
