import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms
import InfoGeometry.Canonical.ZornMatrixVectorCarrierBridge

/-!
# Signed colour generators on the canonical rational Zorn carrier

This owner transports the already proved multiplicative colour cycle and
orientation-corrected reflection through the existing rational split-octonion
and Zorn coordinate equivalences.  It proves two concrete signed generators on
`ZornMatrix ℚ`; it does not identify them with the raw order-twelve hexagon
action, construct a Yang--Baxter operator, or assert an Artin braid/loop-group
representation.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCartanSignedColorZornLift

open InfoGeometry.Canonical

abbrev RationalSplitOctonion := StandardRationalSplitOctonion
abbrev RationalZorn := ZornMatrix ℚ

/-- The established rational Cartesian coordinates, read in the canonical
Zorn carrier rather than the older vector-matrix carrier. -/
noncomputable def rationalCanonicalZornEquiv :
    RationalSplitOctonion ≃ₗ[ℚ] RationalZorn :=
  zornVectorMatrixRationalEquiv.trans
    (zornMatrixVectorLinearEquiv (R := ℚ)).symm

theorem rationalCanonicalZornEquiv_map_mul
    (x y : RationalSplitOctonion) :
    rationalCanonicalZornEquiv (splitOctonionMulQ x y) =
      ZornMatrix.mul (rationalCanonicalZornEquiv x)
        (rationalCanonicalZornEquiv y) := by
  apply (zornMatrixVectorLinearEquiv (R := ℚ)).injective
  simpa [rationalCanonicalZornEquiv, zornMatrixToVector_mul] using
    zornVectorMatrixRationalEquiv_map_mul x y

/-- The order-three signed colour cycle transported to canonical Zorn
coordinates. -/
noncomputable def signedColorCycleZorn : RationalZorn ≃ₗ[ℚ] RationalZorn :=
  rationalCanonicalZornEquiv.symm.trans
    (trialityColorCycle.trans rationalCanonicalZornEquiv)

/-- The orientation-corrected colour reflection transported to canonical Zorn
coordinates. -/
noncomputable def signedColorReflectionZorn :
    RationalZorn ≃ₗ[ℚ] RationalZorn :=
  rationalCanonicalZornEquiv.symm.trans
    (colorReflection.trans rationalCanonicalZornEquiv)

theorem signedColorCycleZorn_intertwines (x : RationalSplitOctonion) :
    signedColorCycleZorn (rationalCanonicalZornEquiv x) =
      rationalCanonicalZornEquiv (trialityColorCycle x) := by
  simp [signedColorCycleZorn]

theorem signedColorReflectionZorn_intertwines (x : RationalSplitOctonion) :
    signedColorReflectionZorn (rationalCanonicalZornEquiv x) =
      rationalCanonicalZornEquiv (colorReflection x) := by
  simp [signedColorReflectionZorn]

theorem signedColorCycleZorn_map_mul (X Y : RationalZorn) :
    signedColorCycleZorn (ZornMatrix.mul X Y) =
      ZornMatrix.mul (signedColorCycleZorn X) (signedColorCycleZorn Y) := by
  have hinv : rationalCanonicalZornEquiv.symm (ZornMatrix.mul X Y) =
      splitOctonionMulQ (rationalCanonicalZornEquiv.symm X)
        (rationalCanonicalZornEquiv.symm Y) := by
    apply rationalCanonicalZornEquiv.injective
    simpa using (rationalCanonicalZornEquiv_map_mul
      (rationalCanonicalZornEquiv.symm X)
      (rationalCanonicalZornEquiv.symm Y)).symm
  simp only [signedColorCycleZorn, LinearEquiv.trans_apply]
  rw [hinv, trialityColorCycle_map_mul,
    rationalCanonicalZornEquiv_map_mul]

theorem signedColorReflectionZorn_map_mul (X Y : RationalZorn) :
    signedColorReflectionZorn (ZornMatrix.mul X Y) =
      ZornMatrix.mul (signedColorReflectionZorn X)
        (signedColorReflectionZorn Y) := by
  have hinv : rationalCanonicalZornEquiv.symm (ZornMatrix.mul X Y) =
      splitOctonionMulQ (rationalCanonicalZornEquiv.symm X)
        (rationalCanonicalZornEquiv.symm Y) := by
    apply rationalCanonicalZornEquiv.injective
    simpa using (rationalCanonicalZornEquiv_map_mul
      (rationalCanonicalZornEquiv.symm X)
      (rationalCanonicalZornEquiv.symm Y)).symm
  simp only [signedColorReflectionZorn, LinearEquiv.trans_apply]
  rw [hinv, colorReflection_map_mul,
    rationalCanonicalZornEquiv_map_mul]

theorem signedColorCycleZorn_order_three :
    signedColorCycleZorn.trans
        (signedColorCycleZorn.trans signedColorCycleZorn) =
      LinearEquiv.refl ℚ RationalZorn := by
  apply LinearEquiv.ext
  intro X
  have h := LinearEquiv.congr_fun trialityColorCycle_order_three
    (rationalCanonicalZornEquiv.symm X)
  have h' : trialityColorCycle
      (trialityColorCycle
        (trialityColorCycle (rationalCanonicalZornEquiv.symm X))) =
      rationalCanonicalZornEquiv.symm X := by
    simpa [LinearEquiv.trans_apply] using h
  simp only [signedColorCycleZorn, LinearEquiv.trans_apply,
    LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply]
  change rationalCanonicalZornEquiv
      (trialityColorCycle
        (trialityColorCycle
          (trialityColorCycle (rationalCanonicalZornEquiv.symm X)))) = X
  rw [h']
  exact rationalCanonicalZornEquiv.apply_symm_apply X

theorem signedColorReflectionZorn_sq :
    signedColorReflectionZorn.trans signedColorReflectionZorn =
      LinearEquiv.refl ℚ RationalZorn := by
  apply LinearEquiv.ext
  intro X
  have h := LinearEquiv.congr_fun colorReflection_sq
    (rationalCanonicalZornEquiv.symm X)
  have h' : colorReflection
      (colorReflection (rationalCanonicalZornEquiv.symm X)) =
      rationalCanonicalZornEquiv.symm X := by
    simpa [LinearEquiv.trans_apply] using h
  simp only [signedColorReflectionZorn, LinearEquiv.trans_apply,
    LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply]
  change rationalCanonicalZornEquiv
      (colorReflection
        (colorReflection (rationalCanonicalZornEquiv.symm X))) = X
  rw [h']
  exact rationalCanonicalZornEquiv.apply_symm_apply X

end InfoGeometry.Lie.SplitOctonionCartanSignedColorZornLift
