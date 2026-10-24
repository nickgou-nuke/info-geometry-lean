/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability
import InfoGeometry.Core.PeirceDensityIntertwining
import InfoGeometry.OperatorAlgebra.TracialCARDensity

/-! # Algebraic reflection and tracial readouts for reflexive seeds

Use the existing ambient reflection unit, not the supported sum as a putative
ambient inverse. Fixed-vector statements concern arbitrary left modules, not
spinor descent or Dirac zero modes. Parity defects are exact annihilation
criteria, not physical CP violation. No positive or normalized state is assumed.
-/
namespace InfoGeometry.Canonical.ReflexiveParityReadout

open DeBruijnRotorAlternationCycle
open GrassmannianBundleCyclotomicOrientability

variable {A : Type*} [Ring A] {d B : A}

/-- Completion by the complementary identity does not change supported sandwiches. -/
theorem ambientReflection_on_support (h : IsDualSeedPair d B) (X : A)
    (hL : carrierSupport d B * X = X) (hR : X * carrierSupport d B = X) :
    unitOrbitMap X (ambientReflectionUnit h.d_sq h.B_sq h.dBd h.BdB) =
      transitionVelocity d B * X * transitionVelocity d B := by
  have h0L : zeroModeSupport d B * X = 0 := by
    rw [zeroModeSupport, sub_mul, one_mul, hL, sub_self]
  have h0R : X * zeroModeSupport d B = 0 := by
    rw [zeroModeSupport, mul_sub, mul_one, hR, sub_self]
  change (transitionVelocity d B + zeroModeSupport d B) * X *
    (transitionVelocity d B + zeroModeSupport d B) = _
  rw [add_mul, h0L, add_zero, mul_add,
    mul_assoc (transitionVelocity d B) X (zeroModeSupport d B), h0R, mul_zero, add_zero]

/-- The already constructed ambient unit exchanges the two nilpotent arrows. -/
theorem ambientReflection_swaps_seeds (h : IsDualSeedPair d B) :
    unitOrbitMap d (ambientReflectionUnit h.d_sq h.B_sq h.dBd h.BdB) = B ∧
    unitOrbitMap B (ambientReflectionUnit h.d_sq h.B_sq h.dBd h.BdB) = d := by
  obtain ⟨hdL, hdR, hBL, hBR⟩ := active_support_absorbs h.d_sq h.B_sq h.dBd h.BdB
  constructor
  · rw [ambientReflection_on_support h d hdL hdR]
    exact reflection_swaps_generators h.d_sq h.BdB
  · rw [ambientReflection_on_support h B hBL hBR]
    simpa only [transitionVelocity, add_comm] using reflection_swaps_generators h.B_sq h.dBd

/-- The ambient unit reverses the supported grading, including for proper support. -/
theorem ambientReflection_reverses_polarization (h : IsDualSeedPair d B) :
    unitOrbitMap (phasePolarization d B)
      (ambientReflectionUnit h.d_sq h.B_sq h.dBd h.BdB) = -phasePolarization d B := by
  have hL : carrierSupport d B * phasePolarization d B = phasePolarization d B := by
    simp only [carrierSupport, phasePolarization, add_mul, mul_sub, polePlus_idem h,
      poleMinus_idem h, polePlus_mul_poleMinus h, poleMinus_mul_polePlus h]
    abel
  have hR : phasePolarization d B * carrierSupport d B = phasePolarization d B := by
    simp only [carrierSupport, phasePolarization, sub_mul, mul_add, polePlus_idem h,
      poleMinus_idem h, polePlus_mul_poleMinus h, poleMinus_mul_polePlus h]
    abel
  rw [ambientReflection_on_support h _ hL hR]
  exact reflection_conjugates_grading h.d_sq h.B_sq h.dBd h.BdB

section Coefficients
variable {R : Type*} [CommRing R] [Algebra R A]

/-- Even and odd components for this particular algebraic reflection. -/
theorem odd_combination_conjugation (h : IsDualSeedPair d B) (α β : R) :
    unitOrbitMap (α • transitionVelocity d B + β • wheelGenerator d B)
      (ambientReflectionUnit h.d_sq h.B_sq h.dBd h.BdB) =
      α • transitionVelocity d B - β • wheelGenerator d B := by
  obtain ⟨hd, hB⟩ := ambientReflection_swaps_seeds h
  unfold unitOrbitMap homogeneousProj at hd hB ⊢
  simp only [transitionVelocity, wheelGenerator, mul_add, add_mul, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, hd, hB, smul_add, smul_sub]
  abel

/-- Exact defect, including coefficient torsion and degenerate seeds. -/
theorem odd_combination_defect (h : IsDualSeedPair d B) (α β : R) :
    unitOrbitMap (α • transitionVelocity d B + β • wheelGenerator d B)
      (ambientReflectionUnit h.d_sq h.B_sq h.dBd h.BdB) -
      (α • transitionVelocity d B + β • wheelGenerator d B) =
      -((2 * β) • wheelGenerator d B) := by
  rw [odd_combination_conjugation h, two_mul, add_smul]
  abel

/-- Nonzero coefficients alone do not imply a nonzero reflection defect. -/
theorem odd_combination_fixed_iff (h : IsDualSeedPair d B) (α β : R) :
    unitOrbitMap (α • transitionVelocity d B + β • wheelGenerator d B)
      (ambientReflectionUnit h.d_sq h.B_sq h.dBd h.BdB) =
      α • transitionVelocity d B + β • wheelGenerator d B ↔
      (2 * β) • wheelGenerator d B = 0 := by
  rw [← sub_eq_zero, odd_combination_defect h, neg_eq_zero]

/-- Polarization of the existing Peirce density; its weights are arbitrary scalars. -/
theorem polarization_mul_density (h : IsDualSeedPair d B) (a b : R) :
    phasePolarization d B * InfoGeometry.Core.PeirceDensityIntertwining.density d B b a =
      a • polePlus d B - b • poleMinus d B := by
  change (polePlus d B - poleMinus d B) * (b • poleMinus d B + a • polePlus d B) = _
  simp only [mul_add, sub_mul, mul_smul_comm, polePlus_idem h, poleMinus_idem h,
    polePlus_mul_poleMinus h, poleMinus_mul_polePlus h, sub_zero, zero_sub, smul_neg]
  abel

/-- Cyclicity supplies equality of the two support traces, not positivity or nonvanishing. -/
theorem tracial_polarization_density (h : IsDualSeedPair d B)
    (τ : InfoGeometry.NCG.TracialFunctional R A) (a b : R) :
    τ (phasePolarization d B * InfoGeometry.Core.PeirceDensityIntertwining.density d B b a) =
      (a - b) * τ (polePlus d B) := by
  have ht : τ (poleMinus d B) = τ (polePlus d B) := τ.cyclic B d
  rw [polarization_mul_density h, τ.map_sub, τ.map_smul, τ.map_smul, ht]
  exact (sub_mul a b (τ (polePlus d B))).symm

end Coefficients

section LeftModule
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- A pointwise reflection-fixed vector supported on the positive pole is zero. -/
theorem pure_positive_fixed_eq_zero (h : IsDualSeedPair d B) {v : M}
    (hfix : transitionVelocity d B • v = v) (hp : polePlus d B • v = v) : v = 0 := by
  have hb : B • v = v := by
    calc B • v = (transitionVelocity d B * polePlus d B) • v := by
          rw [velocity_mul_polePlus h]
      _ = v := by rw [mul_smul, hp, hfix]
  have hPB : polePlus d B * B = 0 := by
    simp only [polePlus, mul_assoc, h.B_sq, mul_zero]
  calc v = polePlus d B • v := hp.symm
    _ = polePlus d B • (B • v) := by rw [hb]
    _ = 0 := by rw [← mul_smul, hPB, zero_smul]

/-- The opposite pole has the same obstruction; no extra vanishing premise is needed. -/
theorem pure_negative_fixed_eq_zero (h : IsDualSeedPair d B) {v : M}
    (hfix : transitionVelocity d B • v = v) (hp : poleMinus d B • v = v) : v = 0 := by
  have hs : IsDualSeedPair B d := ⟨h.B_sq, h.d_sq, h.BdB, h.dBd⟩
  apply pure_positive_fixed_eq_zero hs _ hp
  simpa only [transitionVelocity, add_comm] using hfix

end LeftModule
end InfoGeometry.Canonical.ReflexiveParityReadout
