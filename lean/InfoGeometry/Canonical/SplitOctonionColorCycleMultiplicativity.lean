import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms

namespace InfoGeometry.Canonical

/-!
# Multiplicative colour symmetries

This file packages the already constructed rational linear equivalences.  The
carrier is the rational coordinate model, so this is deliberately a
non-associative algebra-automorphism witness rather than a Mathlib `AlgEquiv`.
It does not claim full `D₄` triality or a `G₂` Lie-group construction.
-/

structure SplitRationalOctonionAlgAut where
  toLinearEquiv : StandardRationalSplitOctonion ≃ₗ[ℚ]
    StandardRationalSplitOctonion
  map_one' :
    toLinearEquiv (Pi.single IntegralSplitBasis.one (1 : ℚ)) =
      Pi.single IntegralSplitBasis.one (1 : ℚ)
  map_mul' : ∀ x y,
    toLinearEquiv (splitOctonionMulQ x y) =
      splitOctonionMulQ (toLinearEquiv x) (toLinearEquiv y)

noncomputable def colorCycleAlgAut : SplitRationalOctonionAlgAut where
  toLinearEquiv := trialityColorCycle
  map_one' := trialityColorCycle_one_basis
  map_mul' := trialityColorCycle_map_mul

noncomputable def colorCycle : StandardRationalSplitOctonion ≃ₗ[ℚ]
    StandardRationalSplitOctonion :=
  trialityColorCycle

theorem colorCycleAlgAut_order_three (x : StandardRationalSplitOctonion) :
    colorCycleAlgAut.toLinearEquiv
        (colorCycleAlgAut.toLinearEquiv
          (colorCycleAlgAut.toLinearEquiv x)) = x := by
  have h := congrArg (fun e => e x) trialityColorCycle_order_three
  exact h

theorem colorCycle_order_three (x : StandardRationalSplitOctonion) :
    colorCycle (colorCycle (colorCycle x)) = x := by
  have h := congrArg (fun e => e x) trialityColorCycle_order_three
  simpa [colorCycle] using h

theorem colorCycle_fixes_sharedHyperbolicAxis
    {x : StandardRationalSplitOctonion}
    (h_axis : x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0 ∧
      x .k = 0 ∧ x .kl = 0) :
    colorCycle x = x := by
  funext b
  cases b <;>
    simp [colorCycle, trialityColorCycle, colorCycleBasisEquiv,
      colorCycleBasis, colorCycleBasisInv, h_axis.1, h_axis.2.1,
      h_axis.2.2.1, h_axis.2.2.2.1, h_axis.2.2.2.2.1,
      h_axis.2.2.2.2.2]

end InfoGeometry.Canonical
