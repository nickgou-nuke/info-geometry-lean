import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms

namespace InfoGeometry.Canonical

/-!
## Compatibility surface for the former G₂ triality owner

The canonical owner is `SplitOctonionColorS3Automorphisms`.  This module keeps
only theorem-level names for clients of the old file; it introduces no second
coordinate map, no duplicate linear equivalence, and no proposition-valued
multiplicativity certificate.
-/

theorem g2_triality_order_three
    (x : StandardRationalSplitOctonion) :
    trialityColorCycle (trialityColorCycle (trialityColorCycle x)) = x := by
  have h := congrArg
    (fun e : StandardRationalSplitOctonion ≃ₗ[ℚ] StandardRationalSplitOctonion => e x)
    trialityColorCycle_order_three
  exact h

theorem g2_triality_map_mul
    (x y : StandardRationalSplitOctonion) :
    trialityColorCycle (splitOctonionMulQ x y) =
      splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y) :=
  trialityColorCycle_map_mul x y

theorem g2_triality_fixes_shared_axis
    {x : StandardRationalSplitOctonion}
    (hx : x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0 ∧
      x .k = 0 ∧ x .kl = 0) :
    trialityColorCycle x = x := by
  funext b
  cases b <;>
    simp [trialityColorCycle, colorCycleBasisEquiv, colorCycleBasis,
      colorCycleBasisInv, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
      hx.2.2.2.2.1, hx.2.2.2.2.2]

end InfoGeometry.Canonical
