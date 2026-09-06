import InfoGeometry.Topology.DelaunayPureBraidInvariant

/-!
# Delaunay Flip Interfaces

This file provides the clean boundary interfaces for the Delaunay flip word equivalence,
without altering the native quotient proofs.
-/

namespace InfoGeometry.Topology.Delaunay

/-- Notation for local word equivalence under witnessed inverse, commute, and pentagon moves. -/
infix:50 " ~ " => DelaunayEquiv

/--
The central quotient/factorization theorem: the Rohozhkin matrix evaluates identically
on equivalent Delaunay flip words.
-/
theorem rohozhkinMatrix_respects_flip_word_equiv {n : ℕ} {W₁ W₂ : DelaunayFlipWord n} :
    W₁ ~ W₂ → rohozhkinMatrix W₁ = rohozhkinMatrix W₂ :=
  rohozhkin_invariant_under_equiv

end InfoGeometry.Topology.Delaunay
