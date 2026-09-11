import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.OperatorAlgebra.ZornBaseConservation

Owner-safe readback for the concrete split-octonion base coordinates.

This file packages the theorem-honest base conservation surface already supported
by `SplitOctonionMultiplication`.

Closed content:
- the pure-bosonic trace formula for `mulZ`;
- exact base-coordinate readback of `projectToBase (mulZ X Y)` on the pure-bosonic section;
- a conditional trace-multiplicativity theorem when the mixed diagonal term vanishes.

Open residue:
- pure-bosonicity alone does NOT imply `trZ (mulZ X Y) = trZ X * trZ Y`;
- no measure-theoretic or smooth-manifold theorem is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.ZornBaseConservation

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

abbrev IsPureBosonic :=
  InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.IsPureBosonic

/-- Exact trace readback on the pure bosonic section. -/
@[simp] theorem pureBosonic_trace_conservation_formula
    (X Y : SplitOct)
    (hX : IsPureBosonic X) (hY : IsPureBosonic Y) :
    trZ (mulZ X Y) = X.a * Y.a + X.b * Y.b :=
  trZ_mulZ_pureBosonic_formula X Y hX hY

/-- Exact base-coordinate readback on the pure bosonic section. -/
@[simp] theorem pureBosonic_global_base_conservation
    (X Y : SplitOct)
    (hX : IsPureBosonic X) (hY : IsPureBosonic Y) :
    (projectToBase (mulZ X Y)).trace = X.a * Y.a + X.b * Y.b ∧
      (projectToBase (mulZ X Y)).det = detZ X * detZ Y :=
  pureBosonic_projectToBase_mul_trace_det X Y hX hY

/--
On the pure bosonic section, trace multiplicativity holds only when the mixed
scalar term vanishes.
-/
theorem pureBosonic_trace_multiplicative_of_mixed_zero
    (X Y : SplitOct)
    (hX : IsPureBosonic X) (hY : IsPureBosonic Y)
    (hmix : X.a * Y.b + X.b * Y.a = 0) :
    trZ (mulZ X Y) = trZ X * trZ Y := by
  rw [pureBosonic_trace_conservation_formula X Y hX hY, trZ]
  calc
    X.a * Y.a + X.b * Y.b
        = X.a * Y.a + X.b * Y.b + (X.a * Y.b + X.b * Y.a) := by
            rw [hmix, add_zero]
    _ = (X.a + X.b) * (Y.a + Y.b) := by ring

end InfoGeometry.OperatorAlgebra.ZornBaseConservation
