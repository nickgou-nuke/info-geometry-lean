import InfoGeometry.Algebra.CornerCompressionTraceCounterexample

/-!
# Global criterion for cyclic compression

Contract: for an arbitrary finite square matrix algebra over a commutative
coefficient ring and an idempotent P, the functional X ↦ trace (P X P)
is cyclic on the entire algebra exactly when P commutes with every matrix.
No commutativity of the matrix algebra is assumed.
Dependency: trace-pairing nondegeneracy → fixed-factor criterion → global criterion.
-/

namespace InfoGeometry.Algebra.CornerCompressionTraceCounterexample

variable {R ι : Type*} [CommRing R] [Fintype ι]

theorem compressed_trace_globally_cyclic_iff
    (P : Matrix ι ι R) (hP : P * P = P) :
    (∀ X Y : Matrix ι ι R,
      Matrix.trace (P * (X * Y) * P) = Matrix.trace (P * (Y * X) * P)) ↔
    ∀ Y : Matrix ι ι R, Y * P = P * Y := by
  constructor
  · intro h Y
    exact (compressed_trace_cyclic_iff_commutes P Y hP).mp (fun X => h X Y)
  · intro h X Y
    exact (compressed_trace_cyclic_iff_commutes P Y hP).mpr (h Y) X

end InfoGeometry.Algebra.CornerCompressionTraceCounterexample
