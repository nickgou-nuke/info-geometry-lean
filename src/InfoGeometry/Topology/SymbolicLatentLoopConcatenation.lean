import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentLoop
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction

namespace InfoGeometry.Topology

/-!
# Loop closure for canonical concatenation

This owner records only the endpoint consequence needed for based loops.  It
does not promote the path quotient to a fundamental group; that requires a
separate composition/well-definedness layer.
-/

theorem canonicalSymbolicConcatenation_isLoop
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start)
    (hbase : γ₀.start = γ₁.finish) :
    SymbolicLatentLoop (canonicalSymbolicConcatenation hend) := by
  change (canonicalSymbolicConcatenation hend).start =
    (canonicalSymbolicConcatenation hend).finish
  change (canonicalSymbolicLatentPathConcatenation hend).path.start =
    (canonicalSymbolicLatentPathConcatenation hend).path.finish
  rw [(canonicalSymbolicLatentPathConcatenation hend).start_eq_first_start,
    (canonicalSymbolicLatentPathConcatenation hend).finish_eq_second_finish]
  exact hbase

theorem canonicalSymbolicConcatenation_isBasedLoop
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    {x : X}
    (hstart : γ₀.start = x)
    (hend : γ₀.finish = γ₁.start)
    (hfinish : γ₁.finish = x) :
    SymbolicLatentLoop (canonicalSymbolicConcatenation hend) := by
  apply canonicalSymbolicConcatenation_isLoop hend
  exact hstart.trans hfinish.symm

end InfoGeometry.Topology
