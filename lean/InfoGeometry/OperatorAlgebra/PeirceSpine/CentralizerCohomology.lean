import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Additive cohomology of the centralizer differential

Cycles and boundaries are defined using the kernel and range of the actual
graded derivation restricted to the V-centralizer. Their quotient is an
additive cohomology group; no manifold or de Rham comparison is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)

def centralizerCycles (A C : B) : AddSubgroup (metricCentralizer P A C) :=
  (centralizerDifferentialHom hP A C).ker

theorem centralizer_boundaries_are_cycles (A C : B) :
    (centralizerDifferentialHom hP A C).range ≤ centralizerCycles hP A C := by
  exact (AddMonoidHom.range_le_ker_iff _ _).2
    (centralizerDifferentialHom_comp_self hP A C)

/-- Boundaries viewed as a subgroup of cycles. -/
def centralizerBoundaries (A C : B) : AddSubgroup (centralizerCycles hP A C) :=
  (centralizerDifferentialHom hP A C).range.comap
    (centralizerCycles hP A C).subtype

/-- The additive group of cycles modulo boundaries of the square-zero map. -/
def CentralizerCohomology (A C : B) :=
  (centralizerCycles hP A C) ⧸ centralizerBoundaries hP A C

noncomputable instance (A C : B) : AddCommGroup (CentralizerCohomology hP A C) :=
  inferInstanceAs (AddCommGroup
    ((centralizerCycles hP A C) ⧸ centralizerBoundaries hP A C))

end InfoGeometry.OperatorAlgebra.PeirceSpine
