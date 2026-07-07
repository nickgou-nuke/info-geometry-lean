import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.FiniteSUSYBlocks
import InfoGeometry.Algebra.AnyonFiniteSpinBraid.AnyonLocalDefectSteps
import InfoGeometry.Algebra.AnyonFiniteSpinBraid.AnyonHomologicalStability
import InfoGeometry.Algebra.AnyonFiniteSpinBraid.AnyonCoxeterQuotient

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

open Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.FiniteSUSY

/-- Consolidated finite spin/SUSY anyon braid packet. -/
theorem finite_spin_anyon_braid_packet :
    canonicalDefectSteps.create = J_plus ∧
      canonicalDefectSteps.annihilate = J_minus ∧
        witten_index_trace = 0 ∧
          canonicalHomologicalBraidStability.unpairedLeak = 0 ∧
          CoxeterDQuotientCertificate.gapWitness.D4_order = 192 ∧
          CoxeterDQuotientCertificate.gapWitness.D5_order = 1920 :=
  ⟨canonical_create_eq, canonical_annihilate_eq,
    witten_index_trace_vanishes, canonical_no_unpaired_leak,
    CoxeterDQuotientCertificate.D4_order_readout,
    CoxeterDQuotientCertificate.D5_order_readout⟩

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
