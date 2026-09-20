import InfoGeometry.Exceptional.SplitOctonionG2FiveGrading
import InfoGeometry.Exceptional.TrialityContactCantor
import InfoGeometry.Algebra.KantorTripleFiveGrading
import InfoGeometry.KTheory.ConcreteFredholmIndex

namespace InfoGeometry.Exceptional.ContactSynthesisTests

open SplitOctonionG2FiveGrading

example : Module.finrank ℝ (gradeSpace 2) = 1 := contact_dimensions.2.2.2.2

example : gradeSpace 3 = ⊥ := gradeSpace_eq_bot 3 (by omega)

example : iSupIndep gradeSpace := gradeSpaces_independent

example : (⨆ degree : ℤ, gradeSpace degree) = ⊤ := gradeSpaces_span

example (first second : Carrier) (hfirst : first ∈ gradeSpace 1)
    (hsecond : second ∈ gradeSpace 2) : ⁅first, second⁆ = 0 :=
  grade_one_two_truncation hfirst hsecond

open InfoGeometry.KTheory.ConcreteFredholmIndex

example : Module.finrank ℝ (LinearMap.ker (D_plus 0)) = 1 :=
  massless_kernel_dimensions.1

example : Module.finrank ℝ (LinearMap.ker (D_plus 1)) = 0 :=
  (massive_kernel_dimensions 1 (by norm_num)).1

example (mass : ℝ) : fredholm_index mass = 0 := fredholm_index_eq_zero mass

#print axioms contact_dimensions
#print axioms gradeSpaces_independent
#print axioms gradeSpaces_span
#print axioms polarized_triple_closed
#print axioms TrialityContactCantor.range_reynolds_eq_fixedLieSubalgebra
#print axioms InfoGeometry.Algebra.KantorTripleFiveGrading.KantorTripleSystem.triple_cubic_phase_invariant
#print axioms fredholm_index_eq_chiral_kernel_difference

end InfoGeometry.Exceptional.ContactSynthesisTests
