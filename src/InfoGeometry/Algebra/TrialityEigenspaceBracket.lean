import InfoGeometry.Algebra.TrialityG2
import InfoGeometry.Algebra.KantorTripleFiveGrading

namespace InfoGeometry.Algebra.TrialityG2

variable {Scalar Space : Type*} [CommRing Scalar] [LieRing Space] [LieAlgebra Scalar Space]

theorem eigenspace_bracket (triality : TrialityAutomorphism Scalar Space)
    (firstWeight secondWeight : Scalar) (first second : Space)
    (hfirst : triality.toEquiv first = firstWeight • first)
    (hsecond : triality.toEquiv second = secondWeight • second) :
    triality.toEquiv ⁅first, second⁆ = (firstWeight * secondWeight) • ⁅first, second⁆ := by
  rw [triality.toEquiv.map_lie, hfirst, hsecond, smul_lie, lie_smul, smul_smul]

theorem cubic_eigenspace_bracket_fixed (triality : TrialityAutomorphism Scalar Space)
    (phase : Scalar) (hphase : phase ^ 3 = 1) :
    eigenspaceBracketGradingStatement triality phase := by
  intro first second hfirst hsecond
  change triality.toEquiv ⁅first, second⁆ = ⁅first, second⁆
  rw [eigenspace_bracket triality phase (phase ^ 2) first second hfirst hsecond]
  rw [show phase * phase ^ 2 = phase ^ 3 by ring, hphase, one_smul]

end InfoGeometry.Algebra.TrialityG2

namespace InfoGeometry.Algebra.KantorTripleFiveGrading.KantorTripleSystem

variable {Scalar Space : Type*} [CommRing Scalar] [AddCommGroup Space] [Module Scalar Space]

theorem cubic_phase_invariant (system : KantorTripleSystem Scalar Space)
    (phase : Scalar) (hphase : phase ^ 3 = 1) (first second third : Space) :
    system.triple (phase • first) (phase • second) (phase • third) =
      system.triple first second third := by
  rw [system.triple_smul_left, system.triple_smul_middle, system.triple_smul_right,
    smul_smul, smul_smul, show phase * phase * phase = phase ^ 3 by ring,
    hphase, one_smul]

end InfoGeometry.Algebra.KantorTripleFiveGrading.KantorTripleSystem
