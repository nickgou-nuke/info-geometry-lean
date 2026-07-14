import InfoGeometry.Projective.Twistor.Incidence
import InfoGeometry.Projective.SplitCl44NullBoundary

/-!
# Penrose / split `Cl(4,4)` projective null bridge

This module packages the two inhabited projective-null quotients that the
repository already owns:

* Penrose twistor null rays;
* split `Cl(4,4)` causal-envelope null rays.

No identification of the two carriers is claimed.  The theorem only records
that they share the same quotient pattern and are both nonempty.
-/

namespace InfoGeometry.Projective.Twistor

/-- The Penrose and split `Cl(4,4)` projective-null spaces are both inhabited. -/
theorem penrose_and_splitCl44_projectiveNull_nonempty :
    Nonempty PenroseProjectiveNullTwistor ∧
      (∃ Z : InfoGeometry.Projective.SplitCl44NullBoundary.SplitCl44ProjectiveNullRep,
        Z.Z = InfoGeometry.Clifford.ClNN.headNullMinus 3 ∧
          InfoGeometry.Projective.SplitCl44NullBoundary.splitCl44NullMk Z =
            ProjectiveNullBoundaryDatum.nullMk
              InfoGeometry.Projective.SplitCl44NullBoundary.asProjectiveNullBoundaryDatum Z) := by
  constructor
  · exact penroseProjectiveNullTwistor_nonempty
  · refine ⟨⟨InfoGeometry.Clifford.ClNN.headNullMinus 3,
        InfoGeometry.Clifford.SplitCl44CausalEnvelope.splitCl44_headNullMinus_isotropic,
        ?_⟩, rfl, rfl⟩
    intro hzero
    have hzeroγ : InfoGeometry.Clifford.ClNN.gammaHeadNullMinus 3 = 0 := by
      rw [InfoGeometry.Clifford.ClNN.gammaHeadNullMinus, hzero]
      exact LinearMap.map_zero
        (CliffordAlgebra.ι (InfoGeometry.Clifford.ClNN.Quad 4))
    have hcontr :
        (0 : InfoGeometry.Clifford.SplitCl44CausalEnvelope.SplitCl44Algebra) = 1 := by
      simpa [hzeroγ] using
        (InfoGeometry.Clifford.SplitCl44CausalEnvelope.splitCl44_headNull_clifford_car)
    exact zero_ne_one hcontr

end InfoGeometry.Projective.Twistor
