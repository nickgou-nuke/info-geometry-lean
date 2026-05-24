import InfoGeometry.Projective.Twistor.Basic
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
      Nonempty InfoGeometry.Projective.SplitCl44NullBoundary.SplitCl44ProjectiveNullSpace := by
  constructor
  · exact penroseProjectiveNullTwistor_nonempty
  · exact InfoGeometry.Projective.SplitCl44NullBoundary.splitCl44ProjectiveNullBoundary_nonempty

end InfoGeometry.Projective.Twistor
