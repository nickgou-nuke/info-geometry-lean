/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.TomitaConjugationCPTInvariant

/-!
# Audit Module for Section 145: Tomita-Takesaki Modular Conjugation and CPT Invariance
Target: `InfoGeometry/Superalgebra/TomitaConjugationCPTInvariantAudit.lean`

Provides concrete integer (`ℤ`) evaluations and checks by `decide`.
-/

namespace InfoGeometry.Superalgebra.TomitaCPTAudit

open InfoGeometry.Superalgebra.TomitaCPT

/-- Concrete integer verification of `J (paraSymplecticK0) = neg paraSymplecticK0`. -/
theorem audit_cpt_time_inversion_int :
    SplitOctonion.J (SplitOctonion.paraSymplecticK0 : SplitOctonion ℤ) =
      SplitOctonion.neg (SplitOctonion.paraSymplecticK0 : SplitOctonion ℤ) := by decide

/-- Concrete integer verification of composition norm identity `X * J(X) = intervalNorm(X) • 1`. -/
theorem audit_composition_norm_identity_int :
    SplitOctonion.mul canonicalSplitOctonionInt
      (SplitOctonion.modularConjugationJ canonicalSplitOctonionInt) =
    SplitOctonion.scale (15 : ℤ) SplitOctonion.one := by decide

/-- Concrete integer verification of anti-automorphism `J(X * Y) = J(Y) * J(X)`. -/
theorem audit_anti_automorphism_int :
    SplitOctonion.modularConjugationJ
      (SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int) =
    SplitOctonion.mul
      (SplitOctonion.modularConjugationJ octonionBasisU2Int)
      (SplitOctonion.modularConjugationJ octonionBasisU1Int) := by decide

/-- Concrete integer verification of Dirac vector reversal `J(H(d)) = -H(d)`. -/
theorem audit_dirac_vector_reversal_int :
    SplitOctonion.modularConjugationJ (SplitOctonion.diracVecH canonicalColorVec3Int) =
      SplitOctonion.neg (SplitOctonion.diracVecH canonicalColorVec3Int) := by decide

/-- Concrete integer non-commutativity of split-octonion multiplication. -/
theorem audit_split_octonion_noncommutative_int :
    SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int ≠
      SplitOctonion.mul octonionBasisU2Int octonionBasisU1Int := by decide

end InfoGeometry.Superalgebra.TomitaCPTAudit
