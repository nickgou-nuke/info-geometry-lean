/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.SplitOctonionManivelCompositionBridge
import InfoGeometry.Canonical.SplitOctonionConjugation

/-!
# Split-octonion composition norm and null-factor identities

This owner records the algebraic statements that are actually available for
the real split-octonion carrier. It does not identify these identities with a
projective Hopf fibration.
-/

namespace InfoGeometry.Canonical.HopfTest

open SplitOctonion InfoGeometry.Algebra.SplitOctonionManivelBridge
open InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge

/-- The split-octonion quadratic norm is multiplicative on the native
nonassociative composition algebra. -/
theorem split_octonion_composition_norm (x y : SplitOctonion) :
    normSQ (x * y) = normSQ x * normSQ y := by
  exact splitOctonionCompositionAlgebra.q_mul x y

/-- Split conjugation gives the quadratic norm in both multiplication
orders; no associative rearrangement of split-octonion factors is assumed. -/
theorem split_octonion_two_sided_norm (x : SplitOctonion) :
    splitConj x * x = (normSQ x) • (1 : SplitOctonion) ∧
    x * splitConj x = (normSQ x) • (1 : SplitOctonion) := by
  exact ⟨splitConj_mul_self x, self_mul_splitConj x⟩

/-- Nonzero zero-divisor factors in the split composition algebra are null for
the split quadratic norm. -/
theorem split_octonion_zero_divisors_are_null
    (x y : SplitOctonion) (hxy : x * y = 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    normSQ x = 0 ∧ normSQ y = 0 := by
  exact zero_divisor_isotropic_splitOctonion x y hxy hx hy

/-- The split quadratic null locus is carried exactly to the canonical Zorn
determinant cone by the repository's linear carrier equivalence. -/
theorem split_octonion_null_norm_iff_zorn_determinant (x : SplitOctonion) :
    normSQ x = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (splitOctonionCanonicalZornEquiv x) = 0 := by
  exact (isIsotropic_iff_normSQ x).symm.trans (isIsotropic_iff_detZ x)

end InfoGeometry.Canonical.HopfTest
