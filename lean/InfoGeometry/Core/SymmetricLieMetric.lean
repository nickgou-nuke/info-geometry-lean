import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Symmetric Lie Metric Owner Surface

Stable owner surface for Cartan-form-based odd/even metric obligations on a
`SymmetricLieAlgebra`.

This module intentionally stays in `Core` and does not carry Yang-Mills bridge
interpretation.
-/

namespace InfoGeometry.Core

namespace SymmetricLieAlgebra

variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]

/--
Stable owner package for odd/even sign obligations of the Cartan form on a
symmetric pair.
-/
structure CartanOddMetricData where
  S : SymmetricLieAlgebra L
  signature : CartanSignature S

/-- Cartan-form quadratic value used as the information-mass observable. -/
noncomputable def informationMassSq (M : CartanOddMetricData (L := L)) (x : L) : ℝ :=
  M.S.cartanForm x x

/-- Restricted odd-sector mass observable. -/
noncomputable def oddInformationMassSq (M : CartanOddMetricData (L := L))
    (x : M.S.oddSubmodule) : ℝ :=
  informationMassSq (M := M) x

/-- Restricted even-sector quadratic form observable. -/
noncomputable def evenInformationMassSq (M : CartanOddMetricData (L := L))
    (x : M.S.evenLieSubalgebra) : ℝ :=
  informationMassSq (M := M) x

theorem informationMassSq_nonneg_of_mem_odd
    (M : CartanOddMetricData (L := L)) {x : L}
    (hx : x ∈ M.S.oddSubmodule) :
    0 ≤ informationMassSq (M := M) x := by
  simpa [informationMassSq] using M.signature.nonneg_on_odd x hx

theorem informationMassSq_nonpos_of_mem_even
    (M : CartanOddMetricData (L := L)) {x : L}
    (hx : x ∈ M.S.evenLieSubalgebra) :
    informationMassSq (M := M) x ≤ 0 := by
  simpa [informationMassSq] using M.signature.nonpos_on_even x hx

theorem oddInformationMassSq_nonneg
    (M : CartanOddMetricData (L := L))
    (x : M.S.oddSubmodule) :
    0 ≤ oddInformationMassSq (M := M) x := by
  exact informationMassSq_nonneg_of_mem_odd (M := M) x.property

theorem evenInformationMassSq_nonpos
    (M : CartanOddMetricData (L := L))
    (x : M.S.evenLieSubalgebra) :
    evenInformationMassSq (M := M) x ≤ 0 := by
  exact informationMassSq_nonpos_of_mem_even (M := M) x.property

end SymmetricLieAlgebra

end InfoGeometry.Core
