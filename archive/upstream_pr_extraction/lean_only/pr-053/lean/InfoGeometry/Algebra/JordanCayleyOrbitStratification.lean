import InfoGeometry.Algebra.JordanCayleyInversionOsQ

/-!
# Coordinate stratification for the split-octonionic `J₂` packet

This module gives a theorem-safe three-way case split for the concrete
`Herm2x2OsQ` determinant packet:

* zero coordinate packet;
* nonzero null packet (`det = 0`);
* generic packet (`det ≠ 0`).

It is a predicate classification only.  It does **not** prove an orbit
classification under `SL(2,O_s)`, `Pin(5,5)`, `O(5,5)`, a quotient by
`{I,-I}`, a Klein-bottle closure theorem, a CCC theorem, or any stabilizer
completeness result.
-/

namespace InfoGeometry.Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ

open InfoGeometry.Algebra.SplitOctonionQ

/-- The zero coordinate packet. -/
def IsZero (X : Herm2x2OsQ) : Prop :=
  X.xp = 0 ∧ X.xm = 0 ∧ X.z = ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A nonzero determinant-null coordinate packet. -/
def IsNull (X : Herm2x2OsQ) : Prop :=
  ¬ IsZero X ∧ X.det = 0

/-- A determinant-nonzero coordinate packet. -/
def IsGeneric (X : Herm2x2OsQ) : Prop :=
  X.det ≠ 0

/-- Three-way coordinate stratification by zero-ness and determinant. -/
inductive Stratum (X : Herm2x2OsQ) : Prop where
  | zero : IsZero X → Stratum X
  | null : IsNull X → Stratum X
  | generic : IsGeneric X → Stratum X

/-- Every coordinate packet lies in one of the three predicate strata. -/
theorem stratum_exhaustive (X : Herm2x2OsQ) : Stratum X := by
  by_cases hzero : IsZero X
  · exact Stratum.zero hzero
  · by_cases hdet : X.det = 0
    · exact Stratum.null ⟨hzero, hdet⟩
    · exact Stratum.generic hdet

/-- Null packets are exactly nonzero packets on the determinant-null locus. -/
theorem isNull_iff (X : Herm2x2OsQ) :
    IsNull X ↔ ¬ IsZero X ∧ X.det = 0 :=
  Iff.rfl

/-- Generic packets are exactly determinant-nonzero packets. -/
theorem isGeneric_iff (X : Herm2x2OsQ) :
    IsGeneric X ↔ X.det ≠ 0 :=
  Iff.rfl

/-- The zero coordinate packet has zero determinant. -/
theorem det_eq_zero_of_isZero (X : Herm2x2OsQ) (h : IsZero X) : X.det = 0 := by
  rcases h with ⟨hxp, hxm, hz⟩
  dsimp [det]
  rw [hxp, hxm, hz]
  simp [SplitO.norm]

/-- Therefore zero packets are never generic. -/
theorem not_isGeneric_of_isZero (X : Herm2x2OsQ) (h : IsZero X) :
    ¬ IsGeneric X := by
  intro hg
  exact hg (det_eq_zero_of_isZero X h)

/-- Null packets are never generic. -/
theorem not_isGeneric_of_isNull (X : Herm2x2OsQ) (h : IsNull X) :
    ¬ IsGeneric X := by
  intro hg
  exact hg h.2

/-- On the null stratum, the trace-reversal diagonal packet vanishes. -/
theorem mulTraceReversal_vanishes_of_isNull (X : Herm2x2OsQ) (h : IsNull X) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 :=
  on_klein_quadric X h.2

end InfoGeometry.Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ
