import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Lie.RealSplitOctonionG2Classification

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionAssociatorG2Capstone

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation

abbrev SplitOct := CanonicalZorn
abbrev Deriv := canonicalZornDerivations

/-- The canonical split-octonion associator. -/
def associator (x y z : SplitOct) : SplitOct :=
  (x * y) * z - x * (y * z)

/-- The commutator in the nonassociative split-octonion algebra. -/
def commutator (x y : SplitOct) : SplitOct :=
  x * y - y * x

/--
Schafer--Baez normal form for the canonical standard derivation:

`D_{x,y}(z) = [[x,y],z] - 3 (x,y,z)`.

This is the exact finite statement that the associator defect is absorbed into
the standard derivation operator.
-/
theorem standardDerivation_eq_commutator_sub_three_associator
    (x y z : SplitOct) :
    directCanonicalStanDerMap x y z =
      commutator (commutator x y) z - 3 • associator x y z := by
  simpa [commutator, associator, sub_eq_add_neg, add_assoc] using
    directCanonicalStanDerMap_apply_normal_form x y z

/-- Every canonical standard operator is a genuine split-octonion derivation. -/
theorem standardDerivation_isDerivation (x y : SplitOct) :
    IsDerivation (directCanonicalStanDerMap x y) := by
  exact (canonicalStandardDerivationOfCanonical x y).property

/-- The standard derivation packaged in the native canonical derivation Lie algebra. -/
noncomputable def standardDerivation (x y : SplitOct) : Deriv :=
  canonicalStandardDerivationOfCanonical x y

/-- The native canonical split-octonion derivation space has dimension fourteen. -/
theorem derivation_finrank :
    Module.finrank ℝ Deriv = 14 :=
  canonical_derivation_finrank

/--
Every canonical split-octonion derivation belongs to the linear span of the
standard Schafer--Baez derivations.
-/
theorem every_derivation_mem_standard_span (D : Deriv) :
    D ∈ standardDerivationSpan := by
  rw [standardDerivations_span_top]
  exact Submodule.mem_top

/-- The standard inner derivations span the entire native derivation algebra. -/
theorem standardDerivationSpan_eq_top :
    standardDerivationSpan = (⊤ : Submodule ℝ Deriv) :=
  standardDerivations_span_top

/--
Canonical identification packet: the full real split-octonion derivation lane
is fourteen-dimensional and generated linearly by standard inner derivations.
-/
theorem associator_absorption_g2_packet :
    Module.finrank ℝ Deriv = 14 ∧
      standardDerivationSpan = (⊤ : Submodule ℝ Deriv) := by
  exact ⟨derivation_finrank, standardDerivationSpan_eq_top⟩

end InfoGeometry.Canonical.SplitOctonionAssociatorG2Capstone
