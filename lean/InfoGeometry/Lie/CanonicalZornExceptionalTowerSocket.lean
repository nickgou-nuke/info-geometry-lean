import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.Algebra.FiveGradedTKKSpec
import InfoGeometry.Lie.CanonicalZornDerivationLane
import InfoGeometry.Lie.RealSplitOctonionG2Classification

/-!
# Native Zorn derivations and the five-graded TKK socket

The repository already owns the concrete split-octonion derivation lane:
the canonical Zorn carrier, its derivation Lie subalgebra, the faithful
operator action, and the finite dimension/span readouts.  This file composes
that lane with the abstract five-graded TKK specification.

The TKK specification is intentionally a contract.  It is not a concrete
E₇(7) or E₈(8) construction, and this file does not introduce one.  A
concrete exceptional realization must supply the target specification and the
grade-zero Lie homomorphism in `ZornToFiveGradedTKKSocket`.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornExceptionalTowerSocket

/-- The native canonical Zorn carrier used by the derivation lane. -/
abbrev ZornCarrier := InfoGeometry.Canonical.ZornMatrix ℝ

/-- The concrete Lie algebra of Leibniz derivations of the Zorn carrier. -/
abbrev NativeDerivation :=
  InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations

/-- The already-existing faithful operator Lie lane on the native carrier. -/
noncomputable def nativeDerivationLane :
    InfoGeometry.Algebra.DerivationLieLane ℝ ZornCarrier :=
  InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivationLane

/-- The native derivation action is faithful. -/
theorem nativeDerivationLane_faithful :
    Function.Injective nativeDerivationLane.act :=
  nativeDerivationLane.faithful

/-- The native lane acts by evaluation of its derivation operator. -/
@[simp] theorem nativeDerivationLane_operatorAction
    (D : NativeDerivation) (X : ZornCarrier) :
    nativeDerivationLane.operatorAction D X = D.1 X :=
  InfoGeometry.Lie.CanonicalZornDerivation
    .canonicalZornDerivationLane_operatorAction D X

/-- The native split-octonion derivation lane has dimension 14. -/
theorem nativeDerivation_finrank :
    Module.finrank ℝ NativeDerivation = 14 :=
  InfoGeometry.Lie.RealSplitOctonionG2Classification
    .canonical_split_octonion_derivation_finrank

/-- The standard split-octonion derivations span the native derivation lane. -/
theorem nativeStandardDerivations_span_top :
    InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivationSpan = ⊤ :=
  InfoGeometry.Lie.RealSplitOctonionG2Classification
    .standard_split_octonion_derivations_span

/-- A typed socket from the native Zorn derivation algebra into a
five-graded TKK target.

The map is a genuine Mathlib Lie homomorphism.  The grade-zero condition
records that the native derivations land in the structure/degree-zero layer.
The faithfulness field is an explicit embedding obligation; it is not
inferred from the abstract TKK specification. -/
structure ZornToFiveGradedTKKSocket where
  target : InfoGeometry.Algebra.FiveGradedTKKSpec ℝ
  map : NativeDerivation →ₗ⁅ℝ⁆ target.lie.L
  image_in_zero :
    ∀ D : NativeDerivation,
      map D ∈ target.grade InfoGeometry.Algebra.TKKGrade.z0
  faithful : Function.Injective map

namespace ZornToFiveGradedTKKSocket

variable (S : ZornToFiveGradedTKKSocket)

/-- Lie-bracket preservation supplied by the bundled Mathlib Lie homomorphism. -/
theorem map_lie (D E : NativeDerivation) :
    S.map ⁅D, E⁆ = ⁅S.map D, S.map E⁆ :=
  S.map.map_lie D E

/-- The image of the native derivation lane lies in grade zero. -/
theorem map_mem_zero (D : NativeDerivation) :
    S.map D ∈ S.target.grade InfoGeometry.Algebra.TKKGrade.z0 :=
  S.image_in_zero D

/-- The supplied map is injective. -/
theorem map_injective : Function.Injective S.map :=
  S.faithful

end ZornToFiveGradedTKKSocket

end InfoGeometry.Lie.CanonicalZornExceptionalTowerSocket
