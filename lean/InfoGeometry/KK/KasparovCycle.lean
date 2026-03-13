import InfoGeometry.Krein.Clifford
import InfoGeometry.Krein.Superalgebra
import InfoGeometry.Canonical.AnalyticalIndex
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Algebra.Lie.OfAssociative

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Canonical.AnalyticalIndex

/-- Endomorphism algebra on a real Krein-graded Hilbert carrier. -/
abbrev EndH (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] := H →L[ℝ] H

/-- Concrete compact-operator predicate on bounded real endomorphisms. -/
abbrev IsCompactEnd (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : EndH H) : Prop :=
  IsCompactOperator (A : H → H)

/--
Bounded Kasparov-cycle interface over a graded Krein module.
This is the structural 6A layer: no unbounded operators or functional calculus.
-/
structure KasparovCycle
    (A B H : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] where
  /-- Left representation of `A`. -/
  π : A →ₐ[ℝ] EndH H
  /-- Secondary representation of `B` (right-action refinement can be layered later). -/
  ρ : B →ₐ[ℝ] EndH H
  /-- Bounded odd phase / Fredholm operator. -/
  F : EndH H
  /-- Oddness with respect to the grading involution. -/
  F_odd : KreinGradedModule.IsOdd (H := H) F
  /-- Krein skew-adjointness of `F` (corresponds to Hilbert self-adjointness for odd operators). -/
  F_skewAdj : KreinSpace.IsKreinSkewAdjoint (H := H) F
  /-- `F² - 1` is compact. -/
  F_sq_one_compact : IsCompactEnd H (F * F - (1 : EndH H))
  /-- Graded commutator condition (even algebra reps => ordinary commutator). -/
  comm_compact : ∀ a : A, IsCompactEnd H (F * (π a) - (π a) * F)

section
variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]
variable (X : KasparovCycle A B H)

/--
The analytical index of a finite-dimensional Kasparov cycle.
The odd operator F acts as the Dirac operator for the index calculation.
-/
noncomputable def KasparovCycle.analyticalIndex [FiniteDimensional ℝ H] : ℤ :=
  InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
    X.F.toLinearMap
    (KreinGradedModule.gradeCLM (H := H)).toLinearMap

/-- Lemma `comm_compact_lie`. -/
lemma comm_compact_lie (a : A) : IsCompactEnd H ⁅X.F, X.π a⁆ := by
  simpa [Ring.lie_def] using X.comm_compact a

/-- Lemma `superComm_compact_of_even_rep`. -/
lemma superComm_compact_of_even_rep
    (hπ_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (X.π a))
    (a : A) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) X.F (X.π a)) := by
  have hsuper :
      KreinGradedModule.superComm (H := H) X.F (X.π a)
        = KreinGradedModule.comm (H := H) X.F (X.π a) :=
    KreinGradedModule.superComm_odd_even (H := H) X.F_odd (hπ_even a)
  rw [hsuper]
  simpa [KreinGradedModule.comm] using X.comm_compact a

/--
Theorem: If F is a spectral projection (F² = 1), the Kasparov index
is exactly the analytical index of the Dirac phase `F`.
-/
theorem index_bridge_spectral [FiniteDimensional ℝ H]
    (_hF : X.F * X.F = 1) :
    X.analyticalIndex = InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
      X.F.toLinearMap
      (KreinGradedModule.gradeCLM (H := H)).toLinearMap := rfl

end

end InfoGeometry.KK
