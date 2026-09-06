import Mathlib.Algebra.Algebra.Equiv
import InfoGeometry.Physics.SouriauLieThermodynamics
import InfoGeometry.Canonical.SouriauKKSContragredientBridge
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

/-!
# Souriau--Klein operator orbit geometry

This file is a thin algebraic SSOT connecting four structures already present
in the repository:

* symmetry generators represented by a `QuantumMomentMap`;
* multiplicative transport of observable sectors and their commutants;
* contragredient transport of dual states and invariance of the KKS form;
* five-graded bracket selection rules for KKS readouts.

The commutant in this file is the algebraic commutant of a subset of a monoid.
No analytic weak/operator-topology closure is asserted here; a von Neumann
algebra adapter may add that structure without changing these algebraic facts.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauKleinOperatorOrbitGeometry

open SouriauKKS
open InfoGeometry.Physics.SouriauLieThermodynamics
open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
open InfoGeometry.Canonical.SouriauKKSContragredientBridge

/-! ## Algebraic commutant transport -/

section Commutant

variable {B : Type*} [Monoid B]

/-- The algebraic commutant of a set of multiplicative observables. -/
def algebraicCommutant (S : Set B) : Set B :=
  {a | ∀ ⦃s : B⦄, s ∈ S → a * s = s * a}

/-- Transport a subset by a multiplicative equivalence. -/
def transportSet (e : B ≃* B) (S : Set B) : Set B :=
  e '' S

/-- Membership in a transported commutant is equivalent to membership of the
inverse-transported element in the original commutant. -/
theorem mem_algebraicCommutant_transport_iff
    (e : B ≃* B) (S : Set B) (a : B) :
    a ∈ algebraicCommutant (transportSet e S) ↔
      e.symm a ∈ algebraicCommutant S := by
  constructor
  · intro ha x hx
    have hcomm := ha ⟨x, hx, rfl⟩
    apply e.injective
    simpa using hcomm
  · intro ha y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hcomm := ha hx
    apply e.symm.injective
    simpa using hcomm

/-- Exact commutant transport under a multiplicative equivalence:
`e(M') = e(M)'`. -/
theorem commutant_transport
    (e : B ≃* B) (S : Set B) :
    transportSet e (algebraicCommutant S) =
      algebraicCommutant (transportSet e S) := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_algebraicCommutant_transport_iff e S (e x)).2 (by simpa using hx)
  · intro ha
    refine ⟨e.symm a, ?_, by simp⟩
    exact (mem_algebraicCommutant_transport_iff e S a).1 ha

end Commutant

/-! ## Moment-map transport -/

section MomentMap

variable {R g A : Type*}
variable [CommRing R] [LieRing g] [LieAlgebra R g]
variable [Ring A] [Algebra R A]

/-- Transport a quantum moment map by a bracket-preserving linear equivalence
of the symmetry Lie algebra and an algebra equivalence of observables. -/
def transportQuantumMomentMap
    (e : g ≃ₗ[R] g)
    (hLie : ∀ X Y : g, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (φ : A ≃ₐ[R] A)
    (J : QuantumMomentMap (R := R) (g := g) (A := A)) :
    QuantumMomentMap (R := R) (g := g) (A := A) where
  toLinearMap := φ.toLinearMap.comp (J.toLinearMap.comp e.symm.toLinearMap)
  lie_compat := by
    intro X Y
    have hLieInv : e.symm ⁅X, Y⁆ = ⁅e.symm X, e.symm Y⁆ := by
      apply e.injective
      rw [hLie]
      simp
    change φ (J.toLinearMap (e.symm ⁅X, Y⁆)) =
      φ (J.toLinearMap (e.symm X)) * φ (J.toLinearMap (e.symm Y)) -
        φ (J.toLinearMap (e.symm Y)) * φ (J.toLinearMap (e.symm X))
    rw [hLieInv, J.lie_compat]
    simp

/-- The transported moment map is equivariant by construction. -/
theorem momentMap_equivariant
    (e : g ≃ₗ[R] g)
    (hLie : ∀ X Y : g, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (φ : A ≃ₐ[R] A)
    (J : QuantumMomentMap (R := R) (g := g) (A := A))
    (X : g) :
    (transportQuantumMomentMap e hLie φ J).toLinearMap (e X) =
      φ (J.toLinearMap X) := by
  simp [transportQuantumMomentMap]

end MomentMap

/-! ## Coadjoint/KKS and symmetric-metric transport -/

section OrbitForms

variable {R g : Type*} [CommRing R] [LieRing g] [LieAlgebra R g]

/-- Repository-level KKS invariance, re-exported at the operator-orbit SSOT. -/
theorem kks_transport_invariant
    (e : g ≃ₗ[R] g)
    (hLie : ∀ X Y : g, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (μ : Module.Dual R g) (X Y : g) :
    kksForm (InfoGeometry.Canonical.SouriauContragredientPairing.contragredient e μ)
        (e X) (e Y) =
      kksForm μ X Y :=
  kksForm_contragredient_invariant e hLie μ X Y

/-- Pull a Souriau--Fisher covariance readout through a symmetry equivalence. -/
def transportedMetricValue
    (e : g ≃ₗ[R] g)
    (metric : SouriauState.SouriauFisherMetric R g)
    (X Y : g) : R :=
  metric.cov (e.symm X) (e.symm Y)

/-- The pulled-back symmetric metric readout is invariant on transported
vectors, by construction. -/
theorem metric_transport_invariant
    (e : g ≃ₗ[R] g)
    (metric : SouriauState.SouriauFisherMetric R g)
    (X Y : g) :
    transportedMetricValue e metric (e X) (e Y) = metric.cov X Y := by
  simp [transportedMetricValue]

end OrbitForms

/-! ## Five-grade KKS selection rules -/

section FiveGradeSelection

variable {L : Type*}
variable [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]

variable (G : FiveGrading L)

/-- `g₋₁ × g₊₁` KKS readouts see a grade-zero bracket component. -/
theorem grade_selection_kks_negOne_posOne
    (μ : Module.Dual ℝ L) {X Y : L}
    (hX : X ∈ G.gNegOne) (hY : Y ∈ G.gPosOne) :
    ∃ Z : L, Z ∈ G.gZero ∧ kksForm μ X Y = μ Z := by
  refine ⟨⁅X, Y⁆, G.negOne_posOne_mem_zero hX hY, ?_⟩
  rfl

/-- `g₋₂ × g₊₂` KKS readouts see a grade-zero bracket component. -/
theorem grade_selection_kks_negTwo_posTwo
    (μ : Module.Dual ℝ L) {X Y : L}
    (hX : X ∈ G.gNegTwo) (hY : Y ∈ G.gPosTwo) :
    ∃ Z : L, Z ∈ G.gZero ∧ kksForm μ X Y = μ Z := by
  refine ⟨⁅X, Y⁆, G.bracket_negTwo_posTwo X Y hX hY, ?_⟩
  rfl

/-- `g₊₁ × g₊₁` KKS readouts see a grade-`+2` bracket component. -/
theorem grade_selection_kks_posOne_posOne
    (μ : Module.Dual ℝ L) {X Y : L}
    (hX : X ∈ G.gPosOne) (hY : Y ∈ G.gPosOne) :
    ∃ Z : L, Z ∈ G.gPosTwo ∧ kksForm μ X Y = μ Z := by
  refine ⟨⁅X, Y⁆, G.posOne_posOne_mem_posTwo hX hY, ?_⟩
  rfl

/-- `g₋₁ × g₋₁` KKS readouts see a grade-`-2` bracket component. -/
theorem grade_selection_kks_negOne_negOne
    (μ : Module.Dual ℝ L) {X Y : L}
    (hX : X ∈ G.gNegOne) (hY : Y ∈ G.gNegOne) :
    ∃ Z : L, Z ∈ G.gNegTwo ∧ kksForm μ X Y = μ Z := by
  refine ⟨⁅X, Y⁆, G.negOne_negOne_mem_negTwo hX hY, ?_⟩
  rfl

/-- If the dual state annihilates the selected grade, the corresponding KKS
block vanishes.  This is the exact algebraic form of a grade-selection rule. -/
theorem grade_selection_kks_vanishes
    (μ : Module.Dual ℝ L)
    (P Q Target : Submodule ℝ L)
    (hBracket : ∀ {X Y : L}, X ∈ P → Y ∈ Q → ⁅X, Y⁆ ∈ Target)
    (hAnnihilates : ∀ Z : L, Z ∈ Target → μ Z = 0)
    {X Y : L} (hX : X ∈ P) (hY : Y ∈ Q) :
    kksForm μ X Y = 0 := by
  exact hAnnihilates ⁅X, Y⁆ (hBracket hX hY)

/-- A symmetric metric has a grade-selection zero whenever the corresponding
pair of grade submodules is declared orthogonal.  No unsupported orthogonality
is inferred merely from the Lie grading. -/
theorem grade_selection_metric
    (metric : SouriauState.SouriauFisherMetric ℝ L)
    (P Q : Submodule ℝ L)
    (hOrthogonal : ∀ {X Y : L}, X ∈ P → Y ∈ Q → metric.cov X Y = 0)
    {X Y : L} (hX : X ∈ P) (hY : Y ∈ Q) :
    metric.cov X Y = 0 :=
  hOrthogonal hX hY

end FiveGradeSelection

end InfoGeometry.Canonical.SouriauKleinOperatorOrbitGeometry
