import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# Native observable Poisson and metriplectic algebra

This file reconstructs the observable-level algebra behind the finite bipolar
GENERIC model. Coordinate derivatives are represented by Mathlib's native
`Derivation ℝ A A`, rather than by raw functions accompanied by duplicated
additivity and Leibniz axioms.

A frame contains three derivations `(Dη,Dθ,Da)`. Only `Dθ` and `Da` must commute
for the constant bivector

`Π = ∂θ ∧ ∂a`

to satisfy Jacobi. The dissipative lane is the rank-one symmetric biderivation

`(F,G)_M = Dη(F) Dη(G)`.

Their sum is a metriplectic biderivation, not a Poisson bracket: it is neither
skew nor symmetric in general. Under the two mutual degeneracy conditions, the
single generator `H+S` yields energy conservation and entropy production.

The final section identifies the covector contraction of the already-owned
three-coordinate reversible operator with the same coordinate bivector.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra

variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- Three native coordinate derivations. Jacobi for the chosen constant
Poisson bivector requires only commutation of the `θ` and auxiliary lanes. -/
structure DerivationFrame (A : Type*) [CommRing A] [Algebra ℝ A] where
  Deta : Derivation ℝ A A
  Dtheta : Derivation ℝ A A
  Da : Derivation ℝ A A
  commute_theta_a : ∀ F : A, Dtheta (Da F) = Da (Dtheta F)

/-- Multiplicative Leibniz rule in ordinary ring notation. -/
theorem nativeDerivation_mul (δ : Derivation ℝ A A) (F G : A) :
    δ (F * G) = δ F * G + F * δ G := by
  rw [δ.leibniz]
  simp [Algebra.smul_def]
  ring

/-- Additive rule in ordinary notation. -/
theorem nativeDerivation_add (δ : Derivation ℝ A A) (F G : A) :
    δ (F + G) = δ F + δ G :=
  δ.map_add F G

/-- Subtractive rule in ordinary notation. -/
theorem nativeDerivation_sub (δ : Derivation ℝ A A) (F G : A) :
    δ (F - G) = δ F - δ G :=
  δ.toLinearMap.map_sub F G

/-- Constant Poisson bracket associated with `∂θ ∧ ∂a`. -/
def poissonBracket (D : DerivationFrame A) (F G : A) : A :=
  D.Dtheta F * D.Da G - D.Da F * D.Dtheta G

/-- Skew-symmetry of the Poisson bracket. -/
theorem poissonBracket_skew (D : DerivationFrame A) (F G : A) :
    poissonBracket D F G = -poissonBracket D G F := by
  unfold poissonBracket
  ring

@[simp] theorem poissonBracket_self (D : DerivationFrame A) (F : A) :
    poissonBracket D F F = 0 := by
  unfold poissonBracket
  ring

/-- Additivity in the first observable. -/
theorem poissonBracket_add_left
    (D : DerivationFrame A) (F₁ F₂ G : A) :
    poissonBracket D (F₁ + F₂) G =
      poissonBracket D F₁ G + poissonBracket D F₂ G := by
  unfold poissonBracket
  rw [nativeDerivation_add, nativeDerivation_add]
  ring

/-- Additivity in the second observable. -/
theorem poissonBracket_add_right
    (D : DerivationFrame A) (F G₁ G₂ : A) :
    poissonBracket D F (G₁ + G₂) =
      poissonBracket D F G₁ + poissonBracket D F G₂ := by
  unfold poissonBracket
  rw [nativeDerivation_add, nativeDerivation_add]
  ring

/-- Real homogeneity in the first observable. -/
theorem poissonBracket_smul_left
    (D : DerivationFrame A) (c : ℝ) (F G : A) :
    poissonBracket D (c • F) G = c • poissonBracket D F G := by
  simp [poissonBracket, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, smul_sub]

/-- Real homogeneity in the second observable. -/
theorem poissonBracket_smul_right
    (D : DerivationFrame A) (c : ℝ) (F G : A) :
    poissonBracket D F (c • G) = c • poissonBracket D F G := by
  simp [poissonBracket, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, smul_sub]

/-- Right Leibniz identity for the Poisson bracket. -/
theorem poissonBracket_leibniz_right
    (D : DerivationFrame A) (F G H : A) :
    poissonBracket D F (G * H) =
      poissonBracket D F G * H + G * poissonBracket D F H := by
  unfold poissonBracket
  rw [nativeDerivation_mul, nativeDerivation_mul]
  ring

/-- Left Leibniz identity for the Poisson bracket. -/
theorem poissonBracket_leibniz_left
    (D : DerivationFrame A) (F G H : A) :
    poissonBracket D (F * G) H =
      F * poissonBracket D G H + poissonBracket D F H * G := by
  unfold poissonBracket
  rw [nativeDerivation_mul, nativeDerivation_mul]
  ring

lemma Dtheta_poissonBracket
    (D : DerivationFrame A) (F G : A) :
    D.Dtheta (poissonBracket D F G) =
      (D.Dtheta (D.Dtheta F) * D.Da G +
        D.Dtheta F * D.Dtheta (D.Da G)) -
      (D.Dtheta (D.Da F) * D.Dtheta G +
        D.Da F * D.Dtheta (D.Dtheta G)) := by
  unfold poissonBracket
  rw [nativeDerivation_sub,
    nativeDerivation_mul, nativeDerivation_mul]

lemma Da_poissonBracket
    (D : DerivationFrame A) (F G : A) :
    D.Da (poissonBracket D F G) =
      (D.Da (D.Dtheta F) * D.Da G +
        D.Dtheta F * D.Da (D.Da G)) -
      (D.Da (D.Da F) * D.Dtheta G +
        D.Da F * D.Da (D.Dtheta G)) := by
  unfold poissonBracket
  rw [nativeDerivation_sub,
    nativeDerivation_mul, nativeDerivation_mul]

/-- Jacobi identity for the constant bivector `∂θ ∧ ∂a`. -/
theorem poissonBracket_jacobi
    (D : DerivationFrame A) (F G H : A) :
    poissonBracket D (poissonBracket D F G) H +
      poissonBracket D (poissonBracket D G H) F +
      poissonBracket D (poissonBracket D H F) G = 0 := by
  change
    (D.Dtheta (poissonBracket D F G) * D.Da H -
      D.Da (poissonBracket D F G) * D.Dtheta H) +
    (D.Dtheta (poissonBracket D G H) * D.Da F -
      D.Da (poissonBracket D G H) * D.Dtheta F) +
    (D.Dtheta (poissonBracket D H F) * D.Da G -
      D.Da (poissonBracket D H F) * D.Dtheta G) = 0
  rw [Dtheta_poissonBracket, Da_poissonBracket,
    Dtheta_poissonBracket, Da_poissonBracket,
    Dtheta_poissonBracket, Da_poissonBracket]
  rw [D.commute_theta_a F, D.commute_theta_a G,
    D.commute_theta_a H]
  ring

/-- Symmetric rank-one metric bracket in the `η` direction. -/
def metricBracket (D : DerivationFrame A) (F G : A) : A :=
  D.Deta F * D.Deta G

/-- Symmetry of the metric bracket. -/
theorem metricBracket_symm (D : DerivationFrame A) (F G : A) :
    metricBracket D F G = metricBracket D G F := by
  unfold metricBracket
  ring

/-- Additivity in the first observable. -/
theorem metricBracket_add_left
    (D : DerivationFrame A) (F₁ F₂ G : A) :
    metricBracket D (F₁ + F₂) G =
      metricBracket D F₁ G + metricBracket D F₂ G := by
  unfold metricBracket
  rw [nativeDerivation_add]
  ring

/-- Additivity in the second observable. -/
theorem metricBracket_add_right
    (D : DerivationFrame A) (F G₁ G₂ : A) :
    metricBracket D F (G₁ + G₂) =
      metricBracket D F G₁ + metricBracket D F G₂ := by
  unfold metricBracket
  rw [nativeDerivation_add]
  ring

/-- Right Leibniz identity for the metric biderivation. -/
theorem metricBracket_leibniz_right
    (D : DerivationFrame A) (F G H : A) :
    metricBracket D F (G * H) =
      metricBracket D F G * H + G * metricBracket D F H := by
  unfold metricBracket
  rw [nativeDerivation_mul]
  ring

/-- Left Leibniz identity for the metric biderivation. -/
theorem metricBracket_leibniz_left
    (D : DerivationFrame A) (F G H : A) :
    metricBracket D (F * G) H =
      F * metricBracket D G H + metricBracket D F H * G := by
  unfold metricBracket
  rw [nativeDerivation_mul]
  ring

/-- Diagonal metric response is a square. -/
theorem metricBracket_sq (D : DerivationFrame A) (F : A) :
    metricBracket D F F = (D.Deta F) ^ 2 := by
  unfold metricBracket
  ring

/-- Positivity of the diagonal metric response for real-valued observables. -/
theorem metricBracket_nonneg (D : DerivationFrame ℝ) (F : ℝ) :
    0 ≤ metricBracket D F F := by
  rw [metricBracket_sq]
  exact sq_nonneg _

/-- Sum of the reversible and dissipative biderivations. It is not asserted to
be skew-symmetric. -/
def metriplecticBracket (D : DerivationFrame A) (F G : A) : A :=
  poissonBracket D F G + metricBracket D F G

/-- Additivity in the first observable. -/
theorem metriplecticBracket_add_left
    (D : DerivationFrame A) (F₁ F₂ G : A) :
    metriplecticBracket D (F₁ + F₂) G =
      metriplecticBracket D F₁ G + metriplecticBracket D F₂ G := by
  rw [metriplecticBracket, poissonBracket_add_left,
    metricBracket_add_left]
  ring

/-- Additivity in the second observable. -/
theorem metriplecticBracket_add_right
    (D : DerivationFrame A) (F G₁ G₂ : A) :
    metriplecticBracket D F (G₁ + G₂) =
      metriplecticBracket D F G₁ + metriplecticBracket D F G₂ := by
  rw [metriplecticBracket, poissonBracket_add_right,
    metricBracket_add_right]
  ring

/-- Right Leibniz identity for the combined biderivation. -/
theorem metriplecticBracket_leibniz_right
    (D : DerivationFrame A) (F G H : A) :
    metriplecticBracket D F (G * H) =
      metriplecticBracket D F G * H +
        G * metriplecticBracket D F H := by
  rw [metriplecticBracket, poissonBracket_leibniz_right,
    metricBracket_leibniz_right]
  ring

/-- Entropy is a Casimir of the Poisson lane. -/
def IsPoissonCasimir (D : DerivationFrame A) (S : A) : Prop :=
  ∀ F : A, poissonBracket D F S = 0

/-- Energy lies in the kernel of the metric lane. -/
def IsMetricKernel (D : DerivationFrame A) (H : A) : Prop :=
  ∀ F : A, metricBracket D F H = 0

/-- Invariance under both `Dθ` and `Da` implies the Poisson-Casimir law. -/
theorem isPoissonCasimir_of_invariant
    (D : DerivationFrame A) (S : A)
    (hθ : D.Dtheta S = 0) (ha : D.Da S = 0) :
    IsPoissonCasimir D S := by
  intro F
  simp [poissonBracket, hθ, ha]

/-- Invariance under `Dη` implies the metric-kernel law. -/
theorem isMetricKernel_of_eta_invariant
    (D : DerivationFrame A) (H : A)
    (hη : D.Deta H = 0) :
    IsMetricKernel D H := by
  intro F
  simp [metricBracket, hη]

/-- Mutual degeneracy reduces the single generator `H+S` to the desired
reversible-plus-dissipative evolution. -/
theorem metriplectic_unified_evolution
    (D : DerivationFrame A) (H S : A)
    (hS : IsPoissonCasimir D S)
    (hH : IsMetricKernel D H) (F : A) :
    metriplecticBracket D F (H + S) =
      poissonBracket D F H + metricBracket D F S := by
  rw [metriplecticBracket, poissonBracket_add_right,
    metricBracket_add_right, hS F, hH F]
  ring

/-- Energy conservation under the unified generator. -/
theorem metriplectic_first_law
    (D : DerivationFrame A) (H S : A)
    (hS : IsPoissonCasimir D S)
    (hH : IsMetricKernel D H) :
    metriplecticBracket D H (H + S) = 0 := by
  rw [metriplectic_unified_evolution D H S hS hH H,
    poissonBracket_self]
  have hm : metricBracket D H S = 0 := by
    rw [metricBracket_symm]
    exact hH S
  rw [hm, add_zero]

/-- Entropy rate is exactly the diagonal metric square. -/
theorem metriplectic_second_law
    (D : DerivationFrame A) (H S : A)
    (hS : IsPoissonCasimir D S)
    (hH : IsMetricKernel D H) :
    metriplecticBracket D S (H + S) = (D.Deta S) ^ 2 := by
  rw [metriplectic_unified_evolution D H S hS hH S]
  have hp : poissonBracket D S H = 0 := by
    rw [poissonBracket_skew, hS H, neg_zero]
  rw [hp, zero_add, metricBracket_sq]

/-- Real-valued entropy production is nonnegative. -/
theorem metriplectic_second_law_nonneg
    (D : DerivationFrame ℝ) (H S : ℝ)
    (hS : IsPoissonCasimir D S)
    (hH : IsMetricKernel D H) :
    0 ≤ metriplecticBracket D S (H + S) := by
  rw [metriplectic_second_law D H S hS hH]
  exact sq_nonneg _

/-! ## Bridge to the finite three-coordinate GENERIC carrier -/

open InfoGeometry.Thermo.GenericMetriplecticFlow
open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel

/-- Covector contraction of the already-owned reversible operator. -/
def covectorPoissonPairing
    (α β : Covector State3) : ℝ :=
  α (reversibleOperator β)

/-- The reversible operator is exactly the coordinate bivector
`∂θ ∧ ∂a` under covector evaluation. -/
theorem covectorPoissonPairing_eq
    (α β : Covector State3) :
    covectorPoissonPairing α β =
      α thetaBasis3 * β auxiliaryBasis3 -
        α auxiliaryBasis3 * β thetaBasis3 := by
  unfold covectorPoissonPairing reversibleOperator
  simp
  ring

/-- Skewness of the covector Poisson pairing. -/
theorem covectorPoissonPairing_skew
    (α β : Covector State3) :
    covectorPoissonPairing α β =
      -covectorPoissonPairing β α := by
  exact reversibleOperator_skew α β

/-- The longitudinal coordinate covector is a Casimir of the reversible
bivector. -/
theorem etaCovector_is_reversible_casimir :
    reversibleOperator etaCovector = 0 := by
  have h := reversibleOperator_neg_eta_zero
  simpa using congrArg Neg.neg h

/-- Compact observable-level packet. -/
theorem bipolar_observable_metriplectic_packet
    (D : DerivationFrame ℝ) (H S F G K : ℝ)
    (hS : IsPoissonCasimir D S)
    (hH : IsMetricKernel D H) :
    poissonBracket D (poissonBracket D F G) K +
        poissonBracket D (poissonBracket D G K) F +
        poissonBracket D (poissonBracket D K F) G = 0 ∧
      metriplecticBracket D H (H + S) = 0 ∧
      metriplecticBracket D S (H + S) = (D.Deta S) ^ 2 ∧
      0 ≤ metriplecticBracket D S (H + S) := by
  exact ⟨poissonBracket_jacobi D F G K,
    metriplectic_first_law D H S hS hH,
    metriplectic_second_law D H S hS hH,
    metriplectic_second_law_nonneg D H S hS hH⟩

end InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra
