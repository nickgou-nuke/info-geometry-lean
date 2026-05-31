import Mathlib

namespace InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

/-- Critical line in the complex zeta plane. -/
def CriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- Functional-equation reflection `s ↦ 1 - s`. -/
def functionalReflection (s : ℂ) : ℂ :=
  1 - s

/-- Antiunitary critical reflection `s ↦ 1 - star s`. -/
def antiunitaryCriticalReflection (s : ℂ) : ℂ :=
  1 - star s

/-- Conjugation reflection `s ↦ star s`. -/
def conjugationReflection (s : ℂ) : ℂ :=
  star s

theorem functionalReflection_involutive :
    Function.Involutive functionalReflection := by
  intro s; simp [functionalReflection]

theorem conjugationReflection_involutive :
    Function.Involutive conjugationReflection := by
  intro s; simp [conjugationReflection]

theorem antiunitaryCriticalReflection_involutive :
    Function.Involutive antiunitaryCriticalReflection := by
  intro s
  apply Complex.ext <;> simp [antiunitaryCriticalReflection]

theorem fixed_antiunitaryCriticalReflection_iff_criticalLine (s : ℂ) :
    s = antiunitaryCriticalReflection s ↔ CriticalLine s := by
  constructor
  · intro h
    unfold CriticalLine antiunitaryCriticalReflection at *
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  · intro hs
    unfold CriticalLine antiunitaryCriticalReflection at *
    apply Complex.ext
    · simp [hs]
      norm_num
    · simp

theorem functional_conjugation_commute (s : ℂ) :
    functionalReflection (conjugationReflection s) =
      conjugationReflection (functionalReflection s) := by
  apply Complex.ext <;> simp [functionalReflection, conjugationReflection]

inductive CompletedZetaSymmetry where
  | functional
  | conjugation
  | functionalConjugation

def completedZetaAct : CompletedZetaSymmetry → ℂ → ℂ
  | CompletedZetaSymmetry.functional, s => functionalReflection s
  | CompletedZetaSymmetry.conjugation, s => conjugationReflection s
  | CompletedZetaSymmetry.functionalConjugation, s =>
      functionalReflection (conjugationReflection s)

theorem completedZetaAct_involutive (g : CompletedZetaSymmetry) :
    Function.Involutive (completedZetaAct g) := by
  cases g <;> intro s <;> apply Complex.ext <;> simp [completedZetaAct, functionalReflection,
    conjugationReflection]

theorem completedZetaAct_preserves_criticalLine (g : CompletedZetaSymmetry) (s : ℂ) :
    CriticalLine s → CriticalLine (completedZetaAct g s) := by
  intro hs
  cases g <;> unfold CriticalLine completedZetaAct functionalReflection conjugationReflection at * <;>
    simp [hs] <;> linarith

/-! ## 2. Massieu potential and moment-map decomposition -/

structure CompletedZetaMassieuPacket where
  completedPartition : ℂ → ℂ
  xi : ℂ → ℂ
  xi_star_invariant :
    ∀ s, xi (star s) = star (xi s)
  momentMap : ℂ → ℂ
  fisherMetric : ℂ → ℂ

structure SouriauMomentMapDecompositionPacket where
  totalMoment : ℂ → ℂ
  vonMangoldtForce : ℂ → ℂ
  piForce : ℂ
  archimedeanDigammaForce : ℂ → ℂ
  boundaryConstraintForce : ℂ → ℂ
  decomposition_True :
    ∀ s : ℂ,
      totalMoment s =
        vonMangoldtForce s + piForce +
        archimedeanDigammaForce s + boundaryConstraintForce s

structure FisherSouriauMetricPacket where
  potential : ℂ → ℂ
  momentMap : ℂ → ℂ
  fisherMetric : ℂ → ℂ
  moment_variation_True : ∀ s, momentMap s = deriv potential s
  fisher_metric_True : ∀ s, fisherMetric s = deriv momentMap s

structure SouriauSymplecticCocyclePacket (G : Type*) [Group G] where
  actOnBeta : G → ℂ → ℂ
  momentMap : ℂ → ℂ
  cocycle : G → ℂ → ℂ
  equivariance_defect_True :
    ∀ (g : G) (s : ℂ),
      momentMap (actOnBeta g s) = momentMap s + cocycle g s

structure DInfinitySouriauThermodynamics (G : Type*) [Group G] where
  reflection₀ : G
  reflection₁ : G
  reflection₀_sq : reflection₀ * reflection₀ = 1
  reflection₁_sq : reflection₁ * reflection₁ = 1
  product_infinite_order_True : ∀ (n : ℕ), n > 0 → (reflection₀ * reflection₁) ^ n ≠ 1

structure BostConnesArchimedeanCompletionSocket where
  rawPrimePartition : ℂ → ℂ
  archimedeanHeatBath : ℂ → ℂ
  completedPartition : ℂ → ℂ
  completed_eq_raw_mul_archimedean :
    ∀ s : ℂ,
      completedPartition s =
        rawPrimePartition s * archimedeanHeatBath s

def completedZetaBregman
    (Phi : ℂ → ℂ)
    (gradPhi : ℂ → ℂ)
    (s₁ s₂ : ℂ) : ℂ :=
  Phi s₁ - Phi s₂ - gradPhi s₂ * (s₁ - s₂)

theorem completedZetaBregman_self_eq_zero
    (Phi : ℂ → ℂ)
    (gradPhi : ℂ → ℂ)
    (s : ℂ) :
    completedZetaBregman Phi gradPhi s s = 0 := by
  unfold completedZetaBregman; simp

end InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
