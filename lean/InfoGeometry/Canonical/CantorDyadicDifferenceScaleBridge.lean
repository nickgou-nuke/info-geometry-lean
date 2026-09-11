import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorMomentumSpinIntertwinerBridge

set_option linter.unusedSimpArgs false

/-!
# Cantor Dyadic Difference Scale Bridge

This owner module formalizes the discrete scale translations and dyadic finite-difference
derivatives on the Cantor prefix resolutions:

1. **Discrete Scale Carrier:**
   $$\text{DyadicScale}(n) := \operatorname{Fin}(2^n) \to \mathbb{R}$$

2. **Discrete Translations:**
   $T_n : \text{DyadicScale}(n) \toₗ[ℝ] \text{DyadicScale}(n)$ preserving the unit constant function.

3. **Dyadic Difference Operator:**
   $$\boxed{D_n := 2^n (I - T_n)}$$

4. **Vacuum State Annihilation:**
   $$\boxed{D_n(1) = 0}$$

5. **Finite Difference Commutativity:**
   $$[T_n, T'_n] = 0 \implies \boxed{[D_n, D'_n] = 0}$$

6. **Dyadic Step Doubling Scaling:**
   $$\boxed{2 \cdot D_n(f) = 2^{n+1} (f - T_n(f))}$$

7. **Exact Finite Inversion Pair:**
   $$D_n(T_n(D)) = D \qquad \text{and} \qquad T_n(D_n(T)) = T$$
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorDyadicDifferenceScaleBridge

open InfoGeometry.Canonical.CantorMomentumSpinIntertwinerBridge

variable {n : ℕ}

/-- Space of discrete functions at scale $n$. -/
abbrev DyadicScale (n : ℕ) := Fin (2 ^ n) → ℝ

/-- The discrete translation operator $T_n$ acting on functions of scale $n$. -/
structure DiscreteTranslation (n : ℕ) where
  T : DyadicScale n →ₗ[ℝ] DyadicScale n
  preserves_one : T (fun _ => 1) = (fun _ => 1)

/-- The dyadic finite-difference derivative operator $D_n = 2^n (I - T_n)$. -/
def dyadicDifference (trans : DiscreteTranslation n) : DyadicScale n →ₗ[ℝ] DyadicScale n :=
  ((2 : ℝ) ^ n) • (LinearMap.id - trans.T)

theorem dyadicDifference_apply (trans : DiscreteTranslation n) (f : DyadicScale n) :
    dyadicDifference trans f = ((2 : ℝ) ^ n) • (f - trans.T f) := by
  rfl

/-- 🏆 THEOREM 1: Annihilation of constant vacuum / ground state:
    $D_n(1) = 0$. -/
theorem dyadicDifference_const_zero (trans : DiscreteTranslation n) :
    dyadicDifference trans (fun _ => 1) = 0 := by
  rw [dyadicDifference_apply, trans.preserves_one, sub_self, smul_zero]

/-- 🏆 THEOREM 2: Commutativity of dyadic differences for commuting translations:
    $[T, T'] = 0 \implies [D, D'] = 0$. -/
theorem dyadicDifference_comm
    (trans1 trans2 : DiscreteTranslation n)
    (hcomm : trans1.T ∘ₗ trans2.T = trans2.T ∘ₗ trans1.T) :
    dyadicDifference trans1 ∘ₗ dyadicDifference trans2 =
    dyadicDifference trans2 ∘ₗ dyadicDifference trans1 := by
  apply LinearMap.ext
  intro f
  have hTcomm : trans1.T (trans2.T f) = trans2.T (trans1.T f) := by
    exact LinearMap.congr_fun hcomm f
  calc
    (dyadicDifference trans1 ∘ₗ dyadicDifference trans2) f
      = dyadicDifference trans1 (dyadicDifference trans2 f) := by rfl
    _ = dyadicDifference trans1 (((2 : ℝ) ^ n) • (f - trans2.T f)) := by
      rw [dyadicDifference_apply trans2 f]
    _ = ((2 : ℝ) ^ n) • (dyadicDifference trans1 (f - trans2.T f)) := by
      rw [map_smul]
    _ = ((2 : ℝ) ^ n) • (((2 : ℝ) ^ n) • ((f - trans2.T f) - trans1.T (f - trans2.T f))) := by
      rw [dyadicDifference_apply trans1 (f - trans2.T f)]
    _ = ((2 : ℝ) ^ n * (2 : ℝ) ^ n) • (f - trans2.T f - (trans1.T f - trans1.T (trans2.T f))) := by
      rw [smul_smul, map_sub]
    _ = ((2 : ℝ) ^ n * (2 : ℝ) ^ n) • (f - trans1.T f - (trans2.T f - trans2.T (trans1.T f))) := by
      rw [hTcomm]
      have h_ab : f - trans2.T f - (trans1.T f - trans2.T (trans1.T f))
          = f - trans1.T f - (trans2.T f - trans2.T (trans1.T f)) := by abel
      rw [h_ab]
    _ = ((2 : ℝ) ^ n) • (((2 : ℝ) ^ n) • ((f - trans1.T f) - trans2.T (f - trans1.T f))) := by
      rw [smul_smul, map_sub]
    _ = ((2 : ℝ) ^ n) • (dyadicDifference trans2 (f - trans1.T f)) := by
      rw [← dyadicDifference_apply trans2 (f - trans1.T f)]
    _ = dyadicDifference trans2 (((2 : ℝ) ^ n) • (f - trans1.T f)) := by
      rw [← map_smul]
    _ = dyadicDifference trans2 (dyadicDifference trans1 f) := by
      rw [← dyadicDifference_apply trans1 f]
    _ = (dyadicDifference trans2 ∘ₗ dyadicDifference trans1) f := by rfl

/-! Since the dyadic coefficient is nonzero, the finite affine change of
variables preserves commutators in both directions.  This is still a
finite-scale statement: it does not assert anything about a continuum
generator or a limit in `n`. -/

theorem dyadicDifference_comm_iff
    (trans1 trans2 : DiscreteTranslation n) :
    dyadicDifference trans1 ∘ₗ dyadicDifference trans2 =
        dyadicDifference trans2 ∘ₗ dyadicDifference trans1 ↔
      trans1.T ∘ₗ trans2.T = trans2.T ∘ₗ trans1.T := by
  constructor
  · intro h
    apply LinearMap.ext
    intro f
    have hpoint := LinearMap.congr_fun h f
    simp only [LinearMap.comp_apply, dyadicDifference_apply, map_smul,
      map_sub, smul_smul] at hpoint
    have hsq : ((2 : ℝ) ^ n * (2 : ℝ) ^ n : ℝ) ≠ 0 := by positivity
    have hnorm :
        ((2 : ℝ) ^ n) • ((2 : ℝ) ^ n) •
            (trans1.T (trans2.T f) - trans2.T (trans1.T f)) = 0 := by
      simp only [smul_sub, smul_add, smul_smul] at hpoint ⊢
      linear_combination hpoint
    have hcancel :
        ((2 : ℝ) ^ n * (2 : ℝ) ^ n) •
            (trans1.T (trans2.T f) - trans2.T (trans1.T f)) = 0 := by
      simpa [smul_smul] using hnorm
    have hdiff : trans1.T (trans2.T f) - trans2.T (trans1.T f) = 0 := by
      exact (smul_eq_zero.mp hcancel).resolve_left hsq
    exact sub_eq_zero.mp hdiff
  · intro h
    exact dyadicDifference_comm trans1 trans2 h

/-- 🏆 THEOREM 3: Scaling property under dyadic step doubling:
    $2 \cdot D_n(f) = 2^{n+1} (f - T_n(f))$. -/
theorem dyadicDifference_step_doubling (trans : DiscreteTranslation n) (f : DyadicScale n) :
    (2 : ℝ) • (dyadicDifference trans f) =
      ((2 : ℝ) ^ (n + 1)) • (f - trans.T f) := by
  rw [dyadicDifference_apply, smul_smul, pow_succ, mul_comm]

/-! The following two maps package the exact finite algebraic inverse pair
behind the scaled difference formula. -/

def translationOfGenerator (D : DyadicScale n →ₗ[ℝ] DyadicScale n) :
    DyadicScale n →ₗ[ℝ] DyadicScale n :=
  LinearMap.id - (1 / (2 ^ n : ℝ)) • D

def generatorOfTranslation (T : DyadicScale n →ₗ[ℝ] DyadicScale n) :
    DyadicScale n →ₗ[ℝ] DyadicScale n :=
  ((2 : ℝ) ^ n) • (LinearMap.id - T)

/-- 🏆 THEOREM 4: Exact generator recovery from its induced discrete translation. -/
theorem dyadicDifference_of_translation
    (D : DyadicScale n →ₗ[ℝ] DyadicScale n) :
    generatorOfTranslation (translationOfGenerator D) = D := by
  apply LinearMap.ext
  intro f
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  have hcancel : (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) = 1 := mul_one_div_cancel hpow
  calc
    generatorOfTranslation (translationOfGenerator D) f
      = (2 : ℝ) ^ n • (f - (f - (1 / (2 ^ n : ℝ)) • D f)) := by rfl
    _ = (2 : ℝ) ^ n • ((1 / (2 ^ n : ℝ)) • D f) := by
      have h_sub : f - (f - (1 / (2 ^ n : ℝ)) • D f) = (1 / (2 ^ n : ℝ)) • D f := by abel
      rw [h_sub]
    _ = ((2 : ℝ) ^ n * (1 / (2 ^ n : ℝ))) • D f := by rw [smul_smul]
    _ = (1 : ℝ) • D f := by rw [hcancel]
    _ = D f := one_smul ℝ (D f)

/-- 🏆 THEOREM 5: Exact discrete translation recovery from its difference operator. -/
theorem translation_of_dyadicDifference
    (T : DyadicScale n →ₗ[ℝ] DyadicScale n) :
    translationOfGenerator (generatorOfTranslation T) = T := by
  apply LinearMap.ext
  intro f
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  have hcancel : (1 / (2 ^ n : ℝ)) * (2 ^ n : ℝ) = 1 := one_div_mul_cancel hpow
  calc
    translationOfGenerator (generatorOfTranslation T) f
      = f - (1 / (2 ^ n : ℝ)) • ((2 : ℝ) ^ n • (f - T f)) := by rfl
    _ = f - ((1 / (2 ^ n : ℝ)) * (2 : ℝ) ^ n) • (f - T f) := by rw [smul_smul]
    _ = f - (1 : ℝ) • (f - T f) := by rw [hcancel]
    _ = f - (f - T f) := by rw [one_smul]
    _ = T f := by abel

/-! The continuum step is intentionally represented as a contract.  The finite
stage identities above do not construct an unbounded operator or prove strong
convergence on a Cantor `L²` carrier. -/

def StrongDyadicLimitStatement
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (core : Set H) (approximants : ℕ → H → H)
    (generator : H →L[ℂ] H) : Prop :=
  ∀ ψ ∈ core,
    Filter.Tendsto (fun n => approximants n ψ) Filter.atTop
      (nhds (generator ψ))

structure StrongDyadicGeneratorDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] where
  core : Set H
  approximants : ℕ → H → H
  generator : H →L[ℂ] H
  strong_limit : StrongDyadicLimitStatement core approximants generator

theorem StrongDyadicGeneratorDatum.limit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (datum : StrongDyadicGeneratorDatum H) {ψ : H} (hψ : ψ ∈ datum.core) :
    Filter.Tendsto (fun n => datum.approximants n ψ) Filter.atTop
      (nhds (datum.generator ψ)) :=
  datum.strong_limit ψ hψ

end InfoGeometry.Canonical.CantorDyadicDifferenceScaleBridge
