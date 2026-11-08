import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A finite, representation-theoretic normalization of the electroweak Cartan
embedding.  This is intentionally a rational finite model, not an E₈ claim. -/
namespace InfoGeometry.Canonical.SMNormalizedGaugeEmbedding

abbrev WeylState := Fin 16
abbrev FermionMatrix := Matrix WeylState WeylState ℚ

def weakT3Weight : WeylState → ℚ :=
  ![1/2,1/2,1/2,-1/2,-1/2,-1/2,0,0,0,0,0,0,1/2,-1/2,0,0]

def hyperchargeWeight : WeylState → ℚ :=
  ![1/6,1/6,1/6,1/6,1/6,1/6,2/3,2/3,2/3,-1/3,-1/3,-1/3,-1/2,-1/2,-1,0]

def weakT3Generator : FermionMatrix := Matrix.diagonal weakT3Weight
def hyperchargeGenerator : FermionMatrix := Matrix.diagonal hyperchargeWeight

def electroweakCartanEmbedding : (ℚ × ℚ) →ₗ[ℚ] FermionMatrix where
  toFun x := x.1 • weakT3Generator + x.2 • hyperchargeGenerator
  map_add' x y := by ext <;> simp <;> ring
  map_smul' c x := by ext <;> simp <;> ring

theorem electroweakCartanEmbedding_injective :
    Function.Injective electroweakCartanEmbedding := by
  intro x y h
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  have h₆ := congrArg (fun M : FermionMatrix => M 6 6) h
  have h₀ := congrArg (fun M : FermionMatrix => M 0 0) h
  simp [electroweakCartanEmbedding, weakT3Generator, hyperchargeGenerator,
    weakT3Weight, hyperchargeWeight, Matrix.diagonal] at h₆ h₀
  apply Prod.ext <;> linarith

def traceNormSq (A : FermionMatrix) : ℚ := Matrix.trace (A * A)

theorem weakT3_traceNormSq : traceNormSq weakT3Generator = 2 := by
  rw [traceNormSq, weakT3Generator, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  norm_num [weakT3Weight, Fin.sum_univ_succ]

theorem hypercharge_traceNormSq : traceNormSq hyperchargeGenerator = 10 / 3 := by
  rw [traceNormSq, hyperchargeGenerator, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  norm_num [hyperchargeWeight, Fin.sum_univ_succ]

def hyperchargeNormalizationIndex : ℚ :=
  traceNormSq hyperchargeGenerator / traceNormSq weakT3Generator
def normalizedWeakCouplingSq : ℚ := (traceNormSq weakT3Generator)⁻¹
def normalizedHyperchargeCouplingSq : ℚ := (traceNormSq hyperchargeGenerator)⁻¹
def derivedWeakAngleSinSq : ℚ :=
  normalizedHyperchargeCouplingSq /
    (normalizedWeakCouplingSq + normalizedHyperchargeCouplingSq)

theorem hyperchargeNormalizationIndex_eq_five_thirds :
    hyperchargeNormalizationIndex = 5 / 3 := by
  rw [hyperchargeNormalizationIndex, weakT3_traceNormSq,
    hypercharge_traceNormSq]; norm_num

theorem normalized_coupling_ratio :
    normalizedHyperchargeCouplingSq / normalizedWeakCouplingSq = 3 / 5 := by
  rw [normalizedHyperchargeCouplingSq, normalizedWeakCouplingSq,
    weakT3_traceNormSq, hypercharge_traceNormSq]; norm_num

theorem derivedWeakAngleSinSq_eq_three_eighths :
    derivedWeakAngleSinSq = 3 / 8 := by
  rw [derivedWeakAngleSinSq, normalizedHyperchargeCouplingSq,
    normalizedWeakCouplingSq, weakT3_traceNormSq, hypercharge_traceNormSq]
  norm_num

theorem normalized_sm_gauge_embedding_packet :
    Function.Injective electroweakCartanEmbedding ∧
    traceNormSq weakT3Generator = 2 ∧
    traceNormSq hyperchargeGenerator = 10 / 3 ∧
    hyperchargeNormalizationIndex = 5 / 3 ∧
    normalizedHyperchargeCouplingSq / normalizedWeakCouplingSq = 3 / 5 ∧
    derivedWeakAngleSinSq = 3 / 8 :=
  ⟨electroweakCartanEmbedding_injective, weakT3_traceNormSq,
    hypercharge_traceNormSq, hyperchargeNormalizationIndex_eq_five_thirds,
    normalized_coupling_ratio, derivedWeakAngleSinSq_eq_three_eighths⟩

end InfoGeometry.Canonical.SMNormalizedGaugeEmbedding
