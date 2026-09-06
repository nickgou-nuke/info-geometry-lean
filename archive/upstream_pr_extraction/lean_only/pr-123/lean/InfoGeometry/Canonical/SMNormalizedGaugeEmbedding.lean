import Mathlib

/-!
# Normalized Standard-Model electroweak embedding

This file replaces the bare numerical assignment `sin^2 θ_W = 3/8` by a
finite representation-theoretic derivation on one Standard-Model generation.

The carrier is the 16 Weyl-state spectrum

* six left-handed quark-doublet states;
* three up-type singlets;
* three down-type singlets;
* two left-handed lepton-doublet states;
* one charged-lepton singlet;
* one sterile-neutrino singlet.

We use the convention `Q = T₃ + Y`, matching the anomaly-normalized owner
`FureyLadderSerreResidues`.  The electroweak Cartan generators are embedded as
actual diagonal `16 × 16` rational matrices.  Their representation trace norms
are proved to be

`Tr(T₃²) = 2`, `Tr(Y²) = 10/3`,

so the hypercharge embedding index relative to weak isospin is `5/3`.
Equal normalization of the coupled generators therefore forces

`g'² / g² = 3/5`,

and hence

`sin² θ_W = g'² / (g² + g'²) = 3/8`.

The theorem is deliberately finite.  It does not claim that the 16-state
representation or its common coupling normalization has already been derived
from an E₈ root embedding.  That is a separate upstream theorem obligation.
-/

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Canonical.SMNormalizedGaugeEmbedding

abbrev WeylState := Fin 16
abbrev FermionMatrix := Matrix WeylState WeylState ℚ

/-- Weak-isospin `T₃` weights on one 16-state Standard-Model generation.

Ordering:
`u_L^{r,g,b}, d_L^{r,g,b}, u_R^{r,g,b}, d_R^{r,g,b}, ν_L, e_L, e_R, ν_R`.
-/
def weakT3Weight : WeylState → ℚ :=
  ![1/2, 1/2, 1/2,
    -1/2, -1/2, -1/2,
    0, 0, 0,
    0, 0, 0,
    1/2, -1/2,
    0, 0]

/-- Hypercharge weights in the convention `Q = T₃ + Y`. -/
def hyperchargeWeight : WeylState → ℚ :=
  ![1/6, 1/6, 1/6,
    1/6, 1/6, 1/6,
    2/3, 2/3, 2/3,
    -1/3, -1/3, -1/3,
    -1/2, -1/2,
    -1, 0]

/-- The weak Cartan generator represented on the one-generation Weyl carrier. -/
def weakT3Generator : FermionMatrix := Matrix.diagonal weakT3Weight

/-- The hypercharge generator represented on the same carrier. -/
def hyperchargeGenerator : FermionMatrix := Matrix.diagonal hyperchargeWeight

/-- Concrete electroweak Cartan embedding `(a,b) ↦ a T₃ + b Y`. -/
def electroweakCartanEmbedding : (ℚ × ℚ) →ₗ[ℚ] FermionMatrix where
  toFun x := x.1 • weakT3Generator + x.2 • hyperchargeGenerator
  map_add' x y := by
    ext i j
    simp [weakT3Generator, hyperchargeGenerator]
    ring
  map_smul' c x := by
    ext i j
    simp [weakT3Generator, hyperchargeGenerator]
    ring

/-- The Cartan embedding is faithful: `T₃` and `Y` are linearly independent
on the physical one-generation carrier. -/
theorem electroweakCartanEmbedding_injective :
    Function.Injective electroweakCartanEmbedding := by
  intro x y hxy
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  have h6 := congrArg (fun M : FermionMatrix => M (6 : Fin 16) (6 : Fin 16)) hxy
  have hb : b = d := by
    norm_num [electroweakCartanEmbedding, weakT3Generator, hyperchargeGenerator,
      weakT3Weight, hyperchargeWeight, Matrix.diagonal] at h6 ⊢
    linarith
  have h0 := congrArg (fun M : FermionMatrix => M (0 : Fin 16) (0 : Fin 16)) hxy
  have ha : a = c := by
    norm_num [electroweakCartanEmbedding, weakT3Generator, hyperchargeGenerator,
      weakT3Weight, hyperchargeWeight, Matrix.diagonal, hb] at h0 ⊢
    linarith
  simp [ha, hb]

/-- Quadratic representation trace form used to normalize gauge generators. -/
def traceNormSq (A : FermionMatrix) : ℚ := Matrix.trace (A * A)

/-- Exact weak-isospin index of one generation. -/
theorem weakT3_traceNormSq : traceNormSq weakT3Generator = 2 := by
  rw [traceNormSq, weakT3Generator, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  norm_num [weakT3Weight, Fin.sum_univ_succ]

/-- Exact hypercharge index of one generation. -/
theorem hypercharge_traceNormSq : traceNormSq hyperchargeGenerator = 10 / 3 := by
  rw [traceNormSq, hyperchargeGenerator, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  norm_num [hyperchargeWeight, Fin.sum_univ_succ]

/-- The representation-theoretic hypercharge normalization index is `5/3`. -/
def hyperchargeNormalizationIndex : ℚ :=
  traceNormSq hyperchargeGenerator / traceNormSq weakT3Generator

/-- This is the nontrivial normalization theorem behind the GUT-scale weak angle. -/
theorem hyperchargeNormalizationIndex_eq_five_thirds :
    hyperchargeNormalizationIndex = 5 / 3 := by
  rw [hyperchargeNormalizationIndex, weakT3_traceNormSq, hypercharge_traceNormSq]
  norm_num

/-- Squared gauge couplings normalized by a common representation trace scale.
The common scale is chosen to be one; changing it rescales both couplings and
leaves the weak mixing angle unchanged. -/
def normalizedWeakCouplingSq : ℚ :=
  (traceNormSq weakT3Generator)⁻¹

def normalizedHyperchargeCouplingSq : ℚ :=
  (traceNormSq hyperchargeGenerator)⁻¹

/-- Common trace normalization of the weak coupled generator. -/
theorem normalizedWeakCouplingSq_traceNorm :
    normalizedWeakCouplingSq * traceNormSq weakT3Generator = 1 := by
  rw [normalizedWeakCouplingSq, weakT3_traceNormSq]
  norm_num

/-- Common trace normalization of the hypercharge coupled generator. -/
theorem normalizedHyperchargeCouplingSq_traceNorm :
    normalizedHyperchargeCouplingSq * traceNormSq hyperchargeGenerator = 1 := by
  rw [normalizedHyperchargeCouplingSq, hypercharge_traceNormSq]
  norm_num

/-- Unified normalization forces the squared coupling ratio `g'²/g² = 3/5`. -/
theorem normalized_coupling_ratio :
    normalizedHyperchargeCouplingSq / normalizedWeakCouplingSq = 3 / 5 := by
  rw [normalizedHyperchargeCouplingSq, normalizedWeakCouplingSq,
    weakT3_traceNormSq, hypercharge_traceNormSq]
  norm_num

/-- Weak mixing angle formed only after the representation normalization has
fixed the two squared coupling weights. -/
def derivedWeakAngleSinSq : ℚ :=
  normalizedHyperchargeCouplingSq /
    (normalizedWeakCouplingSq + normalizedHyperchargeCouplingSq)

/-- Main quantitative theorem: the normalized one-generation Standard-Model
embedding derives the tree-level GUT-scale value `sin² θ_W = 3/8`. -/
theorem derivedWeakAngleSinSq_eq_three_eighths :
    derivedWeakAngleSinSq = 3 / 8 := by
  rw [derivedWeakAngleSinSq, normalizedHyperchargeCouplingSq,
    normalizedWeakCouplingSq, weakT3_traceNormSq, hypercharge_traceNormSq]
  norm_num

/-- A compact theorem packet exposing every non-numerological step in the
normalization chain. -/
theorem normalized_sm_gauge_embedding_packet :
    Function.Injective electroweakCartanEmbedding ∧
    traceNormSq weakT3Generator = 2 ∧
    traceNormSq hyperchargeGenerator = 10 / 3 ∧
    hyperchargeNormalizationIndex = 5 / 3 ∧
    normalizedHyperchargeCouplingSq / normalizedWeakCouplingSq = 3 / 5 ∧
    derivedWeakAngleSinSq = 3 / 8 :=
  ⟨electroweakCartanEmbedding_injective,
   weakT3_traceNormSq,
   hypercharge_traceNormSq,
   hyperchargeNormalizationIndex_eq_five_thirds,
   normalized_coupling_ratio,
   derivedWeakAngleSinSq_eq_three_eighths⟩

end InfoGeometry.Canonical.SMNormalizedGaugeEmbedding
