/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Topology.Order.Filter
import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Elitzur Lattice Gauge Projection, Haar–Reynolds Invariance & Physical Projections

This module formalizes Archetype 8:
1. Classical finite Haar–Reynolds Gibbs gauge invariance and Elitzur's theorem:
   - Haar–Reynolds average of observables under a finite gauge group.
   - Gauge-invariant Gibbs measures and exact Haar–Reynolds expectation preservation.
   - Character-covariant observables have identically zero expectation for all couplings and temperatures.
   - Thermodynamic limit vanishing (`Filter.Tendsto ... atTop (𝓝 0)`).
2. ℤ₂ link-Higgs witness (`z2_link_higgs_elitzur_vs_wilson_string`):
   - 2-site lattice with ℤ₂ = ℤˣ matter and gauge fields.
   - Bare matter expectation vanishes identically: `⟨σ₀⟩ = 0`.
   - Wilson-dressed string has strictly positive expectation: `⟨σ₀ U₀₁ σ₁⟩ = Real.tanh J > 0` for `J > 0`.
3. Quantum representation-theoretic physical projection:
   - Physical projection `P_phys := ρ.averageMap`.
   - Annihilation of character-covariant operators: `P_phys ∘ₗ A ∘ₗ P_phys = 0` and `(linHom ρ ρ).averageMap A = 0`.
   - Concrete ℝ × ℝ witness under ℤ₂.
4. OpenGauss T16 non-commutativity witness:
   - Operator non-commutativity `opA ∘ₗ opZ ≠ opZ ∘ₗ opA`.
   - Matrix non-commutativity `pauliX * pauliZ ≠ pauliZ * pauliX`.
-/

open scoped BigOperators
open Representation

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ElitzurLatticeGaugeProjection

/-! ### Section 1: Classical Haar–Reynolds Gibbs Invariance & Elitzur's Theorem -/

section ClassicalElitzur

variable {G : Type*} [Group G] [Fintype G]

/-- Haar–Reynolds average of an observable under a finite group action. -/
def haarReynolds (G : Type*) [Group G] [Fintype G] {α : Type*} [MulAction G α] (O : α → ℝ) : α → ℝ :=
  fun c => (1 / (Fintype.card G : ℝ)) * ∑ g : G, O (g • c)

/-- Classical partition function with given Boltzmann weights. -/
def partitionFunction {α : Type*} [Fintype α] (w : α → ℝ) : ℝ := ∑ c : α, w c

/-- Gibbs expectation value of an observable. -/
def gibbsExpectation {α : Type*} [Fintype α] (w : α → ℝ) (O : α → ℝ) : ℝ :=
  (∑ c : α, O c * w c) / partitionFunction w

/-- Gauge invariance of Boltzmann weights under local transformations. -/
def IsGaugeInvariant {α : Type*} [MulAction G α] (w : α → ℝ) : Prop :=
  ∀ (g : G) (c : α), w (g • c) = w c

/-- Covariance of an observable under a 1D character χ. -/
def IsCovariant {α : Type*} [MulAction G α] (O : α → ℝ) (χ : G → ℝ) : Prop :=
  ∀ (g : G) (c : α), O (g • c) = χ g * O c

omit [Fintype G] in
theorem sum_comp_mulAction {α : Type*} [Fintype α] [MulAction G α] (g : G) (f : α → ℝ) :
    ∑ c : α, f (g • c) = ∑ c : α, f c := by
  let e : α ≃ α := MulAction.toPerm g
  exact Equiv.sum_comp e f

theorem card_G_pos : 0 < (Fintype.card G : ℝ) := by
  have : 0 < Fintype.card G := Fintype.card_pos_iff.mpr (by infer_instance)
  positivity

theorem card_G_ne_zero : (Fintype.card G : ℝ) ≠ 0 :=
  ne_of_gt card_G_pos

/-- A character-covariant observable averages to zero pointwise under the Haar–Reynolds projector. -/
theorem haarReynolds_apply_eq_zero {α : Type*} [MulAction G α] {O : α → ℝ} {χ : G → ℝ}
    (hcov : IsCovariant (G := G) O χ) (hchi : ∑ g : G, χ g = 0) (c : α) :
    haarReynolds G O c = 0 := by
  dsimp [haarReynolds]
  have hsum : ∑ g : G, O (g • c) = 0 := by
    calc ∑ g : G, O (g • c)
      _ = ∑ g : G, (χ g * O c) := by
        apply Finset.sum_congr rfl
        intro g _
        exact hcov g c
      _ = (∑ g : G, χ g) * O c := by
        rw [Finset.sum_mul]
      _ = 0 * O c := by
        rw [hchi]
      _ = 0 := by
        rw [MulZeroClass.zero_mul]
  rw [hsum, mul_zero]

/-- The Haar–Reynolds projector preserves Gibbs expectations for any gauge-invariant measure. -/
theorem haarReynolds_gibbs_invariance {α : Type*} [Fintype α] [MulAction G α]
    (w : α → ℝ) (hw : IsGaugeInvariant (G := G) w) (O : α → ℝ) :
    ∑ c : α, haarReynolds G O c * w c = ∑ c : α, O c * w c := by
  dsimp [haarReynolds]
  have hcard := card_G_ne_zero (G := G)
  calc ∑ c : α, ((1 / (Fintype.card G : ℝ)) * ∑ g : G, O (g • c)) * w c
    _ = ∑ c : α, (1 / (Fintype.card G : ℝ)) * ((∑ g : G, O (g • c)) * w c) := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = (1 / (Fintype.card G : ℝ)) * ∑ c : α, ((∑ g : G, O (g • c)) * w c) := by
      rw [← Finset.mul_sum]
    _ = (1 / (Fintype.card G : ℝ)) * ∑ c : α, ∑ g : G, (O (g • c) * w c) := by
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
    _ = (1 / (Fintype.card G : ℝ)) * ∑ g : G, ∑ c : α, (O (g • c) * w c) := by
      rw [Finset.sum_comm]
    _ = (1 / (Fintype.card G : ℝ)) * ∑ g : G, ∑ c : α, (O (g • c) * w (g • c)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro c _
      rw [hw g c]
    _ = (1 / (Fintype.card G : ℝ)) * ∑ g : G, ∑ c : α, (O c * w c) := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      exact sum_comp_mulAction g (fun x => O x * w x)
    _ = (1 / (Fintype.card G : ℝ)) * ((Fintype.card G : ℝ) * ∑ c : α, (O c * w c)) := by
      congr 1
      simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card]
    _ = ∑ c : α, O c * w c := by
      rw [← mul_assoc, one_div_mul_cancel hcard, one_mul]

/-- Elitzur's theorem on finite lattices: the expectation of a local gauge-variant observable vanishes identically. -/
theorem elitzur_local_gauge_expectation_zero {α : Type*} [Fintype α] [MulAction G α]
    (w : α → ℝ) (hw : IsGaugeInvariant (G := G) w)
    (O : α → ℝ) (χ : G → ℝ) (hcov : IsCovariant (G := G) O χ) (hchi : ∑ g : G, χ g = 0) :
    gibbsExpectation w O = 0 := by
  dsimp [gibbsExpectation]
  have hsum_eq : ∑ c : α, O c * w c = 0 := by
    rw [← haarReynolds_gibbs_invariance w hw O]
    have hzero : ∀ c : α, haarReynolds G O c = 0 :=
      fun c => haarReynolds_apply_eq_zero hcov hchi c
    simp [hzero]
  rw [hsum_eq, zero_div]

/-- Elitzur's theorem in the thermodynamic limit: the sequence of expectation values converges to zero. -/
theorem elitzur_thermodynamic_limit_zero {α : ℕ → Type*} [∀ n, Fintype (α n)] [∀ n, MulAction G (α n)]
    (w : (n : ℕ) → (α n → ℝ)) (hw : ∀ n, IsGaugeInvariant (G := G) (w n))
    (O : (n : ℕ) → (α n → ℝ)) (χ : G → ℝ) (hcov : ∀ n, IsCovariant (G := G) (O n) χ)
    (hchi : ∑ g : G, χ g = 0) :
    Filter.Tendsto (fun n => gibbsExpectation (w n) (O n)) Filter.atTop (nhds 0) := by
  have heq : (fun n => gibbsExpectation (w n) (O n)) = fun _ => 0 := by
    ext n
    exact elitzur_local_gauge_expectation_zero (w n) (hw n) (O n) χ (hcov n) hchi
  rw [heq]
  exact tendsto_const_nhds

end ClassicalElitzur

/-! ### Section 2: ℤ₂ Link-Higgs Witness -/

section Z2LinkHiggs

/-- Microstates on a 2-site lattice with ℤ₂ matter and gauge link: triples (s₀, u, s₁). -/
structure Config where
  s0 : Units ℤ
  u  : Units ℤ
  s1 : Units ℤ
  deriving DecidableEq

def configEquiv : Config ≃ (Units ℤ × (Units ℤ × Units ℤ)) where
  toFun c := (c.s0, (c.u, c.s1))
  invFun := fun (s0, (u, s1)) => ⟨s0, u, s1⟩
  left_inv := by
    intro ⟨s0, u, s1⟩
    rfl
  right_inv := by
    intro (s0, (u, s1))
    rfl

instance : Fintype Config := Fintype.ofEquiv _ configEquiv.symm

/-- Gauge-invariant Wilson-dressed matter string observable σ₀ U₀₁ σ₁. -/
def wilson (c : Config) : ℝ :=
  (c.s0 : ℝ) * (c.u : ℝ) * (c.s1 : ℝ)

/-- Bare local matter observable σ₀ at site 0. -/
def s0Obs (c : Config) : ℝ := (c.s0 : ℝ)

/-- Boltzmann weight at coupling J. -/
def weight (J : ℝ) (c : Config) : ℝ :=
  Real.exp (J * wilson c)

/-- Partition function for the 2-site ℤ₂ link-Higgs system. -/
def Z (J : ℝ) : ℝ := ∑ c : Config, weight J c

/-- Expectation of the Wilson-dressed string observable. -/
def expWilson (J : ℝ) : ℝ := (∑ c : Config, wilson c * weight J c) / Z J

/-- Expectation of the bare matter observable. -/
def expS0 (J : ℝ) : ℝ := (∑ c : Config, s0Obs c * weight J c) / Z J

lemma units_int_sum (f : Units ℤ → ℝ) :
    ∑ u : Units ℤ, f u = f 1 + f (-1) := by
  have hu : (Finset.univ : Finset (Units ℤ)) = {1, -1} := by
    decide
  rw [hu]
  exact Finset.sum_pair (by decide)

theorem sum_config (f : Config → ℝ) :
    ∑ c : Config, f c =
      f ⟨1, 1, 1⟩ + f ⟨1, 1, -1⟩ + f ⟨1, -1, 1⟩ + f ⟨1, -1, -1⟩ +
      f ⟨-1, 1, 1⟩ + f ⟨-1, 1, -1⟩ + f ⟨-1, -1, 1⟩ + f ⟨-1, -1, -1⟩ := by
  rw [← Equiv.sum_comp configEquiv.symm]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product, units_int_sum]
  dsimp [configEquiv]
  simp only [add_assoc]

theorem Z_eq (J : ℝ) : Z J = 4 * Real.exp J + 4 * Real.exp (-J) := by
  dsimp [Z, weight]
  rw [sum_config]
  dsimp [wilson]
  simp only [Int.cast_one, Int.cast_neg, mul_one, neg_mul, one_mul, neg_neg]
  ring_nf

theorem sum_wilson_weight (J : ℝ) :
    ∑ c : Config, wilson c * weight J c = 4 * Real.exp J - 4 * Real.exp (-J) := by
  dsimp [weight]
  rw [sum_config]
  dsimp [wilson]
  simp only [Int.cast_one, Int.cast_neg, mul_one, neg_mul, one_mul, neg_neg]
  ring_nf

theorem sum_s0_weight (J : ℝ) :
    ∑ c : Config, s0Obs c * weight J c = 0 := by
  dsimp [weight]
  rw [sum_config]
  dsimp [wilson, s0Obs]
  simp only [Int.cast_one, Int.cast_neg, mul_one, neg_mul, one_mul, neg_neg]
  ring_nf

theorem Z_pos (J : ℝ) : 0 < Z J := by
  rw [Z_eq]
  have h1 : 0 < Real.exp J := Real.exp_pos J
  have h2 : 0 < Real.exp (-J) := Real.exp_pos (-J)
  linarith [h1, h2]

theorem Z_ne_zero (J : ℝ) : Z J ≠ 0 :=
  ne_of_gt (Z_pos J)

/-- The bare matter expectation vanishes for all couplings J. -/
theorem expS0_eq_zero (J : ℝ) : expS0 J = 0 := by
  dsimp [expS0]
  rw [sum_s0_weight, zero_div]

/-- The Wilson-dressed string expectation is exactly tanh J. -/
theorem expWilson_eq_tanh (J : ℝ) : expWilson J = Real.tanh J := by
  dsimp [expWilson]
  rw [sum_wilson_weight, Z_eq, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  calc (4 * Real.exp J - 4 * Real.exp (-J)) / (4 * Real.exp J + 4 * Real.exp (-J))
    _ = (4 * (Real.exp J - Real.exp (-J))) / (4 * (Real.exp J + Real.exp (-J))) := by
      ring
    _ = (Real.exp J - Real.exp (-J)) / (Real.exp J + Real.exp (-J)) := by
      rw [mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]
    _ = ((Real.exp J - Real.exp (-J)) / 2) / ((Real.exp J + Real.exp (-J)) / 2) := by
      rw [div_div_div_comm, div_self (by norm_num : (2 : ℝ) ≠ 0), div_one]

theorem expWilson_pos_of_pos {J : ℝ} (hJ : 0 < J) : 0 < expWilson J := by
  rw [expWilson_eq_tanh, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
  have hlt : Real.exp (-J) < Real.exp J := by
    rw [Real.exp_lt_exp]
    linarith [hJ]
  have hsinh_pos : 0 < (Real.exp J - Real.exp (-J)) / 2 := by
    linarith [hlt]
  exact div_pos hsinh_pos (Real.cosh_pos J)

/-- ℤ₂ link-Higgs witness: bare matter expectation is identically zero while the Wilson string is strictly positive for J > 0. -/
theorem z2_link_higgs_elitzur_vs_wilson_string (J : ℝ) (hJ : 0 < J) :
    expS0 J = 0 ∧ expWilson J = Real.tanh J ∧ 0 < expWilson J :=
  ⟨expS0_eq_zero J, expWilson_eq_tanh J, expWilson_pos_of_pos hJ⟩

end Z2LinkHiggs

/-! ### Section 3: Quantum Physical Projection P_phys -/

section QuantumAverage

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable [Fintype G] [Invertible (Fintype.card G : k)]
variable (ρ : Representation k G V)

/-- Physical subspace projection via group averaging. -/
def P_phys : V →ₗ[k] V := ρ.averageMap

theorem averageMap_apply (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
  dsimp [averageMap, GroupAlgebra.average]
  simp only [map_smul, map_sum, MonoidAlgebra.of_apply, asAlgebraHom_single_one]
  rw [LinearMap.smul_apply, LinearMap.sum_apply]

/-- An operator is covariant under 1D character χ. -/
def IsOpCovariant (A : V →ₗ[k] V) (χ : G → k) : Prop :=
  ∀ g : G, (linHom ρ ρ) g A = χ g • A

/-- Any character-covariant operator is annihilated by the operator-level averageMap. -/
theorem averageMap_linHom_apply_eq_zero {A : V →ₗ[k] V} {χ : G → k}
    (hcov : IsOpCovariant ρ A χ) (hchi : ∑ g : G, χ g = 0) :
    (linHom ρ ρ).averageMap A = 0 := by
  rw [averageMap_apply]
  have hsum : ∑ g : G, (linHom ρ ρ) g A = 0 := by
    calc ∑ g : G, (linHom ρ ρ) g A
      _ = ∑ g : G, χ g • A := by
        apply Finset.sum_congr rfl
        intro g _
        exact hcov g
      _ = (∑ g : G, χ g) • A := by
        rw [Finset.sum_smul]
      _ = (0 : k) • A := by
        rw [hchi]
      _ = 0 := by
        rw [zero_smul]
  rw [hsum, smul_zero]

/-- Sandwiched between physical projections P_phys ∘ₗ A ∘ₗ P_phys, any character-covariant operator vanishes identically. -/
theorem P_phys_comp_A_comp_P_phys_eq_zero {A : V →ₗ[k] V} {χ : G → k}
    (hcov : IsOpCovariant ρ A χ) (hchi : ∑ g : G, χ g = 0) :
    (P_phys ρ) ∘ₗ A ∘ₗ (P_phys ρ) = 0 := by
  ext v
  change ρ.averageMap (A (ρ.averageMap v)) = 0
  rw [averageMap_apply]
  have h_inv : ∀ g : G, ρ g⁻¹ (ρ.averageMap v) = ρ.averageMap v := by
    intro g
    have := ρ.averageMap_invariant v
    rw [mem_invariants] at this
    exact this g⁻¹
  have h_term : ∀ g : G, ρ g (A (ρ.averageMap v)) = χ g • (A (ρ.averageMap v)) := by
    intro g
    have hlin : ρ g (A (ρ.averageMap v)) = (linHom ρ ρ g A) (ρ.averageMap v) := by
      dsimp [linHom]
      congr 1
      congr 1
      exact (h_inv g).symm
    rw [hlin, hcov g]
    rfl
  have h_sum : ∑ g : G, ρ g (A (ρ.averageMap v)) = 0 := by
    calc ∑ g : G, ρ g (A (ρ.averageMap v))
      _ = ∑ g : G, χ g • (A (ρ.averageMap v)) := by
        apply Finset.sum_congr rfl
        intro g _
        exact h_term g
      _ = (∑ g : G, χ g) • (A (ρ.averageMap v)) := by
        rw [Finset.sum_smul]
      _ = (0 : k) • (A (ρ.averageMap v)) := by
        rw [hchi]
      _ = 0 := by
        rw [zero_smul]
  rw [h_sum, smul_zero]

end QuantumAverage

/-! ### Section 4: Concrete ℝ × ℝ Witness under ℤ₂ -/

section R2Witness

/-- Representation of ℤ₂ = ℤˣ on ℝ × ℝ. -/
def rhoZ2 : Representation ℝ (Units ℤ) (ℝ × ℝ) where
  toFun u :=
    { toFun := fun ⟨x, y⟩ => ⟨x, (u : ℝ) * y⟩
      map_add' := by
        intro ⟨x1, y1⟩ ⟨x2, y2⟩
        ext <;> dsimp <;> ring
      map_smul' := by
        intro c ⟨x, y⟩
        ext <;> dsimp <;> ring }
  map_one' := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    ext
    · rfl
    · dsimp
      simp
  map_mul' u1 u2 := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    ext
    · rfl
    · dsimp
      push_cast
      ring

/-- Character-covariant off-diagonal operator (Pauli X swap). -/
def opA : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := fun ⟨x, y⟩ => ⟨y, x⟩
  map_add' := by
    intro ⟨x1, y1⟩ ⟨x2, y2⟩
    ext <;> rfl
  map_smul' := by
    intro c ⟨x, y⟩
    ext <;> rfl

/-- Diagonal operator (Pauli Z). -/
def opZ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := fun ⟨x, y⟩ => ⟨x, -y⟩
  map_add' := by
    intro ⟨x1, y1⟩ ⟨x2, y2⟩
    ext <;> dsimp <;> ring
  map_smul' := by
    intro c ⟨x, y⟩
    ext <;> dsimp <;> ring

/-- Non-trivial character of ℤ₂. -/
def chiSign : Units ℤ → ℝ := fun u => (u : ℝ)

lemma chiSign_sum : ∑ u : Units ℤ, chiSign u = 0 := by
  have hu : (Finset.univ : Finset (Units ℤ)) = {1, -1} := by
    decide
  rw [hu, Finset.sum_pair (by decide)]
  dsimp [chiSign]
  simp only [Int.cast_one, Int.cast_neg]
  ring

lemma opA_covariant : IsOpCovariant rhoZ2 opA chiSign := by
  intro u
  apply LinearMap.ext
  rintro ⟨x, y⟩
  ext <;> dsimp [linHom, rhoZ2, opA, chiSign] <;> rcases Int.units_eq_one_or u with rfl | rfl <;> simp

instance : Invertible ((Fintype.card (Units ℤ) : ℕ) : ℝ) where
  invOf := 1 / 2
  invOf_mul_self := by
    have hcard : Fintype.card (Units ℤ) = 2 := by
      decide
    rw [hcard]
    norm_num
  mul_invOf_self := by
    have hcard : Fintype.card (Units ℤ) = 2 := by
      decide
    rw [hcard]
    norm_num

theorem r2_averageMap_linHom_zero :
    (linHom rhoZ2 rhoZ2).averageMap opA = 0 :=
  averageMap_linHom_apply_eq_zero rhoZ2 opA_covariant chiSign_sum

theorem r2_P_phys_annihilation :
    (P_phys rhoZ2) ∘ₗ opA ∘ₗ (P_phys rhoZ2) = 0 :=
  P_phys_comp_A_comp_P_phys_eq_zero rhoZ2 opA_covariant chiSign_sum

/-- OpenGauss T16 non-commutativity witness on the operator algebra of ℝ × ℝ:
    opA (flip/Pauli X) and opZ (Pauli Z) do not commute. -/
theorem r2_operator_noncommutative :
    opA ∘ₗ opZ ≠ opZ ∘ₗ opA := by
  intro h
  have h1 : (opA ∘ₗ opZ) (1, 0) = (opZ ∘ₗ opA) (1, 0) := by
    rw [h]
  dsimp [opA, opZ] at h1
  injection h1 with _ h2
  linarith

end R2Witness

/-! ### Section 5: OpenGauss T16 Matrix Non-Commutativity Witness -/

section OpenGaussT16

abbrev RealMatrix := Matrix (Fin 2) (Fin 2) ℝ
def pauliX : RealMatrix := !![0, 1; 1, 0]
def pauliZ : RealMatrix := !![1, 0; 0, -1]

/-- OpenGauss T16 non-commutativity witness on Matrix (Fin 2) (Fin 2) ℝ. -/
theorem pauli_matrix_noncommutative :
    pauliX * pauliZ ≠ pauliZ * pauliX := by
  intro h
  have hh := congrArg (fun a : RealMatrix => a 0 1) h
  norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at hh

end OpenGaussT16

end InfoGeometry.OperatorAlgebra.ElitzurLatticeGaugeProjection
