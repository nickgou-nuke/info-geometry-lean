import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

noncomputable section

/-!
# Section 5.84: Quantum Fisher Information Metric (QFIM), SLD, and Bures Distance on the Null Cone

This module formalizes:
1. Associative quantum operator algebra with trace functional `QuantumAlgebra`:
   - Trace linearity and cyclicity: `Tr(A * B) = Tr(B * A)`.
   - Positive-semidefinite state expectation: `0 ≤ Tr(ρ * A * A)`.
2. Symmetric Logarithmic Derivative (SLD) system `QuantumSLDSystem`:
   - State derivative condition: `∂_μ ρ = (1/2) • (ρ * L_μ + L_μ * ρ)`.
3. The Quantum Fisher Information Metric:
   `g_{μν} = (1/2) * Tr(ρ * (L_μ * L_ν + L_ν * L_μ))`.
4. Master Theorem 1: Pairing equivalence `g_{μν} = Tr(∂_μ ρ * L_ν)`.
5. Master Theorem 2: Metric symmetry `g_{μν} = g_{νμ}`.
6. Master Theorem 3: Diagonal reduction `g_{μμ} = Tr(ρ * L_μ²)`.
7. Master Theorem 4: Diagonal non-negativity `0 ≤ g_{μμ}`.
8. Master Theorem 5: Bures metric quadratic expansion:
   `ds_B² = (1/4) * (g₀₀ (u⁰)² + 2 g₀₁ u⁰ u¹ + g₁₁ (u¹)²)`
9. Null-Cone Field Retrodiction `NullConeRetrodictionData`:
   - QFI scaling under Sachs optical expansion: `F_Q = (η V Δt) / (A₀ (d + d₀)²)`.
   - Cramér-Rao lower bound: `CRB = 1 / F_Q = (A₀ (d + d₀)²) / (η V Δt)`.
10. Master Theorem 6: Exact bound reciprocity `F_Q * CRB = 1`.
11. Master Theorem 7: Asymptotic variance collapse under volume scaling:
    `V ↦ k * V ⟹ CRB ↦ (1/k) * CRB`.
12. Master Certified Synthesis:
    `certified_quantum_fisher_null_cone_synthesis`.
-/

namespace InfoGeometry.Physics.QuantumFisherNullCone

/-- Abstract associative operator algebra with a cyclic trace functional. -/
structure QuantumAlgebra (V : Type*) [AddCommGroup V] [Module ℝ V] where
  mul : V → V → V
  mul_assoc : ∀ A B C, mul (mul A B) C = mul A (mul B C)
  mul_add : ∀ A B C, mul A (B + C) = mul A B + mul A C
  add_mul : ∀ A B C, mul (A + B) C = mul A C + mul B C
  smul_mul : ∀ (c : ℝ) (A B : V), mul (c • A) B = c • mul A B
  mul_smul : ∀ (c : ℝ) (A B : V), mul A (c • B) = c • mul A B
  tr : V → ℝ
  tr_add : ∀ A B, tr (A + B) = tr A + tr B
  tr_smul : ∀ (c : ℝ) (A : V), tr (c • A) = c * tr A
  tr_mul_comm : ∀ A B, tr (mul A B) = tr (mul B A)

namespace QuantumAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (alg : QuantumAlgebra V)

/-- Anti-commutator (Jordan product bracket): `{A, B} = A * B + B * A`. -/
def anticomm (A B : V) : V :=
  alg.mul A B + alg.mul B A

/-- Symmetric Jordan product: `(1/2) • {A, B}`. -/
def jordan (A B : V) : V :=
  (1 / 2 : ℝ) • alg.anticomm A B

end QuantumAlgebra

/-- Parameterized quantum density operator with its Symmetric Logarithmic Derivatives. -/
structure QuantumSLDSystem (V : Type*) [AddCommGroup V] [Module ℝ V] where
  alg : QuantumAlgebra V
  rho : V
  /-- State normalization: Tr(ρ) = 1 -/
  tr_rho : alg.tr rho = 1
  /-- Positivity of the state: for any Hermitian observable A, Tr(ρ A²) ≥ 0 -/
  pos : ∀ A, 0 ≤ alg.tr (alg.mul rho (alg.mul A A))
  /-- Partial derivatives of the state ∂_μ ρ along parameters μ ∈ Fin 2 -/
  drho : Fin 2 → V
  /-- Symmetric Logarithmic Derivative operators L_μ -/
  L : Fin 2 → V
  /-- Defining identity of the SLD: ∂_μ ρ = (1/2) • (ρ * L_μ + L_μ * ρ) -/
  sld_eq : ∀ i, drho i = (1 / 2 : ℝ) • (alg.mul rho (L i) + alg.mul (L i) rho)

namespace QuantumSLDSystem

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (sys : QuantumSLDSystem V)

/-- Quantum Fisher Information Metric tensor components:
    `g_{μν} = (1/2) * Tr(ρ * (L_μ * L_ν + L_ν * L_μ))`. -/
def qfim (i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * sys.alg.tr (sys.alg.mul sys.rho (sys.alg.mul (sys.L i) (sys.L j) + sys.alg.mul (sys.L j) (sys.L i)))

/-- **Master Theorem 1 (QFIM Derivative-SLD Pairing)**:
    The metric element equals the trace pairing of the state derivative and the SLD:
    `g_{μν} = Tr(∂_μ ρ * L_ν)`. -/
theorem qfim_eq_tr_drho_mul_L (i j : Fin 2) :
    sys.qfim i j = sys.alg.tr (sys.alg.mul (sys.drho i) (sys.L j)) := by
  dsimp [qfim]
  have hsld := sys.sld_eq i
  rw [hsld]
  rw [sys.alg.smul_mul]
  rw [sys.alg.tr_smul]
  have h_add := sys.alg.add_mul (sys.alg.mul sys.rho (sys.L i)) (sys.alg.mul (sys.L i) sys.rho) (sys.L j)
  rw [h_add]
  rw [sys.alg.tr_add]
  rw [sys.alg.mul_assoc sys.rho (sys.L i) (sys.L j)]
  rw [sys.alg.mul_assoc (sys.L i) sys.rho (sys.L j)]
  have h_comm : sys.alg.tr (sys.alg.mul (sys.L i) (sys.alg.mul sys.rho (sys.L j))) =
      sys.alg.tr (sys.alg.mul (sys.alg.mul sys.rho (sys.L j)) (sys.L i)) :=
    sys.alg.tr_mul_comm (sys.L i) (sys.alg.mul sys.rho (sys.L j))
  rw [h_comm]
  rw [sys.alg.mul_assoc sys.rho (sys.L j) (sys.L i)]
  have h_distrib := (sys.alg.mul_add sys.rho (sys.alg.mul (sys.L i) (sys.L j)) (sys.alg.mul (sys.L j) (sys.L i))).symm
  rw [← sys.alg.tr_add]
  rw [← h_distrib]

/-- **Master Theorem 2 (Symmetry of the QFIM)**:
    The Quantum Fisher Information Metric is strictly symmetric:
    `g_{μν} = g_{νμ}`. -/
theorem qfim_symmetric (i j : Fin 2) :
    sys.qfim i j = sys.qfim j i := by
  dsimp [qfim]
  rw [add_comm (sys.alg.mul (sys.L i) (sys.L j)) (sys.alg.mul (sys.L j) (sys.L i))]

/-- **Master Theorem 3 (Diagonal Reduction)**:
    The diagonal elements reduce to the unweighted expectation of the squared SLD:
    `g_{μμ} = Tr(ρ * L_μ²)`. -/
theorem qfim_diag_eq (i : Fin 2) :
    sys.qfim i i = sys.alg.tr (sys.alg.mul sys.rho (sys.alg.mul (sys.L i) (sys.L i))) := by
  dsimp [qfim]
  have h_two : sys.alg.mul (sys.L i) (sys.L i) + sys.alg.mul (sys.L i) (sys.L i) =
      (2 : ℝ) • (sys.alg.mul (sys.L i) (sys.L i)) := by
    rw [two_smul]
  rw [h_two]
  rw [sys.alg.mul_smul]
  rw [sys.alg.tr_smul]
  ring

/-- **Master Theorem 4 (Diagonal Non-Negativity)**:
    The diagonal QFIM metric elements are strictly non-negative:
    `0 ≤ g_{μμ}`. -/
theorem qfim_diag_nonneg (i : Fin 2) :
    0 ≤ sys.qfim i i := by
  rw [qfim_diag_eq]
  exact sys.pos (sys.L i)

/-- Infinitesimal Bures distance quadratic form:
    `ds_B²(u) = (1/4) * ∑_{i, j} g_{ij} uⁱ uʲ`. -/
def buresMetric (u : Fin 2 → ℝ) : ℝ :=
  (1 / 4 : ℝ) * (∑ i : Fin 2, ∑ j : Fin 2, sys.qfim i j * u i * u j)

/-- **Master Theorem 5 (Bures Quadratic Form Expansion)**:
    The Bures metric on a 2-parameter space expands into the canonical Riemannian form:
    `ds_B² = (1/4) * (g₀₀ (u⁰)² + 2 g₀₁ u⁰ u¹ + g₁₁ (u¹)²)` -/
theorem bures_expansion (u : Fin 2 → ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, sys.qfim i j * u i * u j) =
    sys.qfim 0 0 * (u 0) ^ 2 + 2 * sys.qfim 0 1 * (u 0) * (u 1) + sys.qfim 1 1 * (u 1) ^ 2 := by
  rw [Fin.sum_univ_two]
  simp only [Fin.sum_univ_two]
  have h_symm := sys.qfim_symmetric 1 0
  rw [h_symm]
  ring

end QuantumSLDSystem

/-- Physical parameters for field state retrodiction along the null cone. -/
structure NullConeRetrodictionData where
  A0 : ℝ
  volume : ℝ
  delta_t : ℝ
  efficiency : ℝ
  distance : ℝ
  offset : ℝ
  hA0_pos : 0 < A0
  hvol_pos : 0 < volume
  hdt_pos : 0 < delta_t
  heff_pos : 0 < efficiency
  hdist_pos : 0 < distance + offset

namespace NullConeRetrodictionData

variable (D : NullConeRetrodictionData)

/-- Total detected quanta from the volume integral over the backward null cone:
    `N = (η * V * Δt * A₀) / (d + d₀)²`. -/
def detectedQuanta : ℝ :=
  (D.efficiency * D.volume * D.delta_t * D.A0) / (D.distance + D.offset) ^ 2

/-- Quantum Fisher Information for the nuclear source activity A₀:
    `F_Q = N / A₀² = (η * V * Δt) / (A₀ * (d + d₀)²)`. -/
def qfiA0 : ℝ :=
  (D.efficiency * D.volume * D.delta_t) / (D.A0 * (D.distance + D.offset) ^ 2)

/-- Quantum Cramér-Rao lower bound on the estimator variance:
    `CRB = 1 / F_Q = (A₀ * (d + d₀)²) / (η * V * Δt)`. -/
def cramerRaoBound : ℝ :=
  (D.A0 * (D.distance + D.offset) ^ 2) / (D.efficiency * D.volume * D.delta_t)

theorem qfiA0_pos : 0 < D.qfiA0 := by
  dsimp [qfiA0]
  have h_num : 0 < D.efficiency * D.volume * D.delta_t :=
    mul_pos (mul_pos D.heff_pos D.hvol_pos) D.hdt_pos
  have h_dist_sq : 0 < (D.distance + D.offset) ^ 2 := by
    have := D.hdist_pos
    nlinarith
  have h_den : 0 < D.A0 * (D.distance + D.offset) ^ 2 :=
    mul_pos D.hA0_pos h_dist_sq
  exact div_pos h_num h_den

theorem cramerRaoBound_pos : 0 < D.cramerRaoBound := by
  dsimp [cramerRaoBound]
  have h_dist_sq : 0 < (D.distance + D.offset) ^ 2 := by
    have := D.hdist_pos
    nlinarith
  have h_num : 0 < D.A0 * (D.distance + D.offset) ^ 2 :=
    mul_pos D.hA0_pos h_dist_sq
  have h_den : 0 < D.efficiency * D.volume * D.delta_t :=
    mul_pos (mul_pos D.heff_pos D.hvol_pos) D.hdt_pos
  exact div_pos h_num h_den

/-- **Master Theorem 6 (Exact Quantum Information Reciprocity)**:
    The product of the QFI and the Cramér-Rao lower bound is identically 1:
    `F_Q * CRB = 1`. -/
theorem qfi_mul_crb_eq_one :
    D.qfiA0 * D.cramerRaoBound = 1 := by
  dsimp [qfiA0, cramerRaoBound]
  have h_num_pos : 0 < D.efficiency * D.volume * D.delta_t :=
    mul_pos (mul_pos D.heff_pos D.hvol_pos) D.hdt_pos
  have h_dist_sq : 0 < (D.distance + D.offset) ^ 2 := by
    have := D.hdist_pos
    nlinarith
  have h_den_pos : 0 < D.A0 * (D.distance + D.offset) ^ 2 :=
    mul_pos D.hA0_pos h_dist_sq
  have h_num_ne : D.efficiency * D.volume * D.delta_t ≠ 0 := ne_of_gt h_num_pos
  have h_den_ne : D.A0 * (D.distance + D.offset) ^ 2 ≠ 0 := ne_of_gt h_den_pos
  rw [div_mul_div_comm, mul_comm (D.A0 * (D.distance + D.offset) ^ 2),
      div_self (mul_ne_zero h_num_ne h_den_ne)]

/-- Rescaling the detector volume by a factor `k > 0`: `V ↦ k * V`. -/
def rescaleVolume (k : ℝ) (hk_pos : 0 < k) : NullConeRetrodictionData where
  A0 := D.A0
  volume := k * D.volume
  delta_t := D.delta_t
  efficiency := D.efficiency
  distance := D.distance
  offset := D.offset
  hA0_pos := D.hA0_pos
  hvol_pos := mul_pos hk_pos D.hvol_pos
  hdt_pos := D.hdt_pos
  heff_pos := D.heff_pos
  hdist_pos := D.hdist_pos

/-- **Master Theorem 7 (Asymptotic Variance Collapse under Volume Scaling)**:
    Scaling the detector volume by `k` compresses the Cramér-Rao uncertainty bound by `1/k`:
    `CRB(k * V) = (1/k) * CRB(V)`.
    As `V → ∞`, the lower bound on retrodiction error vanishes strictly. -/
theorem crb_volume_scaling (k : ℝ) (hk_pos : 0 < k) :
    (D.rescaleVolume k hk_pos).cramerRaoBound = (1 / k) * D.cramerRaoBound := by
  dsimp [cramerRaoBound, rescaleVolume]
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  have h_den_ne : D.efficiency * D.volume * D.delta_t ≠ 0 := by
    have : 0 < D.efficiency * D.volume * D.delta_t :=
      mul_pos (mul_pos D.heff_pos D.hvol_pos) D.hdt_pos
    exact ne_of_gt this
  field_simp [hk_ne, h_den_ne]

end NullConeRetrodictionData

/-- **Certified Master Synthesis for Quantum Fisher Null Cone Retrodiction (Section 5.84)** -/
theorem certified_quantum_fisher_null_cone_synthesis
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (sys : QuantumSLDSystem V)
    (u : Fin 2 → ℝ)
    (D : NullConeRetrodictionData)
    (k : ℝ) (hk_pos : 0 < k) :
    (sys.qfim 0 1 = sys.alg.tr (sys.alg.mul (sys.drho 0) (sys.L 1))) ∧
    (sys.qfim 0 1 = sys.qfim 1 0) ∧
    (sys.qfim 0 0 = sys.alg.tr (sys.alg.mul sys.rho (sys.alg.mul (sys.L 0) (sys.L 0)))) ∧
    (0 ≤ sys.qfim 0 0) ∧
    ((∑ i : Fin 2, ∑ j : Fin 2, sys.qfim i j * u i * u j) =
      sys.qfim 0 0 * (u 0) ^ 2 + 2 * sys.qfim 0 1 * (u 0) * (u 1) + sys.qfim 1 1 * (u 1) ^ 2) ∧
    (D.qfiA0 * D.cramerRaoBound = 1) ∧
    ((D.rescaleVolume k hk_pos).cramerRaoBound = (1 / k) * D.cramerRaoBound) := by
  refine ⟨sys.qfim_eq_tr_drho_mul_L 0 1,
          sys.qfim_symmetric 0 1,
          sys.qfim_diag_eq 0,
          sys.qfim_diag_nonneg 0,
          sys.bures_expansion u,
          D.qfi_mul_crb_eq_one,
          D.crb_volume_scaling k hk_pos⟩

end InfoGeometry.Physics.QuantumFisherNullCone
