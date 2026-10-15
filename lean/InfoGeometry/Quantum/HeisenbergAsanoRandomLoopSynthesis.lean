import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra
import InfoGeometry.Analysis.AsanoContractionNative
import InfoGeometry.Analysis.AsanoUnitDiskContractionBridge
import InfoGeometry.Analysis.AsanoLeeYangCircleBridge
import InfoGeometry.Quantum.LeeYangAsanoPoincareContraction
import InfoGeometry.Canonical.LeeYangAsanoFullReduction
import InfoGeometry.Canonical.LeeYangAsanoInductiveContraction

/-!
# Heisenberg–Asano–Tóth Random-Loop Synthesis

This module formalizes the six canonical mathematical archetypes synthesizing
quantum spin-$1/2$ Pauli algebra, Tóth's spin-exchange identity and random-loop
representation of the quantum Heisenberg ferromagnet, Asano–Ruelle polynomial
contractions, Lee–Yang unit-circle root localization, and macroscopic loop
spontaneous magnetization bounds, directly reusing and bridging the repository's
preexisting Pauli, Lee–Yang, and Asano–Ruelle owner modules:

1. **Archetype I (Quantum Spin-$1/2$ Pauli Matrices & Non-Commutativity)**:
   * Reuses `InfoGeometry.Algebra.FiniteSpin.Mat2C` and
     `InfoGeometry.Physics.ChiralPoincareSouriauBridge.{σ1, σ2, σ3}` (`pauliX`, `pauliY`, `pauliZ`)
   * `pauliX_sq`, `pauliY_sq`, `pauliZ_sq`, `pauliX_mul_pauliZ_ne_pauliZ_mul_pauliX`,
     `commutator_pauliX_pauliY`
2. **Archetype II (Two-Site Swap Operator $P_{12}$ & Tóth's Spin-Exchange Identity)**:
   * `spinSwapMatrix`, `tensor2`
   * `spinSwapMatrix_sq`, `trace_spinSwapMatrix`, `toth_pauli_exchange_identity`
3. **Archetype III (Tóth Random-Loop Partition Weights & Fugacity Polynomials)**:
   * `tothLoopWeight`, `tothLoopWeight_pos`, `tothLoopWeight_add`
   * `singleLoopFugacityFactor`, `configLoopPoly`
   * `singleLoopFugacityFactor_ne_zero_of_norm_lt_one`,
     `configLoopPoly_ne_zero_of_norm_lt_one`
4. **Archetype IV (Lee–Yang Reciprocal Spin-Flip Symmetry & Unit-Circle Localization)**:
   * `singleLoopFugacityFactor_inv`, `singleLoopFugacityFactor_zero_iff_inv_zero`,
     `singleLoopFugacityFactor_root_norm_eq_one`
   * `configLoopPoly_zero_iff_inv_zero`, `configLoopPoly_root_norm_eq_one`,
     `configLoopPoly_hasLeeYangProperty`, `configLoopPoly_inner_ball_zero_free`,
     `configLoopPoly_outer_ball_zero_free`, `configLoopPoly_root_to_critical_line`
5. **Archetype V (Asano–Ruelle Contraction & Multiaffine Inductive Zero-Free Stability)**:
   * `ferromagnetic_asanoContract_root_iff`,
     `ferromagnetic_asanoContract_root_on_unitCircle`,
     `ferromagnetic_asanoContract_ne_zero_in_openDisk`,
     `asano_rankOne_contracted_root_radius_bound`,
     `asano_full_contraction_root_mem_negProductSet`,
     `asano_multiaffine_inductive_step_root_mem_forbidden`
6. **Archetype VI (Macroscopic Loop Fraction & Spontaneous Magnetization Bound $m \ge S/4$)**:
   * `loopMagnetization`
   * `loopMagnetization_ge_quarter_spin`, `loopMagnetization_ge_eighth_of_spin_half`,
     `loopMagnetization_pos_of_spin_half`
-/

noncomputable section

namespace InfoGeometry.Quantum.HeisenbergAsanoRandomLoopSynthesis

open scoped BigOperators Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra
open InfoGeometry.Analysis.AsanoContractionNative
open InfoGeometry.Analysis.AsanoUnitDiskContraction
open InfoGeometry.Analysis.AsanoLeeYangCircle
open InfoGeometry.Quantum.LeeYangAsanoPoincareContraction
open InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoInduction
open InfoGeometry.Canonical.LeeYangAsanoNativeCore
open InfoGeometry.Canonical.LeeYangAsanoInductiveContraction

/-!
## Archetype I & II: Quantum Spin-1/2 Pauli Matrices, Swap Operator & Tóth's Identity
-/

/-- Two-site $4 \times 4$ complex spin-$1/2$ matrices indexed by `Fin 2 × Fin 2`. -/
abbrev TwoSiteMat4C := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Pauli $\sigma_x$ matrix, reusing `ChiralPoincareSouriauBridge.σ1`. -/
abbrev pauliX : Mat2C := σ1

/-- Pauli $\sigma_y$ matrix, reusing `ChiralPoincareSouriauBridge.σ2`. -/
abbrev pauliY : Mat2C := σ2

/-- Pauli $\sigma_z$ matrix, reusing `ChiralPoincareSouriauBridge.σ3`. -/
abbrev pauliZ : Mat2C := σ3

/-- Involutivity $\sigma_x^2 = I_2$, reusing `HestenesCuntzSpacetimeAlgebra.pauli_sigma1_sq`. -/
theorem pauliX_sq : pauliX * pauliX = (1 : Mat2C) := pauli_sigma1_sq

/-- Involutivity $\sigma_y^2 = I_2$, reusing `HestenesCuntzSpacetimeAlgebra.pauli_sigma2_sq`. -/
theorem pauliY_sq : pauliY * pauliY = (1 : Mat2C) := pauli_sigma2_sq

/-- Involutivity $\sigma_z^2 = I_2$, reusing `HestenesCuntzSpacetimeAlgebra.pauli_sigma3_sq`. -/
theorem pauliZ_sq : pauliZ * pauliZ = (1 : Mat2C) := pauli_sigma3_sq

/-- Quantum non-commutativity of Pauli spin operators: $\sigma_x \sigma_z \neq \sigma_z \sigma_x$. -/
theorem pauliX_mul_pauliZ_ne_pauliZ_mul_pauliX :
    pauliX * pauliZ ≠ pauliZ * pauliX := by
  intro h
  have h01 : (pauliX * pauliZ) 0 1 = (pauliZ * pauliX) 0 1 :=
    congr_fun (congr_fun h 0) 1
  have hL : (pauliX * pauliZ) 0 1 = -1 := by
    simp [pauliX, pauliZ, σ1, σ3, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : (pauliZ * pauliX) 0 1 = 1 := by
    simp [pauliX, pauliZ, σ1, σ3, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hL, hR] at h01
  norm_num at h01

/-- Canonical $\mathfrak{su}(2)$ Pauli commutator: $[\sigma_x, \sigma_y] = 2 i \sigma_z$. -/
theorem commutator_pauliX_pauliY :
    pauliX * pauliY - pauliY * pauliX = (2 * Complex.I) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, σ1, σ2, σ3] <;> ring

/-- Two-site spin permutation (swap) operator $P_{12}$ on $\mathbb{C}^2 \otimes \mathbb{C}^2$. -/
def spinSwapMatrix : TwoSiteMat4C :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- The two-site spin swap matrix is an involution: $P_{12}^2 = I_4$. -/
theorem spinSwapMatrix_sq :
    spinSwapMatrix * spinSwapMatrix = 1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    spinSwapMatrix, Matrix.one_apply, Prod.mk.injEq]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;> norm_num

/-- The trace of the two-site spin swap operator on $\mathbb{C}^2 \otimes \mathbb{C}^2$ is $2$,
corresponding to a single cycle of length $2$ in Tóth's loop trace formula $(2S+1)^c = 2^1$. -/
theorem trace_spinSwapMatrix :
    Matrix.trace spinSwapMatrix = 2 := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, spinSwapMatrix]
  norm_num

/-- Kronecker tensor product $A \otimes B$ of two $2 \times 2$ matrices on `Fin 2 × Fin 2`. -/
def tensor2 (A B : Mat2C) : TwoSiteMat4C :=
  fun p q => A p.1 q.1 * B p.2 q.2

/-- **Tóth's Fundamental Spin-Exchange Identity**:
$\sigma_x \otimes \sigma_x + \sigma_y \otimes \sigma_y + \sigma_z \otimes \sigma_z + I_4 = 2 P_{12}$,
expressing the quantum Heisenberg exchange interaction in terms of the permutation swap operator. -/
theorem toth_pauli_exchange_identity :
    tensor2 pauliX pauliX + tensor2 pauliY pauliY + tensor2 pauliZ pauliZ + (1 : TwoSiteMat4C) =
      (2 : ℂ) • spinSwapMatrix := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [tensor2, pauliX, pauliY, pauliZ, σ1, σ2, σ3, spinSwapMatrix, Complex.I_mul_I] <;>
    ring

/-!
## Archetype III & IV: Tóth Random-Loop Weights, Fugacity Polynomials & Lee–Yang Symmetry
-/

/-- Spin-trace multiplicity weight $(2S + 1)^c$ of a random-loop configuration with
`numCycles` closed permutation cycles. -/
def tothLoopWeight (twoS_plus_one : ℝ) (numCycles : ℕ) : ℝ :=
  twoS_plus_one ^ numCycles

/-- For any positive spin multiplicity $2S + 1 > 0$, the Tóth random-loop weight is strictly
positive, enabling a bona fide probabilistic loop measure. -/
theorem tothLoopWeight_pos {twoS_plus_one : ℝ} (hS : 0 < twoS_plus_one) (c : ℕ) :
    0 < tothLoopWeight twoS_plus_one c :=
  pow_pos hS c

/-- Multiplicativity of Tóth random-loop weights across disjoint cycle decompositions. -/
theorem tothLoopWeight_add (twoS_plus_one : ℝ) (c₁ c₂ : ℕ) :
    tothLoopWeight twoS_plus_one (c₁ + c₂) =
      tothLoopWeight twoS_plus_one c₁ * tothLoopWeight twoS_plus_one c₂ :=
  pow_add twoS_plus_one c₁ c₂

/-- Magnetic fugacity polynomial factor $1 + z^L$ of a single spin-1/2 loop of length $L$. -/
def singleLoopFugacityFactor (L : ℕ) (z : ℂ) : ℂ :=
  1 + z ^ L

/-- Configuration loop partition polynomial $\prod_{i} (1 + z^{L_i})$ over a finite family of
closed loops with lengths $L : \iota \to \mathbb{N}$. -/
def configLoopPoly {ι : Type*} [Fintype ι] (L : ι → ℕ) (z : ℂ) : ℂ :=
  ∏ i : ι, (1 + z ^ (L i))

/-- Elementary real power bound: if $0 \le r < 1$ and $L > 0$, then $r^L < 1$. -/
theorem real_pow_lt_one_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ {L : ℕ}, 0 < L → r ^ L < 1
  | 0, hL => False.elim (lt_irrefl 0 hL)
  | 1, _ => by simpa only [pow_one] using hr1
  | n + 2, _ => by
      have ih : r ^ (n + 1) < 1 := real_pow_lt_one_of_lt_one hr0 hr1 (Nat.succ_pos n)
      calc
        r ^ (n + 2) = r ^ (n + 1) * r := pow_succ r (n + 1)
        _ ≤ 1 * r := mul_le_mul_of_nonneg_right (le_of_lt ih) hr0
        _ < 1 := by linarith

/-- A single-loop fugacity factor $1 + z^L$ ($L > 0$) has no zeros in the open unit disk
$\|z\| < 1$. -/
theorem singleLoopFugacityFactor_ne_zero_of_norm_lt_one
    {L : ℕ} (hL : 0 < L) {z : ℂ} (hz : ‖z‖ < 1) :
    singleLoopFugacityFactor L z ≠ 0 := by
  intro hzero
  have hzL : z ^ L = -1 := by
    calc
      z ^ L = singleLoopFugacityFactor L z - 1 := by
        unfold singleLoopFugacityFactor
        ring
      _ = 0 - 1 := by rw [hzero]
      _ = -1 := by ring
  have hnorm_eq : ‖z‖ ^ L = 1 := by
    calc
      ‖z‖ ^ L = ‖z ^ L‖ := (norm_pow z L).symm
      _ = ‖(-1 : ℂ)‖ := by rw [hzL]
      _ = 1 := by simp
  have hnorm_lt : ‖z‖ ^ L < 1 :=
    real_pow_lt_one_of_lt_one (norm_nonneg z) hz hL
  linarith

/-- Any random-loop configuration partition polynomial $\prod_i (1 + z^{L_i})$ with positive cycle
lengths $L_i > 0$ is strictly non-vanishing on the open unit disk $\|z\| < 1$. -/
theorem configLoopPoly_ne_zero_of_norm_lt_one
    {ι : Type*} [Fintype ι] (L : ι → ℕ) (hL : ∀ i, 0 < L i)
    {z : ℂ} (hz : ‖z‖ < 1) :
    configLoopPoly L z ≠ 0 := by
  unfold configLoopPoly
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact singleLoopFugacityFactor_ne_zero_of_norm_lt_one (hL i) hz

/-- Reciprocal spin-flip identity ($z \mapsto z^{-1}$) for a single loop fugacity factor:
$1 + (z^{-1})^L = (z^{-1})^L (1 + z^L)$. -/
theorem singleLoopFugacityFactor_inv (L : ℕ) {z : ℂ} (hz : z ≠ 0) :
    singleLoopFugacityFactor L z⁻¹ = z⁻¹ ^ L * singleLoopFugacityFactor L z := by
  unfold singleLoopFugacityFactor
  have hzL : z ^ L ≠ 0 := pow_ne_zero L hz
  rw [inv_pow, mul_add, mul_one, inv_mul_cancel₀ hzL, add_comm]

/-- Lee–Yang reciprocal root invariance for a single loop fugacity factor ($z \neq 0$). -/
theorem singleLoopFugacityFactor_zero_iff_inv_zero (L : ℕ) {z : ℂ} (hz : z ≠ 0) :
    singleLoopFugacityFactor L z = 0 ↔ singleLoopFugacityFactor L z⁻¹ = 0 := by
  rw [singleLoopFugacityFactor_inv L hz]
  have h_inv_ne : z⁻¹ ^ L ≠ 0 := pow_ne_zero L (inv_ne_zero hz)
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with h_abs | h_zero
    · exact False.elim (h_inv_ne h_abs)
    · exact h_zero

/-- Every zero of the single-loop fugacity factor $1 + z^L = 0$ ($L > 0$) lies strictly on the
Lee–Yang unit circle $\|z\| = 1$. -/
theorem singleLoopFugacityFactor_root_norm_eq_one
    {L : ℕ} (hL : 0 < L) {z : ℂ} (hroot : singleLoopFugacityFactor L z = 0) :
    ‖z‖ = 1 := by
  rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
  · exact False.elim (singleLoopFugacityFactor_ne_zero_of_norm_lt_one hL hlt hroot)
  · exact heq
  · exfalso
    have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0, norm_zero] at hgt
      linarith
    have hroot_inv : singleLoopFugacityFactor L z⁻¹ = 0 :=
      (singleLoopFugacityFactor_zero_iff_inv_zero L hz0).mp hroot
    have h_inv_lt : ‖z⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hgt
    exact singleLoopFugacityFactor_ne_zero_of_norm_lt_one hL h_inv_lt hroot_inv

/-- Lee–Yang reciprocal root invariance for the multi-loop configuration polynomial. -/
theorem configLoopPoly_zero_iff_inv_zero
    {ι : Type*} [Fintype ι] (L : ι → ℕ) {z : ℂ} (hz : z ≠ 0) :
    configLoopPoly L z = 0 ↔ configLoopPoly L z⁻¹ = 0 := by
  unfold configLoopPoly
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  exact exists_congr fun i => singleLoopFugacityFactor_zero_iff_inv_zero (L i) hz

/-- Every zero of the multi-loop configuration polynomial $\prod_i (1 + z^{L_i}) = 0$ ($L_i > 0$)
lies strictly on the Lee–Yang unit circle $\|z\| = 1$. -/
theorem configLoopPoly_root_norm_eq_one
    {ι : Type*} [Fintype ι] (L : ι → ℕ) (hL : ∀ i, 0 < L i)
    {z : ℂ} (hroot : configLoopPoly L z = 0) :
    ‖z‖ = 1 := by
  unfold configLoopPoly at hroot
  rw [Finset.prod_eq_zero_iff] at hroot
  rcases hroot with ⟨i, _, hi⟩
  exact singleLoopFugacityFactor_root_norm_eq_one (hL i) hi

/-- The zero set of `configLoopPoly L` ($L_i > 0$) satisfies the repository's canonical
`HasLeeYangProperty` (`LeeYangAsanoPoincareContraction`). -/
theorem configLoopPoly_hasLeeYangProperty
    {ι : Type*} [Fintype ι] (L : ι → ℕ) (hL : ∀ i, 0 < L i) :
    HasLeeYangProperty {z : ℂ | configLoopPoly L z = 0} :=
  fun _ hz => configLoopPoly_root_norm_eq_one L hL hz

/-- Inner Poincaré ball zero-freeness for `configLoopPoly L`, deduced from
`LeeYangAsanoPoincareContraction.inner_ball_zero_free`. -/
theorem configLoopPoly_inner_ball_zero_free
    {ι : Type*} [Fintype ι] (L : ι → ℕ) (hL : ∀ i, 0 < L i) :
    ∀ z ∈ {w : ℂ | configLoopPoly L w = 0}, ¬ (‖z‖ < 1) :=
  inner_ball_zero_free _ (configLoopPoly_hasLeeYangProperty L hL)

/-- Outer Poincaré ball zero-freeness for `configLoopPoly L`, deduced from
`LeeYangAsanoPoincareContraction.outer_ball_zero_free`. -/
theorem configLoopPoly_outer_ball_zero_free
    {ι : Type*} [Fintype ι] (L : ι → ℕ) (hL : ∀ i, 0 < L i) :
    ∀ z ∈ {w : ℂ | configLoopPoly L w = 0}, ¬ (1 < ‖z‖) :=
  outer_ball_zero_free _ (configLoopPoly_hasLeeYangProperty L hL)

/-- Canonical Cayley transport of multi-loop partition roots ($z \neq -1$) to the critical line
$\operatorname{Re}(s) = 1/2$. -/
theorem configLoopPoly_root_to_critical_line
    {ι : Type*} [Fintype ι] (L : ι → ℕ) (hL : ∀ i, 0 < L i)
    {z : ℂ} (hroot : configLoopPoly L z = 0) (hz_ne : z ≠ -1) :
    (riemannCayleyInverse z).re = 1 / 2 :=
  partition_root_to_critical_line_of_disk_free_reciprocal_symmetry
    (fun _ hw => configLoopPoly_ne_zero_of_norm_lt_one L hL hw)
    (fun _ hw => configLoopPoly_zero_iff_inv_zero L hw)
    hroot hz_ne

/-!
## Archetype V: Asano–Ruelle Contraction & Multiaffine Inductive Zero-Free Stability
-/

/-- The ferromagnetic two-site Asano contraction `asanoContract 1 1 z = 1 + z` vanishes if and
only if $z = -1$. -/
theorem ferromagnetic_asanoContract_root_iff (z : ℂ) :
    asanoContract 1 1 z = 0 ↔ z = -1 := by
  unfold asanoContract
  constructor
  · intro h
    calc
      z = (1 + 1 * z) - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
  · rintro rfl
    ring

/-- The unique root of the ferromagnetic Asano contraction `asanoContract 1 1 z = 0` lies on the
Lee–Yang unit circle $\|z\| = 1$. -/
theorem ferromagnetic_asanoContract_root_on_unitCircle {z : ℂ}
    (hz : asanoContract 1 1 z = 0) :
    ‖z‖ = 1 := by
  rw [(ferromagnetic_asanoContract_root_iff z).mp hz]
  simp

/-- The ferromagnetic Asano contraction `asanoContract 1 1 z` is zero-free on the open unit disk
$\|z\| < 1$. -/
theorem ferromagnetic_asanoContract_ne_zero_in_openDisk {z : ℂ} (hz : ‖z‖ < 1) :
    asanoContract 1 1 z ≠ 0 := by
  intro h0
  have h1 : ‖z‖ = 1 := ferromagnetic_asanoContract_root_on_unitCircle h0
  linarith

/-- Rank-one Asano contraction root radius bound: if `asanoPoly A B C D` is zero-free outside
sets $K_1 \subseteq \text{closedDisk } r_1$ and $K_2 \subseteq \text{closedDisk } r_2$ ($r_1 \ge 0$)
with $0 \notin K_1, K_2$, then any rank-one contracted root satisfies $\|z\| \le r_1 r_2$. -/
theorem asano_rankOne_contracted_root_radius_bound
    {K₁ K₂ : Set ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) {A B C D z : ℂ}
    (hK₁ : K₁ ⊆ closedDisk r₁)
    (hK₂ : K₂ ⊆ closedDisk r₂)
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C = 0)
    (hzero : IsContractedZero A D z) :
    ‖z‖ ≤ r₁ * r₂ := by
  have hmem : z ∈ signedProductSet K₁ K₂ :=
    contracted_zero_mem_signedProduct_of_rankOne h0₁ h0₂ hzf hD hdet hzero
  rcases hmem with ⟨u, hu, v, hv, rfl⟩
  exact signedProduct_closedDisks_subset r₁ r₂ hr₁ ⟨u, hK₁ hu, v, hK₂ hv, rfl⟩

/-- **Full Two-Variable Asano–Ruelle Root Localization** (reusing
`LeeYangAsanoFullReduction.asano_contraction_full_of_topological_combined`):
For any closed forbidden sets $K_1, K_2 \subseteq \mathbb{C} \setminus \{0\}$ with at least one
bounded (including all rank-1 and non-degenerate $A D - B C \neq 0$ branches), if
`asanoPhi A B C D` is zero-free outside $K_1 \times K_2$ and $A + D z = 0$, then
$z \in - K_1 K_2$ (`negProductSet K₁ K₂`). -/
theorem asano_full_contraction_root_mem_negProductSet
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hBddOr : Bornology.IsBounded K₁ ∨ Bornology.IsBounded K₂)
    (hPhi : ∀ z₁ z₂ : ℂ, z₁ ∉ K₁ → z₂ ∉ K₂ → asanoPhi A B C D z₁ z₂ ≠ 0)
    (hroot : A + D * z = 0) :
    z ∈ negProductSet K₁ K₂ := by
  by_contra hzOff
  exact asano_contraction_full_of_topological_combined
    h0K₁ h0K₂ hClosed₁ hClosed₂ hBddOr hPhi hzOff hroot

/-- **Multiaffine $N$-Site Inductive Asano Contraction Root Localization** (reusing
`LeeYangAsanoInductiveContraction.asanoInductiveStep_closed_bounded`):
For any multiaffine polynomial $P(z_0, z_1, w_1, \dots, w_n)$ zero-free outside
$K_0 \times K_1 \times \prod_j K_j$, any root $z$ of the contracted polynomial
`(toTwoVar P w).contract z = 0` must lie in `asanoForbiddenSet (K (Sum.inl 0)) (K (Sum.inl 1))`. -/
theorem asano_multiaffine_inductive_step_root_mem_forbidden
    {n : ℕ}
    (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ)
    (hmulti : ∀ m ∈ P.support, ∀ i, (m i : ℕ) ≤ 1)
    (K : Fin 2 ⊕ Fin n → Set ℂ)
    (hzero : ∀ i, 0 ∉ K i)
    (hclosed₀ : IsClosed (K (Sum.inl 0)))
    (hclosed₁ : IsClosed (K (Sum.inl 1)))
    (hbdd : Bornology.IsBounded (K (Sum.inl 0)) ∨ Bornology.IsBounded (K (Sum.inl 1)))
    (hfree : ∀ z : Fin 2 ⊕ Fin n → ℂ, (∀ i, z i ∉ K i) → MvPolynomial.eval z P ≠ 0)
    (w : Fin n → ℂ)
    (hw : ∀ j, w j ∉ K (Sum.inr j))
    {z : ℂ}
    (hroot : (toTwoVar P w).contract z = 0) :
    z ∈ asanoForbiddenSet (K (Sum.inl 0)) (K (Sum.inl 1)) := by
  by_contra hzOff
  exact asanoInductiveStep_closed_bounded
    P hmulti K hzero hclosed₀ hclosed₁ hbdd hfree w hw z hzOff hroot

/-!
## Archetype VI: Macroscopic Loop Fraction & Spontaneous Magnetization Bound ($m \ge S/4$)
-/

/-- Spontaneous magnetization functional $m(S, \alpha) = S \alpha$ induced by a macroscopic
random-loop fraction $\alpha \in [0, 1]$ for spin quantum number $S$. -/
def loopMagnetization (S α : ℝ) : ℝ :=
  S * α

/-- When the macroscopic loop density satisfies $\alpha \ge 1/4$ and $S \ge 0$, the random-loop
spontaneous magnetization is bounded below by $S / 4$. -/
theorem loopMagnetization_ge_quarter_spin (S α : ℝ) (hS : 0 ≤ S) (hα : 1 / 4 ≤ α) :
    S / 4 ≤ loopMagnetization S α := by
  unfold loopMagnetization
  nlinarith

/-- For any quantum spin $S \ge 1/2$ and macroscopic loop fraction $\alpha \ge 1/4$, the
spontaneous magnetization satisfies the uniform positive lower bound $m \ge 1/8$. -/
theorem loopMagnetization_ge_eighth_of_spin_half (S α : ℝ) (hS : 1 / 2 ≤ S) (hα : 1 / 4 ≤ α) :
    1 / 8 ≤ loopMagnetization S α := by
  unfold loopMagnetization
  nlinarith

/-- Strict positivity of spontaneous magnetization ($m > 0$) whenever $S \ge 1/2$ and
macroscopic loop density $\alpha \ge 1/4$. -/
theorem loopMagnetization_pos_of_spin_half (S α : ℝ) (hS : 1 / 2 ≤ S) (hα : 1 / 4 ≤ α) :
    0 < loopMagnetization S α := by
  have h := loopMagnetization_ge_eighth_of_spin_half S α hS hα
  linarith

end InfoGeometry.Quantum.HeisenbergAsanoRandomLoopSynthesis
