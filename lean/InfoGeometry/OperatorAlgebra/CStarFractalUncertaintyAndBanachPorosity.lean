/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset
import InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# InfoGeometry.OperatorAlgebra.CStarFractalUncertaintyAndBanachPorosity

Kernel-checked C*-algebraic operator-norm fractal uncertainty principle (`h^β` polynomial decay via
`ν`-porosity), Berezin–Toeplitz all-powers norm isometry, Banach Newton–Peirce healing of
noncommuting porous compressions `porousSymCompress P Q`, and explicit Pythagorean `Mat2C`
(`Matrix (Fin 2) (Fin 2) ℂ`) L2-operator witnesses.

## Three-Bucket Audit Map

* **BUCKET 1 (Reused upstream owners)**:
  - `InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset`:
    `biCompress`, `porousSymCompress`, `rangeProj`, `berezinOp`, `toeplitzOp`,
    `multiscaleLoc`, `toeplitzOp_pow_succ`, `porousSymCompress_variance_and_idempotencyDefect`,
    `peircePlus2`, `weylSigma`.
  - `InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence`:
    `idempotencyDefect`, `newtonPeirceStep`, `banach_newtonPeirce_limit_idempotent_and_intertwiner`,
    `idempotencyDefect_eq_zero_iff`.
  - Mathlib `CStarRing` (`CStarRing.norm_star_mul_self`, `CStarRing.norm_one`,
    `CStarRing.norm_mem_unitary_mul`, `CStarRing.norm_mul_mem_unitary`) and
    `Matrix.Norms.L2Operator` (`Matrix.instCStarRing`, `Matrix.l2_opNorm_diagonal`).
* **BUCKET 2 (New native theorems)**:
  - Self-adjoint projection norm rigidity (`‖P‖ = 0 ∨ ‖P‖ = 1`), bi-compression `C*`-norm
    identities, and exact all-powers Berezin–Toeplitz norm isometry
    `‖toeplitzOp V S ^ (n + 1)‖ = ‖berezinOp V S ^ (n + 1)‖`.
  - Multiscale `ν`-porosity (`IsNuPorousDefect`), Hilbert-space escape lower bound bridge,
    exponential operator decay, logarithmic fractal uncertainty exponent `fupExponent ν M > 0`,
    polynomial `((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2))` decay, and strong convergence
    `multiscaleLoc L m → 0`.
  - `C*`-commutator bound `‖idempotencyDefect (porousSymCompress P Q)‖ = ‖⁅P, Q⁆ * P‖ ^ 2 ≤ ‖⁅P, Q⁆‖ ^ 2`
    and complete Banach Newton–Peirce healing preserving self-adjointness and corner support
    `P * e = e ∧ e * P = e`.
  - Concrete noncommuting Pythagorean `Mat2C` witnesses exhibiting both `ν = 25/169` multiscale FUP
    decay to `0` and sharp Newton–Peirce corner healing bifurcation (`pythQ12_5 → peircePlus2` vs
    `pythQ5_12 → 0`).
* **BUCKET 3 (Explicitly isolated parameters & open analytic continuation)**:
  - Infinite-dimensional harmonic/Fourier Bourgain–Dyatlov porosity estimates producing
    `IsNuPorousDefect` from continuous Cantor-set geometry remain explicit theorem hypotheses.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.CStarFractalUncertaintyAndBanachPorosity

open InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
open InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset
open InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.MetaCompiler

section ScalarHelpers

private theorem scalar_mul_self_eq_self_iff {r : ℝ} (hr : r * r = r) :
    r = 0 ∨ r = 1 := by
  have hfac : r * (r - 1) = 0 := by nlinarith [hr]
  rcases mul_eq_zero.mp hfac with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem scalar_sq_mul_le_self_of_le_one {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha1 : a ≤ 1) (hc1 : c ≤ 1) :
    a * b * c ≤ b := by
  have hab : a * b ≤ b := by nlinarith [ha, hb, ha1]
  have hab_nn : 0 ≤ a * b := mul_nonneg ha hb
  nlinarith [hab, hab_nn, hc, hc1]

private theorem scalar_one_sub_nonneg_of_lt_one {ν : ℝ} (hν1 : ν < 1) : 0 ≤ 1 - ν := by
  linarith [hν1]

private theorem scalar_one_sub_lt_one_of_pos {ν : ℝ} (hν0 : 0 < ν) : 1 - ν < 1 := by
  linarith [hν0]

private theorem scalar_mul_pow_le {a b x y : ℝ}
    (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hax : a ≤ x) (hby : b ≤ y) : a * b ≤ x * y := by
  calc a * b
    _ ≤ x * b := mul_le_mul_of_nonneg_right hax hb
    _ ≤ x * y := mul_le_mul_of_nonneg_left hby hx

private theorem scalar_sq_le_sq_of_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith [ha, hab]

private theorem scalar_sq_lt_sixth_of_le_third {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 3) : c ^ 2 < 1 / 6 := by
  nlinarith [hc0, hc]

private theorem scalar_newton_poly_one_sub (r : ℝ) :
    1 - (3 * r * r - 2 * r * r * r) = (1 - r) ^ 2 * (3 - 2 * (1 - r)) := by
  ring

private theorem scalar_newton_poly_zero (r : ℝ) :
    3 * r * r - 2 * r * r * r = r ^ 2 * (3 - 2 * r) := by
  ring

private theorem scalar_newton_residual_step {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 3) :
    0 ≤ d ^ 2 * (3 - 2 * d) ∧ d ^ 2 * (3 - 2 * d) ≤ 1 / 3 := by
  constructor <;> nlinarith [hd0, hd1]

private theorem scalar_log_inv_one_sub_pos {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) :
    0 < Real.log (1 / (1 - ν)) := by
  have hpos : 0 < 1 - ν := by linarith [hν1]
  have hlt : 1 - ν < 1 := by linarith [hν0]
  have hgt : 1 < 1 / (1 - ν) := one_lt_one_div hpos hlt
  exact Real.log_pos hgt

private theorem scalar_log_nat_pos {M : ℕ} (hM : 2 ≤ M) : 0 < Real.log (M : ℝ) := by
  have hM1 : (1 : ℝ) < (M : ℝ) := by
    have : (1 : ℕ) < M := lt_of_lt_of_le (by norm_num) hM
    exact_mod_cast this
  exact Real.log_pos hM1

private theorem scalar_rpow_neg_fup_eq_one_sub_pow
    {ν : ℝ} (hν1 : ν < 1) {M : ℕ} (hM : 2 ≤ M) (m : ℕ) :
    ((M : ℝ) ^ m) ^ (-(Real.log (1 / (1 - ν)) / Real.log M)) = (1 - ν) ^ m := by
  have hpos : 0 < 1 - ν := by linarith [hν1]
  have hM0 : 0 < (M : ℝ) := by
    have : 0 < M := lt_of_lt_of_le (by norm_num) hM
    exact_mod_cast this
  have hMm_pos : 0 < (M : ℝ) ^ m := pow_pos hM0 m
  have hlogM_ne : Real.log (M : ℝ) ≠ 0 := (scalar_log_nat_pos hM).ne'
  rw [Real.rpow_def_of_pos hMm_pos, Real.log_pow, one_div, Real.log_inv]
  have harg :
      ((m : ℝ) * Real.log (M : ℝ)) * -((-Real.log (1 - ν)) / Real.log (M : ℝ)) =
        Real.log (1 - ν) * (m : ℝ) := by
    field_simp [hlogM_ne]
  rw [harg]
  calc Real.exp (Real.log (1 - ν) * (m : ℝ))
    _ = ((1 - ν) ^ (m : ℝ)) := (Real.rpow_def_of_pos hpos (m : ℝ)).symm
    _ = (1 - ν) ^ m := Real.rpow_natCast (1 - ν) m

private theorem scalar_rpow_neg_half_fup_sq
    {ν : ℝ} (hν1 : ν < 1) {M : ℕ} (hM : 2 ≤ M) (m : ℕ) :
    (((M : ℝ) ^ m) ^ (-(Real.log (1 / (1 - ν)) / Real.log M / 2))) ^ 2 = (1 - ν) ^ m := by
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMm_nn : 0 ≤ (M : ℝ) ^ m := pow_nonneg hM0 m
  rw [← Real.rpow_natCast (((M : ℝ) ^ m) ^ (-(Real.log (1 / (1 - ν)) / Real.log M / 2))) 2,
    ← Real.rpow_mul hMm_nn]
  have h2 :
      (-(Real.log (1 / (1 - ν)) / Real.log M / 2)) * ((2 : ℕ) : ℝ) =
        -(Real.log (1 / (1 - ν)) / Real.log M) := by
    push_cast
    ring
  rw [h2]
  exact scalar_rpow_neg_fup_eq_one_sub_pow hν1 hM m

end ScalarHelpers

/-! ## Section 1: C*-Algebraic Bi-Compressions & Berezin–Toeplitz All-Powers Norm Isometry -/

section CStarBiCompressionAndBerezinToeplitz

/-- Every self-adjoint idempotent `P` in a `C*`-ring has operator norm equal to `0` or `1`. -/
theorem norm_sa_idempotent_eq_zero_or_one
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    {P : B} (hPp : P * P = P) (hPs : star P = P) :
    ‖P‖ = 0 ∨ ‖P‖ = 1 := by
  have hmul : ‖P‖ * ‖P‖ = ‖P‖ := by
    calc ‖P‖ * ‖P‖
      _ = ‖star P * P‖ := (CStarRing.norm_star_mul_self (x := P)).symm
      _ = ‖P * P‖ := by rw [hPs]
      _ = ‖P‖ := by rw [hPp]
  exact scalar_mul_self_eq_self_iff hmul

/-- Every self-adjoint idempotent in a `C*`-ring has operator norm at most `1`. -/
theorem norm_sa_idempotent_le_one
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    {P : B} (hPp : P * P = P) (hPs : star P = P) :
    ‖P‖ ≤ 1 := by
  rcases norm_sa_idempotent_eq_zero_or_one hPp hPs with h0 | h1
  · linarith
  · linarith

/-- Any nonzero self-adjoint idempotent in a `C*`-ring has operator norm strictly equal to `1`. -/
theorem norm_sa_idempotent_eq_one
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    {P : B} (hPp : P * P = P) (hPs : star P = P) (hPne : P ≠ 0) :
    ‖P‖ = 1 := by
  rcases norm_sa_idempotent_eq_zero_or_one hPp hPs with h0 | h1
  · exfalso; exact hPne (norm_eq_zero.mp h0)
  · exact h1

/-- Self-adjoint idempotent rigidity: any self-adjoint idempotent of norm strictly less than `1`
must vanish identically. -/
theorem eq_zero_of_sa_idempotent_norm_lt_one
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    {P : B} (hPp : P * P = P) (hPs : star P = P) (hPlt : ‖P‖ < 1) :
    P = 0 := by
  rcases norm_sa_idempotent_eq_zero_or_one hPp hPs with h0 | h1
  · exact norm_eq_zero.mp h0
  · exfalso; linarith [hPlt, h1]

/-- Exact `C*`-identity for the noncommutative bi-compression `biCompress P_Ω U P_T`. -/
theorem norm_biCompress_sq_eq
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    (P_Ω U P_T : B) :
    ‖biCompress P_Ω U P_T‖ ^ 2 =
      ‖star P_T * star U * star P_Ω * P_Ω * U * P_T‖ := by
  rw [sq, ← CStarRing.norm_star_mul_self (x := biCompress P_Ω U P_T)]
  dsimp [biCompress]
  rw [star_mul, star_mul]
  congr 1
  noncomm_ring

/-- For a self-adjoint idempotent `P_Ω` and self-adjoint `P_T` in a unital `C*`-ring, the squared
bi-compression norm equals the norm of `porousSymCompress P_T (star U * P_Ω * U)`. -/
theorem norm_biCompress_sq_eq_porousSymCompress
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    {P_Ω P_T : B} (U : B)
    (hΩp : P_Ω * P_Ω = P_Ω) (hΩs : star P_Ω = P_Ω)
    (hTs : star P_T = P_T) :
    ‖biCompress P_Ω U P_T‖ ^ 2 = ‖porousSymCompress P_T (star U * P_Ω * U)‖ := by
  rw [norm_biCompress_sq_eq, hΩs, hTs]
  have hsimp : P_T * star U * P_Ω * P_Ω * U * P_T = P_T * (star U * P_Ω * U) * P_T := by
    calc P_T * star U * P_Ω * P_Ω * U * P_T
      _ = P_T * star U * (P_Ω * P_Ω) * U * P_T := by noncomm_ring
      _ = P_T * star U * P_Ω * U * P_T := by rw [hΩp]
      _ = P_T * (star U * P_Ω * U) * P_T := by noncomm_ring
  rw [hsimp]
  dsimp [porousSymCompress]

/-- Bi-compression between self-adjoint idempotents never increases operator norm. -/
theorem norm_biCompress_le_of_sa_idempotents
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    {P_Ω P_T : B} (U : B)
    (hΩp : P_Ω * P_Ω = P_Ω) (hΩs : star P_Ω = P_Ω)
    (hTp : P_T * P_T = P_T) (hTs : star P_T = P_T) :
    ‖biCompress P_Ω U P_T‖ ≤ ‖U‖ := by
  have hΩ1 : ‖P_Ω‖ ≤ 1 := norm_sa_idempotent_le_one hΩp hΩs
  have hT1 : ‖P_T‖ ≤ 1 := norm_sa_idempotent_le_one hTp hTs
  dsimp [biCompress]
  have hmul1 : ‖P_Ω * U * P_T‖ ≤ ‖P_Ω * U‖ * ‖P_T‖ := norm_mul_le (P_Ω * U) P_T
  have hmul2 : ‖P_Ω * U‖ ≤ ‖P_Ω‖ * ‖U‖ := norm_mul_le P_Ω U
  have hmul3 : ‖P_Ω * U‖ * ‖P_T‖ ≤ (‖P_Ω‖ * ‖U‖) * ‖P_T‖ :=
    mul_le_mul_of_nonneg_right hmul2 (norm_nonneg P_T)
  have hmul4 : ‖P_Ω‖ * ‖U‖ * ‖P_T‖ ≤ ‖U‖ :=
    scalar_sq_mul_le_self_of_le_one (norm_nonneg P_Ω) (norm_nonneg U) (norm_nonneg P_T) hΩ1 hT1
  exact hmul1.trans (hmul3.trans hmul4)

/-- Every isometry `V` (`star V * V = 1`) in a nontrivial unital `C*`-ring has unit norm `‖V‖ = 1`. -/
theorem norm_eq_one_of_star_mul_self_eq_one
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [Nontrivial B]
    {V : B} (hV : star V * V = 1) :
    ‖V‖ = 1 := by
  have hsq : ‖V‖ * ‖V‖ = 1 := by
    calc ‖V‖ * ‖V‖
      _ = ‖star V * V‖ := (CStarRing.norm_star_mul_self (x := V)).symm
      _ = ‖(1 : B)‖ := by rw [hV]
      _ = 1 := CStarRing.norm_one
  have hge : 0 ≤ ‖V‖ := norm_nonneg V
  nlinarith

/-- Conjugation by an isometry `V` (`star V * V = 1`) is an exact operator-norm isometry on all
elements `Y : B`. -/
theorem norm_isometry_conj_eq
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [Nontrivial B]
    {V : B} (hV : star V * V = 1) (Y : B) :
    ‖V * Y * star V‖ = ‖Y‖ := by
  have hVn : ‖V‖ = 1 := norm_eq_one_of_star_mul_self_eq_one hV
  have hsVn : ‖star V‖ = 1 := by rw [norm_star, hVn]
  have hle : ‖V * Y * star V‖ ≤ ‖Y‖ := by
    have h1 : ‖V * Y * star V‖ ≤ ‖V * Y‖ * ‖star V‖ := norm_mul_le (V * Y) (star V)
    have h2 : ‖V * Y‖ ≤ ‖V‖ * ‖Y‖ := norm_mul_le V Y
    have h3 : ‖V * Y‖ * ‖star V‖ ≤ (‖V‖ * ‖Y‖) * ‖star V‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg (star V))
    have h4 : (‖V‖ * ‖Y‖) * ‖star V‖ = ‖Y‖ := by rw [hVn, hsVn, one_mul, mul_one]
    exact h1.trans (h3.trans h4.le)
  have hge : ‖Y‖ ≤ ‖V * Y * star V‖ := by
    have hid : star V * (V * Y * star V) * V = Y := by
      calc star V * (V * Y * star V) * V
        _ = (star V * V) * Y * (star V * V) := by noncomm_ring
        _ = 1 * Y * 1 := by rw [hV]
        _ = Y := by rw [one_mul, mul_one]
    have h1 : ‖star V * (V * Y * star V) * V‖ ≤ ‖star V * (V * Y * star V)‖ * ‖V‖ :=
      norm_mul_le _ V
    have h2 : ‖star V * (V * Y * star V)‖ ≤ ‖star V‖ * ‖V * Y * star V‖ := norm_mul_le _ _
    have h3 : ‖star V * (V * Y * star V)‖ * ‖V‖ ≤ (‖star V‖ * ‖V * Y * star V‖) * ‖V‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg V)
    have h4 : (‖star V‖ * ‖V * Y * star V‖) * ‖V‖ = ‖V * Y * star V‖ := by
      rw [hsVn, hVn, one_mul, mul_one]
    rw [hid] at h1
    exact h1.trans (h3.trans h4.le)
  exact le_antisymm hle hge

/-- **Exact Berezin–Toeplitz All-Powers Norm Isometry**:
for any isometry `V` (`star V * V = 1`) and arbitrary symbol `S` in a nontrivial unital `C*`-ring,
every positive power of the compressed Toeplitz operator `toeplitzOp V S` has the exact same
operator norm as the corresponding power of its Berezin symbol `berezinOp V S`. -/
theorem norm_toeplitzOp_pow_eq_berezinOp_pow
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [Nontrivial B]
    {V : B} (hV : star V * V = 1) (S : B) (n : ℕ) :
    ‖toeplitzOp V S ^ (n + 1)‖ = ‖berezinOp V S ^ (n + 1)‖ := by
  rw [toeplitzOp_pow_succ hV n, norm_isometry_conj_eq hV (berezinOp V S ^ (n + 1))]

/-- Bi-compression of an isometry `U` between self-adjoint idempotents is a contraction (`≤ 1`). -/
theorem norm_biCompress_le_one_of_isometry
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [Nontrivial B]
    {P_Ω U P_T : B}
    (hΩp : P_Ω * P_Ω = P_Ω) (hΩs : star P_Ω = P_Ω)
    (hTp : P_T * P_T = P_T) (hTs : star P_T = P_T)
    (hU : star U * U = 1) :
    ‖biCompress P_Ω U P_T‖ ≤ 1 := by
  have h1 : ‖biCompress P_Ω U P_T‖ ≤ ‖U‖ :=
    norm_biCompress_le_of_sa_idempotents U hΩp hΩs hTp hTs
  have h2 : ‖U‖ = 1 := norm_eq_one_of_star_mul_self_eq_one hU
  exact h1.trans h2.le

end CStarBiCompressionAndBerezinToeplitz

/-! ## Section 2: C*-Operator Fractal Uncertainty Principle (`ν`-Porosity → `h^β` Decay) -/

section CStarFractalUncertainty

/-- Operator-norm `ν`-porosity hypothesis on a multiscale localized step family `L : ℕ → B`:
at every scale `k`, the compressed survival form `star (L k) * L k` drops by at least `ν ∈ [0, 1)`. -/
def IsNuPorousDefect {B : Type*} [NormedRing B] [StarRing B] (L : ℕ → B) (ν : ℝ) : Prop :=
  0 ≤ ν ∧ ν < 1 ∧ ∀ k : ℕ, ‖star (L k) * L k‖ ≤ 1 - ν

/-- Bourgain–Dyatlov logarithmic fractal uncertainty exponent `β = log (1 / (1 - ν)) / log M` for
branching factor `M ≥ 2` and porosity parameter `ν ∈ (0, 1)`. -/
noncomputable def fupExponent (ν : ℝ) (M : ℕ) : ℝ :=
  Real.log (1 / (1 - ν)) / Real.log M

/-- Strictly positive FUP exponent `fupExponent ν M > 0` whenever `ν ∈ (0, 1)` and `M ≥ 2`. -/
theorem fupExponent_pos {ν : ℝ} {M : ℕ} (hν0 : 0 < ν) (hν1 : ν < 1) (hM : 2 ≤ M) :
    0 < fupExponent ν M := by
  dsimp [fupExponent]
  exact div_pos (scalar_log_inv_one_sub_pos hν0 hν1) (scalar_log_nat_pos hM)

/-- Every `ν`-porous step has operator norm at most `Real.sqrt (1 - ν)`. -/
theorem norm_step_le_sqrt_of_isNuPorousDefect
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    {L : ℕ → B} {ν : ℝ} (hPor : IsNuPorousDefect L ν) (k : ℕ) :
    ‖L k‖ ≤ Real.sqrt (1 - ν) := by
  have hsq : ‖L k‖ ^ 2 ≤ 1 - ν := by
    calc ‖L k‖ ^ 2
      _ = ‖L k‖ * ‖L k‖ := sq (‖L k‖)
      _ = ‖star (L k) * L k‖ := (CStarRing.norm_star_mul_self (x := L k)).symm
      _ ≤ 1 - ν := hPor.2.2 k
  exact Real.le_sqrt_of_sq_le hsq

/-- **Multiscale Exponential `ν`-Porosity Contraction**:
under `IsNuPorousDefect L ν`, the multiscale product `multiscaleLoc L m` satisfies exponential
decay `‖multiscaleLoc L m‖ ^ 2 ≤ (1 - ν) ^ m`, `‖star (multiscaleLoc L m) * multiscaleLoc L m‖ ≤ (1 - ν) ^ m`,
and `‖multiscaleLoc L m‖ ≤ (Real.sqrt (1 - ν)) ^ m`. -/
theorem norm_multiscaleLoc_decay_of_isNuPorousDefect
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [Nontrivial B]
    {L : ℕ → B} {ν : ℝ} (hPor : IsNuPorousDefect L ν) (m : ℕ) :
    ‖multiscaleLoc L m‖ ≤ (Real.sqrt (1 - ν)) ^ m ∧
    ‖multiscaleLoc L m‖ ^ 2 ≤ (1 - ν) ^ m ∧
    ‖star (multiscaleLoc L m) * multiscaleLoc L m‖ ≤ (1 - ν) ^ m := by
  have hr_nn : 0 ≤ 1 - ν := scalar_one_sub_nonneg_of_lt_one hPor.2.1
  have hsqrt_nn : 0 ≤ Real.sqrt (1 - ν) := Real.sqrt_nonneg (1 - ν)
  have hlin : ‖multiscaleLoc L m‖ ≤ (Real.sqrt (1 - ν)) ^ m := by
    induction m with
    | zero =>
        simp only [multiscaleLoc, pow_zero, CStarRing.norm_one, le_refl]
    | succ m ih =>
        have hstep : ‖L m‖ ≤ Real.sqrt (1 - ν) := norm_step_le_sqrt_of_isNuPorousDefect hPor m
        calc ‖multiscaleLoc L (m + 1)‖
          _ = ‖L m * multiscaleLoc L m‖ := by simp only [multiscaleLoc]
          _ ≤ ‖L m‖ * ‖multiscaleLoc L m‖ := norm_mul_le (L m) (multiscaleLoc L m)
          _ ≤ Real.sqrt (1 - ν) * (Real.sqrt (1 - ν)) ^ m :=
              scalar_mul_pow_le (norm_nonneg (multiscaleLoc L m))
                hsqrt_nn hstep ih
          _ = (Real.sqrt (1 - ν)) ^ (m + 1) := by rw [pow_succ']
  have hsq : ‖multiscaleLoc L m‖ ^ 2 ≤ (1 - ν) ^ m := by
    have hsq1 : ‖multiscaleLoc L m‖ ^ 2 ≤ ((Real.sqrt (1 - ν)) ^ m) ^ 2 :=
      scalar_sq_le_sq_of_nonneg (norm_nonneg (multiscaleLoc L m)) hlin
    have hsq2 : ((Real.sqrt (1 - ν)) ^ m) ^ 2 = (1 - ν) ^ m := by
      rw [← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt hr_nn]
    exact hsq1.trans hsq2.le
  have hstar : ‖star (multiscaleLoc L m) * multiscaleLoc L m‖ ≤ (1 - ν) ^ m := by
    calc ‖star (multiscaleLoc L m) * multiscaleLoc L m‖
      _ = ‖multiscaleLoc L m‖ * ‖multiscaleLoc L m‖ := CStarRing.norm_star_mul_self
      _ = ‖multiscaleLoc L m‖ ^ 2 := (sq _).symm
      _ ≤ (1 - ν) ^ m := hsq
  exact ⟨hlin, hsq, hstar⟩

/-- **Semiclassical `h^β` Fractal Uncertainty Principle in C*-Algebras**:
at resolution `h_m = (M : ℝ) ^ (-m)` (`M ≥ 2`, `ν ∈ (0, 1)`), the multiscale porous operator decays
polynomially as `h_m ^ (β / 2)` (`β = fupExponent ν M > 0`), its survival form decays as `h_m ^ β`,
every initial operator `u₀` suffers quantitative attenuation, and `multiscaleLoc L m → 0`. -/
theorem multiscaleLoc_fup_polynomial_decay
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [Nontrivial B]
    {L : ℕ → B} {ν : ℝ} (hPor : IsNuPorousDefect L ν) (hν0 : 0 < ν) {M : ℕ} (hM : 2 ≤ M) :
    0 < fupExponent ν M ∧
    (∀ m : ℕ, ‖multiscaleLoc L m‖ ≤ ((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2))) ∧
    (∀ m : ℕ, ‖star (multiscaleLoc L m) * multiscaleLoc L m‖ ≤ ((M : ℝ) ^ m) ^ (-(fupExponent ν M))) ∧
    (∀ (m : ℕ) (u₀ : B),
      ‖multiscaleLoc L m * u₀‖ ≤ ((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2)) * ‖u₀‖) ∧
    Filter.Tendsto (fun m : ℕ => multiscaleLoc L m) Filter.atTop (nhds 0) := by
  have hβ : 0 < fupExponent ν M := fupExponent_pos hν0 hPor.2.1 hM
  refine ⟨hβ, ?_, ?_, ?_, ?_⟩
  · intro m
    have hdec := (norm_multiscaleLoc_decay_of_isNuPorousDefect hPor m).2.1
    have hpow : (((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2))) ^ 2 = (1 - ν) ^ m := by
      dsimp [fupExponent]
      exact scalar_rpow_neg_half_fup_sq hPor.2.1 hM m
    have hnn_rhs : 0 ≤ ((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2)) :=
      Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg M) m) _
    have hsq_le : ‖multiscaleLoc L m‖ ^ 2 ≤ (((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2))) ^ 2 :=
      hpow ▸ hdec
    exact (sq_le_sq₀ (norm_nonneg _) hnn_rhs).1 hsq_le
  · intro m
    have hdec := (norm_multiscaleLoc_decay_of_isNuPorousDefect hPor m).2.2
    have hpow : ((M : ℝ) ^ m) ^ (-(fupExponent ν M)) = (1 - ν) ^ m := by
      dsimp [fupExponent]
      exact scalar_rpow_neg_fup_eq_one_sub_pow hPor.2.1 hM m
    exact hpow ▸ hdec
  · intro m u₀
    have hdec := (norm_multiscaleLoc_decay_of_isNuPorousDefect hPor m).2.1
    have hpow : (((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2))) ^ 2 = (1 - ν) ^ m := by
      dsimp [fupExponent]
      exact scalar_rpow_neg_half_fup_sq hPor.2.1 hM m
    have hnn_rhs : 0 ≤ ((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2)) :=
      Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg M) m) _
    have hm_le : ‖multiscaleLoc L m‖ ≤ ((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2)) :=
      (sq_le_sq₀ (norm_nonneg _) hnn_rhs).1 (hpow ▸ hdec)
    calc ‖multiscaleLoc L m * u₀‖
      _ ≤ ‖multiscaleLoc L m‖ * ‖u₀‖ := norm_mul_le (multiscaleLoc L m) u₀
      _ ≤ ((M : ℝ) ^ m) ^ (-(fupExponent ν M / 2)) * ‖u₀‖ :=
          mul_le_mul_of_nonneg_right hm_le (norm_nonneg u₀)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hq_nn : 0 ≤ Real.sqrt (1 - ν) := Real.sqrt_nonneg (1 - ν)
    have hq_lt : Real.sqrt (1 - ν) < 1 := by
      have hsq : Real.sqrt (1 - ν) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (scalar_one_sub_nonneg_of_lt_one hPor.2.1) (scalar_one_sub_lt_one_of_pos hν0)
      simpa using hsq
    have hlim : Filter.Tendsto (fun m : ℕ => (Real.sqrt (1 - ν)) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
    exact squeeze_zero (fun m => norm_nonneg (multiscaleLoc L m))
      (fun m => (norm_multiscaleLoc_decay_of_isNuPorousDefect hPor m).1) hlim

/-- **Hilbert-Space Escape-Energy Bridge to `IsNuPorousDefect`**:
on any nontrivial complete complex Hilbert space `H`, if bounded operators `L k, R k : H →L[ℂ] H`
satisfy Pythagorean energy conservation `‖L k v‖^2 + ‖R k v‖^2 = ‖v‖^2` and uniform `ν`-pore
escape `ν * ‖v‖^2 ≤ ‖R k v‖^2`, then `IsNuPorousDefect L ν` holds in `CStarAlgebra (H →L[ℂ] H)`
and therefore `multiscaleLoc L m → 0` with full `h^β` FUP decay. -/
theorem isNuPorousDefect_of_hilbert_escape_energy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (L R : ℕ → (H →L[ℂ] H)) {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1)
    (hCons : ∀ k (v : H), ‖L k v‖ ^ 2 + ‖R k v‖ ^ 2 = ‖v‖ ^ 2)
    (hEsc : ∀ k (v : H), ν * ‖v‖ ^ 2 ≤ ‖R k v‖ ^ 2) :
    IsNuPorousDefect L ν := by
  refine ⟨hν0, hν1, fun k => ?_⟩
  have hr_nn : 0 ≤ 1 - ν := scalar_one_sub_nonneg_of_lt_one hν1
  have hsqrt_nn : 0 ≤ Real.sqrt (1 - ν) := Real.sqrt_nonneg (1 - ν)
  have hop : ‖L k‖ ≤ Real.sqrt (1 - ν) := by
    refine ContinuousLinearMap.opNorm_le_bound (L k) hsqrt_nn fun v => ?_
    have hv_sq : ‖L k v‖ ^ 2 ≤ (1 - ν) * ‖v‖ ^ 2 := by
      have hc := hCons k v
      have he := hEsc k v
      linarith
    have hrhs_sq : (Real.sqrt (1 - ν) * ‖v‖) ^ 2 = (1 - ν) * ‖v‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hr_nn]
    exact (sq_le_sq₀ (norm_nonneg (L k v)) (mul_nonneg hsqrt_nn (norm_nonneg v))).1
      (hrhs_sq.symm ▸ hv_sq)
  have hsq : ‖L k‖ ^ 2 ≤ 1 - ν := by
    have h1 := scalar_sq_le_sq_of_nonneg (norm_nonneg (L k)) hop
    rwa [Real.sq_sqrt hr_nn] at h1
  calc ‖star (L k) * L k‖
    _ = ‖L k‖ * ‖L k‖ := CStarRing.norm_star_mul_self
    _ = ‖L k‖ ^ 2 := (sq _).symm
    _ ≤ 1 - ν := hsq

end CStarFractalUncertainty

/-! ## Section 3: Banach Newton–Peirce Healing of Porous Compressions -/

section BanachPorousHealing

/-- **Exact `C*`-Identity for Porous Compression Defect**:
for self-adjoint idempotents `P, Q` in a unital `C*`-ring, the norm of the noncommutative porous
idempotency defect equals the squared norm `‖⁅P, Q⁆ * P‖ ^ 2` and is bounded by `‖⁅P, Q⁆‖ ^ 2`. -/
theorem norm_idempotencyDefect_porousSymCompress_le_commutator_sq
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    {P Q : B}
    (hPp : P * P = P) (hPs : star P = P)
    (hQp : Q * Q = Q) (hQs : star Q = Q) :
    ‖idempotencyDefect (porousSymCompress P Q)‖ = ‖⁅P, Q⁆ * P‖ ^ 2 ∧
    ‖idempotencyDefect (porousSymCompress P Q)‖ ≤ ‖⁅P, Q⁆‖ ^ 2 := by
  have hVar := (porousSymCompress_variance_and_idempotencyDefect hPp hPs hQp hQs).2.2
  have hEq : ‖idempotencyDefect (porousSymCompress P Q)‖ = ‖⁅P, Q⁆ * P‖ ^ 2 := by
    calc ‖idempotencyDefect (porousSymCompress P Q)‖
      _ = ‖-((P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P))‖ := by rw [hVar]
      _ = ‖(P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P)‖ := norm_neg _
      _ = ‖star (⁅P, Q⁆ * P) * (⁅P, Q⁆ * P)‖ := by rw [star_mul, hPs]
      _ = ‖⁅P, Q⁆ * P‖ * ‖⁅P, Q⁆ * P‖ := CStarRing.norm_star_mul_self
      _ = ‖⁅P, Q⁆ * P‖ ^ 2 := (sq _).symm
  have hP1 : ‖P‖ ≤ 1 := norm_sa_idempotent_le_one hPp hPs
  have hmul : ‖⁅P, Q⁆ * P‖ ≤ ‖⁅P, Q⁆‖ := by
    calc ‖⁅P, Q⁆ * P‖
      _ ≤ ‖⁅P, Q⁆‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖⁅P, Q⁆‖ * 1 := mul_le_mul_of_nonneg_left hP1 (norm_nonneg _)
      _ = ‖⁅P, Q⁆‖ := mul_one _
  have hLe : ‖idempotencyDefect (porousSymCompress P Q)‖ ≤ ‖⁅P, Q⁆‖ ^ 2 :=
    hEq.symm ▸ scalar_sq_le_sq_of_nonneg (norm_nonneg (⁅P, Q⁆ * P)) hmul
  exact ⟨hEq, hLe⟩

private theorem star_porousSymCompress
    {B : Type*} [Ring B] [StarRing B] {P Q : B}
    (hPs : star P = P) (hQs : star Q = Q) :
    star (porousSymCompress P Q) = porousSymCompress P Q := by
  dsimp [porousSymCompress]
  rw [star_mul, star_mul, hPs, hQs, mul_assoc]

private theorem star_newtonPeirceStep_selfAdjoint
    {B : Type*} [Ring B] [StarRing B] {x : B} (hx : star x = x) :
    star (newtonPeirceStep x) = newtonPeirceStep x := by
  have h3 : star ((3 : B) * x * x) = (3 : B) * x * x := by
    calc star ((3 : B) * x * x)
      _ = star x * star ((3 : B) * x) := star_mul _ _
      _ = star x * (star x * star (3 : B)) := by rw [star_mul]
      _ = x * (x * 3) := by rw [hx, star_ofNat]
      _ = 3 * x * x := by noncomm_ring
  have h2 : star ((2 : B) * x * x * x) = (2 : B) * x * x * x := by
    calc star ((2 : B) * x * x * x)
      _ = star x * star ((2 : B) * x * x) := star_mul _ _
      _ = star x * (star x * (star x * star (2 : B))) := by rw [star_mul, star_mul]
      _ = x * (x * (x * 2)) := by rw [hx, star_ofNat]
      _ = 2 * x * x * x := by noncomm_ring
  dsimp [newtonPeirceStep]
  rw [star_sub, h3, h2]

private theorem star_newtonPeirceStep_iterate_selfAdjoint
    {B : Type*} [Ring B] [StarRing B] {x : B} (hx : star x = x) (k : ℕ) :
    star (newtonPeirceStep^[k] x) = newtonPeirceStep^[k] x := by
  induction k with
  | zero => exact hx
  | succ k ih =>
      simp only [Function.iterate_succ_apply']
      exact star_newtonPeirceStep_selfAdjoint ih

/-- **Banach Newton–Peirce Healing of Porous Compressions**:
in any complete `C*`-algebra `B`, whenever self-adjoint idempotents `P, Q` have small commutator
`‖⁅P, Q⁆‖ ^ 2 < 1 / 6`, the porous compression `porousSymCompress P Q` Newton–Peirce heals to an
exact self-adjoint idempotent `e : B` living inside the `P`-corner (`P * e = e ∧ e * P = e`) and
commuting with every operator that commutes with `porousSymCompress P Q`. -/
theorem cstar_porousSymCompress_banach_healing
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [CompleteSpace B]
    {P Q : B}
    (hPp : P * P = P) (hPs : star P = P)
    (hQp : Q * Q = Q) (hQs : star Q = Q)
    (hComm : ‖⁅P, Q⁆‖ ^ 2 < 1 / 6) :
    ∃ e : B,
      Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress P Q))
        Filter.atTop (nhds e) ∧
      e * e = e ∧
      star e = e ∧
      P * e = e ∧
      e * P = e ∧
      Commute (porousSymCompress P Q) e ∧
      (∀ a : B, Commute a (porousSymCompress P Q) → Commute a e) := by
  have hDefLt : ‖idempotencyDefect (porousSymCompress P Q)‖ < 1 / 6 :=
    lt_of_le_of_lt
      (norm_idempotencyDefect_porousSymCompress_le_commutator_sq hPp hPs hQp hQs).2
      hComm
  obtain ⟨e, he, hIdem, hCommSelf, hCommAll, hLeftSup, hRightSup, _⟩ :=
    banach_newtonPeirce_limit_idempotent_and_intertwiner hDefLt
  have hLP : P * porousSymCompress P Q = porousSymCompress P Q := by
    dsimp [porousSymCompress]
    calc P * (P * Q * P)
      _ = (P * P) * Q * P := by noncomm_ring
      _ = P * Q * P := by rw [hPp]
  have hRP : porousSymCompress P Q * P = porousSymCompress P Q := by
    dsimp [porousSymCompress]
    calc (P * Q * P) * P
      _ = P * Q * (P * P) := by noncomm_ring
      _ = P * Q * P := by rw [hPp]
  have hStarLim : Filter.Tendsto (fun k : ℕ => star (newtonPeirceStep^[k] (porousSymCompress P Q)))
      Filter.atTop (nhds (star e)) :=
    (continuous_star.tendsto e).comp he
  have hStarEq :
      (fun k : ℕ => star (newtonPeirceStep^[k] (porousSymCompress P Q))) =
        (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress P Q)) := by
    funext k
    exact star_newtonPeirceStep_iterate_selfAdjoint (star_porousSymCompress hPs hQs) k
  rw [hStarEq] at hStarLim
  have hStarE : star e = e := tendsto_nhds_unique hStarLim he
  exact ⟨e, he, hIdem, hStarE, hLeftSup P hLP, hRightSup P hRP, hCommSelf, hCommAll⟩

/-- Corollary under the concrete commutator threshold `‖⁅P, Q⁆‖ ≤ 1 / 3`. -/
theorem cstar_porousSymCompress_banach_healing_of_le_third
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B] [CompleteSpace B]
    {P Q : B}
    (hPp : P * P = P) (hPs : star P = P)
    (hQp : Q * Q = Q) (hQs : star Q = Q)
    (hComm : ‖⁅P, Q⁆‖ ≤ 1 / 3) :
    ∃ e : B,
      Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress P Q))
        Filter.atTop (nhds e) ∧
      e * e = e ∧
      star e = e ∧
      P * e = e ∧
      e * P = e := by
  obtain ⟨e, he, hIdem, hStar, hPe, hEp, _⟩ :=
    cstar_porousSymCompress_banach_healing hPp hPs hQp hQs
      (scalar_sq_lt_sixth_of_le_third (norm_nonneg ⁅P, Q⁆) hComm)
  exact ⟨e, he, hIdem, hStar, hPe, hEp⟩

end BanachPorousHealing

/-! ## Section 4: Concrete Pythagorean `Mat2C` L2-Operator Witnesses -/

section ConcreteMat2CWitnesses

open scoped Matrix.Norms.L2Operator

/-- Pythagorean rank-1 projection `v vᴴ` with dominant first coordinate `v = (12/13, 5/13)ᵀ`. -/
noncomputable def pythQ12_5 : Mat2C :=
  Matrix.of ![![(144 / 169 : ℂ), 60 / 169], ![60 / 169, 25 / 169]]

/-- Pythagorean rank-1 projection `v vᴴ` with subdominant first coordinate `v = (5/13, 12/13)ᵀ`. -/
noncomputable def pythQ5_12 : Mat2C :=
  Matrix.of ![![(25 / 169 : ℂ), 60 / 169], ![60 / 169, 144 / 169]]

/-- Orthogonal `(3,4,5)` rotation unitary in `Mat2C`. -/
noncomputable def rotW5 : Mat2C :=
  Matrix.of ![![(3 / 5 : ℂ), -(4 / 5)], ![4 / 5, 3 / 5]]

/-- Weyl-flipped `(3,4,5)` unitary in `Mat2C`. -/
noncomputable def rotW5Flip : Mat2C :=
  weylSigma * rotW5

/-- Orthogonal `(5,12,13)` rotation unitary in `Mat2C`. -/
noncomputable def rotV13 : Mat2C :=
  Matrix.of ![![(5 / 13 : ℂ), -(12 / 13)], ![12 / 13, 5 / 13]]

/-- Diagonal `ν = 25/169` contraction profile `diag(5/13, 12/13)` for FUP attenuation. -/
noncomputable def porosityDiagL : Mat2C :=
  Matrix.diagonal ![(5 / 13 : ℂ), 12 / 13]

/-- Complementary diagonal escape profile `diag(12/13, 5/13)` (`D_Lᴴ D_L + D_Rᴴ D_R = 1`). -/
noncomputable def porosityDiagR : Mat2C :=
  Matrix.diagonal ![(12 / 13 : ℂ), 5 / 13]

/-- Non-diagonal porous step operator `W_1 D_L Vᴴ` in `Mat2C`. -/
noncomputable def porousStepL : Mat2C :=
  rotW5 * porosityDiagL * star rotV13

/-- Non-diagonal escaping pore residual `W_2 D_R Vᴴ` in `Mat2C`. -/
noncomputable def porousStepR : Mat2C :=
  rotW5Flip * porosityDiagR * star rotV13

private theorem rotW5_unitary : star rotW5 * rotW5 = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [rotW5] <;> norm_num

private theorem rotW5Flip_unitary : star rotW5Flip * rotW5Flip = 1 := by
  have hSigma : star (weylSigma : Mat2C) * weylSigma = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp [weylSigma]
  calc star rotW5Flip * rotW5Flip
    _ = star (weylSigma * rotW5) * (weylSigma * rotW5) := by dsimp [rotW5Flip]
    _ = star rotW5 * ((star (weylSigma : Mat2C) * weylSigma) * rotW5) := by
          rw [star_mul, mul_assoc, mul_assoc]
    _ = star rotW5 * (1 * rotW5) := by rw [hSigma]
    _ = star rotW5 * rotW5 := by rw [one_mul]
    _ = 1 := rotW5_unitary

private theorem rotV13_mem_unitary : rotV13 ∈ unitary Mat2C := by
  rw [Unitary.mem_iff]
  constructor
  · ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp [rotV13] <;> norm_num
  · ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp [rotV13] <;> norm_num

private theorem star_porosityDiagL_mul_self :
    star porosityDiagL * porosityDiagL = Matrix.diagonal ![(25 / 169 : ℂ), 144 / 169] := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [porosityDiagL] <;> norm_num

private theorem star_porosityDiag_sum :
    star porosityDiagL * porosityDiagL + star porosityDiagR * porosityDiagR = 1 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [porosityDiagL, porosityDiagR] <;> norm_num

/-- Explicit noncommutativity between `porousStepL` and `porousStepR` in `Mat2C`. -/
theorem porousStepL_mul_R_ne :
    porousStepL * porousStepR ≠ porousStepR * porousStepL := by
  intro hEq
  have hsV : star rotV13 = Matrix.of ![![(5 / 13 : ℂ), 12 / 13], ![-(12 / 13), 5 / 13]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotV13]
  have h00 := congrArg (fun M : Mat2C => M 0 0) hEq
  dsimp [porousStepL, porousStepR, rotW5Flip] at h00
  rw [hsV] at h00
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, rotW5, weylSigma,
    porosityDiagL, porosityDiagR] at h00
  norm_num at h00

/-- **Concrete `Mat2C` Pythagorean FUP Example (`ν = 25/169`)**:
`porousStepL` and `porousStepR` are non-diagonal noncommuting L2-operators satisfying exact unitary
pore conservation `star L * L + star R * R = 1`, `IsNuPorousDefect (fun _ => porousStepL) (25 / 169)`,
polynomial decay `h_m ^ (fupExponent (25 / 169) 2 / 2)`, and norm convergence to `0`. -/
theorem concrete_mat2c_pythagorean_fup_example :
    star porousStepL * porousStepL + star porousStepR * porousStepR = 1 ∧
    porousStepL * porousStepR ≠ porousStepR * porousStepL ∧
    IsNuPorousDefect (fun _ => porousStepL) (25 / 169) ∧
    0 < fupExponent (25 / 169) 2 ∧
    (∀ m : ℕ, ‖multiscaleLoc (fun _ => porousStepL) m‖ ≤
      ((2 : ℝ) ^ m) ^ (-(fupExponent (25 / 169) 2 / 2))) ∧
    Filter.Tendsto (fun m : ℕ => multiscaleLoc (fun _ => porousStepL) m)
      Filter.atTop (nhds 0) := by
  have hStarL : star porousStepL * porousStepL =
      rotV13 * (star porosityDiagL * porosityDiagL) * star rotV13 := by
    dsimp [porousStepL]
    calc star (rotW5 * porosityDiagL * star rotV13) * (rotW5 * porosityDiagL * star rotV13)
      _ = rotV13 * (star porosityDiagL * ((star rotW5 * rotW5) * porosityDiagL)) * star rotV13 := by
            rw [star_mul, star_mul, star_star]
            noncomm_ring
      _ = rotV13 * (star porosityDiagL * (1 * porosityDiagL)) * star rotV13 := by rw [rotW5_unitary]
      _ = rotV13 * (star porosityDiagL * porosityDiagL) * star rotV13 := by rw [one_mul]
  have hStarR : star porousStepR * porousStepR =
      rotV13 * (star porosityDiagR * porosityDiagR) * star rotV13 := by
    dsimp [porousStepR]
    calc star (rotW5Flip * porosityDiagR * star rotV13) * (rotW5Flip * porosityDiagR * star rotV13)
      _ = rotV13 * (star porosityDiagR * ((star rotW5Flip * rotW5Flip) * porosityDiagR)) *
            star rotV13 := by
            rw [star_mul, star_mul, star_star]
            noncomm_ring
      _ = rotV13 * (star porosityDiagR * (1 * porosityDiagR)) * star rotV13 := by
            rw [rotW5Flip_unitary]
      _ = rotV13 * (star porosityDiagR * porosityDiagR) * star rotV13 := by rw [one_mul]
  have hCons : star porousStepL * porousStepL + star porousStepR * porousStepR = 1 := by
    rw [hStarL, hStarR]
    calc rotV13 * (star porosityDiagL * porosityDiagL) * star rotV13 +
          rotV13 * (star porosityDiagR * porosityDiagR) * star rotV13
      _ = rotV13 * (star porosityDiagL * porosityDiagL + star porosityDiagR * porosityDiagR) *
            star rotV13 := by noncomm_ring
      _ = rotV13 * 1 * star rotV13 := by rw [star_porosityDiag_sum]
      _ = rotV13 * star rotV13 := by rw [mul_one]
      _ = 1 := Unitary.coe_mul_star_self ⟨rotV13, rotV13_mem_unitary⟩
  have hNormL : ‖star porousStepL * porousStepL‖ ≤ 1 - (25 / 169 : ℝ) := by
    rw [hStarL, mul_assoc, CStarRing.norm_mem_unitary_mul _ rotV13_mem_unitary,
      CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem rotV13_mem_unitary),
      star_porosityDiagL_mul_self, Matrix.l2_opNorm_diagonal]
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i <;> simp <;> norm_num
  have hPor : IsNuPorousDefect (fun _ => porousStepL) (25 / 169) :=
    ⟨by norm_num, by norm_num, fun _ => hNormL⟩
  have hFUP := multiscaleLoc_fup_polynomial_decay hPor (by norm_num) (M := 2) (by norm_num)
  exact ⟨hCons, porousStepL_mul_R_ne, hPor, hFUP.1, hFUP.2.1, hFUP.2.2.2.2⟩

private theorem peircePlus2_idempotent_sa :
    (peircePlus2 : Mat2C) * peircePlus2 = peircePlus2 ∧
    star (peircePlus2 : Mat2C) = peircePlus2 := by
  constructor
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [peircePlus2]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [peircePlus2]

private theorem pythQ12_5_properties :
    pythQ12_5 * pythQ12_5 = pythQ12_5 ∧
    star pythQ12_5 = pythQ12_5 ∧
    (peircePlus2 : Mat2C) * pythQ12_5 ≠ pythQ12_5 * peircePlus2 ∧
    porousSymCompress (peircePlus2 : Mat2C) pythQ12_5 =
      Matrix.diagonal ![(144 / 169 : ℂ), 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [pythQ12_5] <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pythQ12_5]
  · intro hEq
    have h01 := congrArg (fun M : Mat2C => M 0 1) hEq
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01
    dsimp [peircePlus2, pythQ12_5] at h01
    norm_num at h01
  · ext i j
    simp only [porousSymCompress, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp [peircePlus2, pythQ12_5]

private theorem pythQ5_12_properties :
    pythQ5_12 * pythQ5_12 = pythQ5_12 ∧
    star pythQ5_12 = pythQ5_12 ∧
    (peircePlus2 : Mat2C) * pythQ5_12 ≠ pythQ5_12 * peircePlus2 ∧
    porousSymCompress (peircePlus2 : Mat2C) pythQ5_12 =
      Matrix.diagonal ![(25 / 169 : ℂ), 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [pythQ5_12] <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pythQ5_12]
  · intro hEq
    have h01 := congrArg (fun M : Mat2C => M 0 1) hEq
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01
    dsimp [peircePlus2, pythQ5_12] at h01
    norm_num at h01
  · ext i j
    simp only [porousSymCompress, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp [peircePlus2, pythQ5_12]

private theorem norm_defect_diag_pair (a : ℝ) :
    ‖idempotencyDefect (Matrix.diagonal ![(a : ℂ), 0])‖ = |a - a * a| := by
  have hdef : idempotencyDefect (Matrix.diagonal ![(a : ℂ), 0]) =
      Matrix.diagonal ![((a * a - a : ℝ) : ℂ), 0] := by
    dsimp [idempotencyDefect]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hdef, Matrix.l2_opNorm_diagonal]
  have hle : ‖(![((a * a - a : ℝ) : ℂ), 0] : Fin 2 → ℂ)‖ ≤ |a - a * a| := by
    rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro i
    fin_cases i
    · change ‖((a * a - a : ℝ) : ℂ)‖ ≤ |a - a * a|
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    · change ‖(0 : ℂ)‖ ≤ |a - a * a|
      rw [norm_zero]
      exact abs_nonneg _
  have hge : |a - a * a| ≤ ‖(![((a * a - a : ℝ) : ℂ), 0] : Fin 2 → ℂ)‖ := by
    have h0 := norm_le_pi_norm (![((a * a - a : ℝ) : ℂ), 0]) 0
    change ‖((a * a - a : ℝ) : ℂ)‖ ≤ _ at h0
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at h0
  exact le_antisymm hle hge

private theorem diag_first_newtonPeirceStep (r : ℝ) :
    newtonPeirceStep (Matrix.diagonal ![(r : ℂ), 0]) =
      Matrix.diagonal ![((3 * r * r - 2 * r * r * r : ℝ) : ℂ), 0] := by
  dsimp [newtonPeirceStep]
  rw [show (3 : Mat2C) = 1 + 1 + 1 by norm_num, show (2 : Mat2C) = 1 + 1 by norm_num]
  ext i j
  (fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two])
  ring

private def scalarNewtonStep (r : ℝ) : ℝ := 3 * r * r - 2 * r * r * r

private theorem diag_first_newtonPeirceStep_iterate (r : ℝ) (k : ℕ) :
    newtonPeirceStep^[k] (Matrix.diagonal ![(r : ℂ), 0]) =
      Matrix.diagonal ![((scalarNewtonStep^[k] r : ℝ) : ℂ), 0] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Function.iterate_succ_apply'] at ih ⊢
      rw [ih]
      exact diag_first_newtonPeirceStep (scalarNewtonStep^[k] r)

private theorem peircePlus2_eq_diag_one_zero :
    (peircePlus2 : Mat2C) = Matrix.diagonal ![(1 : ℂ), 0] := by
  ext i j
  simp only [Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [peircePlus2]

/-- **Sharp Banach Healing to `peircePlus2` (`Q_{12,5}` Dominant Overlap `144/169`)**:
the noncommuting porous compression `porousSymCompress peircePlus2 pythQ12_5` has defect norm
`3600 / 28561 < 1 / 6` and converges in L2-operator norm strictly to `peircePlus2`. -/
theorem concrete_mat2c_pythagorean_healing_to_peircePlus2 :
    let P : Mat2C := peircePlus2
    P * pythQ12_5 ≠ pythQ12_5 * P ∧
    ‖idempotencyDefect (porousSymCompress P pythQ12_5)‖ = 3600 / 28561 ∧
    ‖idempotencyDefect (porousSymCompress P pythQ12_5)‖ < 1 / 6 ∧
    Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress P pythQ12_5))
      Filter.atTop (nhds P) := by
  have hP := peircePlus2_idempotent_sa
  have hQ := pythQ12_5_properties
  have hDefEq : ‖idempotencyDefect (porousSymCompress peircePlus2 pythQ12_5)‖ = 3600 / 28561 := by
    rw [hQ.2.2.2]
    have hnorm := norm_defect_diag_pair (144 / 169 : ℝ)
    norm_num at hnorm
    exact hnorm
  have hDefLt : ‖idempotencyDefect (porousSymCompress peircePlus2 pythQ12_5)‖ < 1 / 6 := by
    rw [hDefEq]; norm_num
  obtain ⟨e, he, hIdem, hCommSelf, hCommAll, hLeftSup, hRightSup, _⟩ :=
    banach_newtonPeirce_limit_idempotent_and_intertwiner hDefLt
  have hStarLim : Filter.Tendsto
      (fun k : ℕ => star (newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ12_5)))
      Filter.atTop (nhds (star e)) := (continuous_star.tendsto e).comp he
  have hStarEq :
      (fun k : ℕ => star (newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ12_5))) =
        (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ12_5)) := by
    funext k
    exact star_newtonPeirceStep_iterate_selfAdjoint (star_porousSymCompress hP.2 hQ.2.1) k
  rw [hStarEq] at hStarLim
  have hStarE : star e = e := tendsto_nhds_unique hStarLim he
  have hPe : (peircePlus2 : Mat2C) * e = e := hLeftSup peircePlus2 (by
    dsimp [porousSymCompress]; rw [← mul_assoc, ← mul_assoc, hP.1, mul_assoc])
  have heP : e * (peircePlus2 : Mat2C) = e := hRightSup peircePlus2 (by
    dsimp [porousSymCompress]; rw [mul_assoc, hP.1])
  have hd_idem : (peircePlus2 - e) * (peircePlus2 - e) = peircePlus2 - e := by
    calc (peircePlus2 - e) * (peircePlus2 - e)
      _ = peircePlus2 * peircePlus2 - peircePlus2 * e - e * peircePlus2 + e * e := by noncomm_ring
      _ = peircePlus2 - e - e + e := by rw [hP.1, hPe, heP, hIdem]
      _ = peircePlus2 - e := by abel
  have hd_sa : star (peircePlus2 - e : Mat2C) = peircePlus2 - e := by
    rw [star_sub, hP.2, hStarE]
  have hScalarBound : ∀ k : ℕ,
      0 ≤ 1 - scalarNewtonStep^[k] (144 / 169 : ℝ) ∧
      1 - scalarNewtonStep^[k] (144 / 169 : ℝ) ≤ 1 / 3 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        simp only [Function.iterate_succ_apply', scalarNewtonStep]
        rw [scalar_newton_poly_one_sub]
        exact scalar_newton_residual_step ih.1 ih.2
  have hDistK : ∀ k : ℕ,
      ‖(peircePlus2 : Mat2C) - newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ12_5)‖ ≤
        1 / 3 := by
    intro k
    rw [hQ.2.2.2, show (144 / 169 : ℂ) = ((144 / 169 : ℝ) : ℂ) by norm_num,
      diag_first_newtonPeirceStep_iterate, peircePlus2_eq_diag_one_zero]
    have hdiff :
        Matrix.diagonal ![(1 : ℂ), 0] -
            Matrix.diagonal ![((scalarNewtonStep^[k] (144 / 169 : ℝ) : ℝ) : ℂ), 0] =
          Matrix.diagonal ![((1 - scalarNewtonStep^[k] (144 / 169 : ℝ) : ℝ) : ℂ), 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hdiff, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i
    · change ‖((1 - scalarNewtonStep^[k] (144 / 169 : ℝ) : ℝ) : ℂ)‖ ≤ 1 / 3
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hScalarBound k).1]
      exact (hScalarBound k).2
    · change ‖(0 : ℂ)‖ ≤ 1 / 3
      rw [norm_zero]
      norm_num
  have hDistLim :
      Filter.Tendsto
        (fun k : ℕ => ‖(peircePlus2 : Mat2C) - newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ12_5)‖)
        Filter.atTop (nhds ‖(peircePlus2 : Mat2C) - e‖) :=
    (continuous_norm.tendsto _).comp (tendsto_const_nhds.sub he)
  have hDiffLe : ‖(peircePlus2 : Mat2C) - e‖ ≤ 1 / 3 :=
    le_of_tendsto hDistLim (Filter.Eventually.of_forall hDistK)
  have he_eq_P : e = peircePlus2 := by
    have hzero : (peircePlus2 : Mat2C) - e = 0 :=
      eq_zero_of_sa_idempotent_norm_lt_one hd_idem hd_sa (lt_of_le_of_lt hDiffLe (by norm_num))
    exact (sub_eq_zero.mp hzero).symm
  rw [he_eq_P] at he
  exact ⟨hQ.2.2.1, hDefEq, hDefLt, he⟩

/-- **Sharp Banach Healing to `0` (`Q_{5,12}` Subdominant Overlap `25/169`)**:
the noncommuting porous compression `porousSymCompress peircePlus2 pythQ5_12` has the exact same
defect norm `3600 / 28561 < 1 / 6`, yet heals in L2-operator norm strictly to `0`. -/
theorem concrete_mat2c_pythagorean_healing_to_zero :
    let P : Mat2C := peircePlus2
    P * pythQ5_12 ≠ pythQ5_12 * P ∧
    ‖idempotencyDefect (porousSymCompress P pythQ5_12)‖ = 3600 / 28561 ∧
    ‖idempotencyDefect (porousSymCompress P pythQ5_12)‖ < 1 / 6 ∧
    Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress P pythQ5_12))
      Filter.atTop (nhds (0 : Mat2C)) := by
  have hP := peircePlus2_idempotent_sa
  have hQ := pythQ5_12_properties
  have hDefEq : ‖idempotencyDefect (porousSymCompress peircePlus2 pythQ5_12)‖ = 3600 / 28561 := by
    rw [hQ.2.2.2]
    have hnorm := norm_defect_diag_pair (25 / 169 : ℝ)
    norm_num at hnorm
    exact hnorm
  have hDefLt : ‖idempotencyDefect (porousSymCompress peircePlus2 pythQ5_12)‖ < 1 / 6 := by
    rw [hDefEq]; norm_num
  obtain ⟨e, he, hIdem, _⟩ :=
    banach_newtonPeirce_limit_idempotent_and_intertwiner hDefLt
  have hStarLim : Filter.Tendsto
      (fun k : ℕ => star (newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ5_12)))
      Filter.atTop (nhds (star e)) := (continuous_star.tendsto e).comp he
  have hStarEq :
      (fun k : ℕ => star (newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ5_12))) =
        (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ5_12)) := by
    funext k
    exact star_newtonPeirceStep_iterate_selfAdjoint (star_porousSymCompress hP.2 hQ.2.1) k
  rw [hStarEq] at hStarLim
  have hStarE : star e = e := tendsto_nhds_unique hStarLim he
  have hScalarBound : ∀ k : ℕ,
      0 ≤ scalarNewtonStep^[k] (25 / 169 : ℝ) ∧
      scalarNewtonStep^[k] (25 / 169 : ℝ) ≤ 1 / 3 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        simp only [Function.iterate_succ_apply', scalarNewtonStep]
        rw [scalar_newton_poly_zero]
        exact scalar_newton_residual_step ih.1 ih.2
  have hNormK : ∀ k : ℕ,
      ‖newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ5_12)‖ ≤ 1 / 3 := by
    intro k
    rw [hQ.2.2.2, show (25 / 169 : ℂ) = ((25 / 169 : ℝ) : ℂ) by norm_num,
      diag_first_newtonPeirceStep_iterate, Matrix.l2_opNorm_diagonal,
      pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i
    · change ‖((scalarNewtonStep^[k] (25 / 169 : ℝ) : ℝ) : ℂ)‖ ≤ 1 / 3
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hScalarBound k).1]
      exact (hScalarBound k).2
    · change ‖(0 : ℂ)‖ ≤ 1 / 3
      rw [norm_zero]
      norm_num
  have hNormLim :
      Filter.Tendsto
        (fun k : ℕ => ‖newtonPeirceStep^[k] (porousSymCompress peircePlus2 pythQ5_12)‖)
        Filter.atTop (nhds ‖e‖) :=
    (continuous_norm.tendsto _).comp he
  have heLe : ‖e‖ ≤ 1 / 3 := le_of_tendsto hNormLim (Filter.Eventually.of_forall hNormK)
  have he_eq_zero : e = 0 :=
    eq_zero_of_sa_idempotent_norm_lt_one hIdem hStarE (lt_of_le_of_lt heLe (by norm_num))
  rw [he_eq_zero] at he
  exact ⟨hQ.2.2.1, hDefEq, hDefLt, he⟩

/-- Concrete Berezin–Toeplitz all-powers norm isometry in `Mat2C` for the unitary `weylSigma` and
non-diagonal Pythagorean symbol `pythQ12_5`. -/
theorem concrete_mat2c_berezin_toeplitz_pow_norm_isometry (n : ℕ) :
    ‖toeplitzOp (weylSigma : Mat2C) pythQ12_5 ^ (n + 1)‖ =
      ‖berezinOp (weylSigma : Mat2C) pythQ12_5 ^ (n + 1)‖ := by
  have hWeyl : star (weylSigma : Mat2C) * weylSigma = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp [weylSigma]
  exact norm_toeplitzOp_pow_eq_berezinOp_pow hWeyl pythQ12_5 n

end ConcreteMat2CWitnesses

/-! ## Section 5: QMS Kernel-Certified Archetype Registration -/

section QMSArchetype

open scoped Matrix.Norms.L2Operator

/-- Registered QMS `TypedArchetype` certifying `C*`-algebraic Berezin–Toeplitz norm isometries,
multiscale `h^β` fractal uncertainty decay, Banach Newton–Peirce healing of porous compressions,
and concrete Pythagorean `Mat2C` L2-operator witnesses. -/
noncomputable def cstarFractalUncertaintyAndBanachPorosityArchetype :
    TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.CStarFractalUncertaintyAndBanachPorosity.cstarFractalUncertaintyAndBanachPorosityArchetype
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (∀ (B : Type) [NormedRing B] [StarRing B] [CStarRing B] [Nontrivial B]
      (V S : B) (n : ℕ), star V * V = 1 →
      ‖toeplitzOp V S ^ (n + 1)‖ = ‖berezinOp V S ^ (n + 1)‖) ∧
    (∀ (B : Type) [NormedRing B] [StarRing B] [CStarRing B] [CompleteSpace B]
      (P Q : B), P * P = P → star P = P → Q * Q = Q → star Q = Q →
      ‖⁅P, Q⁆‖ ^ 2 < 1 / 6 →
      ∃ e : B,
        Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress P Q))
          Filter.atTop (nhds e) ∧
        e * e = e ∧ star e = e ∧ P * e = e ∧ e * P = e) ∧
    (porousStepL * porousStepR ≠ porousStepR * porousStepL ∧
      IsNuPorousDefect (fun _ => porousStepL) (25 / 169) ∧
      Filter.Tendsto (fun m : ℕ => multiscaleLoc (fun _ => porousStepL) m)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress (peircePlus2 : Mat2C) pythQ12_5))
        Filter.atTop (nhds (peircePlus2 : Mat2C)) ∧
      Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] (porousSymCompress (peircePlus2 : Mat2C) pythQ5_12))
        Filter.atTop (nhds (0 : Mat2C)))
  evidence := fun _ => by
    refine ⟨?_, ?_, ?_⟩
    · intro B _ _ _ _ V S n hV
      exact norm_toeplitzOp_pow_eq_berezinOp_pow hV S n
    · intro B _ _ _ _ P Q hPp hPs hQp hQs hComm
      obtain ⟨e, he, hIdem, hStar, hPe, heP, _⟩ :=
        cstar_porousSymCompress_banach_healing hPp hPs hQp hQs hComm
      exact ⟨e, he, hIdem, hStar, hPe, heP⟩
    · have hFup := concrete_mat2c_pythagorean_fup_example
      have hH1 := concrete_mat2c_pythagorean_healing_to_peircePlus2
      have hH0 := concrete_mat2c_pythagorean_healing_to_zero
      exact ⟨hFup.2.1, hFup.2.2.1, hFup.2.2.2.2.2, hH1.2.2.2, hH0.2.2.2⟩

#register_archetype cstarFractalUncertaintyAndBanachPorosityArchetype
#audit_archetype cstarFractalUncertaintyAndBanachPorosityArchetype

end QMSArchetype

end InfoGeometry.OperatorAlgebra.CStarFractalUncertaintyAndBanachPorosity
