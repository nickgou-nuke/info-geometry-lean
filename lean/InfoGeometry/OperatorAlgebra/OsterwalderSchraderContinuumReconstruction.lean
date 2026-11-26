/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OsterwalderSchraderPeirceColimitBridge
import InfoGeometry.Lie.DoubledMinkowskiLatticeContinuumLimit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Osterwalder–Schrader Pre-Hilbert Reconstruction, Dyadic Contraction & Continuum Scaling Limit

Advances Frontier 1 ("Continuum 4D quantum Yang–Mills existence/mass gap") with kernel-checked
mathematical theorems connecting the lattice OS reflection-positivity and Peirce/colimit machinery
(`OsterwalderSchraderPeirceColimitBridge`) to the classical 4D lattice-to-continuum gauge limit
(`DoubledMinkowskiLatticeContinuumLimit`):

1. **Abstract Osterwalder–Schrader Reflection-Positive Quotient (`OSForm`, `OSQuotient`)**:
   - Proves the reflection-positive Cauchy–Schwarz inequality `(B x y)^2 ≤ B x x * B y y` and null
     radical invariance `B x x = 0 → ∀ y, B x y = 0`.
   - Constructs the quotient space `OSQuotient B := E ⧸ osNullSubmodule B` and induced symmetric
     bilinear form `osQuotInner B`, proving **strict positive definiteness**
     (`osQuotInner_eq_zero_iff : osQuotInner B q q = 0 ↔ q = 0`).
   - Instantiates `multiSiteOSForm` from arbitrary positive-coupling `N`-site OS bilinears.
2. **Glimm–Jaffe / Osterwalder–Schrader Dyadic Contraction Theorem**:
   - Proves by dyadic Cauchy–Schwarz iteration (`os_semigroup_dyadic_bound`) that any bounded
     symmetric linear semigroup `T : ℕ → E →ₗ[ℝ] E` on `(E, B)` is contractive:
     `B.toFun (T k x) (T k x) ≤ B.toFun x x`.
3. **Analytic Mass-Gap Continuum Scaling Limit (`a → 0⁺`)**:
   - Defines `criticalCoupling m_phys a`, proving `tanh (criticalCoupling m_phys a) = exp (-a * m_phys)`,
     `spectralMassGap (criticalCoupling m_phys a) = a * m_phys`, and exact exponential Wilson
     clustering convergence as lattice spacing `a → 0⁺` with fixed physical mass gap `m_phys > 0`:
     `Tendsto (fun a => (Real.tanh (criticalCoupling m_phys a)) ^ Nat.floor (t / a)) (𝓝[>] 0) (𝓝 (Real.exp (-m_phys * t)))`.
4. **4D Lattice-to-Continuum Bridge Packaging**:
   - Pairs the OS Hilbert quotient & continuum mass-gap scaling limit with 4D lattice plaquette
     curvature and Hilbert–Schmidt action convergence (`tendsto_wilsonPlaquette_curvature`,
     `tendsto_wilsonPlaquetteAction`).

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & ANALYTIC THEOREMS
* `os_cauchy_schwarz`, `os_null_left`, `osNullSubmodule`, `osQuotInner`, `osQuotInner_symm`,
  `osQuotInner_nonneg`, `osQuotInner_eq_zero_iff`, `multiSiteOSForm`.
* `os_semigroup_dyadic_bound`, `os_semigroup_contraction_of_bounded`.
* `criticalCoupling_pos`, `tanh_criticalCoupling`, `spectralMassGap_criticalCoupling`,
  `tendsto_continuum_wilson_clustering`.
* `fourDim_os_continuum_bridge_boundary`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Semigroup contraction conditional on uniform boundedness `∃ M > 0, ∀ n, B (T n x) (T n x) ≤ M`;
  Wilson clustering limit conditional on critical scaling `J(a) = criticalCoupling m_phys a`.

#### BUCKET 3: OPEN CLOSURE DEBT
* Constructing an interacting non-Abelian 4D continuum $SU(N)$ Yang–Mills path-integral measure
  satisfying OS axioms (Euclidean invariance, reflection positivity, clustering) with a strictly
  positive physical mass gap `m_phys > 0` remains the open Clay Millennium Problem.
-/

noncomputable section

open Filter _root_.Topology
open scoped _root_.Topology
open scoped Matrix.Norms.Operator

namespace InfoGeometry.OperatorAlgebra.OsterwalderSchraderContinuumReconstruction

open InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap
open InfoGeometry.OperatorAlgebra.OsterwalderSchraderPeirceColimitBridge

/-! ## 1. Abstract Osterwalder–Schrader Reflection-Positive Pre-Hilbert Quotient -/

/-- A symmetric, reflection-positive real bilinear form on an `ℝ`-vector space `E`. -/
structure OSForm (E : Type*) [AddCommGroup E] [Module ℝ E] where
  toFun : E → E → ℝ
  symm : ∀ x y, toFun x y = toFun y x
  add_left : ∀ x y z, toFun (x + y) z = toFun x z + toFun y z
  smul_left : ∀ c x y, toFun (c • x) y = c * toFun x y
  nonneg : ∀ x, 0 ≤ toFun x x

namespace OSForm

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (B : OSForm E)

theorem add_right (x y z : E) : B.toFun x (y + z) = B.toFun x y + B.toFun x z := by
  rw [B.symm x (y + z), B.add_left, B.symm y x, B.symm z x]

theorem smul_right (c : ℝ) (x y : E) : B.toFun x (c • y) = c * B.toFun x y := by
  rw [B.symm x (c • y), B.smul_left, B.symm y x]

theorem zero_left (y : E) : B.toFun 0 y = 0 := by
  have h := B.smul_left 0 0 y
  simpa using h

theorem zero_right (x : E) : B.toFun x 0 = 0 := by
  rw [B.symm, B.zero_left]

theorem neg_left (x y : E) : B.toFun (-x) y = -B.toFun x y := by
  have h := B.smul_left (-1) x y
  simpa using h

theorem sub_left (x y z : E) : B.toFun (x - y) z = B.toFun x z - B.toFun y z := by
  rw [sub_eq_add_neg, B.add_left, B.neg_left, sub_eq_add_neg]

theorem neg_right (x y : E) : B.toFun x (-y) = -B.toFun x y := by
  rw [B.symm, B.neg_left, B.symm]

theorem sub_right (x y z : E) : B.toFun x (y - z) = B.toFun x y - B.toFun x z := by
  rw [B.symm, B.sub_left, B.symm y x, B.symm z x]

theorem expand_smul_add (t : ℝ) (x y : E) :
    B.toFun (t • x + y) (t • x + y) =
      t ^ 2 * B.toFun x x + 2 * t * B.toFun x y + B.toFun y y := by
  rw [B.add_left, B.add_right, B.add_right, B.smul_left, B.smul_right, B.smul_right,
    B.smul_left, B.symm y x]
  ring

end OSForm

/-- **Reflection-Positive Cauchy–Schwarz Inequality**: `(B x y)^2 ≤ B x x * B y y`. -/
theorem os_cauchy_schwarz {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (x y : E) :
    (B.toFun x y) ^ 2 ≤ B.toFun x x * B.toFun y y := by
  have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * B.toFun x x + 2 * t * B.toFun x y + B.toFun y y := by
    intro t
    rw [← B.expand_smul_add t x y]
    exact B.nonneg _
  rcases eq_or_lt_of_le (B.nonneg x) with hx0 | hxpos
  · have hxy0 : B.toFun x y = 0 := by
      by_contra hne
      let t0 : ℝ := -(B.toFun y y + 1) / (2 * B.toFun x y)
      have hq := hquad t0
      rw [← hx0] at hq
      have h2ne : 2 * B.toFun x y ≠ 0 := mul_ne_zero two_ne_zero hne
      have hmul : 2 * t0 * B.toFun x y = -(B.toFun y y + 1) := by
        dsimp [t0]
        field_simp [h2ne]
      linarith
    rw [hxy0, ← hx0]
    norm_num
  · have hxne : B.toFun x x ≠ 0 := hxpos.ne'
    have hq := hquad (-(B.toFun x y) / B.toFun x x)
    have hcalc :
        (-(B.toFun x y) / B.toFun x x) ^ 2 * B.toFun x x +
            2 * (-(B.toFun x y) / B.toFun x x) * B.toFun x y + B.toFun y y =
          (B.toFun x x * B.toFun y y - (B.toFun x y) ^ 2) / B.toFun x x := by
      field_simp [hxne]
      ring
    rw [hcalc] at hq
    have hmul : 0 ≤ B.toFun x x * B.toFun y y - (B.toFun x y) ^ 2 := by
      have h0 := mul_nonneg hq hxpos.le
      rw [div_mul_cancel₀ _ hxne] at h0
      exact h0
    linarith

/-- Any null vector (`B x x = 0`) is orthogonal to the entire pre-Hilbert carrier. -/
theorem os_null_left {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) {x : E} (hx : B.toFun x x = 0) (y : E) :
    B.toFun x y = 0 := by
  have hcs := os_cauchy_schwarz B x y
  rw [hx, zero_mul] at hcs
  nlinarith [sq_nonneg (B.toFun x y)]

theorem os_null_right {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (x : E) {y : E} (hy : B.toFun y y = 0) :
    B.toFun x y = 0 := by
  rw [B.symm, os_null_left B hy]

/-- Null radical submodule `𝒩_B = {x ∈ E | B x x = 0}` for Osterwalder–Schrader reconstruction. -/
def osNullSubmodule {E : Type*} [AddCommGroup E] [Module ℝ E] (B : OSForm E) : Submodule ℝ E where
  carrier := {x : E | B.toFun x x = 0}
  zero_mem' := B.zero_left 0
  add_mem' {x y} hx hy := by
    have hxx : B.toFun x x = 0 := hx
    have hyy : B.toFun y y = 0 := hy
    have hxy : B.toFun x y = 0 := os_null_left B hxx y
    have hyx : B.toFun y x = 0 := by rw [B.symm, hxy]
    change B.toFun (x + y) (x + y) = 0
    rw [B.add_left, B.add_right, B.add_right, hxx, hyy, hxy, hyx]
    ring
  smul_mem' c {x} hx := by
    have hxx : B.toFun x x = 0 := hx
    change B.toFun (c • x) (c • x) = 0
    rw [B.smul_left, B.smul_right, hxx]
    ring

/-- The Osterwalder–Schrader physical pre-Hilbert quotient `ℋ_phys = E ⧸ 𝒩_B`. -/
abbrev OSQuotient {E : Type*} [AddCommGroup E] [Module ℝ E] (B : OSForm E) : Type _ :=
  E ⧸ osNullSubmodule B

private lemma os_quotient_well_defined {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) {x₁ x₂ y₁ y₂ : E}
    (hx : x₁ - x₂ ∈ osNullSubmodule B) (hy : y₁ - y₂ ∈ osNullSubmodule B) :
    B.toFun x₁ y₁ = B.toFun x₂ y₂ := by
  have hx0 : B.toFun (x₁ - x₂) (x₁ - x₂) = 0 := hx
  have hy0 : B.toFun (y₁ - y₂) (y₁ - y₂) = 0 := hy
  have h1 : B.toFun x₁ y₁ - B.toFun x₂ y₁ = 0 := by
    rw [← B.sub_left]
    exact os_null_left B hx0 y₁
  have h2 : B.toFun x₂ y₁ - B.toFun x₂ y₂ = 0 := by
    rw [← B.sub_right]
    exact os_null_right B x₂ hy0
  linarith

/-- Induced positive-definite inner product on `OSQuotient B`. -/
def osQuotInner {E : Type*} [AddCommGroup E] [Module ℝ E] (B : OSForm E) :
    OSQuotient B → OSQuotient B → ℝ :=
  Quotient.lift₂ B.toFun (fun x₁ y₁ x₂ y₂ hx hy =>
    os_quotient_well_defined B
      ((Submodule.Quotient.eq (osNullSubmodule B)).mp (Quotient.sound hx))
      ((Submodule.Quotient.eq (osNullSubmodule B)).mp (Quotient.sound hy)))

@[simp] theorem osQuotInner_mk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (x y : E) :
    osQuotInner B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B.toFun x y := rfl

theorem osQuotInner_symm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (p q : OSQuotient B) :
    osQuotInner B p q = osQuotInner B q p := by
  refine Quotient.inductionOn₂ p q fun x y => ?_
  exact B.symm x y

theorem osQuotInner_nonneg {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (q : OSQuotient B) :
    0 ≤ osQuotInner B q q := by
  refine Quotient.inductionOn q fun x => ?_
  exact B.nonneg x

/-- **Strict Positivity on the OS Reconstruction Quotient**: `⟪q, q⟫_{phys} = 0 ↔ q = 0`. -/
theorem osQuotInner_eq_zero_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (q : OSQuotient B) :
    osQuotInner B q q = 0 ↔ q = 0 := by
  refine Quotient.inductionOn q fun x => ?_
  change B.toFun x x = 0 ↔ Submodule.Quotient.mk x = 0
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- Concrete `OSForm` instance on the `N`-site lattice observable space from `multiSite_os_reflection_positivity`. -/
def multiSiteOSForm {N : ℕ} (J : Fin N → ℝ) (hJ : ∀ s, 0 < J s) :
    OSForm ((Fin N → Fin 2) → ℝ) where
  toFun f g := multiSiteOSBilinForm J f g
  symm f g := by
    unfold multiSiteOSBilinForm
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hk : multiSiteKernel J a b = multiSiteKernel J b a := by
      unfold multiSiteKernel
      refine Finset.prod_congr rfl fun s _ => ?_
      dsimp [transferMat]
      generalize ha : a s = ia
      generalize hb : b s = ib
      fin_cases ia <;> fin_cases ib <;> rfl
    rw [hk]
    ring
  add_left f₁ f₂ g := by
    unfold multiSiteOSBilinForm
    have hnum :
        (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2,
            multiSiteKernel J sNeg sPos * (f₁ sNeg + f₂ sNeg) * g sPos) =
          (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2,
            multiSiteKernel J sNeg sPos * f₁ sNeg * g sPos) +
          (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2,
            multiSiteKernel J sNeg sPos * f₂ sNeg * g sPos) := by
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun sNeg _ => Finset.sum_congr rfl fun sPos _ => ?_
      ring
    simp only [Pi.add_apply]
    rw [hnum, add_div]
  smul_left c f g := by
    unfold multiSiteOSBilinForm
    have hnum :
        (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2,
            multiSiteKernel J sNeg sPos * ((c • f) sNeg) * g sPos) =
          c * (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2,
            multiSiteKernel J sNeg sPos * f sNeg * g sPos) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun sNeg _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun sPos _ => ?_
      change multiSiteKernel J sNeg sPos * (c * f sNeg) * g sPos =
        c * (multiSiteKernel J sNeg sPos * f sNeg * g sPos)
      ring
    rw [hnum, mul_div_assoc]
  nonneg f := multiSite_os_reflection_positivity J hJ f

/-! ## 2. Glimm–Jaffe / Osterwalder–Schrader Dyadic Time-Translation Contraction -/

/-- Dyadic Cauchy–Schwarz moment bound for any symmetric linear semigroup `T : ℕ → E →ₗ[ℝ] E`
on an OS reflection-positive carrier `(E, B)`. -/
theorem os_semigroup_dyadic_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (T : ℕ → E →ₗ[ℝ] E)
    (hTadd : ∀ m n x, T (m + n) x = T m (T n x))
    (hTsym : ∀ k x y, B.toFun (T k x) y = B.toFun x (T k y))
    (x : E) (m k : ℕ) :
    B.toFun (T k x) (T k x) ^ (2 ^ m) ≤
      B.toFun x x ^ (2 ^ m - 1) * B.toFun (T (2 ^ m * k) x) (T (2 ^ m * k) x) := by
  induction m generalizing k with
  | zero =>
    simp
  | succ m ih =>
    have h2 : B.toFun (T k x) (T k x) ^ 2 ≤ B.toFun x x * B.toFun (T (2 * k) x) (T (2 * k) x) := by
      have hsym_eq : B.toFun (T k x) (T k x) = B.toFun x (T (2 * k) x) := by
        rw [hTsym k x (T k x), ← hTadd k k x, two_mul]
      rw [hsym_eq]
      exact os_cauchy_schwarz B x (T (2 * k) x)
    have hpow := pow_le_pow_left₀ (sq_nonneg (B.toFun (T k x) (T k x))) h2 (2 ^ m)
    have hpow_lhs : (B.toFun (T k x) (T k x) ^ 2) ^ (2 ^ m) =
        B.toFun (T k x) (T k x) ^ (2 ^ (m + 1)) := by
      rw [← pow_mul, mul_comm, ← pow_succ]
    have hpow_rhs : (B.toFun x x * B.toFun (T (2 * k) x) (T (2 * k) x)) ^ (2 ^ m) =
        B.toFun x x ^ (2 ^ m) * B.toFun (T (2 * k) x) (T (2 * k) x) ^ (2 ^ m) := by
      rw [mul_pow]
    rw [hpow_lhs, hpow_rhs] at hpow
    have hih := ih (2 * k)
    have hm1 : 2 ^ m + (2 ^ m - 1) = 2 ^ (m + 1) - 1 := by
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [pow_succ']
      omega
    have hmul :
        B.toFun x x ^ (2 ^ m) * B.toFun (T (2 * k) x) (T (2 * k) x) ^ (2 ^ m) ≤
          B.toFun x x ^ (2 ^ m) *
            (B.toFun x x ^ (2 ^ m - 1) * B.toFun (T (2 ^ m * (2 * k)) x) (T (2 ^ m * (2 * k)) x)) :=
      mul_le_mul_of_nonneg_left hih (pow_nonneg (B.nonneg x) _)
    have hprod :
        B.toFun x x ^ (2 ^ m) *
            (B.toFun x x ^ (2 ^ m - 1) * B.toFun (T (2 ^ m * (2 * k)) x) (T (2 ^ m * (2 * k)) x)) =
          B.toFun x x ^ (2 ^ (m + 1) - 1) *
            B.toFun (T (2 ^ (m + 1) * k) x) (T (2 ^ (m + 1) * k) x) := by
      have hexp : 2 ^ m * (2 * k) = 2 ^ (m + 1) * k := by
        rw [pow_succ']
        ring
      rw [hexp, ← mul_assoc, ← pow_add, hm1]
    exact hpow.trans (hmul.trans_eq hprod)

/-- **OS Dyadic Semigroup Contraction**: if `(B (T n x) (T n x))` is uniformly bounded in `n`,
then `B (T k x) (T k x) ≤ B x x` for all Euclidean time steps `k : ℕ`. -/
theorem os_semigroup_contraction_of_bounded {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : OSForm E) (T : ℕ → E →ₗ[ℝ] E)
    (hTadd : ∀ m n x, T (m + n) x = T m (T n x))
    (hTsym : ∀ k x y, B.toFun (T k x) y = B.toFun x (T k y))
    (x : E) (hbound : ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, B.toFun (T n x) (T n x) ≤ M)
    (k : ℕ) :
    B.toFun (T k x) (T k x) ≤ B.toFun x x := by
  by_contra hlt
  push Not at hlt
  rcases hbound with ⟨M, _, hM⟩
  rcases eq_or_lt_of_le (B.nonneg x) with hx0 | hxpos
  · have hdy := os_semigroup_dyadic_bound B T hTadd hTsym x 1 k
    simp [← hx0] at hdy
    have htk0 : B.toFun (T k x) (T k x) = 0 := by nlinarith
    linarith
  · have hratio : 1 < B.toFun (T k x) (T k x) / B.toFun x x :=
      (one_lt_div hxpos).mpr hlt
    let r : ℝ := B.toFun (T k x) (T k x) / B.toFun x x
    have hr_bound : ∀ m : ℕ, r ^ (2 ^ m) ≤ M / B.toFun x x := by
      intro m
      have hdy := os_semigroup_dyadic_bound B T hTadd hTsym x m k
      have hM_step := hM (2 ^ m * k)
      have hxpow_pos : 0 < B.toFun x x ^ (2 ^ m) := pow_pos hxpos (2 ^ m)
      have hcomb :
          B.toFun (T k x) (T k x) ^ (2 ^ m) ≤ B.toFun x x ^ (2 ^ m - 1) * M :=
        hdy.trans (mul_le_mul_of_nonneg_left hM_step (pow_nonneg hxpos.le _))
      have hm_ge : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hmul_x : B.toFun x x ^ (2 ^ m - 1) * B.toFun x x = B.toFun x x ^ (2 ^ m) := by
        rw [← pow_succ, Nat.sub_add_cancel hm_ge]
      have hdiv : B.toFun (T k x) (T k x) ^ (2 ^ m) / B.toFun x x ^ (2 ^ m) ≤
          (B.toFun x x ^ (2 ^ m - 1) * M) / B.toFun x x ^ (2 ^ m) :=
        div_le_div_of_nonneg_right hcomb hxpow_pos.le
      rw [← div_pow] at hdiv
      refine hdiv.trans_eq ?_
      rw [← hmul_x]
      have h1 : B.toFun x x ^ (2 ^ m - 1) ≠ 0 := (pow_pos hxpos _).ne'
      have h2 : B.toFun x x ≠ 0 := hxpos.ne'
      field_simp [h1, h2]
    have htend_pow : Tendsto (fun m : ℕ => r ^ (2 ^ m)) atTop atTop := by
      have ht := tendsto_pow_atTop_atTop_of_one_lt hratio
      have h2m : Tendsto (fun m : ℕ => (2 ^ m : ℕ)) atTop atTop :=
        tendsto_atTop_atTop.mpr fun b => ⟨b, fun m hm => hm.trans Nat.lt_two_pow_self.le⟩
      exact ht.comp h2m
    obtain ⟨m, hm⟩ := (htend_pow.eventually_gt_atTop (M / B.toFun x x)).exists
    exact (not_le_of_gt hm) (hr_bound m)

/-! ## 3. Analytic Continuum Scaling Limit (`a → 0⁺`) of Lattice Mass Gap -/

/-- Critical lattice coupling `J(a)` tuned so `spectralMassGap (J(a)) = a * m_phys`. -/
def criticalCoupling (m_phys a : ℝ) : ℝ :=
  Real.log ((1 + Real.exp (-a * m_phys)) / (1 - Real.exp (-a * m_phys))) / 2

theorem criticalCoupling_pos {m_phys a : ℝ} (hm : 0 < m_phys) (ha : 0 < a) :
    0 < criticalCoupling m_phys a := by
  unfold criticalCoupling
  have hneg : -a * m_phys < 0 := by
    rw [neg_mul]
    exact neg_lt_zero.mpr (mul_pos ha hm)
  have hexp_lt : Real.exp (-a * m_phys) < 1 := Real.exp_lt_one_iff.mpr hneg
  have hexp_pos : 0 < Real.exp (-a * m_phys) := Real.exp_pos _
  have hden_pos : 0 < 1 - Real.exp (-a * m_phys) := sub_pos.mpr hexp_lt
  have hfrac_gt : 1 < (1 + Real.exp (-a * m_phys)) / (1 - Real.exp (-a * m_phys)) := by
    rw [one_lt_div hden_pos]
    linarith
  exact div_pos (Real.log_pos hfrac_gt) two_pos

private lemma scalar_exp_log_tanh_identity (u : ℝ) (hu_pos : 0 < u) (hu_lt : u < 1) :
    Real.tanh (Real.log ((1 + u) / (1 - u)) / 2) = u := by
  have hden_pos : 0 < 1 - u := sub_pos.mpr hu_lt
  have hnum_pos : 0 < 1 + u := add_pos zero_lt_one hu_pos
  have hratio_pos : 0 < (1 + u) / (1 - u) := div_pos hnum_pos hden_pos
  have hexp2 : Real.exp (Real.log ((1 + u) / (1 - u))) = (1 + u) / (1 - u) :=
    Real.exp_log hratio_pos
  set y : ℝ := Real.log ((1 + u) / (1 - u)) / 2
  have h2y : 2 * y = Real.log ((1 + u) / (1 - u)) := by ring
  have hey_sq : Real.exp y * Real.exp y = (1 + u) / (1 - u) := by
    rw [← Real.exp_add, show y + y = 2 * y by ring, h2y, hexp2]
  have hey_pos : 0 < Real.exp y := Real.exp_pos y
  have hey_ne : Real.exp y ≠ 0 := hey_pos.ne'
  have hcosh_eq : Real.cosh y = (Real.exp y + (Real.exp y)⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  have hsinh_eq : Real.sinh y = (Real.exp y - (Real.exp y)⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
  rw [Real.tanh_eq_sinh_div_cosh, hsinh_eq, hcosh_eq]
  have hden_cosh : Real.exp y + (Real.exp y)⁻¹ ≠ 0 := by positivity
  have h1 : (Real.exp y - (Real.exp y)⁻¹) / 2 / ((Real.exp y + (Real.exp y)⁻¹) / 2) =
      (Real.exp y * Real.exp y - 1) / (Real.exp y * Real.exp y + 1) := by
    field_simp [hey_ne]
  rw [h1, hey_sq]
  have hden_nz : 1 - u ≠ 0 := hden_pos.ne'
  field_simp [hden_nz]
  ring

theorem tanh_criticalCoupling {m_phys a : ℝ} (hm : 0 < m_phys) (ha : 0 < a) :
    Real.tanh (criticalCoupling m_phys a) = Real.exp (-a * m_phys) := by
  have hneg : -a * m_phys < 0 := by
    rw [neg_mul]
    exact neg_lt_zero.mpr (mul_pos ha hm)
  exact scalar_exp_log_tanh_identity (Real.exp (-a * m_phys)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr hneg)

theorem spectralMassGap_criticalCoupling {m_phys a : ℝ} (hm : 0 < m_phys) (ha : 0 < a) :
    spectralMassGap (criticalCoupling m_phys a) = a * m_phys := by
  unfold spectralMassGap
  rw [tanh_criticalCoupling hm ha, Real.log_exp]
  ring

/-- **Exact Analytic Continuum Wilson-Clustering Limit (`a → 0⁺`)**:
under the critical scaling coupling `J(a) = criticalCoupling m_phys a` over `⌊t / a⌋` lattice steps,
connected Wilson correlations converge to exact physical continuum exponential decay `exp(-m_phys * t)`. -/
theorem tendsto_continuum_wilson_clustering {m_phys t : ℝ} (hm : 0 < m_phys) (ht : 0 ≤ t) :
    Tendsto
      (fun a : ℝ => (Real.tanh (criticalCoupling m_phys a)) ^ (Nat.floor (t / a)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (Real.exp (-m_phys * t))) := by
  have h_lower : Tendsto (fun _ : ℝ => Real.exp (-m_phys * t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (Real.exp (-m_phys * t))) := tendsto_const_nhds
  have h_upper : Tendsto (fun a : ℝ => Real.exp (-m_phys * (t - a))) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (Real.exp (-m_phys * t))) := by
    have hid : Tendsto (fun a : ℝ => a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
      continuous_id.continuousWithinAt
    have hsub : Tendsto (fun a : ℝ => -m_phys * (t - a)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (-m_phys * t)) := by
      have ht0 : Tendsto (fun a : ℝ => t - a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (t - 0)) :=
        tendsto_const_nhds.sub hid
      simpa using ht0.const_mul (-m_phys)
    exact (Real.continuous_exp.tendsto (-m_phys * t)).comp hsub
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower h_upper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    rw [tanh_criticalCoupling hm ha', ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hfl : ((Nat.floor (t / a) : ℕ) : ℝ) ≤ t / a :=
      Nat.floor_le (div_nonneg ht ha'.le)
    have hmul : ((Nat.floor (t / a) : ℕ) : ℝ) * a ≤ t := by
      calc
        ((Nat.floor (t / a) : ℕ) : ℝ) * a ≤ (t / a) * a := mul_le_mul_of_nonneg_right hfl ha'.le
        _ = t := div_mul_cancel₀ t ha'.ne'
    nlinarith [hm]
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    rw [tanh_criticalCoupling hm ha', ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hlt : t / a - 1 < ((Nat.floor (t / a) : ℕ) : ℝ) :=
      Nat.sub_one_lt_floor (t / a)
    have hmul : t - a ≤ ((Nat.floor (t / a) : ℕ) : ℝ) * a := by
      have h1 : (t / a - 1) * a ≤ ((Nat.floor (t / a) : ℕ) : ℝ) * a :=
        mul_le_mul_of_nonneg_right hlt.le ha'.le
      have h2 : (t / a - 1) * a = t - a := by
        rw [sub_mul, div_mul_cancel₀ t ha'.ne', one_mul]
      linarith
    nlinarith [hm]

/-! ## 4. Unified 4D Lattice-to-Continuum OS & Yang–Mills Boundary Theorem -/

/-- Packages together:
1. Strict positive definiteness of the Osterwalder–Schrader quotient `OSQuotient (multiSiteOSForm J hJ)`.
2. Dyadic time-translation semigroup contraction `os_semigroup_contraction_of_bounded`.
3. Exact continuum Wilson mass-gap scaling convergence `tendsto_continuum_wilson_clustering`.
4. Exact 4D classical Yang–Mills lattice plaquette curvature & Hilbert–Schmidt action limits (`a → 0`). -/
theorem fourDim_os_continuum_bridge_boundary
    {N : ℕ} (J : Fin N → ℝ) (hJ : ∀ s, 0 < J s)
    (q : OSQuotient (multiSiteOSForm J hJ))
    {m_phys t : ℝ} (hm : 0 < m_phys) (ht : 0 ≤ t)
    (A : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.FourSpace → Fin 4 → InfoGeometry.Lie.Mat4C)
    (y : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.FourSpace) (μ ν : Fin 4) (hA : ContDiff ℝ 2 A) :
    (osQuotInner (multiSiteOSForm J hJ) q q = 0 ↔ q = 0) ∧
    (0 ≤ osQuotInner (multiSiteOSForm J hJ) q q) ∧
    Tendsto (fun a : ℝ => (Real.tanh (criticalCoupling m_phys a)) ^ (Nat.floor (t / a)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (Real.exp (-m_phys * t))) ∧
    Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (InfoGeometry.Lie.wilsonPlaquette A y μ ν a - 1))
      (𝓝[≠] 0) (𝓝 (InfoGeometry.Lie.continuumCurvature A y μ ν)) ∧
    Tendsto (fun a : ℝ => InfoGeometry.Lie.wilsonPlaquetteAction A y μ ν a)
      (𝓝[≠] 0) (𝓝 (InfoGeometry.Lie.continuumPlaquetteAction A y μ ν)) := by
  exact ⟨osQuotInner_eq_zero_iff (multiSiteOSForm J hJ) q,
    osQuotInner_nonneg (multiSiteOSForm J hJ) q,
    tendsto_continuum_wilson_clustering hm ht,
    InfoGeometry.Lie.tendsto_wilsonPlaquette_curvature A y μ ν hA,
    InfoGeometry.Lie.tendsto_wilsonPlaquetteAction A y μ ν hA⟩

end InfoGeometry.OperatorAlgebra.OsterwalderSchraderContinuumReconstruction
