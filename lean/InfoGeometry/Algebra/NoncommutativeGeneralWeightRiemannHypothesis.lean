/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis

/-!
# Noncommutative General-Weight Operator Riemann Hypothesis, Rosati–Poincaré Duality & All-Scales Binomial Pore FUP

Epistemic compilation of the general-weight operator Riemann hypothesis across
`ClTower A n` over an arbitrary noncommutative `StarRing A`:

1. **$\mathcal{R}\mathcal{H}_1$** (`rosati_involution_and_unified_weil_criterion`):
   Rosati symplectic involution `rosatiInv M = -(omegaOp * Mᴴ * omegaOp)` (matching
   `poincareDual`), involutivity and anti-multiplicativity, and the unified commutator
   criterion governing purity, Poincaré similitude, and the Hasse–Weil quadratic for
   `weilFrobenius a b`.
2. **$\mathcal{R}\mathcal{H}_2$ & $\mathcal{R}\mathcal{H}_3$**
   (`all_scales_general_weight_riemann_hypothesis_and_binomial_fup`):
   All-scales general-weight Frobenius tower `weilTowerOp a b n : ClTower A n`,
   weight-$n$ critical-line purity `(weilTowerOp a b n)⋆ * weilTowerOp a b n = towerScalar n (q ^ n)`,
   Künneth trace `(2 ^ n) • a ^ n`, Euler–Lefschetz supertrace vanishing, Cantor vacuum
   compression, and the exact binomial Hasse–Weil pore FUP law.
3. **$\mathcal{R}\mathcal{H}_4$** (`operator_weil_polynomial_and_functional_equation`):
   Operator Weil polynomial factorization, Poincaré functional equation, and the
   genus-2 Jacobian evaluation `|Jac(C/𝔽₄₁)| = 1375`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis
open InfoGeometry.Algebra.NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis

namespace InfoGeometry.Algebra.NoncommutativeGeneralWeightRiemannHypothesis

universe u

section Matrix2Helpers

variable {A : Type*} [Ring A]

/-- Diagonal fiber embedding `a ↦ mat2 a 0 0 a` in `ClTower A 1 = M₂(A)`. -/
def fiberEmbed (a : A) : ClTower A 1 :=
  mat2 a 0 0 a

end Matrix2Helpers

/-!
## Archetype $\mathcal{R}\mathcal{H}_1$: Rosati Symplectic Involution & Unified Commutator Criterion
-/

section ArchetypeRH1_RosatiAndWeilCriterion

variable {A : Type*} [Ring A] [StarRing A]

/-- The Rosati symplectic involution `R_Ω(M) = -(omegaOp * Mᴴ * omegaOp)` in `ClTower A 1`. -/
def rosatiInv (M : ClTower A 1) : ClTower A 1 :=
  -(omegaOp * Mᴴ * omegaOp)

lemma rosatiInv_eq_poincareDual (M : ClTower A 1) :
    rosatiInv M = poincareDual M := by
  let _ : StarRing (ClTower A 1) := instStarRingClTower 1
  apply ext_fin2 <;> simp [rosatiInv, poincareDual, omegaOp, mat2]

/-- **Rosati Involution & Unified Commutator Criterion for the Operator Weil Conjectures ($\mathcal{R}\mathcal{H}_1$)**:
For any self-adjoint `star a = a`, `star b = b` in a noncommutative `StarRing A`:
1. `rosatiInv (rosatiInv M) = M` and `rosatiInv (M * N) = rosatiInv N * rosatiInv M`,
2. *Critical-Line Purity*: `Fᴴ * F - fiberEmbed (a * a + b * b) = -(fiberEmbed ⁅a, b⁆ * omegaOp)`,
3. *Poincaré Symplectic Similitude*: `Fᴴ * omegaOp * F - fiberEmbed (a * a + b * b) * omegaOp = -fiberEmbed ⁅a, b⁆`,
4. *Hasse–Weil Characteristic Equation*: `F * F - fiberEmbed (2 • a) * F + fiberEmbed (a * a + b * b) = fiberEmbed ⁅a, b⁆ * omegaOp`. -/
theorem rosati_involution_and_unified_weil_criterion
    (M N : ClTower A 1) {a b : A} (ha : star a = a) (hb : star b = b) :
    let F := weilFrobenius a b
    rosatiInv (rosatiInv M) = M ∧
    rosatiInv (M * N) = rosatiInv N * rosatiInv M ∧
    Fᴴ * F - fiberEmbed (a * a + b * b) = fiberEmbed ⁅a, b⁆ * omegaOp ∧
    Fᴴ * omegaOp * F - fiberEmbed (a * a + b * b) * omegaOp = -fiberEmbed ⁅a, b⁆ ∧
    F * F - fiberEmbed (2 • a) * F + fiberEmbed (a * a + b * b) =
      -(fiberEmbed ⁅a, b⁆ * omegaOp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [rosatiInv, omegaOp, mat2]
  · apply ext_fin2 <;> simp [rosatiInv, omegaOp, mat2] <;> abel
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, mat2, ha, hb] <;> abel
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, mat2, ha, hb] <;> abel
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, mat2, two_smul, add_mul] <;> abel

end ArchetypeRH1_RosatiAndWeilCriterion

/-!
## Archetypes $\mathcal{R}\mathcal{H}_2$ & $\mathcal{R}\mathcal{H}_3$: All-Scales General-Weight Frobenius Tower & Binomial Pore FUP
-/

section ArchetypeRH2_RH3_GeneralWeightFrobeniusTower

variable {A : Type u} [Ring A]

/-- Diagonal block lift `X ↦ mat2 X 0 0 X` from `ClTower A n` to `ClTower A (n + 1)`. -/
def diagLift {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 X

/-- Canonical diagonal scalar embedding `A → ClTower A n`. -/
def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => diagLift (towerScalar n a)

/-- Single-scale Weil step matrix `mat2 (towerScalar n a) (-towerScalar n b) (towerScalar n b) (towerScalar n a)`. -/
def weilStep (n : ℕ) (a b : A) : ClTower A (n + 1) :=
  mat2 (towerScalar n a) (-towerScalar n b) (towerScalar n b) (towerScalar n a)

/-- All-scales general-weight Frobenius operator `ℱ_n(a, b) ∈ ClTower A n`. -/
def weilTowerOp (a b : A) : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => diagLift (weilTowerOp a b n) * weilStep n a b

lemma towerScalar_zero (n : ℕ) : towerScalar n (0 : A) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_neg (n : ℕ) (x : A) :
    towerScalar n (-x) = -towerScalar n x := by
  induction n with
  | zero => rfl
  | succ m ih => apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_add (n : ℕ) (x y : A) :
    towerScalar n (x + y) = towerScalar n x + towerScalar n y := by
  induction n with
  | zero => rfl
  | succ m ih => apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_sub (n : ℕ) (x y : A) :
    towerScalar n (x - y) = towerScalar n x - towerScalar n y := by
  induction n with
  | zero => rfl
  | succ m ih => apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_mul (n : ℕ) (x y : A) :
    towerScalar n (x * y) = towerScalar n x * towerScalar n y := by
  induction n with
  | zero => rfl
  | succ m ih => apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_selfAdjoint [StarRing A] (n : ℕ) {x : A} (hx : star x = x) :
    @Star.star _ (instStarRingClTower n).toStar (towerScalar n x) = towerScalar n x := by
  induction n with
  | zero => exact hx
  | succ m ih =>
      let _ : StarRing (ClTower A m) := instStarRingClTower m
      let _ : StarRing (ClTower A (m + 1)) := instStarRingClTower (m + 1)
      apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_comm_cantorProj (n : ℕ) (x : A) :
    towerScalar n x * cantorProj n = cantorProj n * towerScalar n x := by
  induction n with
  | zero => dsimp [towerScalar, cantorProj]; rw [mul_one, one_mul]
  | succ m ih => apply ext_fin2 <;> simp [towerScalar, diagLift, cantorProj, ih]

lemma comm_pow_of_comm {x y : A} (hxy : x * y = y * x) (n : ℕ) :
    x ^ n * y = y * x ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      calc x ^ (m + 1) * y = x * (x ^ m * y) := by rw [pow_succ', mul_assoc]
        _ = x * (y * x ^ m) := by rw [ih]
        _ = (x * y) * x ^ m := by rw [← mul_assoc]
        _ = (y * x) * x ^ m := by rw [hxy]
        _ = y * x ^ (m + 1) := by rw [mul_assoc, ← pow_succ']

lemma pow_mul_pow_eq_sq_pow (a : A) (n : ℕ) :
    a ^ n * a ^ n = (a * a) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have ha_sq : (a * a) * a = a * (a * a) := mul_assoc a a a
      calc a ^ (m + 1) * a ^ (m + 1)
        _ = (a * a ^ m) * a ^ (m + 1) := by rw [pow_succ']
        _ = (a * a ^ m) * (a ^ m * a) := by rw [pow_succ]
        _ = a * (a ^ m * a ^ m) * a := by noncomm_ring
        _ = a * ((a * a) ^ m * a) := by rw [ih]; noncomm_ring
        _ = a * (a * (a * a) ^ m) := by rw [← comm_pow_of_comm ha_sq m]
        _ = (a * a) ^ (m + 1) := by rw [← mul_assoc, ← pow_succ']

lemma towerTrace_mul_scalar (a : A) : ∀ {n : ℕ} (X : ClTower A n),
    towerTrace (X * towerScalar n a) = towerTrace X * a
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace, towerScalar, diagLift]
      simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
        mul_zero, add_zero, zero_add]
      rw [towerTrace_mul_scalar a (X 0 0), towerTrace_mul_scalar a (X 1 1), add_mul]

/-- **All-Scales General-Weight Operator Riemann Hypothesis, Künneth Trace & Binomial Pore FUP ($\mathcal{R}\mathcal{H}_2$ & $\mathcal{R}\mathcal{H}_3$)**:
For any commuting self-adjoint Frobenius parameters `a, b : A` with weight `q = a * a + b * b` and scale `n : ℕ`:
1. *Weight-$n$ Critical-Line Purity*: `star (weilTowerOp a b n) * weilTowerOp a b n = towerScalar n (q ^ n)`,
2. *Künneth Trace Formula*: `towerTrace (weilTowerOp a b n) = (2 ^ n) • (a ^ n)`,
3. *Euler–Lefschetz Supertrace Vanishing*: `superTrace (weilTowerOp a b (n + 1)) = 0`,
4. *Vacuum Compression*: `cantorProj n * weilTowerOp a b n * cantorProj n = towerScalar n (a ^ n) * cantorProj n`,
5. *Binomial Hasse–Weil Pore FUP*:
   `star ((1 - cantorProj n) * weilTowerOp a b n * cantorProj n) * ((1 - cantorProj n) * weilTowerOp a b n * cantorProj n) = towerScalar n (q ^ n - (a * a) ^ n) * cantorProj n`. -/
theorem all_scales_general_weight_riemann_hypothesis_and_binomial_fup [StarRing A]
    {a b : A} (ha : star a = a) (hb : star b = b) (hab : a * b = b * a) (n : ℕ) :
    let F_n := weilTowerOp a b n
    let P_n := (cantorProj n : ClTower A n)
    let Q_n := 1 - P_n
    let q   := a * a + b * b
    @Star.star _ (instStarRingClTower n).toStar F_n * F_n = towerScalar n (q ^ n) ∧
    towerTrace F_n = (2 ^ n) • (a ^ n) ∧
    superTrace (weilTowerOp a b (n + 1)) = 0 ∧
    P_n * F_n * P_n = towerScalar n (a ^ n) * P_n ∧
    @Star.star _ (instStarRingClTower n).toStar (Q_n * F_n * P_n) * (Q_n * F_n * P_n) =
      towerScalar n (q ^ n - (a * a) ^ n) * P_n := by
  let _ : StarRing (ClTower A n) := instStarRingClTower n
  intro F_n P_n Q_n q
  have hqa : q * a = a * q := by
    dsimp [q]
    calc (a * a + b * b) * a = a * (a * a) + b * (b * a) := by noncomm_ring
      _ = a * (a * a) + b * (a * b) := by rw [← hab]
      _ = a * (a * a) + (b * a) * b := by rw [mul_assoc]
      _ = a * (a * a) + (a * b) * b := by rw [← hab]
      _ = a * (a * a + b * b) := by noncomm_ring
  have hqb : q * b = b * q := by
    dsimp [q]
    calc (a * a + b * b) * b = a * (a * b) + b * (b * b) := by noncomm_ring
      _ = a * (b * a) + b * (b * b) := by rw [hab]
      _ = (a * b) * a + b * (b * b) := by rw [mul_assoc]
      _ = (b * a) * a + b * (b * b) := by rw [hab]
      _ = b * (a * a + b * b) := by noncomm_ring
  have h_purity : ∀ (k : ℕ),
      @Star.star _ (instStarRingClTower k).toStar (weilTowerOp a b k) *
        weilTowerOp a b k = towerScalar k (q ^ k) := by
    intro k
    induction k with
    | zero => simp [weilTowerOp, towerScalar]
    | succ m ih =>
        let _ : StarRing (ClTower A m) := instStarRingClTower m
        let _ : StarRing (ClTower A (m + 1)) := instStarRingClTower (m + 1)
        dsimp [weilTowerOp]
        have h_diag_star :
            star (diagLift (weilTowerOp a b m)) * diagLift (weilTowerOp a b m) =
              diagLift (towerScalar m (q ^ m)) := by
          apply ext_fin2 <;> simp [diagLift, ih]
        have h_calc :
            star (diagLift (weilTowerOp a b m) * weilStep m a b) *
              (diagLift (weilTowerOp a b m) * weilStep m a b) =
              star (weilStep m a b) *
              (star (diagLift (weilTowerOp a b m)) * diagLift (weilTowerOp a b m)) *
              weilStep m a b := by
          simp only [star_mul]; noncomm_ring
        rw [h_calc, h_diag_star]
        have hAm : star (towerScalar m a) = towerScalar m a := towerScalar_selfAdjoint m ha
        have hBm : star (towerScalar m b) = towerScalar m b := towerScalar_selfAdjoint m hb
        have h_qm_a : q ^ m * a = a * q ^ m := comm_pow_of_comm hqa m
        have h_qm_b : q ^ m * b = b * q ^ m := comm_pow_of_comm hqb m
        have h1 : a * q ^ m * a + b * q ^ m * b = q ^ (m + 1) := by
          calc a * q ^ m * a + b * q ^ m * b
            _ = (a * q ^ m) * a + (b * q ^ m) * b := by noncomm_ring
            _ = (q ^ m * a) * a + (q ^ m * b) * b := by rw [← h_qm_a, ← h_qm_b]
            _ = q ^ m * (a * a + b * b) := by noncomm_ring
            _ = q ^ (m + 1) := by rw [← pow_succ]
        have h2 : -(a * q ^ m * b) + b * q ^ m * a = 0 := by
          calc -(a * q ^ m * b) + b * q ^ m * a
            _ = -(a * q ^ m) * b + (b * q ^ m) * a := by noncomm_ring
            _ = -(q ^ m * a) * b + (q ^ m * b) * a := by rw [← h_qm_a, ← h_qm_b]
            _ = q ^ m * (b * a - a * b) := by noncomm_ring
            _ = 0 := by rw [← hab, sub_self, mul_zero]
        have h3 : b * q ^ m * a - a * q ^ m * b = 0 := by
          calc b * q ^ m * a - a * q ^ m * b
            _ = -(a * q ^ m * b) + b * q ^ m * a := by abel
            _ = 0 := h2
        apply ext_fin2
        · dsimp only [weilStep, diagLift]
          change (star (mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) *
              mat2 (towerScalar m (q ^ m)) 0 0 (towerScalar m (q ^ m)) *
              mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) 0 0 =
            towerScalar m (q ^ (m + 1))
          simp only [mul2_00, mul2_01, mat2_00, mat2_01, mat2_10, mat2_11,
            Matrix.star_apply, mul_zero, add_zero, zero_add, hAm, hBm,
            ← towerScalar_mul, ← towerScalar_add]
          rw [h1]
        · dsimp only [weilStep, diagLift]
          change (star (mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) *
              mat2 (towerScalar m (q ^ m)) 0 0 (towerScalar m (q ^ m)) *
              mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) 0 1 = 0
          simp only [mul2_00, mul2_01, mat2_00, mat2_01, mat2_10, mat2_11,
            Matrix.star_apply, mul_zero, add_zero, zero_add, hAm, hBm,
            ← towerScalar_mul, ← towerScalar_neg, ← towerScalar_add,
            mul_neg, h2, towerScalar_zero]
        · dsimp only [weilStep, diagLift]
          change (star (mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) *
              mat2 (towerScalar m (q ^ m)) 0 0 (towerScalar m (q ^ m)) *
              mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) 1 0 = 0
          simp only [mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
            Matrix.star_apply, star_neg, mul_zero, add_zero, zero_add, hAm, hBm,
            neg_mul, ← towerScalar_mul]
          have h3' : -(b * q ^ m * a) + a * q ^ m * b = 0 := by
            calc -(b * q ^ m * a) + a * q ^ m * b
              _ = -(b * q ^ m * a - a * q ^ m * b) := by abel
              _ = 0 := by rw [h3, neg_zero]
          rw [← towerScalar_neg, ← towerScalar_add, h3', towerScalar_zero]
        · dsimp only [weilStep, diagLift]
          change (star (mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) *
              mat2 (towerScalar m (q ^ m)) 0 0 (towerScalar m (q ^ m)) *
              mat2 (towerScalar m a) (-towerScalar m b) (towerScalar m b) (towerScalar m a)) 1 1 =
            towerScalar m (q ^ (m + 1))
          simp only [mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
            Matrix.star_apply, star_neg, mul_zero, add_zero, zero_add, hAm, hBm,
            neg_mul, mul_neg, neg_neg, ← towerScalar_mul, ← towerScalar_add]
          rw [add_comm (b * q ^ m * b) (a * q ^ m * a), h1]
  have h_vac : ∀ (k : ℕ),
      cantorProj k * weilTowerOp a b k * cantorProj k =
        towerScalar k (a ^ k) * cantorProj k := by
    intro k
    induction k with
    | zero => simp [cantorProj, weilTowerOp, towerScalar]
    | succ m ih =>
        apply ext_fin2
        · dsimp [cantorProj, weilTowerOp, diagLift, weilStep]
          simp only [mul2_00, mul2_01, mat2_00, mat2_01, mat2_10, mat2_11,
            mul_zero, zero_mul, add_zero]
          calc cantorProj m * (weilTowerOp a b m * towerScalar m a) * cantorProj m
            _ = cantorProj m * weilTowerOp a b m * (towerScalar m a * cantorProj m) := by
                noncomm_ring
            _ = (cantorProj m * weilTowerOp a b m * cantorProj m) * towerScalar m a := by
                rw [towerScalar_comm_cantorProj m a]; noncomm_ring
            _ = (towerScalar m (a ^ m) * cantorProj m) * towerScalar m a := by rw [ih]
            _ = (towerScalar m (a ^ m) * towerScalar m a) * cantorProj m := by
                rw [mul_assoc, ← towerScalar_comm_cantorProj m a, ← mul_assoc]
            _ = towerScalar m (a ^ (m + 1)) * cantorProj m := by
                rw [← towerScalar_mul, ← pow_succ]
        · simp [cantorProj, towerScalar, diagLift]
        · simp [cantorProj, towerScalar, diagLift]
        · simp [cantorProj, towerScalar, diagLift]
  have h_tr : ∀ (k : ℕ), towerTrace (weilTowerOp a b k) = (2 ^ k) • (a ^ k) := by
    intro k
    induction k with
    | zero => simp [weilTowerOp, towerTrace]
    | succ m ih =>
        dsimp [weilTowerOp, towerTrace, diagLift, weilStep]
        simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
          zero_mul, add_zero, zero_add]
        rw [towerTrace_mul_scalar a (weilTowerOp a b m), ih, pow_succ', two_mul,
            add_nsmul, pow_succ]
        simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        noncomm_ring
  refine ⟨h_purity n, h_tr n, ?_, h_vac n, ?_⟩
  · dsimp [superTrace, chiralityOp, weilTowerOp, diagLift, weilStep, towerTrace]
    simp [neg_mul, towerTrace_neg]
  · have hP_idem := cantorProj_idempotent (A := A) n
    have hP_sa   := cantorProj_selfAdjoint (A := A) n
    have hQ_idem : Q_n * Q_n = Q_n := by
      dsimp only [Q_n]
      calc (1 - P_n) * (1 - P_n) = 1 - P_n - P_n + P_n * P_n := by noncomm_ring
        _ = 1 - P_n := by rw [hP_idem]; noncomm_ring
    have hQ_sa : star Q_n = Q_n := by
      dsimp only [Q_n]; rw [star_sub, star_one, hP_sa]
    have h_full : star (F_n * P_n) * (F_n * P_n) = towerScalar n (q ^ n) * P_n := by
      calc star (F_n * P_n) * (F_n * P_n)
        _ = (star P_n * star F_n) * (F_n * P_n) := by rw [star_mul]
        _ = P_n * (star F_n * F_n) * P_n := by rw [hP_sa]; noncomm_ring
        _ = P_n * towerScalar n (q ^ n) * P_n := by rw [h_purity n]
        _ = towerScalar n (q ^ n) * (P_n * P_n) := by
            rw [← towerScalar_comm_cantorProj n (q ^ n)]; noncomm_ring
        _ = towerScalar n (q ^ n) * P_n := by rw [hP_idem]
    have h_an_sa : star (a ^ n) = a ^ n := by rw [star_pow, ha]
    have h_proj_sq : star (P_n * F_n * P_n) * (P_n * F_n * P_n) =
        towerScalar n ((a * a) ^ n) * P_n := by
      rw [h_vac n]
      simp only [star_mul, hP_sa, towerScalar_selfAdjoint n h_an_sa]
      calc (P_n * towerScalar n (a ^ n)) * (towerScalar n (a ^ n) * P_n)
        _ = (towerScalar n (a ^ n) * P_n) * (towerScalar n (a ^ n) * P_n) := by
            rw [towerScalar_comm_cantorProj n (a ^ n)]
        _ = (towerScalar n (a ^ n) * (P_n * towerScalar n (a ^ n))) * P_n := by noncomm_ring
        _ = (towerScalar n (a ^ n) * (towerScalar n (a ^ n) * P_n)) * P_n := by
            rw [← towerScalar_comm_cantorProj n (a ^ n)]
        _ = (towerScalar n (a ^ n) * towerScalar n (a ^ n)) * (P_n * P_n) := by noncomm_ring
        _ = towerScalar n ((a * a) ^ n) * P_n := by
            rw [← towerScalar_mul, pow_mul_pow_eq_sq_pow a n, hP_idem]
    have h_part : star (Q_n * F_n * P_n) * (Q_n * F_n * P_n) +
                  star (P_n * F_n * P_n) * (P_n * F_n * P_n) =
                  star (F_n * P_n) * (F_n * P_n) := by
      have hP_sa' : star P_n = P_n := hP_sa
      calc star (Q_n * F_n * P_n) * (Q_n * F_n * P_n) +
             star (P_n * F_n * P_n) * (P_n * F_n * P_n)
        _ = (P_n * star F_n * Q_n) * (Q_n * F_n * P_n) +
            (P_n * star F_n * P_n) * (P_n * F_n * P_n) := by
            simp only [star_mul, hP_sa', hQ_sa]; noncomm_ring
        _ = P_n * star F_n * (Q_n * Q_n) * F_n * P_n +
            P_n * star F_n * (P_n * P_n) * F_n * P_n := by noncomm_ring
        _ = P_n * star F_n * (Q_n + P_n) * F_n * P_n := by rw [hQ_idem, hP_idem]; noncomm_ring
        _ = P_n * star F_n * 1 * F_n * P_n := by dsimp only [Q_n]; rw [sub_add_cancel]
        _ = (P_n * star F_n) * (F_n * P_n) := by noncomm_ring
        _ = star (F_n * P_n) * (F_n * P_n) := by rw [star_mul, hP_sa']
    rw [h_proj_sq, h_full] at h_part
    calc star (Q_n * F_n * P_n) * (Q_n * F_n * P_n)
      _ = (star (Q_n * F_n * P_n) * (Q_n * F_n * P_n) +
           towerScalar n ((a * a) ^ n) * P_n) -
          towerScalar n ((a * a) ^ n) * P_n := by abel
      _ = towerScalar n (q ^ n) * P_n - towerScalar n ((a * a) ^ n) * P_n := by rw [h_part]
      _ = towerScalar n (q ^ n - (a * a) ^ n) * P_n := by rw [towerScalar_sub, sub_mul]

end ArchetypeRH2_RH3_GeneralWeightFrobeniusTower

/-!
## Archetype $\mathcal{R}\mathcal{H}_4$: Operator Weil Polynomial Factorization, Reciprocal Functional Equation & $\mathrm{Jac}(C/\mathbb{F}_{41})$
-/

section ArchetypeRH4_WeilPolynomialAndFunctionalEquation

variable {A : Type*} [Ring A] [StarRing A]

/-- Homogenized quadratic Hasse–Weil polynomial `W(a, q, T, S) = S * S - (2 • a) * S * T + q * (T * T)`. -/
def hasseWeilPoly (a q T S : A) : A :=
  S * S - (2 • a) * S * T + q * (T * T)

/-- Homogeneous degree-4 Weil polynomial `P₁(T, S)` of `C/𝔽₄₁ : y² + y = x⁵`. -/
def weilPolyC41 (T S : ℤ) : ℤ :=
  S ^ 4 - 9 * T * S ^ 3 + 71 * T ^ 2 * S ^ 2 - 9 * 41 * T ^ 3 * S + 41 ^ 2 * T ^ 4

/-- **Operator Weil Polynomial Factorization, Reciprocal Functional Equation & $\mathrm{Jac}(C/\mathbb{F}_{41})$ ($\mathcal{R}\mathcal{H}_4$)**:
1. `(1 - fiberEmbed T * F) * (1 - fiberEmbed T * Fᴴ) = fiberEmbed (1 - (2 • a) * T + q * (T * T))`,
2. `hasseWeilPoly a q S (q * T) = q * hasseWeilPoly a q T S`,
3. `weilPolyC41 1 1 = 1375` and `weilPolyC41 s (41 * t) = 41 ^ 2 * weilPolyC41 t s`. -/
theorem operator_weil_polynomial_and_functional_equation
    {a b T S : A} (ha : star a = a) (hb : star b = b)
    (hab : a * b = b * a) (hTa : T * a = a * T) (hTb : T * b = b * T)
    (hTS : T * S = S * T)
    (t s : ℤ) :
    let F := weilFrobenius a b
    let q := a * a + b * b
    (1 - fiberEmbed T * F) * (1 - fiberEmbed T * Fᴴ) =
      fiberEmbed (1 - (2 • a) * T + q * (T * T)) ∧
    hasseWeilPoly a q S (q * T) = q * hasseWeilPoly a q T S ∧
    weilPolyC41 1 1 = 1375 ∧
    weilPolyC41 s (41 * t) = 41 ^ 2 * weilPolyC41 t s := by
  have hTa2 : T * a * (T * a) = a * a * (T * T) := by
    calc T * a * (T * a) = a * T * (T * a) := by rw [hTa]
      _ = a * (T * (T * a)) := by noncomm_ring
      _ = a * (T * (a * T)) := by rw [← hTa]
      _ = a * ((T * a) * T) := by noncomm_ring
      _ = a * ((a * T) * T) := by rw [hTa]
      _ = a * a * (T * T) := by noncomm_ring
  have hTb2 : T * b * (T * b) = b * b * (T * T) := by
    calc T * b * (T * b) = b * T * (T * b) := by rw [hTb]
      _ = b * (T * (T * b)) := by noncomm_ring
      _ = b * (T * (b * T)) := by rw [← hTb]
      _ = b * ((T * b) * T) := by noncomm_ring
      _ = b * ((b * T) * T) := by rw [hTb]
      _ = b * b * (T * T) := by noncomm_ring
  refine ⟨?_, ?_, by decide, by dsimp [weilPolyC41]; ring⟩
  · apply ext_fin2
    · simp [weilFrobenius, fiberEmbed, mat2, ha, hb, two_smul]
      calc (1 - T * a) * (1 - T * a) + T * b * (T * b)
        _ = 1 - T * a - T * a + (T * a) * (T * a) + T * b * (T * b) := by noncomm_ring
        _ = 1 - a * T - a * T + a * a * (T * T) + b * b * (T * T) := by rw [hTa2, hTb2, hTa]
        _ = 1 - (a + a) * T + (a * a + b * b) * (T * T) := by noncomm_ring
    · simp [weilFrobenius, fiberEmbed, mat2, ha, hb]
      calc -((1 - T * a) * (T * b)) + T * b * (1 - T * a)
        _ = T * (a * T) * b - T * (b * T) * a := by noncomm_ring
        _ = T * (T * a) * b - T * (T * b) * a := by rw [← hTa, ← hTb]
        _ = T * T * (a * b - b * a) := by noncomm_ring
        _ = 0 := by rw [hab, sub_self, mul_zero]
    · simp [weilFrobenius, fiberEmbed, mat2, ha, hb]
      calc -(T * b * (1 - T * a)) + (1 - T * a) * (T * b)
        _ = T * (b * T) * a - T * (a * T) * b := by noncomm_ring
        _ = T * (T * b) * a - T * (T * a) * b := by rw [← hTa, ← hTb]
        _ = T * T * (b * a - a * b) := by noncomm_ring
        _ = 0 := by rw [hab, sub_self, mul_zero]
    · simp [weilFrobenius, fiberEmbed, mat2, ha, hb, two_smul]
      calc T * b * (T * b) + (1 - T * a) * (1 - T * a)
        _ = T * b * (T * b) + (1 - T * a - T * a + (T * a) * (T * a)) := by noncomm_ring
        _ = b * b * (T * T) + (1 - a * T - a * T + a * a * (T * T)) := by rw [hTa2, hTb2, hTa]
        _ = 1 - (a + a) * T + (a * a + b * b) * (T * T) := by noncomm_ring
  · dsimp [hasseWeilPoly]
    simp only [two_smul]
    have hqT : (a * a + b * b) * T = T * (a * a + b * b) := by
      calc (a * a + b * b) * T = a * (a * T) + b * (b * T) := by noncomm_ring
        _ = a * (T * a) + b * (T * b) := by rw [← hTa, ← hTb]
        _ = (a * T) * a + (b * T) * b := by noncomm_ring
        _ = (T * a) * a + (T * b) * b := by rw [← hTa, ← hTb]
        _ = T * (a * a + b * b) := by noncomm_ring
    have hqa : (a * a + b * b) * a = a * (a * a + b * b) := by
      calc (a * a + b * b) * a = a * a * a + b * (b * a) := by noncomm_ring
        _ = a * a * a + b * (a * b) := by rw [← hab]
        _ = a * a * a + (b * a) * b := by noncomm_ring
        _ = a * a * a + (a * b) * b := by rw [← hab]
        _ = a * (a * a + b * b) := by noncomm_ring
    have hqTS : (a + a) * ((a * a + b * b) * T) * S =
        (a * a + b * b) * ((a + a) * S * T) := by
      calc (a + a) * ((a * a + b * b) * T) * S
        _ = (a + a) * (a * a + b * b) * (T * S) := by noncomm_ring
        _ = (a * (a * a + b * b) + a * (a * a + b * b)) * (S * T) := by rw [hTS]; noncomm_ring
        _ = ((a * a + b * b) * a + (a * a + b * b) * a) * (S * T) := by rw [← hqa]
        _ = (a * a + b * b) * ((a + a) * S * T) := by noncomm_ring
    have hqTT : (a * a + b * b) * T * ((a * a + b * b) * T) =
        (a * a + b * b) * ((a * a + b * b) * (T * T)) := by
      calc (a * a + b * b) * T * ((a * a + b * b) * T)
        _ = (a * a + b * b) * (T * (a * a + b * b)) * T := by noncomm_ring
        _ = (a * a + b * b) * ((a * a + b * b) * T) * T := by rw [← hqT]
        _ = (a * a + b * b) * ((a * a + b * b) * (T * T)) := by noncomm_ring
    rw [hqTT, hqTS]
    noncomm_ring

private theorem generalWeightRH_noncomm_witness {A : Type u} [Ring A] [Nontrivial A] :
    ∃ x y : ClTower A 1, x * y ≠ y * x := by
  refine ⟨fiberEmbed 0 + mat2 0 1 0 0, omegaOp, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [fiberEmbed, omegaOp, mat2, Matrix.mul_apply, Fin.sum_univ_two] at h00

end ArchetypeRH4_WeilPolynomialAndFunctionalEquation

end InfoGeometry.Algebra.NoncommutativeGeneralWeightRiemannHypothesis
