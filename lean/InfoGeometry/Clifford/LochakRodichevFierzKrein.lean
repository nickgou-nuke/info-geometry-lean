/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Quaternion
import InfoGeometry.Clifford.DaviauChiralPeirceSU2
import InfoGeometry.Clifford.DeBroglieDaviauPhotonProcaFusion

/-!
# Lochak (2007) Rodichev Skew Torsion, Krein `(4,4)` Fierz–Takabayasi Identity & Lightcone Majorana Condition

Formalizes Sections I–II of Georges Lochak (2007), *"Twisted space, chiral gauge and
magnetism"*, Ann. Fond. Louis de Broglie 32 (no 2–3), 125–136, strictly inside Daviau's real
`M₈(ℝ)` representation with Krein metric `Γ⁰ = diag(I₄, -I₄)` (`kreinMetric8`) and real
`γ₅ ↔ Γ^{0123} P_j`, eliminating complexified time `x₄ = i c t` (and keeping all unconfirmed
LENR/experimental claims from pp. 131, 136 outside the formalization).

Key results:
1. **Rodichev Skew-Torsion Axial Reduction (Lochak Eqs. 8–13)**: total antisymmetry of
   `rodichevTorsion σ` and exact algebraic identity
   `∑ a μ b, rodichevTorsion σ a μ b • (Γ^μ Γ^a Γ^b) = 6 • ∑ ν, σ ν • (Γ_ν Γ^{0123})`.
2. **Krein `(4,4)` Bilinear Fierz–Takabayasi Identity (Lochak Eq. 39)**:
   in real `M₈(ℝ)` with `Γ⁰ = kreinMetric8`, `-lochakDot J J = lochakDot Σ Σ = Ω₁² + Ω₂²`
   and `minkowskiDot J Σ = 0`.
3. **Chiral Cross-Pairing & Lightcone Majorana Orthogonality (Lochak Eqs. 27, 47)**:
   `Ω₁² + Ω₂² = 4 * normSq (ξ† η) = 0 ↔ ξ† η = 0`, together with explicit real chiral
   cross-pairing formulas and Daviau Eq. (58) ↔ Eqs. (71–79) bilinear correspondence.
-/

noncomputable section

namespace InfoGeometry.Clifford.LochakRodichevFierzKrein

open Matrix BigOperators
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Clifford.DaviauRealDirac8x8
open InfoGeometry.Clifford.DaviauChiralPeirceSU2
open InfoGeometry.Clifford.DeBroglieDaviauPhotonProcaFusion

private abbrev kreinInnerProduct :=
  InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinInnerProduct
private abbrev kreinMetric8 :=
  InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8

/-! ### Section 1: Rodichev Skew-Torsion Axial Reduction in Real `M₈(ℝ)` -/

/-- Totally antisymmetric 4D Levi-Civita symbol `ε_{abcd} ∈ {-1, 0, 1}` over `Fin 4`. -/
def leviCivita4 (a b c d : Fin 4) : ℤ :=
  if a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d then 0
  else
    let inv :=
      (if b.val < a.val then 1 else 0) +
      (if c.val < a.val then 1 else 0) +
      (if d.val < a.val then 1 else 0) +
      (if c.val < b.val then 1 else 0) +
      (if d.val < b.val then 1 else 0) +
      (if d.val < c.val then 1 else 0)
    if inv % 2 = 0 then 1 else -1

/-- Lowered Dirac matrices `Γ_μ = g_{μμ} Γ^μ` over `ℤ`. -/
def gammaLowZ (μ : Fin 4) : Mat8Z := minkowskiMetricZ μ • gammaZ μ

/-- Lowered Dirac matrices `Γ_μ = g_{μμ} Γ^μ` in `M₈(ℝ)`. -/
def gammaLowR (μ : Fin 4) : Mat8R := castZ8 (gammaLowZ μ)

/-- Daviau–Lochak real `γ₅` operator `Γ^{0123} P_j ∈ M₈(ℝ)`. -/
def gamma5Real (j : Fin 3) : Mat8R := gamma0123R * quatPR j

theorem gammaLowR_eq (μ : Fin 4) : gammaLowR μ = minkowskiMetricR μ • gammaR μ := by
  dsimp [gammaLowR, gammaLowZ, gammaR, minkowskiMetricR]
  rw [castZ8_zsmul]

theorem gamma5Real_sq (j : Fin 3) : gamma5Real j * gamma5Real j = (1 : Mat8R) :=
  chiralInvolutionOp_sq j

theorem gamma5Real_anticomm (j : Fin 3) (μ : Fin 4) :
    gamma5Real j * gammaR μ + gammaR μ * gamma5Real j = 0 := by
  dsimp [gamma5Real]
  have hc := gammaR_comm_quatPR μ j
  have ha := gamma0123R_anticomm_gammaR μ
  calc
    gamma0123R * quatPR j * gammaR μ + gammaR μ * (gamma0123R * quatPR j)
        = (gamma0123R * gammaR μ + gammaR μ * gamma0123R) * quatPR j := by
          calc
            gamma0123R * quatPR j * gammaR μ + gammaR μ * (gamma0123R * quatPR j)
                = gamma0123R * (quatPR j * gammaR μ) + (gammaR μ * gamma0123R) * quatPR j := by
                  simp [mul_assoc]
            _ = gamma0123R * (gammaR μ * quatPR j) + (gammaR μ * gamma0123R) * quatPR j := by
                  rw [← hc]
            _ = (gamma0123R * gammaR μ + gammaR μ * gamma0123R) * quatPR j := by
                  simp [mul_assoc, add_mul]
    _ = 0 * quatPR j := by rw [ha]
    _ = 0 := zero_mul _

theorem leviCivita4_swap12 (a b c d : Fin 4) :
    leviCivita4 b a c d = -leviCivita4 a b c d := by
  revert a b c d; decide

theorem leviCivita4_swap23 (a b c d : Fin 4) :
    leviCivita4 a c b d = -leviCivita4 a b c d := by
  revert a b c d; decide

private def gammaSp : Fin 4 → SpMat8Z
  | ⟨0, _⟩ => ⟨![0, 1, 2, 3, 4, 5, 6, 7], ![1, 1, 1, 1, -1, -1, -1, -1]⟩
  | ⟨1, _⟩ => ⟨![5, 4, 7, 6, 1, 0, 3, 2], ![1, -1, -1, 1, 1, -1, -1, 1]⟩
  | ⟨2, _⟩ => ⟨![6, 7, 4, 5, 2, 3, 0, 1], ![1, -1, 1, -1, -1, 1, -1, 1]⟩
  | ⟨3, _⟩ => ⟨![7, 6, 5, 4, 3, 2, 1, 0], ![1, 1, 1, 1, -1, -1, -1, -1]⟩

private def gammaLowSp (μ : Fin 4) : SpMat8Z :=
  ⟨(gammaSp μ).col, fun i => minkowskiMetricZ μ * (gammaSp μ).sgn i⟩

private def g0123Sp : SpMat8Z :=
  ⟨![4, 5, 6, 7, 0, 1, 2, 3], ![1, 1, -1, -1, -1, -1, 1, 1]⟩

private def p1Sp : SpMat8Z :=
  ⟨![1, 0, 3, 2, 5, 4, 7, 6], ![1, -1, -1, 1, 1, -1, -1, 1]⟩

private def p3Sp : SpMat8Z :=
  ⟨![3, 2, 1, 0, 7, 6, 5, 4], ![-1, 1, -1, 1, 1, -1, 1, -1]⟩

private def tripleTermSp (a μ b : Fin 4) : SpMat8Z :=
  ((gammaSp μ).mul (gammaSp a)).mul (gammaSp b)

private theorem gammaSp_toMat (μ : Fin 4) : (gammaSp μ).toMat = gammaZ μ := by
  fin_cases μ <;> decide

private theorem gammaLowSp_toMat (μ : Fin 4) : (gammaLowSp μ).toMat = gammaLowZ μ := by
  fin_cases μ <;> decide

private theorem g0123Sp_toMat : g0123Sp.toMat = gamma0123Z := by decide
private theorem p1Sp_toMat : p1Sp.toMat = p1Z := by decide
private theorem p3Sp_toMat : p3Sp.toMat = p3Z := by decide

private lemma castZ8_sp_mulVec (A : SpMat8Z) (v : Vec8R) (i : Fin 8) :
    (castZ8 A.toMat).mulVec v i = (A.sgn i : ℝ) * v (A.col i) := by
  dsimp [Matrix.mulVec, dotProduct, castZ8]
  rw [Finset.sum_eq_single (A.col i)]
  · simp [RingHom.mapMatrix_apply, SpMat8Z.toMat]
  · intro b _ hb
    simp [RingHom.mapMatrix_apply, SpMat8Z.toMat, hb]
  · intro hm
    exact False.elim (hm (Finset.mem_univ _))

private lemma kreinInnerProduct_eq (u v : Vec8R) :
    kreinInnerProduct u v =
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 -
        u 4 * v 4 - u 5 * v 5 - u 6 * v 6 - u 7 * v 7 := by
  dsimp [kreinInnerProduct,
    InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinInnerProduct,
    InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  ring

private lemma kreinInner_sp_mulVec (A : SpMat8Z) (u v : Vec8R) :
    kreinInnerProduct u ((castZ8 A.toMat).mulVec v) =
      u 0 * ((A.sgn 0 : ℝ) * v (A.col 0)) +
      u 1 * ((A.sgn 1 : ℝ) * v (A.col 1)) +
      u 2 * ((A.sgn 2 : ℝ) * v (A.col 2)) +
      u 3 * ((A.sgn 3 : ℝ) * v (A.col 3)) -
      u 4 * ((A.sgn 4 : ℝ) * v (A.col 4)) -
      u 5 * ((A.sgn 5 : ℝ) * v (A.col 5)) -
      u 6 * ((A.sgn 6 : ℝ) * v (A.col 6)) -
      u 7 * ((A.sgn 7 : ℝ) * v (A.col 7)) := by
  rw [kreinInnerProduct_eq]
  simp only [castZ8_sp_mulVec]

private theorem triple_leviCivita_sp (a μ b ν : Fin 4) :
    leviCivita4 a μ b ν = 0 ∨
    (leviCivita4 a μ b ν ≠ 0 ∧ ∀ i : Fin 8,
      (tripleTermSp a μ b).col i = ((gammaLowSp ν).mul g0123Sp).col i ∧
      leviCivita4 a μ b ν * (tripleTermSp a μ b).sgn i =
        ((gammaLowSp ν).mul g0123Sp).sgn i) := by
  revert a μ b ν; decide

private theorem leviCivita4_nonzero_count (ν : Fin 4) :
    (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
      if leviCivita4 a μ b ν = 0 then (0 : ℤ) else 1) = 6 := by
  revert ν; decide

private theorem leviCivita4_triple_term (a μ b ν : Fin 4) :
    leviCivita4 a μ b ν • (gammaZ μ * gammaZ a * gammaZ b) =
      (if leviCivita4 a μ b ν = 0 then (0 : ℤ) else 1) • (gammaLowZ ν * gamma0123Z) := by
  rcases triple_leviCivita_sp a μ b ν with h0 | ⟨hne, hmatch⟩
  · simp [h0]
  · simp only [hne, ↓reduceIte, one_zsmul]
    rw [← gammaSp_toMat μ, ← gammaSp_toMat a, ← gammaSp_toMat b,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul,
      ← gammaLowSp_toMat ν, ← g0123Sp_toMat, ← SpMat8Z.toMat_mul]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, SpMat8Z.toMat, mul_ite, mul_zero]
    have hm := hmatch i
    dsimp only [tripleTermSp] at hm
    rw [hm.1, hm.2]

private theorem leviCivita4_triple_gammaZ (ν : Fin 4) :
    ∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
      leviCivita4 a μ b ν • (gammaZ μ * gammaZ a * gammaZ b) =
    (6 : ℤ) • (gammaLowZ ν * gamma0123Z) := by
  simp_rw [fun a μ b => leviCivita4_triple_term a μ b ν, ← Finset.sum_smul]
  rw [leviCivita4_nonzero_count ν]

/-- Axial triple-gamma identity `∑_{a,μ,b} ε_{aμbν} Γ^μ Γ^a Γ^b = 6 Γ_ν Γ^{0123}` in `M₈(ℝ)`. -/
theorem rodichev_leviCivita_triple_gamma (ν : Fin 4) :
    ∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
      (leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b) =
    (6 : ℝ) • (gammaLowR ν * gamma0123R) := by
  have hZ := congrArg castZ8 (leviCivita4_triple_gammaZ ν)
  have hmap : ∀ M : Mat8Z, castZ8 M = (Int.castRingHom ℝ).mapMatrix M := fun _ => rfl
  have hLHS :
      castZ8 (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
        leviCivita4 a μ b ν • (gammaZ μ * gammaZ a * gammaZ b)) =
      ∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
        (leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b) := by
    simp only [hmap, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun b _ => ?_
    change castZ8 (leviCivita4 a μ b ν • (gammaZ μ * gammaZ a * gammaZ b)) = _
    rw [castZ8_zsmul, castZ8_mul, castZ8_mul]
    rfl
  rw [hLHS, castZ8_zsmul, castZ8_mul] at hZ
  have h6 : ((6 : ℤ) : ℝ) = (6 : ℝ) := by norm_num
  rw [h6] at hZ
  exact hZ

/-- Rodichev totally skew torsion tensor `Φ_{[aμb]} = ∑_ν ε_{aμbν} σ^ν` dual to axial
pseudovector `σ`. -/
def rodichevTorsion (σ : Fin 4 → ℝ) (a μ b : Fin 4) : ℝ :=
  ∑ ν : Fin 4, (leviCivita4 a μ b ν : ℝ) * σ ν

theorem rodichevTorsion_antisymm12 (σ : Fin 4 → ℝ) (a μ b : Fin 4) :
    rodichevTorsion σ μ a b = -rodichevTorsion σ a μ b := by
  dsimp [rodichevTorsion]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [leviCivita4_swap12, Int.cast_neg, neg_mul]

theorem rodichevTorsion_antisymm23 (σ : Fin 4 → ℝ) (a μ b : Fin 4) :
    rodichevTorsion σ a b μ = -rodichevTorsion σ a μ b := by
  dsimp [rodichevTorsion]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [leviCivita4_swap23, Int.cast_neg, neg_mul]

/-- **Rodichev Skew-Torsion Axial Reduction (Lochak Eqs. 8–13)** in real `M₈(ℝ)`:
`∑_{a,μ,b} Φ_{[aμb]} Γ^μ Γ^a Γ^b = 6 ∑_ν σ^ν Γ_ν Γ^{0123}`. -/
theorem rodichev_skew_torsion_axial_reduction (σ : Fin 4 → ℝ) :
    ∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
      rodichevTorsion σ a μ b • (gammaR μ * gammaR a * gammaR b) =
    (6 : ℝ) • ∑ ν : Fin 4, σ ν • (gammaLowR ν * gamma0123R) := by
  have step1 :
      (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
        rodichevTorsion σ a μ b • (gammaR μ * gammaR a * gammaR b)) =
      ∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4, ∑ ν : Fin 4,
        σ ν • ((leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b)) := by
    refine Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun b _ => ?_
    dsimp [rodichevTorsion]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul, mul_comm]
  rw [step1]
  have swap2 :
      (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4, ∑ ν : Fin 4,
        σ ν • ((leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b))) =
      ∑ ν : Fin 4, σ ν • (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
        (leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b)) := by
    calc
      (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4, ∑ ν : Fin 4,
        σ ν • ((leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b)))
          = ∑ a : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ b : Fin 4,
              σ ν • ((leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun μ _ => Finset.sum_comm
      _ = ∑ a : Fin 4, ∑ ν : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
            σ ν • ((leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ ν : Fin 4, ∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
            σ ν • ((leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b)) := Finset.sum_comm
      _ = ∑ ν : Fin 4, σ ν • (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
            (leviCivita4 a μ b ν : ℝ) • (gammaR μ * gammaR a * gammaR b)) := by
            refine Finset.sum_congr rfl fun ν _ => ?_
            simp only [Finset.smul_sum]
  rw [swap2]
  simp_rw [rodichev_leviCivita_triple_gamma]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [smul_comm]

/-- Chiral-gauge axial factor: right-multiplying by `-(1 / 12 : ℝ) • P_j` converts
`6 ∑ σ^ν Γ_ν Γ^{0123}` into `-(1 / 2) ∑ σ^ν Γ_ν γ₅` (Lochak Eq. 13). -/
theorem rodichev_chiral_torsion_dirac_term (σ : Fin 4 → ℝ) (j : Fin 3) :
    (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
      rodichevTorsion σ a μ b • (gammaR μ * gammaR a * gammaR b)) *
        (-(1 / 12 : ℝ) • quatPR j) =
    -(1 / 2 : ℝ) • ∑ ν : Fin 4, σ ν • (gammaLowR ν * gamma5Real j) := by
  rw [rodichev_skew_torsion_axial_reduction σ, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Finset.sum_mul]
  have hterm : ∀ ν : Fin 4,
      (σ ν • (gammaLowR ν * gamma0123R)) * quatPR j = σ ν • (gammaLowR ν * gamma5Real j) := by
    intro ν
    rw [Matrix.smul_mul, mul_assoc]
    rfl
  rw [Finset.sum_congr rfl fun ν _ => hterm ν]
  congr 1
  norm_num

/-! ### Section 2: Krein `(4,4)` Bilinear Densities & Fierz–Takabayasi Identity (Lochak Eq. 39) -/

/-- Scalar bilinear density `Ω₁ = Φ̅ Φ = Φᵀ Γ⁰ Φ` using `KreinMajoranaBlockInvariance.kreinInnerProduct`. -/
def omega1 (Φ : Vec8R) : ℝ := kreinInnerProduct Φ Φ

/-- Pseudoscalar bilinear density `Ω₂ = Φ̅ Γ^{0123} Φ`. -/
def omega2 (Φ : Vec8R) : ℝ := kreinInnerProduct Φ (gamma0123R.mulVec Φ)

/-- Electric probability current density `J^μ = Φ̅ Γ^μ Φ` (Daviau Eq. 10, Lochak Eq. 18/31). -/
def electricCurrentJ (Φ : Vec8R) (μ : Fin 4) : ℝ :=
  kreinInnerProduct Φ ((gammaR μ).mulVec Φ)

/-- Axial magnetic current density `Σ^μ = Φ̅ Γ^μ γ₅ Φ` with `γ₅ = Γ^{0123} P₃`. -/
def axialCurrentSigma (Φ : Vec8R) (μ : Fin 4) : ℝ :=
  kreinInnerProduct Φ ((gammaR μ * gamma5Real ⟨2, by decide⟩).mulVec Φ)

/-- Minkowski bilinear inner product `u₀ v₀ - u₁ v₁ - u₂ v₂ - u₃ v₃` (`+---`, Daviau convention). -/
def minkowskiDot (u v : Fin 4 → ℝ) : ℝ :=
  u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

/-- Euclideanized `x₄ = i c t` inner product convention `-g_{μν} u^μ v^ν` used in Lochak Eq. (39)
(`-+++`, so `-J_μ J^μ = Σ_μ Σ^μ = Ω₁² + Ω₂²`). -/
def lochakDot (u v : Fin 4 → ℝ) : ℝ :=
  -minkowskiDot u v

private lemma gammaR_eq_sp (μ : Fin 4) : gammaR μ = castZ8 (gammaSp μ).toMat := by
  dsimp [gammaR]; rw [gammaSp_toMat μ]

private lemma gamma5_op_eq_sp (μ : Fin 4) :
    gammaR μ * gamma5Real 2 = castZ8 ((gammaSp μ).mul (g0123Sp.mul p3Sp)).toMat := by
  dsimp [gamma5Real, gammaR, gamma0123R, quatPR, quatPZ]
  rw [← gammaSp_toMat μ, ← g0123Sp_toMat, ← p3Sp_toMat,
    ← castZ8_mul, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul]

lemma omega1_expand (Φ : Vec8R) :
    omega1 Φ =
      Φ 0 ^ 2 + Φ 1 ^ 2 + Φ 2 ^ 2 + Φ 3 ^ 2 - Φ 4 ^ 2 - Φ 5 ^ 2 - Φ 6 ^ 2 - Φ 7 ^ 2 := by
  dsimp [omega1]
  rw [kreinInnerProduct_eq]
  ring

lemma omega2_expand (Φ : Vec8R) :
    omega2 Φ =
      2 * (Φ 0 * Φ 4 + Φ 1 * Φ 5 - Φ 2 * Φ 6 - Φ 3 * Φ 7) := by
  dsimp [omega2, gamma0123R]
  rw [← g0123Sp_toMat, kreinInner_sp_mulVec]
  simp [g0123Sp]
  ring

lemma electricCurrentJ0_expand (Φ : Vec8R) :
    electricCurrentJ Φ 0 =
      Φ 0 ^ 2 + Φ 1 ^ 2 + Φ 2 ^ 2 + Φ 3 ^ 2 + Φ 4 ^ 2 + Φ 5 ^ 2 + Φ 6 ^ 2 + Φ 7 ^ 2 := by
  dsimp [electricCurrentJ]
  rw [gammaR_eq_sp 0, kreinInner_sp_mulVec]
  simp [gammaSp]
  ring

private lemma electricCurrentJ1_expand (Φ : Vec8R) :
    electricCurrentJ Φ 1 =
      2 * (Φ 0 * Φ 5 - Φ 1 * Φ 4 - Φ 2 * Φ 7 + Φ 3 * Φ 6) := by
  dsimp [electricCurrentJ]
  rw [gammaR_eq_sp 1, kreinInner_sp_mulVec]
  simp [gammaSp]
  ring

private lemma electricCurrentJ2_expand (Φ : Vec8R) :
    electricCurrentJ Φ 2 =
      2 * (Φ 0 * Φ 6 - Φ 1 * Φ 7 + Φ 2 * Φ 4 - Φ 3 * Φ 5) := by
  dsimp [electricCurrentJ]
  rw [gammaR_eq_sp 2, kreinInner_sp_mulVec]
  simp [gammaSp]
  ring

private lemma electricCurrentJ3_expand (Φ : Vec8R) :
    electricCurrentJ Φ 3 =
      2 * (Φ 0 * Φ 7 + Φ 1 * Φ 6 + Φ 2 * Φ 5 + Φ 3 * Φ 4) := by
  dsimp [electricCurrentJ]
  rw [gammaR_eq_sp 3, kreinInner_sp_mulVec]
  simp [gammaSp]
  ring

lemma axialCurrentSigma0_expand (Φ : Vec8R) :
    axialCurrentSigma Φ 0 =
      2 * (Φ 0 * Φ 7 - Φ 1 * Φ 6 - Φ 2 * Φ 5 + Φ 3 * Φ 4) := by
  dsimp [axialCurrentSigma]
  rw [gamma5_op_eq_sp 0, kreinInner_sp_mulVec]
  simp [SpMat8Z.mul, gammaSp, g0123Sp, p3Sp]
  ring

private lemma axialCurrentSigma1_expand (Φ : Vec8R) :
    axialCurrentSigma Φ 1 =
      2 * (-Φ 0 * Φ 2 - Φ 1 * Φ 3 + Φ 4 * Φ 6 + Φ 5 * Φ 7) := by
  dsimp [axialCurrentSigma]
  rw [gamma5_op_eq_sp 1, kreinInner_sp_mulVec]
  simp [SpMat8Z.mul, gammaSp, g0123Sp, p3Sp]
  ring

private lemma axialCurrentSigma2_expand (Φ : Vec8R) :
    axialCurrentSigma Φ 2 =
      2 * (-Φ 0 * Φ 1 + Φ 2 * Φ 3 - Φ 4 * Φ 5 + Φ 6 * Φ 7) := by
  dsimp [axialCurrentSigma]
  rw [gamma5_op_eq_sp 2, kreinInner_sp_mulVec]
  simp [SpMat8Z.mul, gammaSp, g0123Sp, p3Sp]
  ring

private lemma axialCurrentSigma3_expand (Φ : Vec8R) :
    axialCurrentSigma Φ 3 =
      Φ 0 ^ 2 - Φ 1 ^ 2 - Φ 2 ^ 2 + Φ 3 ^ 2 + Φ 4 ^ 2 - Φ 5 ^ 2 - Φ 6 ^ 2 + Φ 7 ^ 2 := by
  dsimp [axialCurrentSigma]
  rw [gamma5_op_eq_sp 3, kreinInner_sp_mulVec]
  simp [SpMat8Z.mul, gammaSp, g0123Sp, p3Sp]
  ring

/-- Minkowski timelike identity `g_{μν} J^μ J^ν = Ω₁² + Ω₂²`. -/
theorem fierz_takabayasi_J_sq (Φ : Vec8R) :
    minkowskiDot (electricCurrentJ Φ) (electricCurrentJ Φ) = omega1 Φ ^ 2 + omega2 Φ ^ 2 := by
  dsimp [minkowskiDot]
  rw [electricCurrentJ0_expand, electricCurrentJ1_expand, electricCurrentJ2_expand,
    electricCurrentJ3_expand, omega1_expand, omega2_expand]
  ring

/-- Minkowski spacelike identity `g_{μν} Σ^μ Σ^ν = -(Ω₁² + Ω₂²)`. -/
theorem fierz_takabayasi_Sigma_sq (Φ : Vec8R) :
    minkowskiDot (axialCurrentSigma Φ) (axialCurrentSigma Φ) = -(omega1 Φ ^ 2 + omega2 Φ ^ 2) := by
  dsimp [minkowskiDot]
  rw [axialCurrentSigma0_expand, axialCurrentSigma1_expand, axialCurrentSigma2_expand,
    axialCurrentSigma3_expand, omega1_expand, omega2_expand]
  ring

/-- Exact orthogonality of electric and magnetic currents: `g_{μν} J^μ Σ^ν = 0`. -/
theorem fierz_takabayasi_J_ortho_Sigma (Φ : Vec8R) :
    minkowskiDot (electricCurrentJ Φ) (axialCurrentSigma Φ) = 0 := by
  dsimp [minkowskiDot]
  rw [electricCurrentJ0_expand, electricCurrentJ1_expand, electricCurrentJ2_expand,
    electricCurrentJ3_expand, axialCurrentSigma0_expand, axialCurrentSigma1_expand,
    axialCurrentSigma2_expand, axialCurrentSigma3_expand]
  ring

/-- **Lochak Eq. (39) (Pauli–Kofink / Fierz–Takabayasi Identity)**:
`-J_μ J^μ = Σ_μ Σ^μ = Ω₁² + Ω₂²` (with `lochakDot` matching Lochak's signature convention). -/
theorem lochak_eq39_fierz_takabayasi (Φ : Vec8R) :
    -lochakDot (electricCurrentJ Φ) (electricCurrentJ Φ) =
      lochakDot (axialCurrentSigma Φ) (axialCurrentSigma Φ) ∧
    lochakDot (axialCurrentSigma Φ) (axialCurrentSigma Φ) =
      omega1 Φ ^ 2 + omega2 Φ ^ 2 := by
  dsimp [lochakDot]
  rw [neg_neg, fierz_takabayasi_J_sq, fierz_takabayasi_Sigma_sq, neg_neg]
  exact ⟨rfl, rfl⟩

private def chiralSign3Sp : SpMat8Z := g0123Sp.mul p3Sp

private lemma peirceLeft2_mulVec_apply (Φ : Vec8R) :
    (peirceLeft ⟨2, by decide⟩).mulVec Φ =
      (1 / 2 : ℝ) • (Φ - (castZ8 chiralSign3Sp.toMat).mulVec Φ) := by
  rw [peirceLeft_eq_half_cast]
  dsimp [twoPeirceLeftZ, quatPZ, chiralSign3Sp]
  rw [← g0123Sp_toMat, ← p3Sp_toMat, ← SpMat8Z.toMat_mul, castZ8_sub, castZ8_one,
    Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]

private lemma peirceRight2_mulVec_apply (Φ : Vec8R) :
    (peirceRight ⟨2, by decide⟩).mulVec Φ =
      (1 / 2 : ℝ) • (Φ + (castZ8 chiralSign3Sp.toMat).mulVec Φ) := by
  rw [peirceRight_eq_half_cast]
  dsimp [twoPeirceRightZ, quatPZ, chiralSign3Sp]
  rw [← g0123Sp_toMat, ← p3Sp_toMat, ← SpMat8Z.toMat_mul, castZ8_add, castZ8_one,
    Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]

/-- Chiral cross-pairing identity purely in `M₈(ℝ)`: `Ω₁(Φ)` equals `2 ⟨Φ_L, Φ_R⟩_Krein`. -/
theorem omega1_eq_two_chiral_cross (Φ : Vec8R) :
    omega1 Φ = 2 * kreinInnerProduct ((peirceLeft ⟨2, by decide⟩).mulVec Φ)
      ((peirceRight ⟨2, by decide⟩).mulVec Φ) := by
  rw [omega1_expand, peirceLeft2_mulVec_apply, peirceRight2_mulVec_apply, kreinInnerProduct_eq]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, castZ8_sp_mulVec]
  simp [chiralSign3Sp, SpMat8Z.mul, g0123Sp, p3Sp]
  ring

/-- Chiral cross-pairing identity purely in `M₈(ℝ)`: `Ω₂(Φ)` equals `2 ⟨Φ_L, Γ^{0123} Φ_R⟩_Krein`. -/
theorem omega2_eq_two_chiral_cross (Φ : Vec8R) :
    omega2 Φ = 2 * kreinInnerProduct ((peirceLeft ⟨2, by decide⟩).mulVec Φ)
      (gamma0123R.mulVec ((peirceRight ⟨2, by decide⟩).mulVec Φ)) := by
  rw [omega2_expand, peirceLeft2_mulVec_apply, peirceRight2_mulVec_apply]
  have hG : gamma0123R.mulVec ((1 / 2 : ℝ) • (Φ + (castZ8 chiralSign3Sp.toMat).mulVec Φ)) =
      (1 / 2 : ℝ) • ((castZ8 g0123Sp.toMat).mulVec Φ +
        (castZ8 (g0123Sp.mul chiralSign3Sp).toMat).mulVec Φ) := by
    dsimp [gamma0123R]
    rw [← g0123Sp_toMat, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      ← castZ8_mul, ← SpMat8Z.toMat_mul]
  rw [hG, kreinInnerProduct_eq]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, castZ8_sp_mulVec]
  simp [chiralSign3Sp, SpMat8Z.mul, g0123Sp, p3Sp]
  ring

/-! ### Section 3: Weyl Spinors & Null Lightcone Majorana Orthogonality (Lochak Eqs. 27, 47) -/

/-- Daviau Eq. (3) bijection `Φ ∈ ℝ⁸ ↦ ψ ∈ ℂ⁴` recovering the complex Dirac spinor for Weyl
comparison (Lochak Eq. 27 / 47). -/
def phiToPsi (Φ : Vec8R) : Fin 4 → ℂ
  | ⟨0, _⟩ => ⟨Φ 0, Φ 3⟩
  | ⟨1, _⟩ => ⟨-Φ 2, -Φ 1⟩
  | ⟨2, _⟩ => ⟨Φ 7, Φ 4⟩
  | ⟨3, _⟩ => ⟨Φ 5, Φ 6⟩

/-- Left-hand Weyl 2-spinor `ξ = (1/√2)(ψ_up + ψ_down)` (Lochak Eq. 27). -/
def weylXi (Φ : Vec8R) : Fin 2 → ℂ :=
  fun k => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (phiToPsi Φ ⟨k.val, by omega⟩ + phiToPsi Φ ⟨k.val + 2, by omega⟩)

/-- Right-hand Weyl 2-spinor `η = (1/√2)(ψ_up - ψ_down)` (Lochak Eq. 27). -/
def weylEta (Φ : Vec8R) : Fin 2 → ℂ :=
  fun k => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (phiToPsi Φ ⟨k.val, by omega⟩ - phiToPsi Φ ⟨k.val + 2, by omega⟩)

/-- Hermitian Weyl cross-pairing `ξ† η = ξ₀* η₀ + ξ₁* η₁`. -/
def weylCrossInner (Φ : Vec8R) : ℂ :=
  star (weylXi Φ 0) * weylEta Φ 0 + star (weylXi Φ 1) * weylEta Φ 1

lemma inv_sqrt2_sq : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = 1 / 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [hs]

theorem weylCrossInner_re (Φ : Vec8R) :
    (weylCrossInner Φ).re = omega1 Φ / 2 := by
  dsimp [weylCrossInner, weylXi, weylEta, phiToPsi]
  rw [omega1_expand]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, zero_mul, add_zero]
  linear_combination (Φ 0 ^ 2 + Φ 1 ^ 2 + Φ 2 ^ 2 + Φ 3 ^ 2 - Φ 4 ^ 2 - Φ 5 ^ 2 - Φ 6 ^ 2 - Φ 7 ^ 2) *
    inv_sqrt2_sq

theorem weylCrossInner_im (Φ : Vec8R) :
    (weylCrossInner Φ).im = -(omega2 Φ / 2) := by
  dsimp [weylCrossInner, weylXi, weylEta, phiToPsi]
  rw [omega2_expand]
  simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, zero_mul, add_zero]
  linear_combination (-2 * (Φ 0 * Φ 4 + Φ 1 * Φ 5 - Φ 2 * Φ 6 - Φ 3 * Φ 7)) * inv_sqrt2_sq

/-! ### Real Weyl coordinates and the internal bivector bound

The complex-valued Weyl comparison above is useful for matching Lochak's notation.  The
following real coordinates retain its two chiral sectors and the phase-plane rotation as a real
operator, so the density and bound statements themselves use only real scalars.
-/

/-- Unnormalised real coordinates of the left Weyl sector under Daviau's realification. -/
def realWeylLeft (Φ : Vec8R) : Fin 4 → ℝ :=
  ![Φ 0 + Φ 7, Φ 3 + Φ 4, -Φ 2 + Φ 5, -Φ 1 + Φ 6]

/-- Unnormalised real coordinates of the right Weyl sector under Daviau's realification. -/
def realWeylRight (Φ : Vec8R) : Fin 4 → ℝ :=
  ![Φ 0 - Φ 7, Φ 3 - Φ 4, -Φ 2 - Φ 5, -Φ 1 - Φ 6]

/-- The internal real bivector rotation on the two chiral phase planes. -/
def realWeylBivector (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-x 1, x 0, -x 3, x 2]

/-- Real form of the simultaneous two-sector unit-quaternion action.  The four real
parameters satisfy the unit-sphere relation in `realWeylSU2_pairings_preserved`.
This is a real matrix action; the internal phase operator remains `realWeylBivector`. -/
def realWeylSU2Action (a b c d : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a * x 0 - b * x 1 + c * x 2 - d * x 3,
    b * x 0 + a * x 1 + d * x 2 + c * x 3,
    -c * x 0 - d * x 1 + a * x 2 + b * x 3,
    d * x 0 - c * x 1 - b * x 2 + a * x 3]

/-- The real action commutes with the internal Weyl bivector. -/
theorem realWeylSU2Action_commutes_bivector (a b c d : ℝ) (x : Fin 4 → ℝ) :
    realWeylSU2Action a b c d (realWeylBivector x) =
      realWeylBivector (realWeylSU2Action a b c d x) := by
  ext i
  fin_cases i <;>
    simp [realWeylSU2Action, realWeylBivector] <;> ring

/-- Under the real unit-quaternion relation, simultaneous action on two chiral sectors
preserves their Euclidean pairing. -/
theorem realWeylSU2Action_preserves_dot (a b c d : ℝ)
    (hunit : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (x y : Fin 4 → ℝ) :
    dotProduct (realWeylSU2Action a b c d x)
      (realWeylSU2Action a b c d y) = dotProduct x y := by
  simp [realWeylSU2Action, dotProduct, Fin.sum_univ_four]
  linear_combination hunit *
    (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/-- Both real Weyl pairings defining `Ω₁` and `Ω₂` are invariant when the same
real unit-quaternion matrix acts on the left and right sectors. -/
theorem realWeylSU2_pairings_preserved (a b c d : ℝ)
    (hunit : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (x y : Fin 4 → ℝ) :
    dotProduct (realWeylSU2Action a b c d x)
        (realWeylSU2Action a b c d y) = dotProduct x y ∧
    dotProduct (realWeylBivector (realWeylSU2Action a b c d x))
        (realWeylSU2Action a b c d y) = dotProduct (realWeylBivector x) y := by
  constructor
  · exact realWeylSU2Action_preserves_dot a b c d hunit x y
  · rw [← realWeylSU2Action_commutes_bivector]
    exact realWeylSU2Action_preserves_dot a b c d hunit (realWeylBivector x) y

/-- The real scalar and pseudoscalar readouts from the two Weyl sectors are
invariant under their simultaneous real unit-quaternion action. -/
theorem realWeylSU2_bilinears_preserved (a b c d : ℝ)
    (hunit : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (x y : Fin 4 → ℝ) :
    dotProduct (realWeylSU2Action a b c d x)
        (realWeylSU2Action a b c d y) = dotProduct x y ∧
    -dotProduct (realWeylBivector (realWeylSU2Action a b c d x))
        (realWeylSU2Action a b c d y) = -dotProduct (realWeylBivector x) y := by
  obtain ⟨hScalar, hPseudo⟩ := realWeylSU2_pairings_preserved a b c d hunit x y
  exact ⟨hScalar, congrArg Neg.neg hPseudo⟩

/-- The two complementary real phase-plane rotations. -/
private def realWeylBivector₂ (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-x 2, x 3, x 0, -x 1]

private def realWeylBivector₃ (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-x 3, -x 2, x 1, x 0]

/-- Squared Euclidean size of a real four-coordinate chiral sector. -/
def realWeylEnergy (x : Fin 4 → ℝ) : ℝ := dotProduct x x

/-- Total density of the two real Weyl sectors, normalized to the original real spinor density. -/
def realWeylProbabilityDensity (Φ : Vec8R) : ℝ :=
  (realWeylEnergy (realWeylLeft Φ) + realWeylEnergy (realWeylRight Φ)) / 2

/-- Chiral density difference of the two real Weyl sectors. -/
def realWeylChiralDensity (Φ : Vec8R) : ℝ :=
  (realWeylEnergy (realWeylLeft Φ) - realWeylEnergy (realWeylRight Φ)) / 2

/-- Real matrix transformation on a Weyl sector, parameterized by four real
coefficients. The unit-sphere condition is stated in the invariance theorem below. -/
def realWeylUnitQuaternionTransform (a b c d : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a * x 0 - b * x 1 + c * x 2 - d * x 3,
    b * x 0 + a * x 1 + d * x 2 + c * x 3,
    -c * x 0 - d * x 1 + a * x 2 + b * x 3,
    d * x 0 - c * x 1 - b * x 2 + a * x 3]

/-- The real unit-quaternion action on one Weyl sector, written through its four real
coordinates and the native Hamilton product on `Quaternion ℝ`. -/
def realWeylQuaternionAction (q : Quaternion ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  realWeylUnitQuaternionTransform q.re q.imI q.imJ q.imK x

/-- The coordinate transformation is a representation of the native real quaternion product. -/
theorem realWeylQuaternionAction_mul (q r : Quaternion ℝ) (x : Fin 4 → ℝ) :
    realWeylQuaternionAction q (realWeylQuaternionAction r x) =
      realWeylQuaternionAction (q * r) x := by
  ext i
  fin_cases i <;>
    simp [realWeylQuaternionAction, realWeylUnitQuaternionTransform] <;>
    ring

/-- The native real quaternion norm squared is multiplicative. -/
theorem realQuaternion_normSq_mul (q r : Quaternion ℝ) :
    Quaternion.normSq (q * r) = Quaternion.normSq q * Quaternion.normSq r := by
  rw [Quaternion.normSq_eq_norm_mul_self, norm_mul,
    Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_eq_norm_mul_self]
  ring

/-- Unit norm is closed under the product used by the Weyl-sector action. -/
theorem realQuaternion_normSq_mul_eq_one {q r : Quaternion ℝ}
    (hq : Quaternion.normSq q = 1) (hr : Quaternion.normSq r = 1) :
    Quaternion.normSq (q * r) = 1 := by
  rw [realQuaternion_normSq_mul, hq, hr]
  norm_num

/-- The identity quaternion acts identically on real Weyl coordinates. -/
theorem realWeylQuaternionAction_one (x : Fin 4 → ℝ) :
    realWeylQuaternionAction 1 x = x := by
  ext i
  fin_cases i <;>
    simp [realWeylQuaternionAction, realWeylUnitQuaternionTransform]

/-- A norm-one quaternion acts invertibly; its inverse action is conjugate
quaternion multiplication. -/
theorem realWeylQuaternionAction_star_inverse (q : Quaternion ℝ)
    (hq : Quaternion.normSq q = 1) (x : Fin 4 → ℝ) :
    realWeylQuaternionAction (star q) (realWeylQuaternionAction q x) = x ∧
    realWeylQuaternionAction q (realWeylQuaternionAction (star q) x) = x := by
  have hstar : Quaternion.normSq (star q) = 1 := by rw [Quaternion.normSq_star, hq]
  have hqstar : q * star q = 1 := by
    rw [Quaternion.self_mul_star, hq]
    simp
  have hstarq : star q * q = 1 := by
    rw [Quaternion.star_mul_self, hq]
    simp
  constructor
  · rw [realWeylQuaternionAction_mul, hstarq, realWeylQuaternionAction_one]
  · rw [realWeylQuaternionAction_mul, hqstar, realWeylQuaternionAction_one]

/-- The real unit-quaternion transformation commutes with the internal Weyl bivector. -/
theorem realWeylUnitQuaternionTransform_commutes_bivector
    (a b c d : ℝ) (x : Fin 4 → ℝ) :
    realWeylUnitQuaternionTransform a b c d (realWeylBivector x) =
      realWeylBivector (realWeylUnitQuaternionTransform a b c d x) := by
  ext i
  fin_cases i <;>
    simp [realWeylUnitQuaternionTransform, realWeylBivector] <;> ring

/-- A simultaneous real unit-quaternion transformation preserves the pairing
between the two chiral sectors. -/
theorem realWeylUnitQuaternionTransform_preserves_dot (a b c d : ℝ)
    (hunit : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (x y : Fin 4 → ℝ) :
    dotProduct (realWeylUnitQuaternionTransform a b c d x)
      (realWeylUnitQuaternionTransform a b c d y) = dotProduct x y := by
  simp [realWeylUnitQuaternionTransform, dotProduct, Fin.sum_univ_four]
  linear_combination hunit *
    (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/-- The scalar and internal-bivector pairings of real Weyl sectors are preserved
when the same unit-quaternion transformation acts on both sectors. -/
theorem realWeylUnitQuaternionTransform_preserves_bilinears (a b c d : ℝ)
    (hunit : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (x y : Fin 4 → ℝ) :
    dotProduct (realWeylUnitQuaternionTransform a b c d x)
        (realWeylUnitQuaternionTransform a b c d y) = dotProduct x y ∧
    -dotProduct (realWeylBivector
        (realWeylUnitQuaternionTransform a b c d x))
        (realWeylUnitQuaternionTransform a b c d y) =
      -dotProduct (realWeylBivector x) y := by
  constructor
  · exact realWeylUnitQuaternionTransform_preserves_dot a b c d hunit x y
  · rw [← realWeylUnitQuaternionTransform_commutes_bivector]
    exact congrArg Neg.neg
      (realWeylUnitQuaternionTransform_preserves_dot a b c d hunit
        (realWeylBivector x) y)

/-- Bilinear invariance for the native quaternion parameter: norm-one quaternion
multiplication preserves both real chiral cross-pairings. -/
theorem realWeylQuaternionAction_preserves_bilinears (q : Quaternion ℝ)
    (hq : Quaternion.normSq q = 1) (x y : Fin 4 → ℝ) :
    dotProduct (realWeylQuaternionAction q x) (realWeylQuaternionAction q y) =
        dotProduct x y ∧
    -dotProduct (realWeylBivector (realWeylQuaternionAction q x))
        (realWeylQuaternionAction q y) = -dotProduct (realWeylBivector x) y := by
  have hcoords : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    simpa [Quaternion.normSq_def'] using hq
  simpa [realWeylQuaternionAction] using
    realWeylUnitQuaternionTransform_preserves_bilinears
      q.re q.imI q.imJ q.imK hcoords x y

private theorem real_weyl_energy_frame (x y : Fin 4 → ℝ) :
    realWeylEnergy x * realWeylEnergy y =
      (dotProduct x y) ^ 2 +
        (dotProduct (realWeylBivector x) y) ^ 2 +
        (dotProduct (realWeylBivector₂ x) y) ^ 2 +
        (dotProduct (realWeylBivector₃ x) y) ^ 2 := by
  simp [realWeylEnergy, realWeylBivector, realWeylBivector₂,
    realWeylBivector₃, dotProduct, Fin.sum_univ_four]
  ring

private theorem omega1_real_weyl_coordinates (Φ : Vec8R) :
    omega1 Φ = dotProduct (realWeylLeft Φ) (realWeylRight Φ) := by
  rw [omega1_expand]
  simp [realWeylLeft, realWeylRight, dotProduct, Fin.sum_univ_four]
  ring

private theorem omega2_real_weyl_coordinates (Φ : Vec8R) :
    omega2 Φ = -dotProduct (realWeylBivector (realWeylLeft Φ))
      (realWeylRight Φ) := by
  rw [omega2_expand]
  simp [realWeylLeft, realWeylRight, realWeylBivector, dotProduct,
    Fin.sum_univ_four]
  ring

/-- Reconstruct the real Dirac carrier from its two real Weyl coordinate vectors.
The half-sums invert the unnormalised sum/difference convention in
`realWeylLeft` and `realWeylRight`. -/
def realWeylJoin (x y : Fin 4 → ℝ) : Vec8R :=
  ![(x 0 + y 0) / 2, -(x 3 + y 3) / 2, -(x 2 + y 2) / 2,
    (x 1 + y 1) / 2, (x 1 - y 1) / 2, (x 2 - y 2) / 2,
    (x 3 - y 3) / 2, (x 0 - y 0) / 2]

@[simp] theorem realWeylLeft_realWeylJoin (x y : Fin 4 → ℝ) :
    realWeylLeft (realWeylJoin x y) = x := by
  ext i
  fin_cases i <;> simp [realWeylLeft, realWeylJoin] <;> ring

@[simp] theorem realWeylRight_realWeylJoin (x y : Fin 4 → ℝ) :
    realWeylRight (realWeylJoin x y) = y := by
  ext i
  fin_cases i <;> simp [realWeylRight, realWeylJoin] <;> ring

theorem realWeylJoin_realWeylLeft_right (Φ : Vec8R) :
    realWeylJoin (realWeylLeft Φ) (realWeylRight Φ) = Φ := by
  funext i
  fin_cases i <;> simp [realWeylLeft, realWeylRight, realWeylJoin] <;> ring

/-- Lift the existing real unit-quaternion action on both Weyl sectors to the
original real `Vec8R` spinor carrier. -/
def realWeylQuaternionSpinorAction (q : Quaternion ℝ) (Φ : Vec8R) : Vec8R :=
  realWeylJoin (realWeylQuaternionAction q (realWeylLeft Φ))
    (realWeylQuaternionAction q (realWeylRight Φ))

@[simp] theorem realWeylLeft_quaternionSpinorAction (q : Quaternion ℝ) (Φ : Vec8R) :
    realWeylLeft (realWeylQuaternionSpinorAction q Φ) =
      realWeylQuaternionAction q (realWeylLeft Φ) := by
  simp [realWeylQuaternionSpinorAction]

@[simp] theorem realWeylRight_quaternionSpinorAction (q : Quaternion ℝ) (Φ : Vec8R) :
    realWeylRight (realWeylQuaternionSpinorAction q Φ) =
      realWeylQuaternionAction q (realWeylRight Φ) := by
  simp [realWeylQuaternionSpinorAction]

/-- The total real Weyl-sector energy is the time component of Daviau's vector current. -/
theorem realWeylProbabilityDensity_eq_electricCurrentJ0 (Φ : Vec8R) :
    realWeylProbabilityDensity Φ = electricCurrentJ Φ 0 := by
  rw [electricCurrentJ0_expand]
  simp [realWeylProbabilityDensity, realWeylEnergy, realWeylLeft,
    realWeylRight, dotProduct, Fin.sum_univ_four]
  ring

/-- The real Weyl-sector energy difference is the time component of the axial current. -/
theorem realWeylChiralDensity_eq_axialCurrentSigma0 (Φ : Vec8R) :
    realWeylChiralDensity Φ = axialCurrentSigma Φ 0 := by
  rw [axialCurrentSigma0_expand]
  simp [realWeylChiralDensity, realWeylEnergy, realWeylLeft,
    realWeylRight, dotProduct, Fin.sum_univ_four]
  ring

/-- On the real Dirac carrier, simultaneous norm-one quaternion action preserves
the two scalar cross-bilinears and the time components of the vector and axial
currents. This is a finite-dimensional real algebraic invariance theorem. -/
theorem realWeylQuaternionSpinorAction_preserves_readouts (q : Quaternion ℝ)
    (hq : Quaternion.normSq q = 1) (Φ : Vec8R) :
    omega1 (realWeylQuaternionSpinorAction q Φ) = omega1 Φ ∧
    omega2 (realWeylQuaternionSpinorAction q Φ) = omega2 Φ ∧
    electricCurrentJ (realWeylQuaternionSpinorAction q Φ) 0 = electricCurrentJ Φ 0 ∧
    axialCurrentSigma (realWeylQuaternionSpinorAction q Φ) 0 = axialCurrentSigma Φ 0 := by
  have hpair := realWeylQuaternionAction_preserves_bilinears q hq
      (realWeylLeft Φ) (realWeylRight Φ)
  have hsectorLeft := realWeylQuaternionAction_preserves_bilinears q hq
      (realWeylLeft Φ) (realWeylLeft Φ)
  have hsectorRight := realWeylQuaternionAction_preserves_bilinears q hq
      (realWeylRight Φ) (realWeylRight Φ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [omega1_real_weyl_coordinates, omega1_real_weyl_coordinates,
      realWeylLeft_quaternionSpinorAction, realWeylRight_quaternionSpinorAction]
    exact hpair.1
  · rw [omega2_real_weyl_coordinates, omega2_real_weyl_coordinates,
      realWeylLeft_quaternionSpinorAction, realWeylRight_quaternionSpinorAction]
    exact hpair.2
  · rw [← realWeylProbabilityDensity_eq_electricCurrentJ0,
      ← realWeylProbabilityDensity_eq_electricCurrentJ0]
    simp only [realWeylProbabilityDensity, realWeylEnergy,
      realWeylLeft_quaternionSpinorAction, realWeylRight_quaternionSpinorAction]
    rw [hsectorLeft.1, hsectorRight.1]
  · rw [← realWeylChiralDensity_eq_axialCurrentSigma0,
      ← realWeylChiralDensity_eq_axialCurrentSigma0]
    simp only [realWeylChiralDensity, realWeylEnergy,
      realWeylLeft_quaternionSpinorAction, realWeylRight_quaternionSpinorAction]
    rw [hsectorLeft.1, hsectorRight.1]

/-- The square difference of total and chiral densities is the product of the two sector
energies. -/
theorem realWeyl_density_difference (Φ : Vec8R) :
    realWeylProbabilityDensity Φ ^ 2 - realWeylChiralDensity Φ ^ 2 =
      realWeylEnergy (realWeylLeft Φ) * realWeylEnergy (realWeylRight Φ) := by
  simp [realWeylProbabilityDensity, realWeylChiralDensity]
  ring

/-- **Real chiral Fierz bound.** The scalar and pseudoscalar bilinears are the two components
of the real internal-bivector pairing between the left and right Weyl sectors.  Their squared
sum is bounded by the product of the two sector energies, equivalently by the square difference
of total and chiral densities.  No complex scalar carrier is used in this statement. -/
theorem lochak_real_chiral_fierz_bound (Φ : Vec8R) :
    omega1 Φ ^ 2 + omega2 Φ ^ 2 ≤
      realWeylProbabilityDensity Φ ^ 2 - realWeylChiralDensity Φ ^ 2 := by
  rw [realWeyl_density_difference, omega1_real_weyl_coordinates,
    omega2_real_weyl_coordinates]
  have h := real_weyl_energy_frame (realWeylLeft Φ) (realWeylRight Φ)
  linarith [sq_nonneg (dotProduct (realWeylBivector₂ (realWeylLeft Φ))
      (realWeylRight Φ)),
    sq_nonneg (dotProduct (realWeylBivector₃ (realWeylLeft Φ))
      (realWeylRight Φ))]

/-- The same estimate expressed directly in the existing real current declarations. -/
theorem lochak_real_chiral_current_bound (Φ : Vec8R) :
    omega1 Φ ^ 2 + omega2 Φ ^ 2 ≤
      (electricCurrentJ Φ 0) ^ 2 - (axialCurrentSigma Φ 0) ^ 2 := by
  calc omega1 Φ ^ 2 + omega2 Φ ^ 2 ≤
        realWeylProbabilityDensity Φ ^ 2 - realWeylChiralDensity Φ ^ 2 :=
          lochak_real_chiral_fierz_bound Φ
    _ = (electricCurrentJ Φ 0) ^ 2 - (axialCurrentSigma Φ 0) ^ 2 := by
          rw [realWeylProbabilityDensity_eq_electricCurrentJ0,
            realWeylChiralDensity_eq_axialCurrentSigma0]

/-- If either real Weyl sector vanishes, both scalar and pseudoscalar cross bilinears vanish. -/
theorem lochak_real_chiral_bilinears_vanish_of_sheet_zero (Φ : Vec8R)
    (h : realWeylLeft Φ = 0 ∨ realWeylRight Φ = 0) :
    omega1 Φ = 0 ∧ omega2 Φ = 0 := by
  rw [omega1_real_weyl_coordinates, omega2_real_weyl_coordinates]
  rcases h with h | h
  · simp [h, realWeylBivector]
  · simp [h, realWeylBivector]

/-- A strictly positive scalar/pseudoscalar Fierz norm requires nonzero content in both real
Weyl sectors. This is the algebraic two-sheet coupling consequence, without a particle
interpretation built into the proposition. -/
theorem both_real_weyl_sectors_nonzero_of_positive_fierz_norm (Φ : Vec8R)
    (h : 0 < omega1 Φ ^ 2 + omega2 Φ ^ 2) :
    realWeylLeft Φ ≠ 0 ∧ realWeylRight Φ ≠ 0 := by
  constructor
  · intro hLeft
    have hzero := lochak_real_chiral_bilinears_vanish_of_sheet_zero Φ (Or.inl hLeft)
    rw [hzero.1, hzero.2] at h
    norm_num at h
  · intro hRight
    have hzero := lochak_real_chiral_bilinears_vanish_of_sheet_zero Φ (Or.inr hRight)
    rw [hzero.1, hzero.2] at h
    norm_num at h

/-- Exact identity `4 |ξ† η|² = Ω₁² + Ω₂²`. -/
theorem four_normSq_weylCrossInner (Φ : Vec8R) :
    4 * Complex.normSq (weylCrossInner Φ) = omega1 Φ ^ 2 + omega2 Φ ^ 2 := by
  rw [Complex.normSq_apply, weylCrossInner_re, weylCrossInner_im]
  ring

/-- **Lochak Eq. (47) (Null Lightcone / Majorana Orthogonality)**: `Ω₁² + Ω₂² = 0 ↔ ξ† η = 0`. -/
theorem lochak_eq47_lightcone_orthogonality (Φ : Vec8R) :
    omega1 Φ ^ 2 + omega2 Φ ^ 2 = 0 ↔ weylCrossInner Φ = 0 := by
  rw [← four_normSq_weylCrossInner, mul_eq_zero]
  constructor
  · intro h
    rcases h with h4 | h0
    · norm_num at h4
    · exact Complex.normSq_eq_zero.mp h0
  · intro h
    right
    exact Complex.normSq_eq_zero.mpr h

/-- Massive spinor witness: `Φ = e₀` has nonzero `Ω₁² + Ω₂² = 1` (timelike `J`). -/
theorem massive_spinor_witness :
    let Φ : Vec8R := ![1, 0, 0, 0, 0, 0, 0, 0]
    omega1 Φ ^ 2 + omega2 Φ ^ 2 = 1 ∧ electricCurrentJ Φ 0 = 1 := by
  intro Φ
  rw [omega1_expand, omega2_expand, electricCurrentJ0_expand]
  simp [Φ]

/-- Null lightcone Majorana witness: `Φ = ![1,0,0,0,0,0,0,-1]` (i.e. `Φ_L` with `a = ![√2,0,0,0]`)
has `Ω₁² + Ω₂² = 0` and `weylCrossInner Φ = 0` while `J⁰ = 2 ≠ 0`. -/
theorem null_lightcone_spinor_witness :
    let Φ : Vec8R := ![1, 0, 0, 0, 0, 0, 0, -1]
    omega1 Φ ^ 2 + omega2 Φ ^ 2 = 0 ∧ weylCrossInner Φ = 0 ∧ electricCurrentJ Φ 0 = 2 := by
  intro Φ
  have h1 : omega1 Φ ^ 2 + omega2 Φ ^ 2 = 0 := by
    rw [omega1_expand, omega2_expand]; simp [Φ]
  have h2 : weylCrossInner Φ = 0 := (lochak_eq47_lightcone_orthogonality Φ).mp h1
  have h3 : electricCurrentJ Φ 0 = 2 := by
    rw [electricCurrentJ0_expand]; simp [Φ]; norm_num
  exact ⟨h1, h2, h3⟩

/-! ### Section 4: Daviau Eq. (58) ↔ Eqs. (71–79) Real `M₈(ℝ)` Bilinear Correspondence -/

private lemma inv_sqrt2_pow2 : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [inv_pow, hs, one_div]

private lemma daviau_A_op_eq (μ : Fin 4) :
    gammaLowR μ * quatPR 0 * quatPR 2 = castZ8 (((gammaLowSp μ).mul p1Sp).mul p3Sp).toMat := by
  dsimp [gammaLowR, quatPR, quatPZ]
  rw [← gammaLowSp_toMat μ, ← p1Sp_toMat, ← p3Sp_toMat,
    ← castZ8_mul, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul]

private lemma daviau_B_op_eq (μ : Fin 4) :
    gammaLowR μ * quatPR 0 = castZ8 ((gammaLowSp μ).mul p1Sp).toMat := by
  dsimp [gammaLowR, quatPR, quatPZ]
  rw [← gammaLowSp_toMat μ, ← p1Sp_toMat, ← castZ8_mul, ← SpMat8Z.toMat_mul]

private lemma daviau_F_op_eq (μ ν : Fin 4) :
    gammaLowR μ * gammaLowR ν * quatPR 2 =
      castZ8 (((gammaLowSp μ).mul (gammaLowSp ν)).mul p3Sp).toMat := by
  dsimp [gammaLowR, quatPR, quatPZ]
  rw [← gammaLowSp_toMat μ, ← gammaLowSp_toMat ν, ← p3Sp_toMat,
    ← castZ8_mul, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul]

/-- Antisymmetrized Clifford bivector `Γ_μ ∧ Γ_ν = ½(Γ_μ Γ_ν - Γ_ν Γ_μ)` used in the field
strength bilinear of Daviau Eq. (58) (`F_{μν}`). Vanishes identically on the diagonal `μ = ν` and
agrees with `gammaLowR μ * gammaLowR ν` off the diagonal `μ ≠ ν`. -/
def gammaLowWedgeR (μ ν : Fin 4) : Matrix (Fin 8) (Fin 8) ℝ :=
  (1 / 2 : ℝ) • (gammaLowR μ * gammaLowR ν - gammaLowR ν * gammaLowR μ)

@[simp] theorem gammaLowWedgeR_self (μ : Fin 4) : gammaLowWedgeR μ μ = 0 := by
  simp [gammaLowWedgeR]

theorem gammaLowWedgeR_of_ne {μ ν : Fin 4} (hne : μ ≠ ν) :
    gammaLowWedgeR μ ν = gammaLowR μ * gammaLowR ν := by
  have hanti := gammaR_anticomm μ ν
  simp [hne] at hanti
  have hanti_low : gammaLowR μ * gammaLowR ν + gammaLowR ν * gammaLowR μ = 0 := by
    rw [gammaLowR_eq μ, gammaLowR_eq ν, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_smul,
      mul_comm (minkowskiMetricR ν), ← smul_add, hanti, smul_zero]
  have hsub :
      gammaLowR μ * gammaLowR ν - gammaLowR ν * gammaLowR μ =
        (2 : ℝ) • (gammaLowR μ * gammaLowR ν) := by
    rw [← add_zero (gammaLowR μ * gammaLowR ν - gammaLowR ν * gammaLowR μ), ← hanti_low,
      two_smul]
    abel
  have hhalf : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [gammaLowWedgeR, hsub, smul_smul, hhalf, one_smul]

/-- Evaluates Daviau Eq. (58)'s Krein cross-bilinears `(s, p, A_μ, B_μ, F_{μν})` in `M₈(ℝ)` on
`(Φ_L, Φ_R)` from Eq. (66) (covariant index convention `Γ_μ`), showing verbatim agreement with
`FusionJetData` formulas in `DeBroglieDaviauPhotonProcaFusion`. The `F_{μν}` tensor bilinear uses
the antisymmetrized Clifford bivector `gammaLowWedgeR μ ν`. -/
theorem daviau_eq58_bilinears_match_eq71_79 (a b : Fin 4 → ℝ) (halfMass : ℝ) :
    let D : FusionJetData ℝ := ⟨a, b, 0, 0, halfMass⟩
    let ΦL := daviauPhiL a
    let ΦR := daviauPhiR b
    kreinInnerProduct ΦL ΦR = fusionScalarS D ∧
    kreinInnerProduct ΦL (gamma0123R.mulVec ΦR) = fusionPseudoscalarP D ∧
    (∀ μ : Fin 4, kreinInnerProduct ΦL ((gammaLowR μ * quatPR 0 * quatPR 2).mulVec ΦR) =
      photonA D μ) ∧
    (∀ μ : Fin 4, kreinInnerProduct ΦL ((gammaLowR μ * quatPR 0).mulVec ΦR) =
      fusionAxialB D μ) ∧
    (∀ μ ν : Fin 4, photonMass D *
      kreinInnerProduct ΦL ((gammaLowWedgeR μ ν * quatPR 2).mulVec ΦR) =
      photonF D μ ν) := by
  intro D ΦL ΦR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [kreinInnerProduct_eq]
    dsimp [ΦL, ΦR, daviauPhiL, daviauPhiR, fusionScalarS, D]
    simp
    ring_nf
    simp only [inv_sqrt2_pow2]
    ring
  · dsimp [gamma0123R]
    rw [← g0123Sp_toMat, kreinInner_sp_mulVec]
    dsimp [ΦL, ΦR, daviauPhiL, daviauPhiR, fusionPseudoscalarP, D]
    simp [g0123Sp]
    ring_nf
    simp only [inv_sqrt2_pow2]
    ring
  · intro μ
    rw [daviau_A_op_eq μ, kreinInner_sp_mulVec]
    fin_cases μ <;>
      · dsimp [ΦL, ΦR, daviauPhiL, daviauPhiR, photonA, D]
        simp [SpMat8Z.mul, gammaLowSp, gammaSp, minkowskiMetricZ, p1Sp, p3Sp]
        ring_nf
        simp only [inv_sqrt2_pow2]
        ring
  · intro μ
    rw [daviau_B_op_eq μ, kreinInner_sp_mulVec]
    fin_cases μ <;>
      · dsimp [ΦL, ΦR, daviauPhiL, daviauPhiR, fusionAxialB, D]
        simp [SpMat8Z.mul, gammaLowSp, gammaSp, minkowskiMetricZ, p1Sp]
        ring_nf
        simp only [inv_sqrt2_pow2]
        ring
  · intro μ ν
    by_cases hμν : μ = ν
    · subst hμν
      rw [gammaLowWedgeR_self, Matrix.zero_mul, Matrix.zero_mulVec, kreinInnerProduct_eq]
      fin_cases μ <;>
        simp [photonF, photonFBase, D]
    · rw [gammaLowWedgeR_of_ne hμν, daviau_F_op_eq μ ν, kreinInner_sp_mulVec]
      fin_cases μ <;> fin_cases ν <;>
        first
        | exact absurd rfl hμν
        | ( dsimp only [ΦL, ΦR, daviauPhiL, daviauPhiR, photonF, photonMass, D]
            simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff,
              SpMat8Z.mul, gammaLowSp, gammaSp, minkowskiMetricZ, p3Sp, photonFBase]
            ring_nf
            simp only [inv_sqrt2_pow2]
            ring )

/-- For distinct spacetime indices `μ ≠ ν`, the wedge `gammaLowWedgeR μ ν` equals
`gammaLowR μ * gammaLowR ν`, recovering Daviau's un-antisymmetrized off-diagonal Eq. (58)
identity for `F_{μν}`. -/
theorem daviau_eq58_F_offdiag (a b : Fin 4 → ℝ) (halfMass : ℝ) {μ ν : Fin 4} (hne : μ ≠ ν) :
    let D : FusionJetData ℝ := ⟨a, b, 0, 0, halfMass⟩
    let ΦL := daviauPhiL a
    let ΦR := daviauPhiR b
    photonMass D *
      kreinInnerProduct ΦL ((gammaLowR μ * gammaLowR ν * quatPR 2).mulVec ΦR) =
      photonF D μ ν := by
  have h5 := (daviau_eq58_bilinears_match_eq71_79 a b halfMass).2.2.2.2 μ ν
  rwa [gammaLowWedgeR_of_ne hne] at h5

/-- **Theorem 3 (`lochak_rodichev_fierz_takabayasi_lightcone`)**:
Unified kernel-verified statement in real `M₈(ℝ)` (`Γ⁰ = kreinMetric8`, no `x₄ = i c t`):
1. Rodichev skew-torsion axial reduction (Lochak Eqs. 8–13),
2. Krein `(4,4)` Fierz–Takabayasi identity `-J_μ J^μ = Σ_μ Σ^μ = Ω₁² + Ω₂²` and `J ⋅ Σ = 0`
   (Lochak Eq. 39),
3. Null lightcone Majorana orthogonality `Ω₁² + Ω₂² = 0 ↔ ξ† η = 0` (Lochak Eq. 47). -/
theorem lochak_rodichev_fierz_takabayasi_lightcone :
    (∀ σ : Fin 4 → ℝ,
      ∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
        rodichevTorsion σ a μ b • (gammaR μ * gammaR a * gammaR b) =
      (6 : ℝ) • ∑ ν : Fin 4, σ ν • (gammaLowR ν * gamma0123R)) ∧
    (∀ Φ : Vec8R,
      -lochakDot (electricCurrentJ Φ) (electricCurrentJ Φ) =
        lochakDot (axialCurrentSigma Φ) (axialCurrentSigma Φ) ∧
      lochakDot (axialCurrentSigma Φ) (axialCurrentSigma Φ) =
        omega1 Φ ^ 2 + omega2 Φ ^ 2 ∧
      minkowskiDot (electricCurrentJ Φ) (axialCurrentSigma Φ) = 0 ∧
      (omega1 Φ ^ 2 + omega2 Φ ^ 2 = 0 ↔ weylCrossInner Φ = 0)) :=
  ⟨rodichev_skew_torsion_axial_reduction,
   fun Φ =>
     ⟨(lochak_eq39_fierz_takabayasi Φ).1,
      (lochak_eq39_fierz_takabayasi Φ).2,
      fierz_takabayasi_J_ortho_Sigma Φ,
      lochak_eq47_lightcone_orthogonality Φ⟩⟩

end InfoGeometry.Clifford.LochakRodichevFierzKrein
