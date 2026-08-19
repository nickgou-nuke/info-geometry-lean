import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.TraceFormula.DeterminantBondNative
import InfoGeometry.TraceFormula.ColimitTrace

/-!
# Finite Itakura--Saito and determinant normalization

This owner proves the finite scalar and inverse-scaling identities, including
the determinant-squaring law for the BitWord block embedding.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.ItakuraSaito

open Matrix
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.PrimonColimitAlgebra

/-! The determinant law is discharged by the native BitWord reindexing proof. -/

theorem determinant_bond_block_native (n : ℕ) (M : MatrixStage n) :
    Matrix.det (matrixBond n M) = (Matrix.det M) ^ 2 :=
  InfoGeometry.TraceFormula.DeterminantBondNative.matrixBond_det_native n M

def mongeAmperePotential (n : ℕ) (P : MatrixStage n) : ℝ :=
  -Real.log (Matrix.det P)

def itakuraSaitoDivergence (n : ℕ) (P Q : MatrixStage n) : ℝ :=
  rawTrace n (P * Q⁻¹) + mongeAmperePotential n (P * Q⁻¹) - (2 ^ n : ℝ)

/-- The finite determinant fact needed by the binary matrix tower. -/
lemma matrixBondFun_eq_reindex_kronecker (n : ℕ) (P : MatrixStage n) :
    matrixBondFun n P =
      Matrix.reindex (bitWordSuccEquiv n).symm (bitWordSuccEquiv n).symm
        (Matrix.kroneckerMap (fun x y : ℝ => x * y) P
          (1 : Matrix Bool Bool ℝ)) := by
  ext v w
  cases hv : bitWordSuccEquiv n v with
  | mk vp vb =>
      cases hw : bitWordSuccEquiv n w with
      | mk wp wb =>
          have hvp : prefixSucc n v = vp := congrArg Prod.fst hv
          have hwp : prefixSucc n w = wp := congrArg Prod.fst hw
          have hvb : v ⟨n, Nat.lt_succ_self n⟩ = vb := by
            exact congrArg Prod.snd hv
          have hwb : w ⟨n, Nat.lt_succ_self n⟩ = wb := by
            exact congrArg Prod.snd hw
          subst vp
          subst wp
          cases vb <;> cases wb <;>
            simp [matrixBondFun, Matrix.reindex, Matrix.kroneckerMap,
              bitWordSuccEquiv, lastBit, hvb, hwb]

theorem determinant_bond_block (n : ℕ) (P : MatrixStage n) :
    Matrix.det (matrixBond n P) = (Matrix.det P) ^ 2 := by
  rw [show matrixBond n P = matrixBondFun n P by rfl,
    matrixBondFun_eq_reindex_kronecker]
  rw [Matrix.det_reindex]
  simp [Matrix.det_kronecker]

theorem mongeAmpere_compatible
    (n : ℕ) (P : MatrixStage n)
    (h_pos : 0 < Matrix.det P) :
    (1 / (2 ^ (n + 1) : ℝ)) * mongeAmperePotential (n + 1) (matrixBond n P) =
      (1 / (2 ^ n : ℝ)) * mongeAmperePotential n P := by
  dsimp [mongeAmperePotential]
  rw [determinant_bond_block]
  have h_log_sq : Real.log ((Matrix.det P) ^ 2) =
      2 * Real.log (Matrix.det P) := by
    rw [show (Matrix.det P) ^ 2 = Matrix.det P * Matrix.det P by ring]
    rw [Real.log_mul (ne_of_gt h_pos) (ne_of_gt h_pos)]
    ring
  rw [h_log_sq]
  have h_pow : (2 ^ (n + 1) : ℝ) = 2 ^ n * 2 := by ring
  rw [h_pow]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

theorem mongeAmpere_compatible_native
    (n : ℕ) (P : MatrixStage n)
    (h_pos : 0 < Matrix.det P) :
    (1 / (2 ^ (n + 1) : ℝ)) * mongeAmperePotential (n + 1) (matrixBond n P) =
      (1 / (2 ^ n : ℝ)) * mongeAmperePotential n P := by
  exact mongeAmpere_compatible n P h_pos

theorem bondMap_det_pos
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m)
    (hP : 0 < Matrix.det P) :
    0 < Matrix.det (bondMap matrixBond m n h P) := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk =>
      0 < Matrix.det (bondMap matrixBond m k hk P))
    ?base ?succ n h
  · simpa only [bondMap_refl, RingHom.id_apply] using hP
  · intro k hmk ih
    rw [bondMap_succ]
    change 0 < Matrix.det (matrixBond k (bondMap matrixBond m k hmk P))
    rw [determinant_bond_block]
    rw [show (Matrix.det (bondMap matrixBond m k hmk P)) ^ 2 =
      Matrix.det (bondMap matrixBond m k hmk P) *
        Matrix.det (bondMap matrixBond m k hmk P) by ring]
    exact mul_pos ih ih

theorem mongeAmpere_bondMap_compatible
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m)
    (hP : 0 < Matrix.det P) :
    mongeAmperePotential n (bondMap matrixBond m n h P) =
      (2 ^ (n - m) : ℝ) * mongeAmperePotential m P := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk =>
      mongeAmperePotential k (bondMap matrixBond m k hk P) =
        (2 ^ (k - m) : ℝ) * mongeAmperePotential m P)
    ?base ?succ n h
  · simp [bondMap_refl]
  · intro k hmk ih
    rw [bondMap_succ]
    simp only [RingHom.coe_comp, Function.comp_apply]
    change mongeAmperePotential (k + 1)
        (matrixBond k (bondMap matrixBond m k hmk P)) = _
    have hstep := mongeAmpere_compatible k
      (bondMap matrixBond m k hmk P)
      (bondMap_det_pos m k hmk P hP)
    have hpow : (2 ^ (k + 1) : ℝ) = 2 ^ k * 2 := by ring
    rw [hpow] at hstep
    field_simp [pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)] at hstep
    rw [hstep]
    rw [ih]
    rw [Nat.succ_sub hmk]
    rw [pow_succ]
    ring

theorem normalized_mongeAmpere_bondMap_compatible
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m)
    (hP : 0 < Matrix.det P) :
    (1 / (2 ^ n : ℝ)) *
        mongeAmperePotential n (bondMap matrixBond m n h P) =
      (1 / (2 ^ m : ℝ)) * mongeAmperePotential m P := by
  rw [mongeAmpere_bondMap_compatible m n h P hP]
  have hpow : (2 ^ n : ℝ) = 2 ^ m * 2 ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  rw [hpow]
  field_simp [pow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0),
    pow_ne_zero (n - m) (by norm_num : (2 : ℝ) ≠ 0)]

theorem smul_mul_inv_smul (n : ℕ) (P Q : MatrixStage n) (c : ℝ)
    (hc : c ≠ 0)
    (hQ : IsUnit Q.det) :
    (c • P) * (c • Q)⁻¹ = P * Q⁻¹ := by
  letI : Invertible c := invertibleOfNonzero hc
  rw [Matrix.inv_smul Q c hQ, invOf_eq_inv, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

theorem itakuraSaito_scale_invariant
    (n : ℕ) (P Q : MatrixStage n) (c : ℝ) (hc : 0 < c)
    (hQ : IsUnit Q.det) :
    itakuraSaitoDivergence n (c • P) (c • Q) =
      itakuraSaitoDivergence n P Q := by
  unfold itakuraSaitoDivergence
  rw [smul_mul_inv_smul n P Q c (ne_of_gt hc) hQ]

theorem matrixBond_inv
    (n : ℕ) (Q : MatrixStage n) (hQ : IsUnit Q.det) :
    (matrixBond n Q)⁻¹ = matrixBond n (Q⁻¹) := by
  have hBondDet : IsUnit (Matrix.det (matrixBond n Q)) := by
    rw [determinant_bond_block]
    exact IsUnit.pow 2 hQ
  have hBondRight : matrixBond n Q * matrixBond n (Q⁻¹) = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv Q hQ, map_one]
  calc
    (matrixBond n Q)⁻¹ = (matrixBond n Q)⁻¹ * 1 := by simp
    _ = (matrixBond n Q)⁻¹ *
        (matrixBond n Q * matrixBond n (Q⁻¹)) := by rw [hBondRight]
    _ = ((matrixBond n Q)⁻¹ * matrixBond n Q) * matrixBond n (Q⁻¹) := by
      rw [mul_assoc]
    _ = 1 * matrixBond n (Q⁻¹) := by
      rw [Matrix.nonsing_inv_mul (matrixBond n Q) hBondDet]
    _ = matrixBond n (Q⁻¹) := by simp

theorem itakuraSaito_bond_compatible
    (n : ℕ) (P Q : MatrixStage n) (hQ : IsUnit Q.det) :
    itakuraSaitoDivergence (n + 1) (matrixBond n P) (matrixBond n Q) =
      2 * itakuraSaitoDivergence n P Q := by
  unfold itakuraSaitoDivergence mongeAmperePotential
  rw [matrixBond_inv n Q hQ]
  have hRatio :
      matrixBond n P * matrixBond n (Q⁻¹) =
        matrixBond n (P * Q⁻¹) := by
    rw [← map_mul]
  rw [hRatio, rawTrace_bond]
  rw [determinant_bond_block]
  have h_log_sq : Real.log (Matrix.det (P * Q⁻¹) ^ 2) =
      2 * Real.log (Matrix.det (P * Q⁻¹)) := by
    by_cases hdet : Matrix.det (P * Q⁻¹) = 0
    · simp [hdet]
    · rw [show Matrix.det (P * Q⁻¹) ^ 2 =
          Matrix.det (P * Q⁻¹) * Matrix.det (P * Q⁻¹) by ring]
      rw [Real.log_mul hdet hdet]
      ring
  rw [h_log_sq]
  have h_pow : (2 ^ (n + 1) : ℝ) = 2 ^ n * 2 := by ring
  rw [h_pow]
  ring

theorem normalized_itakuraSaito_bond_compatible
    (n : ℕ) (P Q : MatrixStage n) (hQ : IsUnit Q.det) :
    (1 / (2 ^ (n + 1) : ℝ)) *
        itakuraSaitoDivergence (n + 1) (matrixBond n P) (matrixBond n Q) =
      (1 / (2 ^ n : ℝ)) * itakuraSaitoDivergence n P Q := by
  rw [itakuraSaito_bond_compatible n P Q hQ]
  have hpow : (2 ^ (n + 1) : ℝ) = 2 ^ n * 2 := by ring
  rw [hpow]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

theorem bondMap_det_isUnit
    (m n : ℕ) (h : m ≤ n) (Q : MatrixStage m) (hQ : IsUnit Q.det) :
    IsUnit (Matrix.det (bondMap matrixBond m n h Q)) := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk => IsUnit (Matrix.det (bondMap matrixBond m k hk Q)))
    ?base ?succ n h
  · simpa only [bondMap_refl, RingHom.id_apply] using hQ
  · intro k hmk ih
    rw [bondMap_succ]
    change IsUnit (Matrix.det (matrixBond k (bondMap matrixBond m k hmk Q)))
    rw [determinant_bond_block]
    exact IsUnit.pow 2 ih

theorem bondMap_inv
    (m n : ℕ) (h : m ≤ n) (Q : MatrixStage m) (hQ : IsUnit Q.det) :
    (bondMap matrixBond m n h Q)⁻¹ =
      bondMap matrixBond m n h (Q⁻¹) := by
  have hdet : IsUnit (Matrix.det (bondMap matrixBond m n h Q)) :=
    bondMap_det_isUnit m n h Q hQ
  have hright :
      bondMap matrixBond m n h Q * bondMap matrixBond m n h (Q⁻¹) = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv Q hQ, map_one]
  calc
    (bondMap matrixBond m n h Q)⁻¹ =
        (bondMap matrixBond m n h Q)⁻¹ * 1 := by simp
    _ = (bondMap matrixBond m n h Q)⁻¹ *
        (bondMap matrixBond m n h Q * bondMap matrixBond m n h (Q⁻¹)) := by
          rw [hright]
    _ = ((bondMap matrixBond m n h Q)⁻¹ *
        bondMap matrixBond m n h Q) * bondMap matrixBond m n h (Q⁻¹) := by
          rw [mul_assoc]
    _ = 1 * bondMap matrixBond m n h (Q⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hdet]
    _ = bondMap matrixBond m n h (Q⁻¹) := by simp

theorem normalized_itakuraSaito_bondMap_compatible
    (m n : ℕ) (h : m ≤ n) (P Q : MatrixStage m) (hQ : IsUnit Q.det) :
    (1 / (2 ^ n : ℝ)) *
        itakuraSaitoDivergence n (bondMap matrixBond m n h P)
          (bondMap matrixBond m n h Q) =
      (1 / (2 ^ m : ℝ)) * itakuraSaitoDivergence m P Q := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk =>
      (1 / (2 ^ k : ℝ)) *
          itakuraSaitoDivergence k (bondMap matrixBond m k hk P)
            (bondMap matrixBond m k hk Q) =
        (1 / (2 ^ m : ℝ)) * itakuraSaitoDivergence m P Q)
    ?base ?succ n h
  · simp [bondMap_refl]
  · intro k hmk ih
    rw [bondMap_succ]
    simp only [RingHom.coe_comp, Function.comp_apply]
    change (1 / (2 ^ (k + 1) : ℝ)) *
        itakuraSaitoDivergence (k + 1)
          (matrixBond k (bondMap matrixBond m k hmk P))
          (matrixBond k (bondMap matrixBond m k hmk Q)) = _
    rw [normalized_itakuraSaito_bond_compatible k
      (bondMap matrixBond m k hmk P)
      (bondMap matrixBond m k hmk Q)
      (bondMap_det_isUnit m k hmk Q hQ)]
    exact ih

theorem itakuraSaito_self
    (n : ℕ) (P : MatrixStage n) (hP : IsUnit P.det) :
    itakuraSaitoDivergence n P P = -Real.log 1 := by
  dsimp [itakuraSaitoDivergence, mongeAmperePotential, rawTrace]
  rw [Matrix.mul_nonsing_inv _ hP]
  have h_tr : Matrix.trace (1 : MatrixStage n) = (2 ^ n : ℝ) := by
    have h_card : Fintype.card (BitWord n) = 2 ^ n := by
      dsimp [BitWord]
      simp
    rw [Matrix.trace_one]
    norm_num [h_card]
  rw [h_tr, Matrix.det_one]
  ring

theorem colimitTrace_stage_readout (n : ℕ) (P : MatrixStage n) :
    InfoGeometry.TraceFormula.ColimitTrace.colimitTrace (toColimit n P) =
      normalizedTrace n P := by
  exact InfoGeometry.TraceFormula.ColimitTrace.colimitTrace_evaluate_ringhom n P

/-! ## Centered relative-ratio readout -/

/-!
The finite algebraic carrier for the centered relative modular ratio is
`P * Q⁻¹ - 1`.  The logarithm below remains the scalar determinant readout;
no operator functional calculus is asserted by this owner.
-/
def centeredRelativeRatio (P Q : MatrixStage n) : MatrixStage n :=
  P * Q⁻¹ - 1

@[simp] theorem centeredRelativeRatio_apply (P Q : MatrixStage n) :
    centeredRelativeRatio P Q = P * Q⁻¹ - 1 :=
  rfl

theorem normalized_itakuraSaitoDivergence_eq
    (n : ℕ) (P Q : MatrixStage n) :
    (1 / (2 ^ n : ℝ)) * itakuraSaitoDivergence n P Q =
      normalizedTrace n (P * Q⁻¹) +
        (1 / (2 ^ n : ℝ)) * mongeAmperePotential n (P * Q⁻¹) - 1 := by
  unfold itakuraSaitoDivergence normalizedTrace
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

theorem normalized_centeredRelativeRatio_eq_zero_of_trace_zero
    (n : ℕ) (X : MatrixStage n)
    (hX : normalizedTrace n X = 0) :
    normalizedTrace n (centeredRelativeRatio (1 + X) 1) = 0 := by
  simpa [centeredRelativeRatio] using hX

theorem normalized_centeredRelativeRatio_eq_zero_of_normalized_trace_eq_one
    (n : ℕ) (P Q : MatrixStage n)
    (hPQ : normalizedTrace n (P * Q⁻¹) = 1) :
    normalizedTrace n (centeredRelativeRatio P Q) = 0 := by
  change normalizedTraceLinear n (P * Q⁻¹ - 1) = 0
  rw [(normalizedTraceLinear n).map_sub]
  have hPQ' : normalizedTraceLinear n (P * Q⁻¹) = 1 := by
    change normalizedTrace n (P * Q⁻¹) = 1
    exact hPQ
  have hOne' : normalizedTraceLinear n (1 : MatrixStage n) = 1 := by
    change normalizedTrace n (1 : MatrixStage n) = 1
    exact normalizedTrace_one n
  rw [hPQ', hOne']
  norm_num

theorem colimitTrace_centeredRelativeRatio_eq_zero_of_normalized_trace_eq_one
    (n : ℕ) (P Q : MatrixStage n)
    (hPQ : normalizedTrace n (P * Q⁻¹) = 1) :
    InfoGeometry.TraceFormula.ColimitTrace.colimitTrace
        (toColimit n (centeredRelativeRatio P Q)) = 0 := by
  rw [InfoGeometry.TraceFormula.ColimitTrace.colimitTrace_evaluate_ringhom]
  exact normalized_centeredRelativeRatio_eq_zero_of_normalized_trace_eq_one n P Q hPQ

/-! ## Scalar positivity of the Itakura--Saito generator -/

def scalarItakuraSaito (x : ℝ) : ℝ :=
  x - 1 - Real.log x

theorem scalarItakuraSaito_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ scalarItakuraSaito x := by
  have h := Real.add_one_le_exp (Real.log x)
  rw [Real.exp_log hx] at h
  unfold scalarItakuraSaito
  linarith

@[simp] theorem scalarItakuraSaito_one :
    scalarItakuraSaito 1 = 0 := by
  simp [scalarItakuraSaito]

theorem scalarItakuraSaito_exp_ratio (u v : ℝ) :
    scalarItakuraSaito (Real.exp u / Real.exp v) =
      Real.exp (u - v) - (u - v) - 1 := by
  unfold scalarItakuraSaito
  rw [← Real.exp_sub, Real.log_exp]
  ring

theorem scalarItakuraSaito_exp_common_shift (u v c : ℝ) :
    scalarItakuraSaito (Real.exp (u + c) / Real.exp (v + c)) =
      scalarItakuraSaito (Real.exp u / Real.exp v) := by
  rw [scalarItakuraSaito_exp_ratio, scalarItakuraSaito_exp_ratio]
  ring_nf

theorem scalarItakuraSaito_common_scale
    (c x y : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) :
    scalarItakuraSaito (c * x / (c * y)) =
      scalarItakuraSaito (x / y) := by
  have hcy : c * y ≠ 0 := by
    exact mul_ne_zero hc hy
  have hratio : c * x / (c * y) = x / y := by
    field_simp [hc, hcy]
  rw [hratio]

end InfoGeometry.TraceFormula.ItakuraSaito
