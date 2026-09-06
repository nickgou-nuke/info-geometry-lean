import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Cuntz transition coefficients and finite Gram states

The Cuntz matrix-unit sector supplies the finite transition carrier.  This
file treats its coefficient matrix directly and proves the finite Gram facts
needed by later polar and modular owners.  No polar factor or logarithm is
introduced without the corresponding full-rank hypotheses.
-/

noncomputable section

namespace InfoGeometry.Physics.CuntzTransitionGramBridge

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat (n : Type*) := Matrix n n ℂ

def rightGram (A : Mat n) : Mat n := Aᴴ * A

def leftGram (A : Mat n) : Mat n := A * Aᴴ

def gramTrace (A : Mat n) : ℝ := (Matrix.trace (rightGram A)).re

def traceFreePart [Nonempty n] (H : Mat n) : Mat n :=
  H - (((Fintype.card n : ℂ)⁻¹) * Matrix.trace H) • (1 : Mat n)

theorem traceFreePart_add_tracePart [Nonempty n] (H : Mat n) :
    traceFreePart H +
        (((Fintype.card n : ℂ)⁻¹) * Matrix.trace H) • (1 : Mat n) = H := by
  unfold traceFreePart
  module

theorem traceOne_eq_traceFreePart_add_uniform [Nonempty n]
    {H : Mat n} (htrace : Matrix.trace H = 1) :
    H = traceFreePart H + ((Fintype.card n : ℂ)⁻¹) • (1 : Mat n) := by
  calc
    H = traceFreePart H +
        (((Fintype.card n : ℂ)⁻¹) * Matrix.trace H) • (1 : Mat n) :=
      (traceFreePart_add_tracePart H).symm
    _ = traceFreePart H + ((Fintype.card n : ℂ)⁻¹) • (1 : Mat n) := by
      rw [htrace]
      simp

theorem trace_traceFreePart [Nonempty n] (H : Mat n) :
    Matrix.trace (traceFreePart H) = 0 := by
  unfold traceFreePart
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [smul_eq_mul]
  field_simp [hcard]
  ring

theorem traceFreePart_add_scalar [Nonempty n] (H : Mat n) (c : ℂ) :
    traceFreePart (H + c • (1 : Mat n)) = traceFreePart H := by
  unfold traceFreePart
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [smul_eq_mul]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    field_simp [hcard]
    ring
  · simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, hij]

def normalizedRightGram (A : Mat n) : Mat n :=
  ((gramTrace A : ℂ)⁻¹) • rightGram A

def normalizedLeftGram (A : Mat n) : Mat n :=
  ((gramTrace A : ℂ)⁻¹) • leftGram A

theorem rightGram_isHermitian (A : Mat n) : (rightGram A).IsHermitian := by
  exact isHermitian_conjTranspose_mul_self A

theorem leftGram_isHermitian (A : Mat n) : (leftGram A).IsHermitian := by
  exact isHermitian_mul_conjTranspose_self A

theorem rightGram_posSemidef (A : Mat n) : (rightGram A).PosSemidef := by
  exact posSemidef_conjTranspose_mul_self A

theorem rightGram_cfcSqrt_mul_self (A : Mat n) :
    CFC.sqrt (rightGram A) * CFC.sqrt (rightGram A) = rightGram A := by
  exact CFC.sqrt_mul_sqrt_self (rightGram A)
    (ha := (rightGram_posSemidef A).nonneg)

theorem rightGram_cfcSqrt_posSemidef (A : Mat n) :
    (CFC.sqrt (rightGram A)).PosSemidef := by
  exact (CFC.sqrt_nonneg (rightGram A)).posSemidef

theorem leftGram_posSemidef (A : Mat n) : (leftGram A).PosSemidef := by
  exact posSemidef_self_mul_conjTranspose A

theorem leftGram_cfcSqrt_mul_self (A : Mat n) :
    CFC.sqrt (leftGram A) * CFC.sqrt (leftGram A) = leftGram A := by
  exact CFC.sqrt_mul_sqrt_self (leftGram A)
    (ha := (leftGram_posSemidef A).nonneg)

theorem leftGram_cfcSqrt_posSemidef (A : Mat n) :
    (CFC.sqrt (leftGram A)).PosSemidef := by
  exact (CFC.sqrt_nonneg (leftGram A)).posSemidef

theorem leftGram_isUnit_of_isUnit (A : Mat n) (hA : IsUnit A) :
    IsUnit (leftGram A) := by
  unfold leftGram
  exact hA.mul ((Matrix.isUnit_conjTranspose A).mpr hA)

theorem leftGram_cfcSqrt_isUnit_of_isUnit (A : Mat n) (hA : IsUnit A) :
    IsUnit (CFC.sqrt (leftGram A)) := by
  exact (CFC.isUnit_sqrt_iff (leftGram A)
      (ha := (leftGram_posSemidef A).nonneg)).2
    (leftGram_isUnit_of_isUnit A hA)

theorem trace_leftGram_eq_trace_rightGram (A : Mat n) :
    Matrix.trace (leftGram A) = Matrix.trace (rightGram A) := by
  exact Matrix.trace_mul_comm A Aᴴ

theorem gramTrace_formula (A : Mat n) :
    gramTrace A = ∑ i, ∑ j, Complex.normSq (A i j) := by
  simp [gramTrace, rightGram, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose, Complex.normSq_apply]
  rw [Finset.sum_comm]

theorem gramTrace_nonneg (A : Mat n) : 0 ≤ gramTrace A := by
  rw [gramTrace_formula]
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j)

theorem gramTrace_scale (A : Mat n) (α : ℂ) :
    gramTrace (α • A) = Complex.normSq α * gramTrace A := by
  have hgram : rightGram (α • A) = (Complex.normSq α : ℂ) • rightGram A := by
    simp only [rightGram, conjTranspose_smul]
    rw [smul_mul, Matrix.mul_smul, smul_smul]
    apply congrArg (fun z : ℂ => z • (Aᴴ * A))
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  rw [gramTrace, hgram, Matrix.trace_smul]
  change ((Complex.normSq α : ℂ) * Matrix.trace (rightGram A)).re =
    Complex.normSq α * (Matrix.trace (rightGram A)).re
  simp

theorem gramTrace_ne_zero_of_ne_zero {A : Mat n} (hA : A ≠ 0) :
    gramTrace A ≠ 0 := by
  intro hzero
  have hsum : ∑ i, ∑ j, Complex.normSq (A i j) = 0 := by
    rw [← gramTrace_formula A, hzero]
  have hrows :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun i => Finset.sum_nonneg fun j hj => Complex.normSq_nonneg _)).mp hsum
  apply hA
  funext i j
  have hrow : (∑ k : n, Complex.normSq (A i k)) = 0 := congrFun hrows i
  exact Complex.normSq_eq_zero.mp
    (congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg
        (fun k => Complex.normSq_nonneg (A i k))).mp hrow) j)

theorem gramTrace_eq_zero_iff (A : Mat n) :
    gramTrace A = 0 ↔ A = 0 := by
  constructor
  · intro hA
    by_contra hne
    exact (gramTrace_ne_zero_of_ne_zero hne) hA
  · intro hA
    rw [hA]
    simp [gramTrace, rightGram]

theorem rightGram_eq_zero_iff (A : Mat n) :
    rightGram A = 0 ↔ A = 0 := by
  constructor
  · intro hA
    apply (gramTrace_eq_zero_iff A).mp
    rw [gramTrace, hA]
    simp
  · intro hA
    rw [hA]
    simp [rightGram]

theorem rightGram_isUnit_of_isUnit (A : Mat n) (hA : IsUnit A) :
    IsUnit (rightGram A) := by
  unfold rightGram
  exact ((Matrix.isUnit_conjTranspose A).mpr hA).mul hA

theorem rightGram_cfcSqrt_isUnit_of_isUnit (A : Mat n) (hA : IsUnit A) :
    IsUnit (CFC.sqrt (rightGram A)) := by
  exact (CFC.isUnit_sqrt_iff (rightGram A)
      (ha := (rightGram_posSemidef A).nonneg)).2
    (rightGram_isUnit_of_isUnit A hA)

theorem rightGram_cfcSqrt_eq_zero_iff (A : Mat n) :
    CFC.sqrt (rightGram A) = 0 ↔ A = 0 := by
  rw [CFC.sqrt_eq_zero_iff (ha := (rightGram_posSemidef A).nonneg),
    rightGram_eq_zero_iff]

theorem leftGram_eq_zero_iff (A : Mat n) :
    leftGram A = 0 ↔ A = 0 := by
  constructor
  · intro hA
    apply (gramTrace_eq_zero_iff A).mp
    rw [gramTrace, ← trace_leftGram_eq_trace_rightGram A, hA]
    simp
  · intro hA
    rw [hA]
    simp [leftGram]

theorem leftGram_cfcSqrt_eq_zero_iff (A : Mat n) :
    CFC.sqrt (leftGram A) = 0 ↔ A = 0 := by
  rw [CFC.sqrt_eq_zero_iff (ha := (leftGram_posSemidef A).nonneg),
    leftGram_eq_zero_iff]

theorem trace_normalizedRightGram (A : Mat n) (hT : gramTrace A ≠ 0) :
    Matrix.trace (normalizedRightGram A) = 1 := by
  rw [normalizedRightGram, Matrix.trace_smul]
  have htrace : Matrix.trace (rightGram A) = (gramTrace A : ℂ) := by
    apply Complex.ext
    · rfl
    · rw [gramTrace_formula]
      simp [rightGram, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose,
        Complex.normSq_apply]
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      ring
  rw [htrace]
  exact inv_mul_cancel₀ (by exact_mod_cast hT)

theorem normalizedRightGram_eq_traceFreePart_add_uniform
    [Nonempty n] (A : Mat n) (hT : gramTrace A ≠ 0) :
    normalizedRightGram A =
      traceFreePart (normalizedRightGram A) +
        ((Fintype.card n : ℂ)⁻¹) • (1 : Mat n) := by
  exact traceOne_eq_traceFreePart_add_uniform
    (trace_normalizedRightGram A hT)

theorem trace_normalizedLeftGram (A : Mat n) (hT : gramTrace A ≠ 0) :
    Matrix.trace (normalizedLeftGram A) = 1 := by
  rw [normalizedLeftGram, Matrix.trace_smul, trace_leftGram_eq_trace_rightGram]
  have htrace : Matrix.trace (rightGram A) = (gramTrace A : ℂ) := by
    apply Complex.ext
    · rfl
    · rw [gramTrace_formula]
      simp [rightGram, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose,
        Complex.normSq_apply]
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      ring
  rw [htrace]
  exact inv_mul_cancel₀ (by exact_mod_cast hT)

theorem normalizedLeftGram_eq_traceFreePart_add_uniform
    [Nonempty n] (A : Mat n) (hT : gramTrace A ≠ 0) :
    normalizedLeftGram A =
      traceFreePart (normalizedLeftGram A) +
        ((Fintype.card n : ℂ)⁻¹) • (1 : Mat n) := by
  exact traceOne_eq_traceFreePart_add_uniform
    (trace_normalizedLeftGram A hT)

theorem normalizedRightGram_posSemidef (A : Mat n) :
    (normalizedRightGram A).PosSemidef := by
  apply Matrix.PosSemidef.smul (rightGram_posSemidef A)
  apply inv_nonneg.mpr
  rw [gramTrace_formula A]
  exact_mod_cast
    (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j))

theorem normalizedRightGram_cfcSqrt_mul_self (A : Mat n) :
    CFC.sqrt (normalizedRightGram A) *
        CFC.sqrt (normalizedRightGram A) = normalizedRightGram A := by
  exact CFC.sqrt_mul_sqrt_self (normalizedRightGram A)
    (ha := (normalizedRightGram_posSemidef A).nonneg)

theorem normalizedRightGram_cfcSqrt_posSemidef (A : Mat n) :
    (CFC.sqrt (normalizedRightGram A)).PosSemidef := by
  exact (CFC.sqrt_nonneg (normalizedRightGram A)).posSemidef

theorem normalizedLeftGram_posSemidef (A : Mat n) :
    (normalizedLeftGram A).PosSemidef := by
  apply Matrix.PosSemidef.smul (leftGram_posSemidef A)
  apply inv_nonneg.mpr
  rw [gramTrace_formula A]
  exact_mod_cast
    (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j))

theorem normalizedLeftGram_cfcSqrt_mul_self (A : Mat n) :
    CFC.sqrt (normalizedLeftGram A) *
        CFC.sqrt (normalizedLeftGram A) = normalizedLeftGram A := by
  exact CFC.sqrt_mul_sqrt_self (normalizedLeftGram A)
    (ha := (normalizedLeftGram_posSemidef A).nonneg)

theorem normalizedLeftGram_cfcSqrt_posSemidef (A : Mat n) :
    (CFC.sqrt (normalizedLeftGram A)).PosSemidef := by
  exact (CFC.sqrt_nonneg (normalizedLeftGram A)).posSemidef

theorem normalizedRightGram_isHermitian (A : Mat n) :
    (normalizedRightGram A).IsHermitian := by
  exact (normalizedRightGram_posSemidef A).isHermitian

theorem normalizedLeftGram_isHermitian (A : Mat n) :
    (normalizedLeftGram A).IsHermitian := by
  exact (normalizedLeftGram_posSemidef A).isHermitian

theorem leftGram_mul_affinity (A : Mat n) :
    leftGram A * A = A * rightGram A := by
  dsimp [leftGram, rightGram]
  rw [mul_assoc]

theorem affinity_adjoint_mul_leftGram (A : Mat n) :
    Aᴴ * leftGram A = rightGram A * Aᴴ := by
  dsimp [leftGram, rightGram]
  rw [← mul_assoc]

theorem normalizedLeftGram_mul_affinity (A : Mat n) :
    normalizedLeftGram A * A = A * normalizedRightGram A := by
  rw [normalizedLeftGram, normalizedRightGram, Matrix.smul_mul, Matrix.mul_smul]
  exact congrArg (fun X : Mat n => ((gramTrace A : ℂ)⁻¹) • X) (leftGram_mul_affinity A)

theorem normalizedRightGram_mul_affinity_adjoint (A : Mat n) :
    normalizedRightGram A * Aᴴ = Aᴴ * normalizedLeftGram A := by
  rw [normalizedRightGram, normalizedLeftGram, Matrix.smul_mul, Matrix.mul_smul]
  exact congrArg (fun X : Mat n => ((gramTrace A : ℂ)⁻¹) • X)
    (affinity_adjoint_mul_leftGram A).symm

theorem normalizedRightGram_scale_invariant
    (A : Mat n) (α : ℂ) (hα : α ≠ 0) (hT : gramTrace A ≠ 0) :
    normalizedRightGram (α • A) = normalizedRightGram A := by
  rw [normalizedRightGram, normalizedRightGram]
  have hgram : rightGram (α • A) = (Complex.normSq α : ℂ) • rightGram A := by
    simp only [rightGram, conjTranspose_smul]
    rw [smul_mul, Matrix.mul_smul, smul_smul]
    apply congrArg (fun z : ℂ => z • (Aᴴ * A))
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  rw [hgram]
  have htrace := gramTrace_scale A α
  rw [htrace]
  have hnorm : Complex.normSq α ≠ 0 := Complex.normSq_pos.mpr hα |>.ne'
  have hT' : (gramTrace A : ℂ) ≠ 0 := by
    exact_mod_cast hT
  have hscalar :
      ((Complex.normSq α * gramTrace A : ℝ) : ℂ)⁻¹ *
          (Complex.normSq α : ℂ) = (gramTrace A : ℂ)⁻¹ := by
    push_cast
    field_simp [hnorm, hT']
  rw [smul_smul, hscalar]

theorem normalizedLeftGram_scale_invariant
    (A : Mat n) (α : ℂ) (hα : α ≠ 0) (hT : gramTrace A ≠ 0) :
    normalizedLeftGram (α • A) = normalizedLeftGram A := by
  rw [normalizedLeftGram, normalizedLeftGram]
  have hgram : leftGram (α • A) = (Complex.normSq α : ℂ) • leftGram A := by
    simp only [leftGram, conjTranspose_smul]
    rw [smul_mul, Matrix.mul_smul, smul_smul]
    apply congrArg (fun z : ℂ => z • (A * Aᴴ))
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  rw [hgram]
  have htrace := gramTrace_scale A α
  rw [htrace]
  have hnorm : Complex.normSq α ≠ 0 := Complex.normSq_pos.mpr hα |>.ne'
  have hT' : (gramTrace A : ℂ) ≠ 0 := by
    exact_mod_cast hT
  have hscalar :
      ((Complex.normSq α * gramTrace A : ℝ) : ℂ)⁻¹ *
          (Complex.normSq α : ℂ) = (gramTrace A : ℂ)⁻¹ := by
    push_cast
    field_simp [hnorm, hT']
  rw [smul_smul, hscalar]

end InfoGeometry.Physics.CuntzTransitionGramBridge
