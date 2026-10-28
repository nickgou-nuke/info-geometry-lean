/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Twistor.PerjesConventions

/-!
# Constructive real null-line incidence

For a nonzero lower spinor the Witt-null condition is exactly solvability
of the Hermitian incidence equation. A concrete Hermitian solution is
constructed; all solutions form an affine real line with a nonzero rank-one
null direction. This is a statement on actual matrices, not an assumed
geodesic or quotient-manifold structure.
-/

noncomputable section
namespace InfoGeometry.Twistor.PerjesNullLineCorrespondence

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PerjesConventions
open scoped BigOperators Matrix

/-- Positive spinor norm used solely to select an explicit point on the line. -/
def spinorNormSq (p : Spinor2) : ℝ := Complex.normSq (p 0) + Complex.normSq (p 1)

def pair (p v : Spinor2) : ℂ := star (p 0) * v 0 + star (p 1) * v 1

lemma normSq_cast (p : Spinor2) :
    (spinorNormSq p : ℂ) = star (p 0) * p 0 + star (p 1) * p 1 := by
  simp [spinorNormSq, Complex.normSq_eq_conj_mul_self]

lemma spinorNormSq_pos (p : Spinor2) (hp : p ≠ 0) : 0 < spinorNormSq p := by
  have h0 := Complex.normSq_nonneg (p 0)
  have h1 := Complex.normSq_nonneg (p 1)
  by_contra h
  have hz0 : Complex.normSq (p 0) = 0 := by dsimp [spinorNormSq] at h; linarith
  have hz1 : Complex.normSq (p 1) = 0 := by dsimp [spinorNormSq] at h; linarith
  apply hp
  ext a
  fin_cases a
  · exact Complex.normSq_eq_zero.mp hz0
  · exact Complex.normSq_eq_zero.mp hz1

lemma normSq_cast_ne_zero (p : Spinor2) (hp : p ≠ 0) : (spinorNormSq p : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (spinorNormSq_pos p hp))

lemma outer_mulVec (u v p : Spinor2) :
    (Matrix.vecMulVec u v).mulVec p = (∑ a : Fin 2, v a * p a) • u := by
  ext a
  simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- An explicit Hermitian solution of X p = v, when p* v is real. -/
def hermitianSolution (p v : Spinor2) : ComplexSpacetime :=
  (spinorNormSq p : ℂ)⁻¹ •
    (Matrix.vecMulVec v (star p) + Matrix.vecMulVec p (star v)) -
  (pair p v / (spinorNormSq p : ℂ) ^ 2) • Matrix.vecMulVec p (star p)

lemma hermitianSolution_hermitian (p v : Spinor2) (hc : star (pair p v) = pair p v) :
    (hermitianSolution p v)ᴴ = hermitianSolution p v := by
  ext a b
  simp [hermitianSolution, Matrix.conjTranspose_apply, Matrix.vecMulVec,
    smul_eq_mul, hc]
  ring

lemma hermitianSolution_mulVec (p v : Spinor2) (hp : p ≠ 0)
    (hc : star (pair p v) = pair p v) :
    (hermitianSolution p v).mulVec p = v := by
  have hr := normSq_cast_ne_zero p hp
  have hn : (∑ a : Fin 2, (star p) a * p a) = (spinorNormSq p : ℂ) := by
    calc
      _ = star (p 0) * p 0 + star (p 1) * p 1 := by
        simp [Fin.sum_univ_two]
      _ = (spinorNormSq p : ℂ) := (normSq_cast p).symm
  have hv : (∑ a : Fin 2, (star v) a * p a) = pair p v := by
    calc
      _ = star (pair p v) := by simp [pair, Fin.sum_univ_two]; ring
      _ = pair p v := hc
  simp only [hermitianSolution, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.add_mulVec, outer_mulVec, hn, hv]
  ext a
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  field_simp [hr]
  ring

lemma pair_real_of_witt_null (Z : Twistor4) (hZ : wittPair Z Z = 0) :
    star (pair Z.2 (Complex.I • Z.1)) = pair Z.2 (Complex.I • Z.1) := by
  have h : pair Z.2 (Complex.I • Z.1) - star (pair Z.2 (Complex.I • Z.1)) =
      Complex.I * wittPair Z Z := by
    simp [pair, wittPair, Fin.sum_univ_two, smul_eq_mul]
    ring
  rw [hZ, mul_zero] at h
  exact (sub_eq_zero.mp h).symm

/-- A canonical affine point; this choice is not asserted Lorentz covariant. -/
def lineOrigin (Z : Twistor4) : ComplexSpacetime :=
  hermitianSolution Z.2 (Complex.I • Z.1)

theorem lineOrigin_hermitian (Z : Twistor4) (hZ : wittPair Z Z = 0) :
    (lineOrigin Z)ᴴ = lineOrigin Z :=
  hermitianSolution_hermitian _ _ (pair_real_of_witt_null Z hZ)

theorem lineOrigin_incident (Z : Twistor4) (hp : Z.2 ≠ 0) (hZ : wittPair Z Z = 0) :
    paperIncidence (lineOrigin Z) Z.2 = Z := by
  have h := hermitianSolution_mulVec Z.2 (Complex.I • Z.1) hp
    (pair_real_of_witt_null Z hZ)
  rw [paperIncidence_apply]
  change (-Complex.I • (hermitianSolution Z.2 (Complex.I • Z.1)).mulVec Z.2, Z.2) = Z
  rw [h]
  simp [smul_smul]

/-- Witt-nullity is equivalent to real incidence, with the nonzero pi condition explicit. -/
theorem null_iff_real_incident (Z : Twistor4) (hp : Z.2 ≠ 0) :
    wittPair Z Z = 0 ↔ ∃ X : ComplexSpacetime, Xᴴ = X ∧ paperIncidence X Z.2 = Z := by
  constructor
  · intro hZ
    exact ⟨lineOrigin Z, lineOrigin_hermitian Z hZ, lineOrigin_incident Z hp hZ⟩
  · rintro ⟨X, hX, hinc⟩
    have h := paperIncidence_witt_isotropic X hX Z.2 Z.2
    simpa [hinc] using h

/-- The orthogonal spinor determines the null direction of the incidence line. -/
def orthogonalSpinor (p : Spinor2) : Spinor2 := ![star (p 1), -star (p 0)]

def lineDirection (p : Spinor2) : ComplexSpacetime :=
  Matrix.vecMulVec (orthogonalSpinor p) (star (orthogonalSpinor p))

lemma lineDirection_hermitian (p : Spinor2) : (lineDirection p)ᴴ = lineDirection p := by
  ext a b
  simp [lineDirection, Matrix.vecMulVec, Matrix.conjTranspose_apply, mul_comm]

lemma lineDirection_mulVec (p : Spinor2) : (lineDirection p).mulVec p = 0 := by
  ext a
  fin_cases a <;>
    simp [lineDirection, orthogonalSpinor, Matrix.mulVec, Matrix.vecMulVec,
      dotProduct, Fin.sum_univ_two] <;> ring

lemma lineDirection_null (p : Spinor2) : (lineDirection p).det = 0 := by
  simp [lineDirection, Matrix.vecMulVec, Matrix.det_fin_two]
  ring

lemma trace_lineDirection (p : Spinor2) :
    Matrix.trace (lineDirection p) = (spinorNormSq p : ℂ) := by
  simp [lineDirection, orthogonalSpinor, Matrix.trace, Matrix.vecMulVec,
    Fin.sum_univ_two, normSq_cast]
  ring

lemma lineDirection_ne_zero (p : Spinor2) (hp : p ≠ 0) : lineDirection p ≠ 0 := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [trace_lineDirection] at ht
  exact normSq_cast_ne_zero p hp (by simpa using ht)

/-- A Hermitian matrix annihilating p lies in exactly one real rank-one direction. -/
lemma hermitian_kernel_identity (D : ComplexSpacetime) (p : Spinor2)
    (hD : Dᴴ = D) (hker : D.mulVec p = 0) :
    (spinorNormSq p : ℂ) • D = Matrix.trace D • lineDirection p := by
  have hs (a b : Fin 2) : star (D b a) = D a b := congrFun (congrFun hD a) b
  have r0 : D 0 0 * p 0 + D 0 1 * p 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hker 0
  have r1 : D 1 0 * p 0 + D 1 1 * p 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hker 1
  have c0 : star (p 0) * D 0 0 + star (p 1) * D 1 0 = 0 := by
    simpa [hs, mul_comm] using congrArg star r0
  have c1 : star (p 0) * D 0 1 + star (p 1) * D 1 1 = 0 := by
    simpa [hs, mul_comm] using congrArg star r1
  change (starRingEnd ℂ) (p 0) * D 0 0 + (starRingEnd ℂ) (p 1) * D 1 0 = 0 at c0
  change (starRingEnd ℂ) (p 0) * D 0 1 + (starRingEnd ℂ) (p 1) * D 1 1 = 0 at c1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [normSq_cast, lineDirection, orthogonalSpinor, Matrix.vecMulVec,
      Matrix.trace, Fin.sum_univ_two, smul_eq_mul]
  · linear_combination (starRingEnd ℂ) (p 0) * r0 - p 1 * c1
  · linear_combination (starRingEnd ℂ) (p 1) * r0 + p 0 * c1
  · linear_combination (starRingEnd ℂ) (p 0) * r1 + p 1 * c0
  · linear_combination (starRingEnd ℂ) (p 1) * r1 - p 0 * c0

lemma hermitian_trace_real (D : ComplexSpacetime) (hD : Dᴴ = D) :
    ((Matrix.trace D).re : ℂ) = Matrix.trace D := by
  have ht : star (Matrix.trace D) = Matrix.trace D := by
    have h := congrArg Matrix.trace hD
    simpa [Matrix.trace, Matrix.conjTranspose_apply] using h
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im ht
    simp at hi ⊢
    linarith

/-- Explicit scalar extraction from the Hermitian kernel identity. -/
theorem hermitian_kernel_line (D : ComplexSpacetime) (p : Spinor2) (hp : p ≠ 0)
    (hD : Dᴴ = D) (hker : D.mulVec p = 0) :
    D = ((Matrix.trace D).re / spinorNormSq p) • lineDirection p := by
  have h := hermitian_kernel_identity D p hD hker
  have hr := normSq_cast_ne_zero p hp
  ext a b
  have hab := congrFun (congrFun h a) b
  simp only [Matrix.smul_apply, smul_eq_mul] at hab ⊢
  change D a b = (((Matrix.trace D).re / spinorNormSq p : ℝ) : ℂ) * lineDirection p a b
  push_cast
  rw [hermitian_trace_real D hD]
  field_simp [hr]
  simpa [mul_comm] using hab

/-- Full affine fibre description, not just the determinant-zero consequence. -/
theorem real_incidence_fibre (Z : Twistor4) (hp : Z.2 ≠ 0)
    (hZ : wittPair Z Z = 0) (X : ComplexSpacetime) :
    (Xᴴ = X ∧ paperIncidence X Z.2 = Z) ↔
      ∃ t : ℝ, X = lineOrigin Z + t • lineDirection Z.2 := by
  have hO := lineOrigin_hermitian Z hZ
  have hi := lineOrigin_incident Z hp hZ
  constructor
  · rintro ⟨hX, hx⟩
    have hk : (X - lineOrigin Z).mulVec Z.2 = 0 := by
      have he := congrArg Prod.fst (hx.trans hi.symm)
      simp only [paperIncidence_apply] at he
      have he' := congrArg (fun v : Spinor2 => Complex.I • v) he
      simp [smul_smul] at he'
      rw [Matrix.sub_mulVec, he', sub_self]
    have hd : (X - lineOrigin Z)ᴴ = X - lineOrigin Z := by
      rw [Matrix.conjTranspose_sub, hX, hO]
    refine ⟨(Matrix.trace (X - lineOrigin Z)).re / spinorNormSq Z.2, ?_⟩
    have h := hermitian_kernel_line (X - lineOrigin Z) Z.2 hp hd hk
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · rintro ⟨t, rfl⟩
    constructor
    · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        hO, lineDirection_hermitian]
    · rw [paperIncidence_apply, Matrix.add_mulVec, Matrix.smul_mulVec,
        lineDirection_mulVec]
      simpa [paperIncidence_apply] using hi

/-- The real line parameter is unique because its null direction is nonzero. -/
theorem line_parameter_unique (Z : Twistor4) (hp : Z.2 ≠ 0) (s t : ℝ)
    (h : lineOrigin Z + s • lineDirection Z.2 =
      lineOrigin Z + t • lineDirection Z.2) : s = t := by
  have he := add_left_cancel h
  have htrace := congrArg (fun D : ComplexSpacetime => (Matrix.trace D).re) he
  have hr := spinorNormSq_pos Z.2 hp
  apply mul_right_cancel₀ (ne_of_gt hr)
  simpa [Matrix.trace_smul, trace_lineDirection] using htrace

end InfoGeometry.Twistor.PerjesNullLineCorrespondence
