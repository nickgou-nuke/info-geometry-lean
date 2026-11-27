/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.GL11LocalGenerators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.LogarithmicJordanPair
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Canonical.TemperleyLiebJonesBridge
import InfoGeometry.Canonical.TemperleyLiebKauffmanYangBaxter
import InfoGeometry.Algebra.CliffordBraidingInterfaces
import InfoGeometry.Physics.ChiralTensorRecoupling
import InfoGeometry.Physics.TwoStrandJonesCasimir

/-!
# A concrete zero-loop Temperley--Lieb representation

At `q = I`, the usual two-site Temperley--Lieb matrix has loop parameter
`q + q⁻¹ = 0`.  This file proves the defining relations directly on two and
three copies of `ℂ²`.  It does not identify this finite representation with a
particular Hamiltonian or continuum theory.
-/

namespace InfoGeometry.Algebra.TemperleyLiebZeroLoop

open Matrix
open scoped Matrix ComplexConjugate

/-- Closed non-commutativity witnesses for the `4 × 4` complex matrix carrier (T16). -/
theorem mat4_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A := by
  let E01 : Matrix (Fin 4) (Fin 4) ℂ := fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let E10 : Matrix (Fin 4) (Fin 4) ℂ := fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  change (∑ k : Fin 4, E01 0 k * E10 k 0) = (∑ k : Fin 4, E10 0 k * E01 k 0) at h00
  norm_num [E01, E10, Fin.sum_univ_four] at h00

/-- The standard two-site Temperley--Lieb generator at `q = I`, in basis
`(00,01,10,11)`. -/
def generator : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, Complex.I, 1, 0;
     0, 1, -Complex.I, 0;
     0, 0, 0, 0]

/-- The loop parameter vanishes at `q = I`. -/
theorem loopParameter_eq_zero :
    Complex.I + Complex.I⁻¹ = 0 := by
  rw [Complex.inv_I]
  simp

/-- The two-site generator is nilpotent, the `δ = 0` specialization of
`e² = δe`. -/
theorem generator_sq_zero :
    generator * generator = (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

/-- A nonzero vector in the image and kernel of the zero-loop generator. -/
def jordanEigenvector : Fin 4 → ℂ :=
  ![0, 1, -Complex.I, 0]

/-- A generalized eigenvector mapped to `jordanEigenvector`. -/
def jordanGeneralized : Fin 4 → ℂ :=
  ![0, 0, 1, 0]

/-- The matrix generator as a native linear endomorphism. -/
def generatorEnd : Module.End ℂ (Fin 4 → ℂ) :=
  Matrix.mulVecLin generator

/-- The proposed eigenvector is genuinely nonzero. -/
theorem jordanEigenvector_ne_zero :
    jordanEigenvector ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 4)
  simp [jordanEigenvector] at h1

/-- The generator kills the image vector. -/
theorem generator_mulVec_jordanEigenvector :
    generator.mulVec jordanEigenvector = 0 := by
  funext i
  fin_cases i <;>
    simp [generator, jordanEigenvector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Complex.I_mul_I]

/-- The generator maps the generalized vector to the nonzero eigenvector. -/
theorem generator_mulVec_jordanGeneralized :
    generator.mulVec jordanGeneralized = jordanEigenvector := by
  funext i
  fin_cases i <;>
    simp [generator, jordanEigenvector, jordanGeneralized, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four]

/-- The displayed vectors form a genuine rank-two Jordan pair at eigenvalue
zero. -/
theorem isJordanPair_generatorEnd :
    LogarithmicJordanPair.IsJordanPair generatorEnd 0
      jordanEigenvector jordanGeneralized := by
  refine ⟨jordanEigenvector_ne_zero, ?_, ?_⟩
  · simpa [generatorEnd] using generator_mulVec_jordanEigenvector
  · simpa [generatorEnd] using generator_mulVec_jordanGeneralized

/-- The zero-loop Temperley--Lieb generator has a finite logarithmic Jordan
cell.  This is a finite non-semisimplicity theorem, not a continuum-limit
claim. -/
theorem generatorEnd_hasLogarithmicJordanCell :
    LogarithmicJordanPair.HasLogarithmicJordanCell generatorEnd :=
  LogarithmicJordanPair.hasLogarithmicJordanCell_of_isJordanPair
    isJordanPair_generatorEnd

/-- Exact rank-two nilpotence on the explicit generalized vector. -/
theorem generatorEnd_rank_two_nilpotence :
    (LogarithmicJordanPair.shifted generatorEnd 0).comp
          (LogarithmicJordanPair.shifted generatorEnd 0) jordanGeneralized = 0 ∧
      LogarithmicJordanPair.shifted generatorEnd 0 jordanGeneralized ≠ 0 :=
  LogarithmicJordanPair.rank_two_shifted_nilpotence
    isJordanPair_generatorEnd

/-- A three-site basis index `(a,b,c)`. -/
abbrev Triple := Fin 2 × Fin 2 × Fin 2

private def pairEntry (a b c d : Fin 2) : ℂ :=
  if a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 1 then Complex.I
  else if a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0 then 1
  else if a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1 then 1
  else if a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0 then -Complex.I
  else 0

/-- The generator acting on sites `1,2` of three sites. -/
def leftGenerator : Matrix Triple Triple ℂ :=
  fun x y =>
    pairEntry x.1 x.2.1 y.1 y.2.1 *
      if x.2.2 = y.2.2 then 1 else 0

/-- The generator acting on sites `2,3` of three sites. -/
def rightGenerator : Matrix Triple Triple ℂ :=
  fun x y =>
    (if x.1 = y.1 then 1 else 0) *
      pairEntry x.2.1 x.2.2 y.2.1 y.2.2

private theorem triple_matrix_ext
    {A B : Matrix Triple Triple ℂ}
    (h : ∀ i j, A i j = B i j) : A = B :=
  Matrix.ext fun i j => h i j

/-- The left three-site generator has loop parameter zero. -/
theorem leftGenerator_sq_zero :
    leftGenerator * leftGenerator = (0 : Matrix Triple Triple ℂ) := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [leftGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

/-- The right three-site generator has loop parameter zero. -/
theorem rightGenerator_sq_zero :
    rightGenerator * rightGenerator = (0 : Matrix Triple Triple ℂ) := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [rightGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

/-- First adjacent Temperley--Lieb relation. -/
theorem left_right_left :
    leftGenerator * rightGenerator * leftGenerator = leftGenerator := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [leftGenerator, rightGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

/-- Second adjacent Temperley--Lieb relation. -/
theorem right_left_right :
    rightGenerator * leftGenerator * rightGenerator = rightGenerator := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [leftGenerator, rightGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

/-- The open three-site zero-loop TL Hamiltonian on the existing carrier. -/
def chainHamiltonian : Matrix Triple Triple ℂ :=
  -(leftGenerator + rightGenerator)

theorem chainHamiltonian_sq :
    chainHamiltonian * chainHamiltonian =
      leftGenerator * rightGenerator + rightGenerator * leftGenerator := by
  unfold chainHamiltonian
  rw [neg_mul, mul_neg, neg_neg]
  simp only [add_mul, mul_add]
  rw [leftGenerator_sq_zero, rightGenerator_sq_zero]
  simp only [zero_add, add_zero]
  rw [add_comm]

section GeneralizedZeroLoopAndObstruction

/-- For any nilpotent element `e * e = 0` in an associative `K`-algebra `R`,
`(a • 1 + b • e)^2 = a^2 • 1 + (2 * a * b) • e`. -/
theorem tlZeroLoopBraid_sq {K R : Type*} [CommRing K] [Ring R] [Algebra K R]
    {e : R} (he : e * e = 0) (a b : K) :
    (a • (1 : R) + b • e) ^ 2 = (a ^ 2) • (1 : R) + (2 * a * b) • e := by
  rw [pow_two]
  simp only [Algebra.smul_def]
  have hcomm : e * algebraMap K R a = algebraMap K R a * e := (Algebra.commutes a e).symm
  have hcommb : e * algebraMap K R b = algebraMap K R b * e := (Algebra.commutes b e).symm
  calc
    (algebraMap K R a * 1 + algebraMap K R b * e) *
        (algebraMap K R a * 1 + algebraMap K R b * e) =
      algebraMap K R a * algebraMap K R a * 1 +
        (algebraMap K R a * algebraMap K R b + algebraMap K R b * algebraMap K R a) * e +
        (algebraMap K R b * algebraMap K R b) * (e * e) := by
      simp only [mul_one, add_mul, mul_add]
      rw [mul_assoc (algebraMap K R b) e (algebraMap K R a), hcomm,
        ← mul_assoc (algebraMap K R b),
        mul_assoc (algebraMap K R b) e (algebraMap K R b * e),
        ← mul_assoc e (algebraMap K R b) e, hcommb,
        mul_assoc (algebraMap K R b) e e]
      abel_nf
      simp only [mul_assoc]
    _ = algebraMap K R (a ^ 2) * 1 + algebraMap K R (2 * a * b) * e := by
      rw [he, mul_zero, add_zero, mul_one, mul_one]
      congr 1
      · rw [← map_mul, pow_two]
      · rw [← map_mul, ← map_mul, ← map_add, show a * b + b * a = 2 * a * b by ring]

/-- Exact fourth power of a zero-loop Kauffman braid operator `a • 1 + b • e` (`e * e = 0`):
`(a • 1 + b • e)^4 = a^4 • 1 + (4 * a^3 * b) • e`. -/
theorem tlZeroLoopBraid_pow_four {K R : Type*} [CommRing K] [Ring R] [Algebra K R]
    {e : R} (he : e * e = 0) (a b : K) :
    (a • (1 : R) + b • e) ^ 4 = (a ^ 4) • (1 : R) + (4 * a ^ 3 * b) • e := by
  have hsq : (a • (1 : R) + b • e) ^ 2 = (a ^ 2) • (1 : R) + (2 * a * b) • e :=
    tlZeroLoopBraid_sq he a b
  calc
    (a • (1 : R) + b • e) ^ 4 = ((a • (1 : R) + b • e) ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
    _ = ((a ^ 2) • (1 : R) + (2 * a * b) • e) ^ 2 := by rw [hsq]
    _ = ((a ^ 2) ^ 2) • (1 : R) + (2 * a ^ 2 * (2 * a * b)) • e :=
      tlZeroLoopBraid_sq he (a ^ 2) (2 * a * b)
    _ = (a ^ 4) • (1 : R) + (4 * a ^ 3 * b) • e := by
      rw [show (a ^ 2) ^ 2 = a ^ 4 by ring, show 2 * a ^ 2 * (2 * a * b) = 4 * a ^ 3 * b by ring]

/-- **Jordan-Cell Obstruction Theorem**: over any field `K` (`CharZero K`), a nontrivial
zero-loop braid operator `B = a • 1 + b • e` (`e * e = 0`, `a ≠ 0`, `b ≠ 0`, `e ≠ 0`) can NEVER
satisfy the `CliffordBraidData` central fourth-power condition `B^4 = -1`. -/
theorem tlZeroLoopBraid_fourth_central_obstruction {K R : Type*} [Field K] [CharZero K]
    [Ring R] [Algebra K R] {e : R} (he : e * e = 0) (hne : e ≠ 0)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a • (1 : R) + b • e) ^ 4 ≠ -(1 : R) := by
  intro h4
  rw [tlZeroLoopBraid_pow_four he a b] at h4
  have hkill : ((a ^ 4) • (1 : R) + (4 * a ^ 3 * b) • e) * e = -(1 : R) * e :=
    congrArg (· * e) h4
  rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul, he, smul_zero,
    add_zero, neg_mul, one_mul] at hkill
  have h1 : (a ^ 4 + 1) • e = 0 := by
    rw [add_smul, one_smul, hkill, neg_add_cancel]
  have ha4 : a ^ 4 + 1 = 0 := by
    by_contra hne0
    have := congrArg ((a ^ 4 + 1)⁻¹ • ·) h1
    rw [smul_smul, inv_mul_cancel₀ hne0, one_smul, smul_zero] at this
    exact hne this
  have ha4' : a ^ 4 = -1 := eq_neg_of_add_eq_zero_left ha4
  rw [ha4', neg_smul, one_smul, add_eq_left] at h4
  have hc4 : (4 * a ^ 3 * b : K) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)) hb
  have he0 := congrArg ((4 * a ^ 3 * b)⁻¹ • ·) h4
  rw [smul_smul, inv_mul_cancel₀ hc4, one_smul, smul_zero] at he0
  exact hne he0

/-- Generalized Artin Yang–Baxter theorem for ANY `TemperleyLiebSystem 0 R` at `a^4 = -1`. -/
theorem zeroLoopTLSystem_artin_braid {R : Type*} [Ring R] [Algebra ℂ R]
    (sys : TemperleyLiebJonesBridge.TemperleyLiebSystem 0 R)
    {a : ℂ} (ha : a ^ 4 = -1) :
    let B₁ := a • (1 : R) + a⁻¹ • sys.e1
    let B₂ := a • (1 : R) + a⁻¹ • sys.e2
    B₁ * B₂ * B₁ = B₂ * B₁ * B₂ := by
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, zero_pow (by decide)] at ha; norm_num at ha
  refine InfoGeometry.Canonical.TemperleyLiebKauffmanYangBaxter.yang_baxter_of_kauffman_coefficient sys a a⁻¹ ?_
  calc
    a ^ 2 * a⁻¹ + a * (a⁻¹) ^ 2 * 0 + (a⁻¹) ^ 3 = a + (a⁻¹) ^ 3 := by
      field_simp [ha0]; ring
    _ = (a ^ 4 + 1) * (a⁻¹) ^ 3 := by field_simp [ha0]
    _ = 0 := by rw [ha, neg_add_cancel, zero_mul]

end GeneralizedZeroLoopAndObstruction

section NSiteZeroLoopFamily

open InfoGeometry.Physics.TwoStrandJonesCasimir

/-- Generalized `n`-site zero-loop Temperley–Lieb generator acting on distinct sites `a ≠ b`
of `(Fin n → Fin 2) → ℂ`, encoding `[[I, 1], [1, -I]]` in the `(01, 10)` block. -/
def nSiteZeroLoopEnd {n : ℕ} (a b : Fin n) : Module.End ℂ ((Fin n → Fin 2) → ℂ) where
  toFun ψ f :=
    if f a = 0 ∧ f b = 1 then Complex.I * ψ f + ψ (swapStrandBits a b f)
    else if f a = 1 ∧ f b = 0 then ψ (swapStrandBits a b f) - Complex.I * ψ f
    else 0
  map_add' ψ φ := by
    funext f
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' r ψ := by
    funext f
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem nSiteZeroLoopEnd_sq_zero {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    nSiteZeroLoopEnd a b * nSiteZeroLoopEnd a b = 0 := by
  apply LinearMap.ext
  intro ψ
  funext f
  change nSiteZeroLoopEnd a b (nSiteZeroLoopEnd a b ψ) f = 0
  have hsw_a : (swapStrandBits a b f) a = f b := swapStrandBits_apply_left a b f
  have hsw_b : (swapStrandBits a b f) b = f a := swapStrandBits_apply_right hab f
  have hsw2 : swapStrandBits a b (swapStrandBits a b f) = f := swapStrandBits_involutive a b f
  by_cases ha0 : f a = 0 <;> by_cases hb0 : f b = 0
  · simp [nSiteZeroLoopEnd, ha0, hb0]
  · have hb1 : f b = 1 := by have := Fin.isLt (f b); omega
    dsimp [nSiteZeroLoopEnd]
    simp only [ha0, hb1, and_self, ↓reduceIte, hsw_a, hsw_b, hsw2]
    ring_nf
    simp [Complex.I_sq]
    ring
  · have ha1 : f a = 1 := by have := Fin.isLt (f a); omega
    dsimp [nSiteZeroLoopEnd]
    simp only [ha1, hb0, and_self, ↓reduceIte, hsw_a, hsw_b, hsw2]
    norm_num [Complex.I_sq]
    ring_nf
    simp [Complex.I_sq]
  · have ha1 : f a = 1 := by have := Fin.isLt (f a); omega
    have hb1 : f b = 1 := by have := Fin.isLt (f b); omega
    simp [nSiteZeroLoopEnd, ha1, hb1]

/-- Generalized `n`-site zero-loop TL contraction `e_{ab} e_{bc} e_{ab} = e_{ab}` for ANY
three distinct sites `a, b, c : Fin n` (`n ≥ 3`). -/
theorem nSiteZeroLoopEnd_contraction {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    nSiteZeroLoopEnd a b * nSiteZeroLoopEnd b c * nSiteZeroLoopEnd a b =
      nSiteZeroLoopEnd a b := by
  apply LinearMap.ext
  intro ψ
  funext f
  change nSiteZeroLoopEnd a b (nSiteZeroLoopEnd b c (nSiteZeroLoopEnd a b ψ)) f =
    nSiteZeroLoopEnd a b ψ f
  have ha2 : f a = 0 ∨ f a = 1 := by have := Fin.isLt (f a); omega
  have hb2 : f b = 0 ∨ f b = 1 := by have := Fin.isLt (f b); omega
  have hc2 : f c = 0 ∨ f c = 1 := by have := Fin.isLt (f c); omega
  rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;> rcases hc2 with hc | hc
  · simp [nSiteZeroLoopEnd, ha, hb]
  · simp [nSiteZeroLoopEnd, ha, hb]
  · -- (0, 1, 0)
    dsimp [nSiteZeroLoopEnd]
    have hsw1_b : (swapStrandBits a b f) b = 0 := by rw [swapStrandBits_apply_right hab, ha]
    have hsw1_c : (swapStrandBits a b f) c = 0 := by
      rw [swapStrandBits_apply_other hac.symm hbc.symm, hc]
    have hsw2_a : (swapStrandBits b c f) a = 0 := by
      rw [swapStrandBits_apply_other hab hac, ha]
    have hsw2_b : (swapStrandBits b c f) b = 0 := by rw [swapStrandBits_apply_left, hc]
    simp only [ha, hb, hc, hsw1_b, hsw1_c, hsw2_a, hsw2_b,
      and_self, ↓reduceIte, zero_ne_one, one_ne_zero,
      and_false, false_and]
    ring_nf
    simp [Complex.I_sq]
    ring
  · -- (0, 1, 1)
    dsimp [nSiteZeroLoopEnd]
    have hsw1_a : (swapStrandBits a b f) a = 1 := by rw [swapStrandBits_apply_left, hb]
    have hsw1_b : (swapStrandBits a b f) b = 0 := by rw [swapStrandBits_apply_right hab, ha]
    have hsw1_c : (swapStrandBits a b f) c = 1 := by
      rw [swapStrandBits_apply_other hac.symm hbc.symm, hc]
    have hsw3_a : (swapStrandBits b c (swapStrandBits a b f)) a = 1 := by
      rw [swapStrandBits_apply_other hab hac, hsw1_a]
    have hsw3_b : (swapStrandBits b c (swapStrandBits a b f)) b = 1 := by
      rw [swapStrandBits_apply_left, hsw1_c]
    simp only [ha, hb, hc, hsw1_a, hsw1_b, hsw1_c, hsw3_a, hsw3_b,
      swapStrandBits_involutive, and_self, ↓reduceIte, zero_ne_one, one_ne_zero,
      and_false, false_and]
    ring_nf
    simp [Complex.I_sq]
  · -- (1, 0, 0)
    dsimp [nSiteZeroLoopEnd]
    have hsw1_a : (swapStrandBits a b f) a = 0 := by rw [swapStrandBits_apply_left, hb]
    have hsw1_b : (swapStrandBits a b f) b = 1 := by rw [swapStrandBits_apply_right hab, ha]
    have hsw1_c : (swapStrandBits a b f) c = 0 := by
      rw [swapStrandBits_apply_other hac.symm hbc.symm, hc]
    have hsw3_a : (swapStrandBits b c (swapStrandBits a b f)) a = 0 := by
      rw [swapStrandBits_apply_other hab hac, hsw1_a]
    have hsw3_b : (swapStrandBits b c (swapStrandBits a b f)) b = 0 := by
      rw [swapStrandBits_apply_left, hsw1_c]
    simp only [ha, hb, hc, hsw1_a, hsw1_b, hsw1_c, hsw3_a, hsw3_b,
      swapStrandBits_involutive, and_self, ↓reduceIte, zero_ne_one, one_ne_zero,
      and_false, false_and]
    ring_nf
    simp [Complex.I_sq]
  · -- (1, 0, 1)
    dsimp [nSiteZeroLoopEnd]
    have hsw1_b : (swapStrandBits a b f) b = 1 := by rw [swapStrandBits_apply_right hab, ha]
    have hsw1_c : (swapStrandBits a b f) c = 1 := by
      rw [swapStrandBits_apply_other hac.symm hbc.symm, hc]
    have hsw2_a : (swapStrandBits b c f) a = 1 := by
      rw [swapStrandBits_apply_other hab hac, ha]
    have hsw2_b : (swapStrandBits b c f) b = 1 := by rw [swapStrandBits_apply_left, hc]
    simp only [ha, hb, hc, hsw1_b, hsw1_c, hsw2_a, hsw2_b,
      and_self, ↓reduceIte, zero_ne_one, one_ne_zero,
      and_false, false_and]
    ring_nf
    simp [Complex.I_sq]
    ring
  · simp [nSiteZeroLoopEnd, ha, hb]
  · simp [nSiteZeroLoopEnd, ha, hb]

theorem nSiteZeroLoopEnd_comm_of_disjoint {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    nSiteZeroLoopEnd a b * nSiteZeroLoopEnd c d =
      nSiteZeroLoopEnd c d * nSiteZeroLoopEnd a b := by
  apply LinearMap.ext
  intro ψ
  funext f
  change nSiteZeroLoopEnd a b (nSiteZeroLoopEnd c d ψ) f =
    nSiteZeroLoopEnd c d (nSiteZeroLoopEnd a b ψ) f
  have hsw_comm : swapStrandBits a b (swapStrandBits c d f) =
      swapStrandBits c d (swapStrandBits a b f) := by
    funext i
    by_cases hia : i = a
    · subst hia
      rw [swapStrandBits_apply_left, swapStrandBits_apply_other hbc hbd,
        swapStrandBits_apply_other hac had, swapStrandBits_apply_left]
    · by_cases hib : i = b
      · subst hib
        rw [swapStrandBits_apply_right hab, swapStrandBits_apply_other hac had,
          swapStrandBits_apply_other hbc hbd, swapStrandBits_apply_right hab]
      · by_cases hic : i = c
        · subst hic
          rw [swapStrandBits_apply_other hac.symm hbc.symm, swapStrandBits_apply_left,
            swapStrandBits_apply_left, swapStrandBits_apply_other had.symm hbd.symm]
        · by_cases hid : i = d
          · subst hid
            rw [swapStrandBits_apply_other had.symm hbd.symm, swapStrandBits_apply_right hcd,
              swapStrandBits_apply_right hcd, swapStrandBits_apply_other hac.symm hbc.symm]
          · simp [swapStrandBits, hia, hib, hic, hid]
  have hsw_cd_a : (swapStrandBits c d f) a = f a := swapStrandBits_apply_other hac had f
  have hsw_cd_b : (swapStrandBits c d f) b = f b := swapStrandBits_apply_other hbc hbd f
  have hsw_ab_c : (swapStrandBits a b f) c = f c := swapStrandBits_apply_other hac.symm hbc.symm f
  have hsw_ab_d : (swapStrandBits a b f) d = f d := swapStrandBits_apply_other had.symm hbd.symm f
  dsimp [nSiteZeroLoopEnd]
  simp only [hsw_cd_a, hsw_cd_b, hsw_ab_c, hsw_ab_d, hsw_comm]
  split_ifs <;> ring

end NSiteZeroLoopFamily

section ConcreteZeroLoopSystemAndSynthesis

open InfoGeometry.Physics.TwoStrandJonesCasimir

/-- Concrete `TemperleyLiebSystem 0 (Matrix Triple Triple ℂ)` instance packaged from
`leftGenerator` and `rightGenerator`. -/
def zeroLoopTLSystem :
    TemperleyLiebJonesBridge.TemperleyLiebSystem 0 (Matrix Triple Triple ℂ) where
  e1 := leftGenerator
  e2 := rightGenerator
  self_loop_1 := by simpa [zero_smul] using leftGenerator_sq_zero
  self_loop_2 := by simpa [zero_smul] using rightGenerator_sq_zero
  contraction_121 := left_right_left
  contraction_212 := right_left_right

/-- Concrete 8th-root-of-unity scalar `a = (1 + I) / sqrt 2` (`a^4 = -1`). -/
noncomputable def zeroLoopBraidScalar : ℂ := ((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℂ)

theorem zeroLoopBraidScalar_pow_four : zeroLoopBraidScalar ^ 4 = -1 := by
  have hsq : zeroLoopBraidScalar ^ 2 = Complex.I := by
    unfold zeroLoopBraidScalar
    have h2 : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [div_pow, h2]
    ring_nf
    simp [Complex.I_sq]
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hsq, Complex.I_sq]

/-- Concrete 3-site zero-loop Artin braid relation together with explicit failure of
`B^4 = -1` (Jordan-cell obstruction preventing `CliffordBraidData` promotion). -/
theorem concrete_zeroLoop_artin_and_fourth_obstruction :
    let B₁ := zeroLoopBraidScalar • (1 : Matrix Triple Triple ℂ) +
        zeroLoopBraidScalar⁻¹ • leftGenerator
    let B₂ := zeroLoopBraidScalar • (1 : Matrix Triple Triple ℂ) +
        zeroLoopBraidScalar⁻¹ • rightGenerator
    (B₁ * B₂ * B₁ = B₂ * B₁ * B₂) ∧
    (B₁ ^ 4 ≠ -(1 : Matrix Triple Triple ℂ)) := by
  intro B₁ B₂
  refine ⟨zeroLoopTLSystem_artin_braid zeroLoopTLSystem zeroLoopBraidScalar_pow_four, ?_⟩
  have hne : leftGenerator ≠ 0 := by
    intro h
    have h0 := congrArg (fun M : Matrix Triple Triple ℂ => M (0, 1, 0) (0, 1, 0)) h
    simp [leftGenerator, pairEntry] at h0
  have ha0 : zeroLoopBraidScalar ≠ 0 := by
    have ha4 := zeroLoopBraidScalar_pow_four
    intro h0
    rw [h0, zero_pow (by decide)] at ha4
    norm_num at ha4
  exact tlZeroLoopBraid_fourth_central_obstruction leftGenerator_sq_zero hne ha0
    (inv_ne_zero ha0)

/-- Basis equivalence `(Fin 2 × Fin 2) ≃ Fin 4` ordering `(0,0),(0,1),(1,0),(1,1)`. -/
def bitPairEquivFin4 : (Fin 2 × Fin 2) ≃ Fin 4 where
  toFun p := ⟨2 * p.1.val + p.2.val, by omega⟩
  invFun k := (⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)
  left_inv p := by
    ext <;> simp only [] <;> omega
  right_inv k := by
    ext; simp only []; omega

/-- **Singlet / Chiral / Zero-Loop Synthesis**: transporting
`ChiralTensorRecoupling.zeroLoopSpinPair` (obtained via local unitary left/right twist of
`ChiralTensorRecoupling.e`) into `Matrix (Fin 4) (Fin 4) ℂ` yields literally
`TemperleyLiebZeroLoop.generator`, unifying `d = 1` (`singletProjector`), `d = 2` (`e`),
and `d = 0` (`generator`). -/
theorem spinPair_zeroLoop_eq_generator :
    ∀ p q : Fin 2 × Fin 2,
      (InfoGeometry.Physics.TwoStrandJonesCasimir.spinPairEquivTwoStrandOperator
        ChiralTensorRecoupling.zeroLoopSpinPair)
        (fun i j => if i = q.1 ∧ j = q.2 then 1 else 0) p.1 p.2 =
      generator (bitPairEquivFin4 p) (bitPairEquivFin4 q) := by
  intro ⟨a, b⟩ ⟨c, d⟩
  unfold ChiralTensorRecoupling.zeroLoopSpinPair ChiralTensorRecoupling.X ChiralTensorRecoupling.Y
  simp only [map_add, map_smul, map_sub,
    InfoGeometry.Physics.TwoStrandJonesCasimir.spinPairEquivTwoStrandOperator_tmul,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, InfoGeometry.Physics.TwoStrandJonesCasimir.leftAction,
    InfoGeometry.Physics.TwoStrandJonesCasimir.rightAction,
    LinearMap.coe_mk, AddHom.coe_mk]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [generator, bitPairEquivFin4, Matrix.vecTail, Matrix.vecHead,
      InfoGeometry.Physics.ChiralCausalCone.σPlus,
      InfoGeometry.Physics.ChiralCausalCone.σMinus, InfoGeometry.Physics.ChiralCausalCone.PPlus,
      InfoGeometry.Physics.ChiralCausalCone.PMinus, Fin.sum_univ_two]

end ConcreteZeroLoopSystemAndSynthesis

end InfoGeometry.Algebra.TemperleyLiebZeroLoop
