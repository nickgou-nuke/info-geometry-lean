/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.CliffordWaveletNativeL2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Clifford-Wavelet Transform and the Uncertainty Principle (arXiv:1905.10169v1)

This owner formalizes the mathematical core of:
  H. Banouh, A. Ben Mabrouk, M. Kesri,
  "Clifford-wavelet Transform and the uncertainty principle",
  `arXiv:1905.10169v1`.

It integrates the existing native Hilbert-space uncertainty layer (`heisenberg`,
`noncollapse`) with:
1. **Theorem 2 (Operator Commutator Uncertainty, Eq. 2.3)**: for symmetric bounded
   operators on a complex Hilbert space `H`,
   `(1/2) * ‖⟨[A, B]f, f⟩‖ ≤ ‖A f‖ * ‖B f‖`.
2. **Section 2.1 (`EuclideanCliffordSpin`)**: the real Clifford algebra
   `ℝ_n = Cl(0, n)` on `EuclideanSpace ℝ (Fin n)` with generators `e_i² = -1`,
   `e_i e_j + e_j e_i = 0`, explicit non-commutativity witness via `Quaternion ℝ`
   at `n = 2`, inner/outer vector decomposition `x y = x · y + x ∧ y`, conjugation
   (`star`), hyperplane reflections `ω x ω`, and `Spin(n)` orthogonal rotations.
3. **Section 3 (`DirectionalSchwartzUncertainty`, Eq. 3.1)**: directional position-
   frequency Heisenberg inequality on `SchwartzMap V H` over any finite-dimensional
   real inner-product space `V` (`1 / (4π)` in Mathlib's `exp (-2πi⟨x,ξ⟩)` Fourier
   convention; exact `1 / 2` in angular frequency `ω_k = 2π ξ_k`).
4. **Sections 4–5 (`CliffordWaveletAnalysisAndUncertainty`)**:
   - Scale invariance of the radial admissibility integral (`da / a`).
   - **Proposition 6 & Proposition 7**: wavelet `L²` isometry (`Eq. 4.1`, `Eq. 4.4`)
     and weak reconstruction for general noncommutative operator multipliers `M p ξ`
     satisfying `M† M = w · I`.
   - **Proposition 3**: injectivity (`T_ψ f = 0` a.e. implies `f = 0`).
   - **Lemma 9 & Theorem 8 (Eq. 5.1)**: weighted frequency identity and full
     Clifford–wavelet Heisenberg uncertainty principle (recording the paper's
     `(2π)^{n/2}` normalization consistently across Eq. 4.4 and Lemma 9).
-/

noncomputable section

namespace InfoGeometry.Analysis.CliffordWaveletUncertainty

open InfoGeometry.Analysis.CliffordWaveletNativeL2
open MeasureTheory

section OperatorUncertainty

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/--
Robertson uncertainty for two bounded operators in a chosen state.

The deviations are norms of the centered operator vectors. The theorem is
therefore valid on a noncommutative operator carrier and requires no spectral
diagonalization.
-/
theorem heisenberg
    (A B : H →L[ℂ] H) (ψ : H) :
    |RCLike.im
        (inner ℂ (centeredOperatorVector A ψ)
          (centeredOperatorVector B ψ))| ≤
      operatorDeviation A ψ * operatorDeviation B ψ :=
  centered_operator_uncertainty A B ψ

omit [CompleteSpace H] in
/--
A nonzero antisymmetric pairing prevents simultaneous collapse of both
operator deviations.
-/
theorem noncollapse
    (A B : H →L[ℂ] H) (ψ : H)
    (hpair :
      RCLike.im
          (inner ℂ (centeredOperatorVector A ψ)
            (centeredOperatorVector B ψ)) ≠ 0) :
    operatorDeviation A ψ ≠ 0 ∨ operatorDeviation B ψ ≠ 0 := by
  by_contra h
  push Not at h
  have hA : centeredOperatorVector A ψ = 0 := by
    exact norm_eq_zero.mp h.1
  have hB : centeredOperatorVector B ψ = 0 := by
    exact norm_eq_zero.mp h.2
  apply hpair
  simp [hA, hB]

omit [CompleteSpace H] in
/-- Paper Theorem 2 (Eq. 2.3): commutator form of Heisenberg's uncertainty
principle for two symmetric bounded operators on a complex Hilbert space. -/
theorem commutator_uncertainty_of_symmetric
    (A B : H →L[ℂ] H)
    (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (hB : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (f : H) :
    (1 / 2 : ℝ) * ‖inner ℂ (A (B f) - B (A f)) f‖ ≤ ‖A f‖ * ‖B f‖ := by
  have hcomm :
      inner ℂ (A (B f) - B (A f)) f =
        starRingEnd ℂ (inner ℂ (A f) (B f)) - inner ℂ (A f) (B f) := by
    rw [inner_sub_left, hA (B f) f, hB (A f) f, inner_conj_symm]
  have hnorm_sub :
      ‖inner ℂ (A (B f) - B (A f)) f‖ ≤ 2 * ‖inner ℂ (A f) (B f)‖ := by
    rw [hcomm]
    calc
      ‖starRingEnd ℂ (inner ℂ (A f) (B f)) - inner ℂ (A f) (B f)‖
          ≤ ‖starRingEnd ℂ (inner ℂ (A f) (B f))‖ + ‖inner ℂ (A f) (B f)‖ :=
            norm_sub_le _ _
      _ = 2 * ‖inner ℂ (A f) (B f)‖ := by
            rw [Complex.norm_conj]
            ring
  have hcs : ‖inner ℂ (A f) (B f)‖ ≤ ‖A f‖ * ‖B f‖ :=
    norm_inner_le_norm (A f) (B f)
  linarith

end OperatorUncertainty

/-! ## Section 2.1: Euclidean Clifford Algebra `Cl(0, n)`, Involutions, Reflections, and `Spin(n)` -/

section EuclideanCliffordSpin

/-- Negative-definite Euclidean bilinear form `-⟪x, y⟫` on `ℝⁿ`. -/
def euclideanNegBilin (n : ℕ) : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.mk₂ ℝ (fun x y : EuclideanSpace ℝ (Fin n) => -inner ℝ x y)
    (fun x y z => by simp [inner_add_left]; rw [add_comm])
    (fun r x y => by simp [inner_smul_left])
    (fun x y z => by simp [inner_add_right]; rw [add_comm])
    (fun r x y => by simp [inner_smul_right])

/-- Quadratic form `Q(x) = -‖x‖²` generating the real Clifford algebra `ℝ_n = Cl(0, n)`. -/
def euclideanNegForm (n : ℕ) : QuadraticForm ℝ (EuclideanSpace ℝ (Fin n)) :=
  (euclideanNegBilin n).toQuadraticMap

/-- The real Clifford algebra `ℝ_n` associated to `(ℝⁿ, -‖·‖²)`. -/
abbrev EuclideanClifford (n : ℕ) : Type :=
  CliffordAlgebra (euclideanNegForm n)

/-- Orthonormal standard basis vector `e_i` in `EuclideanSpace ℝ (Fin n)`. -/
def euclideanBasisVec (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i 1

/-- Clifford generator `e_i = ι(euclideanBasisVec n i)` in `ℝ_n`. -/
def euclideanCliffordGen (n : ℕ) (i : Fin n) : EuclideanClifford n :=
  CliffordAlgebra.ι (euclideanNegForm n) (euclideanBasisVec n i)

@[simp] theorem euclideanNegForm_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    euclideanNegForm n x = -‖x‖ ^ 2 := by
  change -inner ℝ x x = -‖x‖ ^ 2
  rw [real_inner_self_eq_norm_sq]

theorem ι_sq_eq_neg_norm_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    CliffordAlgebra.ι (euclideanNegForm n) x * CliffordAlgebra.ι (euclideanNegForm n) x =
      algebraMap ℝ (EuclideanClifford n) (-‖x‖ ^ 2) := by
  rw [CliffordAlgebra.ι_sq_scalar, euclideanNegForm_apply]

private theorem euclideanNegForm_polar {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    QuadraticMap.polar (euclideanNegForm n) x y = -2 * inner ℝ x y := by
  change euclideanNegForm n (x + y) - euclideanNegForm n x - euclideanNegForm n y =
    -2 * inner ℝ x y
  dsimp [euclideanNegForm, euclideanNegBilin]
  simp only [inner_add_left, inner_add_right, real_inner_comm y x]
  ring

theorem ι_mul_add_swap_eq_neg_two_inner {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    CliffordAlgebra.ι (euclideanNegForm n) x * CliffordAlgebra.ι (euclideanNegForm n) y +
      CliffordAlgebra.ι (euclideanNegForm n) y * CliffordAlgebra.ι (euclideanNegForm n) x =
      algebraMap ℝ (EuclideanClifford n) (-2 * inner ℝ x y) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, euclideanNegForm_polar]

theorem euclideanCliffordGen_sq {n : ℕ} (i : Fin n) :
    euclideanCliffordGen n i * euclideanCliffordGen n i = -1 := by
  unfold euclideanCliffordGen euclideanBasisVec
  rw [ι_sq_eq_neg_norm_sq]
  have hnorm : ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simp [PiLp.norm_single]
  rw [hnorm]
  norm_num

theorem euclideanCliffordGen_anticomm {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    euclideanCliffordGen n i * euclideanCliffordGen n j +
      euclideanCliffordGen n j * euclideanCliffordGen n i = 0 := by
  unfold euclideanCliffordGen euclideanBasisVec
  rw [ι_mul_add_swap_eq_neg_two_inner]
  have hinner :
      inner ℝ (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))
        (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n)) = 0 := by
    simp [EuclideanSpace.inner_single_left, hij.symm]
  rw [hinner, mul_zero, map_zero]

/-- Explicit OpenGauss `T16` non-commutativity witness for `EuclideanClifford 2`
via its canonical homomorphism into `Quaternion ℝ` sending `e₀ ↦ i`, `e₁ ↦ j`. -/
theorem euclideanCliffordGen_two_noncommutative :
    euclideanCliffordGen 2 0 * euclideanCliffordGen 2 1 ≠
      euclideanCliffordGen 2 1 * euclideanCliffordGen 2 0 := by
  let fLin : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] Quaternion ℝ :=
    { toFun := fun x => ⟨0, x 0, x 1, 0⟩
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun r x => by ext <;> simp }
  have hf_cond : ∀ m : EuclideanSpace ℝ (Fin 2),
      fLin m * fLin m = algebraMap ℝ (Quaternion ℝ) (euclideanNegForm 2 m) := by
    intro m
    rw [euclideanNegForm_apply]
    have hnorm : ‖m‖ ^ 2 = m 0 * m 0 + m 1 * m 1 := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, Fin.sum_univ_two]
    rw [hnorm]
    ext <;> simp [fLin] <;> ring
  let Φ : EuclideanClifford 2 →ₐ[ℝ] Quaternion ℝ :=
    CliffordAlgebra.lift (euclideanNegForm 2) ⟨fLin, hf_cond⟩
  have h0 : Φ (euclideanCliffordGen 2 0) = ⟨0, 1, 0, 0⟩ := by
    unfold euclideanCliffordGen euclideanBasisVec
    rw [CliffordAlgebra.lift_ι_apply]
    ext <;> simp [fLin]
  have h1 : Φ (euclideanCliffordGen 2 1) = ⟨0, 0, 1, 0⟩ := by
    unfold euclideanCliffordGen euclideanBasisVec
    rw [CliffordAlgebra.lift_ι_apply]
    ext <;> simp [fLin]
  intro hcomm
  have him := congrArg (fun x => (Φ x).imK) hcomm
  rw [map_mul, map_mul, h0, h1] at him
  norm_num at him

/-- Clifford inner dot product `x · y = (1/2) (x y + y x)` of vectors. -/
def cliffordDot {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : EuclideanClifford n :=
  (1 / 2 : ℝ) • (CliffordAlgebra.ι (euclideanNegForm n) x *
      CliffordAlgebra.ι (euclideanNegForm n) y +
    CliffordAlgebra.ι (euclideanNegForm n) y *
      CliffordAlgebra.ι (euclideanNegForm n) x)

/-- Clifford outer wedge product `x ∧ y = (1/2) (x y - y x)` of vectors. -/
def cliffordWedge {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : EuclideanClifford n :=
  (1 / 2 : ℝ) • (CliffordAlgebra.ι (euclideanNegForm n) x *
      CliffordAlgebra.ι (euclideanNegForm n) y -
    CliffordAlgebra.ι (euclideanNegForm n) y *
      CliffordAlgebra.ι (euclideanNegForm n) x)

theorem cliffordDot_eq_neg_inner {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    cliffordDot x y = algebraMap ℝ (EuclideanClifford n) (-inner ℝ x y) := by
  unfold cliffordDot
  rw [ι_mul_add_swap_eq_neg_two_inner, Algebra.algebraMap_eq_smul_one, smul_smul]
  have hcoeff : (1 / 2 : ℝ) * (-2 * inner ℝ x y) = -inner ℝ x y := by linarith
  rw [hcoeff, ← Algebra.algebraMap_eq_smul_one]

theorem clifford_mul_eq_dot_add_wedge {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    CliffordAlgebra.ι (euclideanNegForm n) x * CliffordAlgebra.ι (euclideanNegForm n) y =
      cliffordDot x y + cliffordWedge x y := by
  unfold cliffordDot cliffordWedge
  rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ, smul_smul]
  norm_num

@[simp] theorem cliffordConj_eq_star {n : ℕ} (a : EuclideanClifford n) :
    CliffordAlgebra.reverse (CliffordAlgebra.involute a) = star a := rfl

theorem cliffordConj_mul {n : ℕ} (a b : EuclideanClifford n) :
    star (a * b) = star b * star a := star_mul a b

theorem cliffordConj_ι {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    star (CliffordAlgebra.ι (euclideanNegForm n) x) =
      -CliffordAlgebra.ι (euclideanNegForm n) x :=
  CliffordAlgebra.star_ι x

/-- Hyperplane reflection `R_ω(x) = x - 2⟨x, ω⟩ ω` across `ω⊥`. -/
def hyperplaneReflection {n : ℕ} (ω x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (2 * inner ℝ x ω) • ω

theorem hyperplaneReflection_inner {n : ℕ} {ω : EuclideanSpace ℝ (Fin n)} (hω : ‖ω‖ = 1)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (hyperplaneReflection ω x) (hyperplaneReflection ω y) = inner ℝ x y := by
  have hω2 : inner ℝ ω ω = 1 := by
    rw [real_inner_self_eq_norm_sq, hω]
    norm_num
  unfold hyperplaneReflection
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, hω2, mul_one, real_inner_comm ω x, real_inner_comm ω y]
  ring

theorem hyperplaneReflection_norm {n : ℕ} {ω : EuclideanSpace ℝ (Fin n)} (hω : ‖ω‖ = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖hyperplaneReflection ω x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  exact hyperplaneReflection_inner hω x x

theorem hyperplaneReflection_involutive {n : ℕ} {ω : EuclideanSpace ℝ (Fin n)} (hω : ‖ω‖ = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    hyperplaneReflection ω (hyperplaneReflection ω x) = x := by
  have hω2 : inner ℝ ω ω = 1 := by
    rw [real_inner_self_eq_norm_sq, hω]
    norm_num
  unfold hyperplaneReflection
  have hsub :
      inner ℝ (x - (2 * inner ℝ x ω) • ω) ω = -inner ℝ x ω := by
    simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial, hω2]
    ring
  rw [hsub]
  module

/-- Clifford reflection identity `ω x ω = R_ω(x)` for unit `ω ∈ S^{n-1}` (Section 2.1). -/
theorem clifford_reflection_eq {n : ℕ} {ω : EuclideanSpace ℝ (Fin n)} (hω : ‖ω‖ = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    CliffordAlgebra.ι (euclideanNegForm n) ω *
        CliffordAlgebra.ι (euclideanNegForm n) x *
        CliffordAlgebra.ι (euclideanNegForm n) ω =
      CliffordAlgebra.ι (euclideanNegForm n) (hyperplaneReflection ω x) := by
  have hanti :
      CliffordAlgebra.ι (euclideanNegForm n) ω * CliffordAlgebra.ι (euclideanNegForm n) x =
        algebraMap ℝ (EuclideanClifford n) (-2 * inner ℝ x ω) -
          CliffordAlgebra.ι (euclideanNegForm n) x * CliffordAlgebra.ι (euclideanNegForm n) ω := by
    have h := ι_mul_add_swap_eq_neg_two_inner ω x
    have hinner : inner ℝ ω x = inner ℝ x ω := real_inner_comm _ _
    rw [hinner] at h
    exact eq_sub_of_add_eq h
  have hωsq :
      CliffordAlgebra.ι (euclideanNegForm n) ω * CliffordAlgebra.ι (euclideanNegForm n) ω = -1 := by
    rw [ι_sq_eq_neg_norm_sq, hω]
    norm_num
  have hlhs :
      CliffordAlgebra.ι (euclideanNegForm n) ω *
          CliffordAlgebra.ι (euclideanNegForm n) x *
          CliffordAlgebra.ι (euclideanNegForm n) ω =
        (algebraMap ℝ (EuclideanClifford n) (-2 * inner ℝ x ω) -
          CliffordAlgebra.ι (euclideanNegForm n) x * CliffordAlgebra.ι (euclideanNegForm n) ω) *
          CliffordAlgebra.ι (euclideanNegForm n) ω := by
    rw [hanti]
  rw [hlhs, sub_mul, mul_assoc, hωsq, mul_neg_one, sub_neg_eq_add]
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, add_comm]
  unfold hyperplaneReflection
  rw [map_sub, map_smul, sub_eq_add_neg, ← neg_smul]
  congr 1
  simp [neg_mul]

/-- Product in `EuclideanClifford n` of a list of unit vectors (even-length products lie in `Spin(n)`). -/
def spinorProd {n : ℕ} : List (EuclideanSpace ℝ (Fin n)) → EuclideanClifford n
  | [] => 1
  | ω :: l => CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd l

/-- Orthogonal composition of hyperplane reflections corresponding to `spinorProd l`. -/
def spinorRotation {n : ℕ} :
    List (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  | [] => id
  | ω :: l => fun x => hyperplaneReflection ω (spinorRotation l x)

theorem spinorProd_mul_star {n : ℕ} (l : List (EuclideanSpace ℝ (Fin n)))
    (hl : ∀ ω ∈ l, ‖ω‖ = 1) :
    spinorProd l * star (spinorProd l) = 1 := by
  induction l with
  | nil => simp [spinorProd]
  | cons ω rest ih =>
      have hω : ‖ω‖ = 1 := hl ω List.mem_cons_self
      have hrest : ∀ u ∈ rest, ‖u‖ = 1 := fun u hu => hl u (List.mem_cons_of_mem ω hu)
      have hωsq :
          CliffordAlgebra.ι (euclideanNegForm n) ω *
              CliffordAlgebra.ι (euclideanNegForm n) ω = -1 := by
        rw [ι_sq_eq_neg_norm_sq, hω]
        norm_num
      change (CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd rest) *
          star (CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd rest) = 1
      rw [star_mul, cliffordConj_ι, mul_assoc, ← mul_assoc (spinorProd rest), ih hrest, one_mul,
        mul_neg, hωsq, neg_neg]

theorem star_mul_spinorProd {n : ℕ} (l : List (EuclideanSpace ℝ (Fin n)))
    (hl : ∀ ω ∈ l, ‖ω‖ = 1) :
    star (spinorProd l) * spinorProd l = 1 := by
  induction l with
  | nil => simp [spinorProd]
  | cons ω rest ih =>
      have hω : ‖ω‖ = 1 := hl ω List.mem_cons_self
      have hrest : ∀ u ∈ rest, ‖u‖ = 1 := fun u hu => hl u (List.mem_cons_of_mem ω hu)
      have hωsq :
          CliffordAlgebra.ι (euclideanNegForm n) ω *
              CliffordAlgebra.ι (euclideanNegForm n) ω = -1 := by
        rw [ι_sq_eq_neg_norm_sq, hω]
        norm_num
      change star (CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd rest) *
          (CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd rest) = 1
      rw [star_mul, cliffordConj_ι, mul_assoc, ← mul_assoc (-CliffordAlgebra.ι (euclideanNegForm n) ω),
        neg_mul, hωsq, neg_neg, one_mul, ih hrest]

private theorem spinorProd_conj_ι_signed {n : ℕ} (l : List (EuclideanSpace ℝ (Fin n)))
    (hl : ∀ ω ∈ l, ‖ω‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    spinorProd l * CliffordAlgebra.ι (euclideanNegForm n) x * star (spinorProd l) =
      ((-1 : ℝ) ^ l.length) • CliffordAlgebra.ι (euclideanNegForm n) (spinorRotation l x) := by
  induction l with
  | nil =>
      simp [spinorProd, spinorRotation]
  | cons ω rest ih =>
      have hω : ‖ω‖ = 1 := hl ω List.mem_cons_self
      have hrest : ∀ u ∈ rest, ‖u‖ = 1 := fun u hu => hl u (List.mem_cons_of_mem ω hu)
      change (CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd rest) *
          CliffordAlgebra.ι (euclideanNegForm n) x *
          star (CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd rest) = _
      rw [star_mul, cliffordConj_ι, List.length_cons, pow_succ', neg_one_mul]
      calc
        CliffordAlgebra.ι (euclideanNegForm n) ω * spinorProd rest *
            CliffordAlgebra.ι (euclideanNegForm n) x *
            (star (spinorProd rest) * -CliffordAlgebra.ι (euclideanNegForm n) ω)
            = -(CliffordAlgebra.ι (euclideanNegForm n) ω *
                (spinorProd rest * CliffordAlgebra.ι (euclideanNegForm n) x *
                  star (spinorProd rest)) *
                CliffordAlgebra.ι (euclideanNegForm n) ω) := by
              simp only [mul_neg, mul_assoc]
        _ = -(CliffordAlgebra.ι (euclideanNegForm n) ω *
              (((-1 : ℝ) ^ rest.length) •
                CliffordAlgebra.ι (euclideanNegForm n) (spinorRotation rest x)) *
              CliffordAlgebra.ι (euclideanNegForm n) ω) := by
              rw [ih hrest]
        _ = -((-1 : ℝ) ^ rest.length •
              (CliffordAlgebra.ι (euclideanNegForm n) ω *
                CliffordAlgebra.ι (euclideanNegForm n) (spinorRotation rest x) *
                CliffordAlgebra.ι (euclideanNegForm n) ω)) := by
              simp only [mul_smul_comm, smul_mul_assoc]
        _ = -(-1 : ℝ) ^ rest.length •
              CliffordAlgebra.ι (euclideanNegForm n) (spinorRotation (ω :: rest) x) := by
              rw [clifford_reflection_eq hω, ← neg_smul]
              rfl

/-- Paper §2.1: any even product of unit vectors `s ∈ Spin(n)` acts on vectors via
`s x s̄ = T(x)`, where `T ∈ SO(n)` is the composition of hyperplane reflections. -/
theorem spinorProd_conj_ι {n : ℕ} (l : List (EuclideanSpace ℝ (Fin n)))
    (hl : ∀ ω ∈ l, ‖ω‖ = 1) (heven : Even l.length) (x : EuclideanSpace ℝ (Fin n)) :
    spinorProd l * CliffordAlgebra.ι (euclideanNegForm n) x * star (spinorProd l) =
      CliffordAlgebra.ι (euclideanNegForm n) (spinorRotation l x) := by
  rw [spinorProd_conj_ι_signed l hl x, heven.neg_one_pow, one_smul]

theorem spinorRotation_inner {n : ℕ} (l : List (EuclideanSpace ℝ (Fin n)))
    (hl : ∀ ω ∈ l, ‖ω‖ = 1) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (spinorRotation l x) (spinorRotation l y) = inner ℝ x y := by
  induction l with
  | nil => rfl
  | cons ω rest ih =>
      have hω : ‖ω‖ = 1 := hl ω List.mem_cons_self
      have hrest : ∀ u ∈ rest, ‖u‖ = 1 := fun u hu => hl u (List.mem_cons_of_mem ω hu)
      change inner ℝ (hyperplaneReflection ω (spinorRotation rest x))
        (hyperplaneReflection ω (spinorRotation rest y)) = inner ℝ x y
      rw [hyperplaneReflection_inner hω, ih hrest]

theorem spinorRotation_norm {n : ℕ} (l : List (EuclideanSpace ℝ (Fin n)))
    (hl : ∀ ω ∈ l, ‖ω‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖spinorRotation l x‖ = ‖x‖ := by
  induction l with
  | nil => rfl
  | cons ω rest ih =>
      have hω : ‖ω‖ = 1 := hl ω List.mem_cons_self
      have hrest : ∀ u ∈ rest, ‖u‖ = 1 := fun u hu => hl u (List.mem_cons_of_mem ω hu)
      change ‖hyperplaneReflection ω (spinorRotation rest x)‖ = ‖x‖
      rw [hyperplaneReflection_norm hω, ih hrest]

end EuclideanCliffordSpin

/-! ## Section 3: Directional Schwartz Uncertainty on `ℝⁿ` (`Eq. 3.1`) -/

section DirectionalSchwartzUncertainty

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {H : Type*} [NormedAddCommGroup H]

private theorem real_inner_toL2 [InnerProductSpace ℝ H] (f g : SchwartzMap V H) :
    inner ℝ (f.toLp 2 volume) (g.toLp 2 volume) =
      ∫ x : V, inner ℝ (f x) (g x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg]

private theorem complex_inner_toL2 [InnerProductSpace ℂ H] (f g : SchwartzMap V H) :
    inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) =
      ∫ x : V, inner ℂ (f x) (g x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg]

private theorem norm_toLp_sq_eq_integral [InnerProductSpace ℂ H] (f : SchwartzMap V H) :
    ‖f.toLp 2 volume‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  rw [← real_inner_self_eq_norm_sq, real_inner_toL2]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  exact real_inner_self_eq_norm_sq (f x)

private theorem toL2_add [NormedSpace ℝ H] (f g : SchwartzMap V H) :
    (f + g).toLp 2 volume = f.toLp 2 volume + g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℝ H 2 volume).map_add f g

private theorem toL2_sub [NormedSpace ℂ H] (f g : SchwartzMap V H) :
    (f - g).toLp 2 volume = f.toLp 2 volume - g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ H 2 volume).map_sub f g

private theorem toL2_smul [NormedSpace ℂ H] (c : ℂ) (f : SchwartzMap V H) :
    (c • f).toLp 2 volume = c • f.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ H 2 volume).map_smul c f

section RealSchwartz

variable [InnerProductSpace ℝ H]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Product rule on Schwartz space along direction `m`:
`∂_m ((⟨·, m⟩ - a) • f) = ‖m‖² • f + (⟨·, m⟩ - a) • ∂_m f`. -/
theorem lineDeriv_position_coord (f : SchwartzMap V H) (m : V) (a : ℝ) :
    LineDeriv.lineDerivOp m (SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) f) =
      (‖m‖ ^ 2) • f +
        SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a)
          (LineDeriv.lineDerivOp m f) := by
  have hg : (fun x : V => inner ℝ x m - a).HasTemperateGrowth := by fun_prop
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply,
    smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  have hf_smul :=
    (((innerSL ℝ m).hasFDerivAt).sub_const a).smul (f.hasFDerivAt x)
  have hderiv :
      fderiv ℝ (SchwartzMap.smulLeftCLM H (fun y : V => inner ℝ y m - a) f) x =
        ((innerSL ℝ m) x - a) • fderiv ℝ f x + (innerSL ℝ m).smulRight (f x) := by
    have hfun :
        (⇑(SchwartzMap.smulLeftCLM H (fun y : V => inner ℝ y m - a) f)) =
          ((fun y : V => (innerSL ℝ m) y - a) • (f : V → H)) := by
      ext y
      rw [SchwartzMap.smulLeftCLM_apply_apply hg f y]
      dsimp
      rw [real_inner_comm]
    rw [hfun]
    exact hf_smul.fderiv
  rw [hderiv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    innerSL_apply_apply, real_inner_comm m x,
    real_inner_self_eq_norm_sq, add_comm]

/-- Integration by parts for directional position and line-derivative operators on `SchwartzMap V H`. -/
theorem real_inner_position_lineDeriv (f : SchwartzMap V H) (m : V) (a : ℝ) :
    inner ℝ
        ((SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) f).toLp 2 volume)
        ((LineDeriv.lineDerivOp m f).toLp 2 volume) =
      -(1 / 2 : ℝ) * ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2 := by
  let q := SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) f
  let d := LineDeriv.lineDerivOp m f
  have hg : (fun x : V => inner ℝ x m - a).HasTemperateGrowth := by fun_prop
  have hmove :
      inner ℝ (f.toLp 2 volume)
          ((SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) d).toLp 2 volume) =
        inner ℝ (q.toLp 2 volume) (d.toLp 2 volume) := by
    rw [real_inner_toL2, real_inner_toL2]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    simp only [q, SchwartzMap.smulLeftCLM_apply_apply hg,
      real_inner_smul_left, real_inner_smul_right]
  have hibp :
      inner ℝ (f.toLp 2 volume) ((LineDeriv.lineDerivOp m q).toLp 2 volume) =
        -inner ℝ (d.toLp 2 volume) (q.toLp 2 volume) := by
    rw [real_inner_toL2, real_inner_toL2]
    exact SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left f q (innerSL ℝ) m
  have hderiv :
      LineDeriv.lineDerivOp m q =
        (‖m‖ ^ 2) • f + SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) d :=
    lineDeriv_position_coord f m a
  have hsmul : ((‖m‖ ^ 2 : ℝ) • f).toLp 2 volume = (‖m‖ ^ 2 : ℝ) • f.toLp 2 volume :=
    (SchwartzMap.toLpCLM ℝ H 2 volume).map_smul (‖m‖ ^ 2) f
  rw [hderiv, toL2_add, hsmul, inner_add_right, inner_smul_right, hmove,
    real_inner_self_eq_norm_sq, real_inner_comm (q.toLp 2 volume) (d.toLp 2 volume)] at hibp
  change inner ℝ (q.toLp 2 volume) (d.toLp 2 volume) = _
  linarith

end RealSchwartz

section ComplexSchwartz

variable [InnerProductSpace ℂ H]

/-- Directional position/derivative uncertainty with imaginary frequency shift `b` (in `2π` units). -/
theorem norm_sq_le_two_mul_position_mul_shifted_lineDeriv
    (f : SchwartzMap V H) (m : V) (a b : ℝ) :
    ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) f).toLp 2 volume‖ *
        ‖(LineDeriv.lineDerivOp m f -
          ((2 * (Real.pi : ℂ) * Complex.I) * b) • f).toLp 2 volume‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  let q := SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) f
  let d := LineDeriv.lineDerivOp m f
  let c : ℂ := (2 * (Real.pi : ℂ) * Complex.I) * b
  have hg : (fun x : V => inner ℝ x m - a).HasTemperateGrowth := by fun_prop
  have hzero : inner ℝ (q.toLp 2 volume) ((c • f).toLp 2 volume) = 0 := by
    rw [real_inner_toL2]
    have hpoint (x : V) : inner ℝ (q x) ((c • f) x) = 0 := by
      simp only [q, SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply,
        real_inner_smul_left]
      have hself : inner ℝ (f x) (c • f x) = 0 := by
        change (inner ℂ (f x) (c • f x)).re = 0
        have hc : c.re = 0 := by simp [c]
        simp only [inner_smul_right, Complex.mul_re, hc, zero_mul]
        have him : (inner ℂ (f x) (f x)).im = 0 :=
          inner_self_im (𝕜 := ℂ) (f x)
        rw [him]
        ring
      rw [hself, mul_zero]
    simp_rw [hpoint]
    simp
  have hpair : inner ℝ (q.toLp 2 volume) ((d - c • f).toLp 2 volume) =
      -(1 / 2 : ℝ) * ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2 := by
    rw [toL2_sub, inner_sub_right, hzero, sub_zero]
    exact real_inner_position_lineDeriv f m a
  have h := real_inner_le_norm (-(q.toLp 2 volume)) ((d - c • f).toLp 2 volume)
  rw [inner_neg_left, norm_neg, hpair] at h
  change ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2 ≤
    2 * ‖q.toLp 2 volume‖ * ‖(d - c • f).toLp 2 volume‖
  nlinarith

variable [CompleteSpace H]

/-- Fourier transform turns the shifted directional derivative into multiplication by
`(2 * π * I) * (⟨ξ, m⟩ - b)`. -/
theorem fourier_shifted_lineDeriv (f : SchwartzMap V H) (m : V) (b : ℝ) :
    FourierTransform.fourier
        (LineDeriv.lineDerivOp m f -
          ((2 * (Real.pi : ℂ) * Complex.I) * b) • f) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
          (FourierTransform.fourier f) := by
  rw [sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_smul,
    CliffordWaveletNativeL2.fourier_lineDeriv_eq_frequencyMultiplication]
  have hg : (fun ξ : V => inner ℝ ξ m).HasTemperateGrowth := by fun_prop
  have hg' : (fun ξ : V => inner ℝ ξ m - b).HasTemperateGrowth := by fun_prop
  ext ξ
  simp only [add_apply, neg_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg']
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul,
    ← neg_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-- Plancherel relates the shifted directional-derivative norm to `2π` times the centered
frequency-coordinate norm on `V`. -/
theorem norm_shifted_lineDeriv_eq_two_pi_mul_frequency
    (f : SchwartzMap V H) (m : V) (b : ℝ) :
    ‖(LineDeriv.lineDerivOp m f -
        ((2 * (Real.pi : ℂ) * Complex.I) * b) • f).toLp 2 volume‖ =
      (2 * Real.pi) *
        ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
          (FourierTransform.fourier f)).toLp 2 volume‖ := by
  rw [← CliffordWaveletNativeL2.norm_fourier_toL2_eq,
    fourier_shifted_lineDeriv, toL2_smul, norm_smul]
  simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- **Paper Eq. (3.1), General Directional Form**: Heisenberg uncertainty inequality on
`SchwartzMap V H` along any direction `m : V` and arbitrary centers `a b : ℝ`. -/
theorem heisenberg_schwartz_nd (f : SchwartzMap V H) (m : V) (a b : ℝ) :
    ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2 ≤
      (4 * Real.pi) *
        ‖(SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
          (FourierTransform.fourier f)).toLp 2 volume‖ := by
  calc
    ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2 ≤
        2 * ‖(SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) f).toLp 2 volume‖ *
          ‖(LineDeriv.lineDerivOp m f -
            ((2 * (Real.pi : ℂ) * Complex.I) * b) • f).toLp 2 volume‖ :=
      norm_sq_le_two_mul_position_mul_shifted_lineDeriv f m a b
    _ = _ := by rw [norm_shifted_lineDeriv_eq_two_pi_mul_frequency]; ring

/-- **Paper Eq. (3.1), Angular-Frequency Coordinate Form**: for `V = ℝⁿ` and coordinate `k`,
using angular frequency `ω_k = 2π ξ_k`, the exact constant is `1 / 2`. -/
theorem heisenberg_schwartz_coord {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) H) (k : Fin n) :
    (1 / 2 : ℝ) * ‖f.toLp 2 volume‖ ^ 2 ≤
      ‖(SchwartzMap.smulLeftCLM H (fun x : EuclideanSpace ℝ (Fin n) => x k) f).toLp 2 volume‖ *
      ‖(SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k)
        (FourierTransform.fourier f)).toLp 2 volume‖ := by
  let m : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single k 1
  have hm : ‖m‖ = 1 := by simp [m, PiLp.norm_single]
  have hnd := heisenberg_schwartz_nd f m 0 0
  rw [hm, one_pow, one_mul] at hnd
  have hpos :
      (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x m - 0) =
        fun x : EuclideanSpace ℝ (Fin n) => x k := by
    ext x
    simp [m, EuclideanSpace.inner_single_right]
  have hfreq :
      SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k)
          (FourierTransform.fourier f) =
        (2 * Real.pi) • SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => inner ℝ ξ m - 0)
          (FourierTransform.fourier f) := by
    have hm_eq :
        (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k) =
          fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * inner ℝ ξ m := by
      ext ξ
      simp [m, EuclideanSpace.inner_single_right]
    have hg₁ : (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k).HasTemperateGrowth := by
      rw [hm_eq]
      fun_prop
    have hg₂ : (fun ξ : EuclideanSpace ℝ (Fin n) => inner ℝ ξ m - 0).HasTemperateGrowth := by
      fun_prop
    ext ξ
    rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg₁,
      SchwartzMap.smulLeftCLM_apply_apply hg₂, smul_smul]
    congr 1
    simp [m, EuclideanSpace.inner_single_right]
  rw [hpos] at hnd
  have hsmulLp :
      ((2 * Real.pi) • SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => inner ℝ ξ m - 0)
          (FourierTransform.fourier f)).toLp 2 volume =
        (2 * Real.pi) • (SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => inner ℝ ξ m - 0)
          (FourierTransform.fourier f)).toLp 2 volume :=
    (SchwartzMap.toLpCLM ℝ H 2 volume).map_smul _ _
  rw [hfreq, hsmulLp, norm_smul,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos), hpos]
  linarith

end ComplexSchwartz

end DirectionalSchwartzUncertainty

/-! ## Sections 4–5: Clifford–Wavelet Admissibility, Isometry, Weak Reconstruction, and Uncertainty Principle -/

section CliffordWaveletAnalysisAndUncertainty

/-- Scale invariance of the radial Haar admissibility integral `∫_{0}^{∞} h(a t) / t dt`. -/
theorem haar_admissibility_scale_invariant {a : ℝ} (ha : 0 < a) (h : ℝ → ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), h (a * t) / t =
      ∫ u in Set.Ioi (0 : ℝ), h u / u := by
  have hrewrite :
      (fun t : ℝ => h (a * t) / t) =
        fun t : ℝ => a • ((fun u : ℝ => h u / u) (a * t)) := by
    ext t
    rw [smul_eq_mul]
    by_cases ht : t = 0
    · subst ht; simp
    · field_simp [ha.ne', ht]
  rw [hrewrite, MeasureTheory.integral_smul]
  have hcomp :=
    MeasureTheory.integral_comp_mul_left_Ioi (fun u : ℝ => h u / u) 0 ha
  rw [mul_zero] at hcomp
  rw [hcomp, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- Measure-theoretic Cauchy–Schwarz inequality `(∫ u v)² ≤ (∫ u²) (∫ v²)` over any measure. -/
theorem integral_mul_sq_le {P : Type*} [MeasurableSpace P] {ν : Measure P}
    (u v : P → ℝ)
    (hu2 : Integrable (fun p => u p ^ 2) ν)
    (hv2 : Integrable (fun p => v p ^ 2) ν)
    (huv : Integrable (fun p => u p * v p) ν) :
    (∫ p, u p * v p ∂ν) ^ 2 ≤
      (∫ p, u p ^ 2 ∂ν) * (∫ p, v p ^ 2 ∂ν) := by
  have hquad : ∀ t : ℝ,
      0 ≤ t ^ 2 * (∫ p, u p ^ 2 ∂ν) - 2 * t * (∫ p, u p * v p ∂ν) +
        (∫ p, v p ^ 2 ∂ν) := by
    intro t
    have hnn : 0 ≤ ∫ p, (t * u p - v p) ^ 2 ∂ν :=
      integral_nonneg (fun p => sq_nonneg _)
    have hexp :
        (fun p => (t * u p - v p) ^ 2) =
          fun p => (t ^ 2 * u p ^ 2 - 2 * t * (u p * v p)) + v p ^ 2 := by
      ext p
      ring
    have h1 : Integrable (fun p => t ^ 2 * u p ^ 2 - 2 * t * (u p * v p)) ν :=
      (hu2.const_mul _).sub (huv.const_mul _)
    rw [hexp, integral_add h1 hv2,
      integral_sub (hu2.const_mul _) (huv.const_mul _),
      integral_const_mul, integral_const_mul] at hnn
    exact hnn
  have hAu : 0 ≤ ∫ p, u p ^ 2 ∂ν := integral_nonneg (fun p => sq_nonneg _)
  rcases eq_or_lt_of_le hAu with h0 | hpos
  · have hzero : ∫ p, u p * v p ∂ν = 0 := by
      by_contra hne
      have ht := hquad (((∫ p, v p ^ 2 ∂ν) + 1) / (2 * (∫ p, u p * v p ∂ν)))
      rw [← h0, mul_zero, zero_sub] at ht
      have hdiv :
          2 * (((∫ p, v p ^ 2 ∂ν) + 1) / (2 * (∫ p, u p * v p ∂ν))) *
              (∫ p, u p * v p ∂ν) =
            (∫ p, v p ^ 2 ∂ν) + 1 := by
        field_simp [hne]
      linarith
    rw [hzero, ← h0]
    norm_num
  · have hmin := hquad ((∫ p, u p * v p ∂ν) / (∫ p, u p ^ 2 ∂ν))
    have hmul := mul_le_mul_of_nonneg_left hmin hAu
    have hid :
        (∫ p, u p ^ 2 ∂ν) *
            (((∫ p, u p * v p ∂ν) / (∫ p, u p ^ 2 ∂ν)) ^ 2 * (∫ p, u p ^ 2 ∂ν) -
              2 * ((∫ p, u p * v p ∂ν) / (∫ p, u p ^ 2 ∂ν)) * (∫ p, u p * v p ∂ν) +
              (∫ p, v p ^ 2 ∂ν)) =
          (∫ p, u p ^ 2 ∂ν) * (∫ p, v p ^ 2 ∂ν) - (∫ p, u p * v p ∂ν) ^ 2 := by
      field_simp [hpos.ne']
      ring
    linarith

private theorem norm_sq_of_scalar_adjoint_mul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (M : H →L[ℂ] H) (w : ℝ)
    (hM : ∀ u v : H, inner ℂ (M u) (M v) = (w : ℂ) * inner ℂ u v)
    (u : H) :
    ‖M u‖ ^ 2 = w * ‖u‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hre : (inner ℂ (M u) (M u)).re = w * (inner ℂ u u).re := by
    rw [hM u u, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change ‖M u‖ ^ 2 = w * ‖u‖ ^ 2
  rw [← real_inner_self_eq_norm_sq (M u), ← real_inner_self_eq_norm_sq u]
  exact hre

section WaveletTheorems

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

/-- **Paper Proposition 6 (Isometry, Eq. 4.1)**: for any wavelet transform realized via
noncommutative frequency multipliers `M p ξ : H →L[ℂ] H` satisfying the operator-level
admissibility relation `(M p ξ)† (M p ξ) = w(p, ξ) I` with `∫ p, w(p, ξ) ∂ν = C_ψ` a.e.,
the wavelet-domain inner product equals `C_ψ` times the signal `L²` inner product. -/
theorem cliffordWavelet_isometry_inner
    (M : P → V → (H →L[ℂ] H)) (w : P → V → ℝ) (C_ψ : ℝ)
    (hM : ∀ p ξ (u v : H), inner ℂ (M p ξ u) (M p ξ v) = (w p ξ : ℂ) * inner ℂ u v)
    (hAdm : ∀ᵐ ξ ∂(volume : Measure V), (∫ p, w p ξ ∂ν) = C_ψ)
    (f g : SchwartzMap V H) (T_f T_g : P → SchwartzMap V H)
    (hTf : ∀ p ξ, FourierTransform.fourier (T_f p) ξ = M p ξ (FourierTransform.fourier f ξ))
    (hTg : ∀ p ξ, FourierTransform.fourier (T_g p) ξ = M p ξ (FourierTransform.fourier g ξ))
    (hInt : Integrable (Function.uncurry fun p ξ =>
      inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_g p) ξ))
      (ν.prod (volume : Measure V))) :
    ∫ p, inner ℂ ((T_f p).toLp 2 volume) ((T_g p).toLp 2 volume) ∂ν =
      (C_ψ : ℂ) * inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  have hpoint :
      (fun p : P => inner ℂ ((T_f p).toLp 2 volume) ((T_g p).toLp 2 volume)) =
        fun p : P => ∫ ξ : V,
          inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_g p) ξ) := by
    ext p
    rw [complex_inner_toL2, ← SchwartzMap.integral_inner_fourier_fourier]
  rw [hpoint, MeasureTheory.integral_integral_swap hInt]
  have hswap :
      (fun ξ : V => ∫ p : P,
        inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_g p) ξ) ∂ν) =ᵐ[volume]
        fun ξ : V => (C_ψ : ℂ) *
          inner ℂ (FourierTransform.fourier f ξ) (FourierTransform.fourier g ξ) := by
    filter_upwards [hAdm] with ξ hξ
    have hfun :
        (fun p : P =>
          inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_g p) ξ)) =
          fun p : P => (w p ξ : ℂ) *
            inner ℂ (FourierTransform.fourier f ξ) (FourierTransform.fourier g ξ) := by
      ext p
      rw [hTf, hTg, hM]
    rw [hfun, integral_mul_const]
    have hofReal :
        (∫ p : P, (w p ξ : ℂ) ∂ν) = ((∫ p : P, w p ξ ∂ν : ℝ) : ℂ) := by
      change ∫ p : P, Complex.ofRealLI (w p ξ) ∂ν = Complex.ofRealLI (∫ p : P, w p ξ ∂ν)
      exact Complex.ofRealLI.integral_comp_comm (fun p : P => w p ξ) (μ := ν)
    rw [hofReal, hξ]
  rw [integral_congr_ae hswap, integral_const_mul,
    SchwartzMap.integral_inner_fourier_fourier, ← complex_inner_toL2]

/-- **Paper Proposition 7 (Weak Reconstruction, Eq. 4.1)**: dividing by `C_ψ ≠ 0`
recovers the exact signal inner product from its Clifford–wavelet transform. -/
theorem cliffordWavelet_weak_reconstruction
    (M : P → V → (H →L[ℂ] H)) (w : P → V → ℝ) {C_ψ : ℝ} (hC : C_ψ ≠ 0)
    (hM : ∀ p ξ (u v : H), inner ℂ (M p ξ u) (M p ξ v) = (w p ξ : ℂ) * inner ℂ u v)
    (hAdm : ∀ᵐ ξ ∂(volume : Measure V), (∫ p, w p ξ ∂ν) = C_ψ)
    (f g : SchwartzMap V H) (T_f T_g : P → SchwartzMap V H)
    (hTf : ∀ p ξ, FourierTransform.fourier (T_f p) ξ = M p ξ (FourierTransform.fourier f ξ))
    (hTg : ∀ p ξ, FourierTransform.fourier (T_g p) ξ = M p ξ (FourierTransform.fourier g ξ))
    (hInt : Integrable (Function.uncurry fun p ξ =>
      inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_g p) ξ))
      (ν.prod (volume : Measure V))) :
    (1 / (C_ψ : ℂ)) *
        ∫ p, inner ℂ ((T_f p).toLp 2 volume) ((T_g p).toLp 2 volume) ∂ν =
      inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  rw [cliffordWavelet_isometry_inner M w C_ψ hM hAdm f g T_f T_g hTf hTg hInt,
    ← mul_assoc]
  have hCℂ : (C_ψ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC
  simp [hCℂ]

/-- **Paper Proposition 6 (Energy Isometry, Eq. 4.4)**:
`∫ p, ‖T_f p‖₂² ∂ν = C_ψ * ‖f‖₂²`. -/
theorem cliffordWavelet_isometry_normSq
    (M : P → V → (H →L[ℂ] H)) (w : P → V → ℝ) (C_ψ : ℝ)
    (hM : ∀ p ξ (u v : H), inner ℂ (M p ξ u) (M p ξ v) = (w p ξ : ℂ) * inner ℂ u v)
    (hAdm : ∀ᵐ ξ ∂(volume : Measure V), (∫ p, w p ξ ∂ν) = C_ψ)
    (f : SchwartzMap V H) (T_f : P → SchwartzMap V H)
    (hTf : ∀ p ξ, FourierTransform.fourier (T_f p) ξ = M p ξ (FourierTransform.fourier f ξ))
    (hInt : Integrable (Function.uncurry fun p ξ =>
      inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_f p) ξ))
      (ν.prod (volume : Measure V))) :
    ∫ p, ‖(T_f p).toLp 2 volume‖ ^ 2 ∂ν = C_ψ * ‖f.toLp 2 volume‖ ^ 2 := by
  let : InnerProductSpace ℝ (MeasureTheory.Lp H 2 (volume : Measure V)) :=
    InnerProductSpace.complexToReal
  have hiso := cliffordWavelet_isometry_inner M w C_ψ hM hAdm f f T_f T_f hTf hTf hInt
  have hre := congrArg Complex.re hiso
  have hlhs :
      (∫ p, inner ℂ ((T_f p).toLp 2 volume) ((T_f p).toLp 2 volume) ∂ν).re =
        ∫ p, ‖(T_f p).toLp 2 volume‖ ^ 2 ∂ν := by
    have hIntegrable :
        Integrable (fun p => inner ℂ ((T_f p).toLp 2 volume) ((T_f p).toLp 2 volume)) ν := by
      have hswap := hInt.integral_prod_left
      convert hswap using 1
      ext p
      rw [complex_inner_toL2, ← SchwartzMap.integral_inner_fourier_fourier]
      rfl
    change Complex.reCLM (∫ p, inner ℂ ((T_f p).toLp 2 volume) ((T_f p).toLp 2 volume) ∂ν) = _
    rw [← Complex.reCLM.integral_comp_comm hIntegrable]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro p
    change (inner ℂ ((T_f p).toLp 2 volume) ((T_f p).toLp 2 volume)).re = _
    change inner ℝ ((T_f p).toLp 2 volume) ((T_f p).toLp 2 volume) = _
    exact real_inner_self_eq_norm_sq ((T_f p).toLp 2 volume)
  have hrhs :
      ((C_ψ : ℂ) * inner ℂ (f.toLp 2 volume) (f.toLp 2 volume)).re =
        C_ψ * ‖f.toLp 2 volume‖ ^ 2 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    change inner ℝ (f.toLp 2 volume) (f.toLp 2 volume) = _
    exact real_inner_self_eq_norm_sq (f.toLp 2 volume)
  rw [← hlhs, ← hrhs]
  exact hre

/-- **Paper Proposition 3 (Injectivity / Frame Completeness)**: if `0 < C_ψ` and `T_f p = 0`
almost everywhere, then the analyzed Schwartz function `f` is identically zero. -/
theorem cliffordWavelet_injective
    (M : P → V → (H →L[ℂ] H)) (w : P → V → ℝ) {C_ψ : ℝ} (hC : 0 < C_ψ)
    (hM : ∀ p ξ (u v : H), inner ℂ (M p ξ u) (M p ξ v) = (w p ξ : ℂ) * inner ℂ u v)
    (hAdm : ∀ᵐ ξ ∂(volume : Measure V), (∫ p, w p ξ ∂ν) = C_ψ)
    (f : SchwartzMap V H) (T_f : P → SchwartzMap V H)
    (hTf : ∀ p ξ, FourierTransform.fourier (T_f p) ξ = M p ξ (FourierTransform.fourier f ξ))
    (hInt : Integrable (Function.uncurry fun p ξ =>
      inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_f p) ξ))
      (ν.prod (volume : Measure V)))
    (hzero : ∀ᵐ p ∂ν, T_f p = 0) :
    f = 0 := by
  have hnorm_zero : ∫ p, ‖(T_f p).toLp 2 volume‖ ^ 2 ∂ν = 0 := by
    have hae : (fun p : P => ‖(T_f p).toLp 2 volume‖ ^ 2) =ᵐ[ν] fun _ => (0 : ℝ) := by
      filter_upwards [hzero] with p hp
      have h0 : (0 : SchwartzMap V H).toLp 2 volume = 0 :=
        (SchwartzMap.toLpCLM ℂ H 2 volume).map_zero
      simp [hp, h0]
    rw [integral_congr_ae hae, integral_zero]
  have hiso := cliffordWavelet_isometry_normSq M w C_ψ hM hAdm f T_f hTf hInt
  rw [hnorm_zero] at hiso
  have hf_norm : ‖f.toLp 2 volume‖ = 0 := by
    have hsq : ‖f.toLp 2 volume‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hiso.symm).resolve_left hC.ne'
    exact sq_eq_zero_iff.mp hsq
  have hLp_zero : f.toLp 2 volume = 0 := norm_eq_zero.mp hf_norm
  have hae_f : (f : V → H) =ᵐ[volume] (0 : V → H) := by
    have h1 := f.coeFn_toLp 2 volume
    have h2 : (f.toLp 2 volume : V → H) =ᵐ[volume] (0 : V → H) := by
      rw [hLp_zero]
      exact MeasureTheory.Lp.coeFn_zero H 2 volume
    exact h1.symm.trans h2
  have hcont_eq : (f : V → H) = (0 : V → H) :=
    f.continuous.ae_eq_iff_eq volume continuous_const |>.mp hae_f
  ext x
  exact congrFun hcont_eq x

omit [CompleteSpace H] in
/-- **Paper Lemma 9 (Eq. 5.2–5.4)**: integrating the centered frequency-moment `L²` norm
squared of the Clifford–wavelet transform over `(P, ν)` equals `C_ψ` times the centered
frequency-moment `L²` norm squared of the analyzed signal `f`. -/
theorem cliffordWavelet_weighted_frequency_identity
    (M : P → V → (H →L[ℂ] H)) (w : P → V → ℝ) (C_ψ : ℝ)
    (hM : ∀ p ξ (u v : H), inner ℂ (M p ξ u) (M p ξ v) = (w p ξ : ℂ) * inner ℂ u v)
    (hAdm : ∀ᵐ ξ ∂(volume : Measure V), (∫ p, w p ξ ∂ν) = C_ψ)
    (f : SchwartzMap V H) (T_f : P → SchwartzMap V H)
    (hTf : ∀ p ξ, FourierTransform.fourier (T_f p) ξ = M p ξ (FourierTransform.fourier f ξ))
    (m : V) (b : ℝ)
    (hIntFreq : Integrable (Function.uncurry fun p ξ =>
      ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
        (FourierTransform.fourier (T_f p))) ξ‖ ^ 2)
      (ν.prod (volume : Measure V))) :
    ∫ p, ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
        (FourierTransform.fourier (T_f p))).toLp 2 volume‖ ^ 2 ∂ν =
      C_ψ * ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
        (FourierTransform.fourier f)).toLp 2 volume‖ ^ 2 := by
  have hg : (fun ξ : V => inner ℝ ξ m - b).HasTemperateGrowth := by fun_prop
  have hpoint :
      (fun p : P =>
        ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
          (FourierTransform.fourier (T_f p))).toLp 2 volume‖ ^ 2) =
        fun p : P => ∫ ξ : V,
          ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
            (FourierTransform.fourier (T_f p))) ξ‖ ^ 2 := by
    ext p
    exact norm_toLp_sq_eq_integral _
  rw [hpoint, MeasureTheory.integral_integral_swap hIntFreq]
  have hswap :
      (fun ξ : V => ∫ p : P,
        ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
          (FourierTransform.fourier (T_f p))) ξ‖ ^ 2 ∂ν) =ᵐ[volume]
        fun ξ : V => C_ψ *
          ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
            (FourierTransform.fourier f)) ξ‖ ^ 2 := by
    filter_upwards [hAdm] with ξ hξ
    have hfun :
        (fun p : P =>
          ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
            (FourierTransform.fourier (T_f p))) ξ‖ ^ 2) =
          fun p : P => w p ξ *
            ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
              (FourierTransform.fourier f)) ξ‖ ^ 2 := by
      ext p
      simp only [SchwartzMap.smulLeftCLM_apply_apply hg]
      rw [hTf p ξ]
      have hcomm :
          M p ξ ((inner ℝ ξ m - b) • FourierTransform.fourier f ξ) =
            (inner ℝ ξ m - b) • M p ξ (FourierTransform.fourier f ξ) :=
        ((M p ξ).restrictScalars ℝ).map_smul (inner ℝ ξ m - b) (FourierTransform.fourier f ξ)
      rw [← hcomm]
      exact norm_sq_of_scalar_adjoint_mul (M p ξ) (w p ξ) (hM p ξ) _
    rw [hfun, integral_mul_const, hξ]
  rw [integral_congr_ae hswap, integral_const_mul, norm_toLp_sq_eq_integral]

/-- **Paper Theorem 8 (Clifford–Wavelet Uncertainty Principle, General Directional Form)**:
combining directional Schwartz uncertainty (`heisenberg_schwartz_nd`), wavelet-domain
Cauchy–Schwarz (`integral_mul_sq_le`), energy isometry (`cliffordWavelet_isometry_normSq`),
and Lemma 9 (`cliffordWavelet_weighted_frequency_identity`). -/
theorem cliffordWavelet_uncertainty_principle
    (M : P → V → (H →L[ℂ] H)) (w : P → V → ℝ) {C_ψ : ℝ} (hC : 0 < C_ψ)
    (hM : ∀ p ξ (u v : H), inner ℂ (M p ξ u) (M p ξ v) = (w p ξ : ℂ) * inner ℂ u v)
    (hAdm : ∀ᵐ ξ ∂(volume : Measure V), (∫ p, w p ξ ∂ν) = C_ψ)
    (f : SchwartzMap V H) (T_f : P → SchwartzMap V H)
    (hTf : ∀ p ξ, FourierTransform.fourier (T_f p) ξ = M p ξ (FourierTransform.fourier f ξ))
    (m : V) (a b : ℝ)
    (hIntEnergy : Integrable (Function.uncurry fun p ξ =>
      inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_f p) ξ))
      (ν.prod (volume : Measure V)))
    (hIntFreq : Integrable (Function.uncurry fun p ξ =>
      ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
        (FourierTransform.fourier (T_f p))) ξ‖ ^ 2)
      (ν.prod (volume : Measure V)))
    (hIntPosSq : Integrable (fun p =>
      ‖(SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a)
        (T_f p)).toLp 2 volume‖ ^ 2) ν)
    (hIntProd : Integrable (fun p =>
      ‖(SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a)
        (T_f p)).toLp 2 volume‖ *
      ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
        (FourierTransform.fourier (T_f p))).toLp 2 volume‖) ν) :
    (Real.sqrt C_ψ / (4 * Real.pi)) * ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2 ≤
      Real.sqrt (∫ p, ‖(SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a)
          (T_f p)).toLp 2 volume‖ ^ 2 ∂ν) *
        ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
          (FourierTransform.fourier f)).toLp 2 volume‖ := by
  let u : P → ℝ := fun p =>
    ‖(SchwartzMap.smulLeftCLM H (fun x : V => inner ℝ x m - a) (T_f p)).toLp 2 volume‖
  let v : P → ℝ := fun p =>
    ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
      (FourierTransform.fourier (T_f p))).toLp 2 volume‖
  have hIntE : Integrable (fun p => ‖(T_f p).toLp 2 volume‖ ^ 2) ν := by
    let : InnerProductSpace ℝ (MeasureTheory.Lp H 2 (volume : Measure V)) :=
      InnerProductSpace.complexToReal
    have hswap := hIntEnergy.integral_prod_left
    have heq :
        (fun p => Complex.reCLM
          (∫ ξ, inner ℂ (FourierTransform.fourier (T_f p) ξ)
            (FourierTransform.fourier (T_f p) ξ))) =
          fun p => ‖(T_f p).toLp 2 volume‖ ^ 2 := by
      ext p
      rw [SchwartzMap.integral_inner_fourier_fourier, ← complex_inner_toL2]
      change (inner ℂ ((T_f p).toLp 2 volume) ((T_f p).toLp 2 volume)).re = _
      change inner ℝ ((T_f p).toLp 2 volume) ((T_f p).toLp 2 volume) = _
      exact real_inner_self_eq_norm_sq ((T_f p).toLp 2 volume)
    rw [← heq]
    exact Complex.reCLM.integrable_comp hswap
  have hv2 : Integrable (fun p => v p ^ 2) ν := by
    have hswap := hIntFreq.integral_prod_left
    have heq :
        (fun p => ∫ ξ, ‖(SchwartzMap.smulLeftCLM H (fun ξ' : V => inner ℝ ξ' m - b)
            (FourierTransform.fourier (T_f p))) ξ‖ ^ 2) =
          fun p => v p ^ 2 := by
      ext p
      exact (norm_toLp_sq_eq_integral _).symm
    rw [← heq]
    exact hswap
  have hpoint_le :
      ∫ p, ‖m‖ ^ 2 * ‖(T_f p).toLp 2 volume‖ ^ 2 ∂ν ≤
        ∫ p, (4 * Real.pi) * (u p * v p) ∂ν := by
    refine integral_mono (hIntE.const_mul _) (hIntProd.const_mul _) ?_
    intro p
    simpa only [mul_assoc] using heisenberg_schwartz_nd (T_f p) m a b
  rw [integral_const_mul, integral_const_mul,
    cliffordWavelet_isometry_normSq M w C_ψ hM hAdm f T_f hTf hIntEnergy] at hpoint_le
  have hcs := integral_mul_sq_le u v hIntPosSq hv2 hIntProd
  rw [cliffordWavelet_weighted_frequency_identity M w C_ψ hM hAdm f T_f hTf m b hIntFreq] at hcs
  have hcs_sqrt :
      ∫ p, u p * v p ∂ν ≤
        Real.sqrt ((∫ p, u p ^ 2 ∂ν) *
          (C_ψ * ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
            (FourierTransform.fourier f)).toLp 2 volume‖ ^ 2)) :=
    Real.le_sqrt_of_sq_le hcs
  have hIu_nonneg : 0 ≤ ∫ p, u p ^ 2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  have hsqrt_eq :
      Real.sqrt ((∫ p, u p ^ 2 ∂ν) *
          (C_ψ * ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
            (FourierTransform.fourier f)).toLp 2 volume‖ ^ 2)) =
        Real.sqrt C_ψ *
          (Real.sqrt (∫ p, u p ^ 2 ∂ν) *
            ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
              (FourierTransform.fourier f)).toLp 2 volume‖) := by
    rw [Real.sqrt_mul hIu_nonneg, Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _)]
    ring
  rw [hsqrt_eq] at hcs_sqrt
  have hcomb :
      ‖m‖ ^ 2 * (C_ψ * ‖f.toLp 2 volume‖ ^ 2) ≤
        (4 * Real.pi) * Real.sqrt C_ψ *
          (Real.sqrt (∫ p, u p ^ 2 ∂ν) *
            ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
              (FourierTransform.fourier f)).toLp 2 volume‖) := by
    nlinarith [Real.pi_pos]
  have hsqrtC_pos : 0 < Real.sqrt C_ψ := Real.sqrt_pos.mpr hC
  have h4pi_pos : 0 < (4 * Real.pi) * Real.sqrt C_ψ :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hsqrtC_pos
  have hC_sq : C_ψ = Real.sqrt C_ψ * Real.sqrt C_ψ := (Real.mul_self_sqrt hC.le).symm
  have hdiv :
      (4 * Real.pi) * Real.sqrt C_ψ *
          ((Real.sqrt C_ψ / (4 * Real.pi)) * ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2) ≤
        (4 * Real.pi) * Real.sqrt C_ψ *
          (Real.sqrt (∫ p, u p ^ 2 ∂ν) *
            ‖(SchwartzMap.smulLeftCLM H (fun ξ : V => inner ℝ ξ m - b)
              (FourierTransform.fourier f)).toLp 2 volume‖) := by
    have heqL :
        (4 * Real.pi) * Real.sqrt C_ψ *
            ((Real.sqrt C_ψ / (4 * Real.pi)) * ‖m‖ ^ 2 * ‖f.toLp 2 volume‖ ^ 2) =
          ‖m‖ ^ 2 * (C_ψ * ‖f.toLp 2 volume‖ ^ 2) := by
      conv_rhs => rw [hC_sq]
      field_simp [Real.pi_pos.ne']
    rw [heqL]
    exact hcomb
  exact le_of_mul_le_mul_left hdiv h4pi_pos

/-- **Paper Theorem 8 (Eq. 5.1, Angular-Frequency Coordinate Form)**: for `V = ℝⁿ` and
coordinate `k`, with angular frequency `ω_k = 2π ξ_k`,
`(√C_ψ / 2) ‖f‖₂² ≤ (∫ ‖b_k T[f]‖₂²)^{1/2} ‖ω_k f̂‖₂`. -/
theorem cliffordWavelet_uncertainty_principle_coord {n : ℕ}
    (M : P → EuclideanSpace ℝ (Fin n) → (H →L[ℂ] H))
    (w : P → EuclideanSpace ℝ (Fin n) → ℝ) {C_ψ : ℝ} (hC : 0 < C_ψ)
    (hM : ∀ p ξ (u v : H), inner ℂ (M p ξ u) (M p ξ v) = (w p ξ : ℂ) * inner ℂ u v)
    (hAdm : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (∫ p, w p ξ ∂ν) = C_ψ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) H)
    (T_f : P → SchwartzMap (EuclideanSpace ℝ (Fin n)) H)
    (hTf : ∀ p ξ, FourierTransform.fourier (T_f p) ξ = M p ξ (FourierTransform.fourier f ξ))
    (k : Fin n)
    (hIntEnergy : Integrable (Function.uncurry fun p ξ =>
      inner ℂ (FourierTransform.fourier (T_f p) ξ) (FourierTransform.fourier (T_f p) ξ))
      (ν.prod (volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hIntFreq : Integrable (Function.uncurry fun p ξ =>
      ‖(SchwartzMap.smulLeftCLM H (fun ξ' : EuclideanSpace ℝ (Fin n) => ξ' k)
        (FourierTransform.fourier (T_f p))) ξ‖ ^ 2)
      (ν.prod (volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hIntPosSq : Integrable (fun p =>
      ‖(SchwartzMap.smulLeftCLM H (fun x : EuclideanSpace ℝ (Fin n) => x k)
        (T_f p)).toLp 2 volume‖ ^ 2) ν)
    (hIntProd : Integrable (fun p =>
      ‖(SchwartzMap.smulLeftCLM H (fun x : EuclideanSpace ℝ (Fin n) => x k)
        (T_f p)).toLp 2 volume‖ *
      ‖(SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => ξ k)
        (FourierTransform.fourier (T_f p))).toLp 2 volume‖) ν) :
    (Real.sqrt C_ψ / 2) * ‖f.toLp 2 volume‖ ^ 2 ≤
      Real.sqrt (∫ p, ‖(SchwartzMap.smulLeftCLM H
          (fun x : EuclideanSpace ℝ (Fin n) => x k) (T_f p)).toLp 2 volume‖ ^ 2 ∂ν) *
        ‖(SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k)
          (FourierTransform.fourier f)).toLp 2 volume‖ := by
  let m : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single k 1
  have hm : ‖m‖ = 1 := by simp [m, PiLp.norm_single]
  have hpos :
      (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x m - 0) =
        fun x : EuclideanSpace ℝ (Fin n) => x k := by
    ext x
    simp [m, EuclideanSpace.inner_single_right]
  have hfreq_raw :
      (fun ξ : EuclideanSpace ℝ (Fin n) => inner ℝ ξ m - 0) =
        fun ξ : EuclideanSpace ℝ (Fin n) => ξ k := hpos
  have hmain := cliffordWavelet_uncertainty_principle M w hC hM hAdm f T_f hTf m 0 0
    hIntEnergy (by simpa only [hfreq_raw] using hIntFreq)
    (by simpa only [hpos] using hIntPosSq)
    (by simpa only [hpos, hfreq_raw] using hIntProd)
  rw [hm, one_pow, mul_one] at hmain
  have hfreq_2pi :
      SchwartzMap.smulLeftCLM H (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k)
          (FourierTransform.fourier f) =
        (2 * Real.pi) • SchwartzMap.smulLeftCLM H
          (fun ξ : EuclideanSpace ℝ (Fin n) => ξ k) (FourierTransform.fourier f) := by
    have hm_eq₁ :
        (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k) =
          fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * inner ℝ ξ m := by
      ext ξ
      simp [m, EuclideanSpace.inner_single_right]
    have hm_eq₂ :
        (fun ξ : EuclideanSpace ℝ (Fin n) => ξ k) =
          fun ξ : EuclideanSpace ℝ (Fin n) => inner ℝ ξ m := by
      ext ξ
      simp [m, EuclideanSpace.inner_single_right]
    have hg₁ : (fun ξ : EuclideanSpace ℝ (Fin n) => (2 * Real.pi) * ξ k).HasTemperateGrowth := by
      rw [hm_eq₁]
      fun_prop
    have hg₂ : (fun ξ : EuclideanSpace ℝ (Fin n) => ξ k).HasTemperateGrowth := by
      rw [hm_eq₂]
      fun_prop
    ext ξ
    simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg₁,
      SchwartzMap.smulLeftCLM_apply_apply hg₂, smul_smul]
  rw [hpos] at hmain
  have hsmulLp :
      ((2 * Real.pi) • SchwartzMap.smulLeftCLM H
          (fun ξ : EuclideanSpace ℝ (Fin n) => ξ k) (FourierTransform.fourier f)).toLp 2 volume =
        (2 * Real.pi) • (SchwartzMap.smulLeftCLM H
          (fun ξ : EuclideanSpace ℝ (Fin n) => ξ k) (FourierTransform.fourier f)).toLp 2 volume :=
    (SchwartzMap.toLpCLM ℝ H 2 volume).map_smul _ _
  rw [hfreq_2pi, hsmulLp, norm_smul,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  calc
    (Real.sqrt C_ψ / 2) * ‖f.toLp 2 volume‖ ^ 2
        = (2 * Real.pi) * ((Real.sqrt C_ψ / (4 * Real.pi)) * ‖f.toLp 2 volume‖ ^ 2) := by
          field_simp [Real.pi_pos.ne']
          ring
    _ ≤ (2 * Real.pi) *
          (Real.sqrt (∫ p, ‖(SchwartzMap.smulLeftCLM H
              (fun x : EuclideanSpace ℝ (Fin n) => x k) (T_f p)).toLp 2 volume‖ ^ 2 ∂ν) *
            ‖(SchwartzMap.smulLeftCLM H
              (fun ξ : EuclideanSpace ℝ (Fin n) => ξ k)
              (FourierTransform.fourier f)).toLp 2 volume‖) :=
          mul_le_mul_of_nonneg_left hmain (mul_pos (by norm_num) Real.pi_pos).le
    _ = _ := by ring

end WaveletTheorems

end CliffordWaveletAnalysisAndUncertainty

end InfoGeometry.Analysis.CliffordWaveletUncertainty
