import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix
open scoped BigOperators

namespace InfoGeometry.Topology.EckmannDiscreteHodge

noncomputable section

def eckmannDot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i

def eckmannLaplacian1 {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ) :
    Matrix (Fin n1) (Fin n1) ℝ :=
  d1.transpose * d1 + d0 * d0.transpose

def eckmannHarmonic1 {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) : Prop :=
  d1.mulVec x = 0 ∧ d0.transpose.mulVec x = 0

def eckmannDegreeOneCochainComplex {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ) :
    Prop :=
  d1 * d0 = 0

def eckmannBetti1Zero {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ) :
    Prop :=
  eckmannDegreeOneCochainComplex d0 d1 ∧
    ∀ x : Fin n1 → ℝ, d1.mulVec x = 0 → ∃ y : Fin n0 → ℝ, d0.mulVec y = x

lemma eckmannDot_zero_right {n : ℕ} (x : Fin n → ℝ) :
    eckmannDot x 0 = 0 := by
  simp [eckmannDot]

lemma eckmannDot_comm {n : ℕ} (x y : Fin n → ℝ) :
    eckmannDot x y = eckmannDot y x := by
  unfold eckmannDot
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

lemma eckmannDot_zero_left {n : ℕ} (x : Fin n → ℝ) :
    eckmannDot 0 x = 0 := by
  rw [eckmannDot_comm, eckmannDot_zero_right]

lemma eckmannDot_add_right {n : ℕ} (x y z : Fin n → ℝ) :
    eckmannDot x (y + z) = eckmannDot x y + eckmannDot x z := by
  unfold eckmannDot
  simp [mul_add, Finset.sum_add_distrib]

lemma eckmannDot_mulVec_transpose {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    eckmannDot y (M.transpose.mulVec x) = eckmannDot (M.mulVec y) x := by
  simp only [eckmannDot, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  calc
    ∑ j, y j * ∑ i, M i j * x i
        = ∑ j, ∑ i, y j * (M i j * x i) := by
          simp [Finset.mul_sum]
    _ = ∑ i, ∑ j, y j * (M i j * x i) := by
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (M i j * y j) * x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = ∑ i, (∑ j, M i j * y j) * x i := by
          simp [Finset.sum_mul]

lemma eckmann_coboundary_orthogonal_coexact {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : eckmannDegreeOneCochainComplex d0 d1)
    (u : Fin n0 → ℝ) (v : Fin n2 → ℝ) :
    eckmannDot (d0.mulVec u) (d1.transpose.mulVec v) = 0 := by
  rw [eckmannDot_mulVec_transpose]
  have hmul : d1.mulVec (d0.mulVec u) = 0 := by
    have hmat : (d1 * d0).mulVec u = 0 := by
      rw [hComplex]
      simp
    simpa [Matrix.mulVec_mulVec] using hmat
  rw [hmul, eckmannDot_zero_left]

lemma eckmannDot_self_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ eckmannDot x x := by
  unfold eckmannDot
  refine Finset.sum_nonneg ?_
  intro i hi
  nlinarith [sq_nonneg (x i)]

lemma eckmannDot_self_eq_zero {n : ℕ} {x : Fin n → ℝ}
    (h : eckmannDot x x = 0) : x = 0 := by
  funext i
  have hnonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ x j * x j := by
    intro j hj
    nlinarith [sq_nonneg (x j)]
  have hterm : x i * x i = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 (by simpa [eckmannDot] using h) i
      (Finset.mem_univ i)
  have hsq : x i ^ (2 : ℕ) = 0 := by
    simpa [pow_two] using hterm
  exact (sq_eq_zero_iff).1 hsq

lemma eckmann_coboundary_coclosed_zero {n0 n1 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) {x : Fin n1 → ℝ}
    (hExact : ∃ y : Fin n0 → ℝ, d0.mulVec y = x)
    (hCoClosed : d0.transpose.mulVec x = 0) :
    x = 0 := by
  rcases hExact with ⟨y, hy⟩
  apply eckmannDot_self_eq_zero
  calc
    eckmannDot x x = eckmannDot (d0.mulVec y) x := by rw [hy]
    _ = eckmannDot y (d0.transpose.mulVec x) := by
      rw [eckmannDot_mulVec_transpose]
    _ = eckmannDot y 0 := by rw [hCoClosed]
    _ = 0 := eckmannDot_zero_right y

lemma eckmannLaplacian1_quadratic {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    eckmannDot x ((eckmannLaplacian1 d0 d1).mulVec x) =
      eckmannDot (d1.mulVec x) (d1.mulVec x) +
        eckmannDot (d0.transpose.mulVec x) (d0.transpose.mulVec x) := by
  unfold eckmannLaplacian1
  rw [Matrix.add_mulVec, eckmannDot_add_right]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hup :
      eckmannDot x (d1.transpose.mulVec (d1.mulVec x)) =
        eckmannDot (d1.mulVec x) (d1.mulVec x) := by
    rw [eckmannDot_mulVec_transpose]
  have hdown :
      eckmannDot x (d0.mulVec (d0.transpose.mulVec x)) =
        eckmannDot (d0.transpose.mulVec x) (d0.transpose.mulVec x) := by
    rw [eckmannDot_comm]
    rw [← eckmannDot_mulVec_transpose]
  rw [hup, hdown]

lemma eckmannLaplacian1_quadratic_nonneg {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    0 ≤ eckmannDot x ((eckmannLaplacian1 d0 d1).mulVec x) := by
  rw [eckmannLaplacian1_quadratic]
  exact add_nonneg (eckmannDot_self_nonneg _) (eckmannDot_self_nonneg _)

lemma eckmannLaplacian1_mulVec_eq_zero_iff_harmonic {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    (eckmannLaplacian1 d0 d1).mulVec x = 0 ↔ eckmannHarmonic1 d0 d1 x := by
  constructor
  · intro hL
    have hquad :
        eckmannDot (d1.mulVec x) (d1.mulVec x) +
          eckmannDot (d0.transpose.mulVec x) (d0.transpose.mulVec x) = 0 := by
      have h := eckmannLaplacian1_quadratic d0 d1 x
      rw [hL, eckmannDot_zero_right] at h
      exact h.symm
    have hnonneg1 : 0 ≤ eckmannDot (d1.mulVec x) (d1.mulVec x) :=
      eckmannDot_self_nonneg _
    have hnonneg0 : 0 ≤ eckmannDot (d0.transpose.mulVec x) (d0.transpose.mulVec x) :=
      eckmannDot_self_nonneg _
    have h1dot : eckmannDot (d1.mulVec x) (d1.mulVec x) = 0 := by
      nlinarith
    have h0dot : eckmannDot (d0.transpose.mulVec x) (d0.transpose.mulVec x) = 0 := by
      nlinarith
    exact ⟨eckmannDot_self_eq_zero h1dot, eckmannDot_self_eq_zero h0dot⟩
  · rintro ⟨hClosed, hCoClosed⟩
    unfold eckmannLaplacian1
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hClosed, hCoClosed]
    simp

theorem eckmann_discrete_hodge_betti1_zero
    {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hBetti1Zero : eckmannBetti1Zero d0 d1)
    (x : Fin n1 → ℝ)
    (hHarmonic : eckmannHarmonic1 d0 d1 x) :
    x = 0 := by
  exact eckmann_coboundary_coclosed_zero d0 (hBetti1Zero.2 x hHarmonic.1)
    hHarmonic.2

theorem eckmann_discrete_hodge_betti1_zero_of_closed_coclosed
    {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hBetti1Zero : eckmannBetti1Zero d0 d1)
    (x : Fin n1 → ℝ)
    (hClosed : d1.mulVec x = 0)
    (hCoClosed : d0.transpose.mulVec x = 0) :
    x = 0 :=
  eckmann_discrete_hodge_betti1_zero d0 d1 hBetti1Zero x ⟨hClosed, hCoClosed⟩

end

end InfoGeometry.Topology.EckmannDiscreteHodge
