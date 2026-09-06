import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic

/-!
# MITF invariant for continuant matrices

This module records a small determinant chain for generalized continued fractions:

* a continuant matrix built from `contsAux`;
* its step-matrix recurrence;
* the determinant formula with a product of partial numerators;
* the specialization to the simple case where all partial numerators are `1`.

The proofs use native mathlib lemmas only.
-/

noncomputable section

namespace MITFInvariant

open Matrix
open GenContFract

variable {K : Type*} [Field K]

/-- The 2×2 continuant matrix
`[[Aₙ₊₁, Aₙ], [Bₙ₊₁, Bₙ]]`. -/
def continuantMatrix (g : GenContFract K) (n : ℕ) : Matrix (Fin 2) (Fin 2) K :=
  !![(g.contsAux (n + 1)).a, (g.contsAux n).a;
     (g.contsAux (n + 1)).b, (g.contsAux n).b]

/-- The step matrix `[[b, 1], [a, 0]]`. -/
def stepMatrix (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![b, 1;
     a, 0]

/-- The continuant matrix satisfies the expected one-step recursion. -/
theorem continuantMatrix_recursion (g : GenContFract K) (n : ℕ)
    (s : GenContFract.Pair K) (hs : g.s.get? n = some s) :
    continuantMatrix g (n + 1) = continuantMatrix g n * stepMatrix s.a s.b := by
  ext i j; fin_cases i <;> fin_cases j
  · have hrec :
        g.contsAux (n + 2) =
          ⟨s.b * (g.contsAux (n + 1)).a + s.a * (g.contsAux n).a,
            s.b * (g.contsAux (n + 1)).b + s.a * (g.contsAux n).b⟩ :=
      GenContFract.contsAux_recurrence
        (g := g) (n := n)
        (gp := s) (ppred := g.contsAux n) (pred := g.contsAux (n + 1))
        hs rfl rfl
    simp [continuantMatrix, stepMatrix, Matrix.mul_apply, Fin.sum_univ_two, hrec]
    ring
  · simp [continuantMatrix, stepMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · have hrec :
        g.contsAux (n + 2) =
          ⟨s.b * (g.contsAux (n + 1)).a + s.a * (g.contsAux n).a,
            s.b * (g.contsAux (n + 1)).b + s.a * (g.contsAux n).b⟩ :=
      GenContFract.contsAux_recurrence
        (g := g) (n := n)
        (gp := s) (ppred := g.contsAux n) (pred := g.contsAux (n + 1))
        hs rfl rfl
    simp [continuantMatrix, stepMatrix, Matrix.mul_apply, Fin.sum_univ_two, hrec]
    ring
  · simp [continuantMatrix, stepMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The product of the partial numerators up to index `n`. -/
def partialNumeratorsProd (g : GenContFract K) : ℕ → K
  | 0 => 1
  | n + 1 =>
      match g.s.get? n with
      | none => partialNumeratorsProd g n
      | some s => partialNumeratorsProd g n * s.a

lemma partialNumeratorsProd_succ_some (g : GenContFract K) (n : ℕ)
    (s : GenContFract.Pair K) (hs : g.s.get? n = some s) :
    partialNumeratorsProd g (n + 1) = partialNumeratorsProd g n * s.a := by
  simp [partialNumeratorsProd, hs]

/-- The step matrix determinant. -/
lemma det_stepMatrix (a b : K) : (stepMatrix a b).det = -a := by
  simp [stepMatrix, Matrix.det_fin_two]

/-- Determinant formula for the continuant matrix. -/
theorem det_continuantMatrix (g : GenContFract K) (n : ℕ)
    (hn : ∀ m < n, (g.s.get? m).isSome) :
    (continuantMatrix g n).det = (-1 : K)^(n + 1) * partialNumeratorsProd g n := by
  induction n with
  | zero =>
      simp [continuantMatrix, partialNumeratorsProd, Matrix.det_fin_two]
  | succ n ih =>
      cases h_get : g.s.get? n with
      | none =>
          have h_some := hn n (Nat.lt_succ_self n)
          rw [h_get] at h_some
          contradiction
      | some s =>
          have h_step := continuantMatrix_recursion g n s h_get
          rw [h_step, Matrix.det_mul]
          have hn_prev : ∀ m < n, (g.s.get? m).isSome := by
            intro m hm
            exact hn m (Nat.lt_trans hm (Nat.lt_succ_self n))
          rw [ih hn_prev]
          rw [partialNumeratorsProd_succ_some g n s h_get]
          rw [det_stepMatrix]
          have hpow : (-1 : K) ^ (n + 1 + 1) = (-1 : K) ^ (n + 1) * (-1 : K) := by
            simpa [Nat.add_assoc] using (pow_succ (-1 : K) (n + 1))
          calc
            (-1 : K) ^ (n + 1) * partialNumeratorsProd g n * -s.a
                = ((-1 : K) ^ (n + 1) * (-1 : K)) * (partialNumeratorsProd g n * s.a) := by
                    ring
            _ = (-1 : K) ^ (n + 1 + 1) * (partialNumeratorsProd g n * s.a) := by
                  rw [← hpow]

/-- For simple continued fractions, every partial numerator is `1`. -/
lemma partialNumeratorsProd_one (g : GenContFract K)
    (h_simple : ∀ n, (g.s.get? n).map (·.a) = some (1 : K)) :
    ∀ n, partialNumeratorsProd g n = 1
  | 0 => rfl
  | n + 1 => by
      cases h_get : g.s.get? n with
      | none =>
          have hmap := h_simple n
          rw [h_get] at hmap
          simp at hmap
      | some s =>
          have hs : s.a = (1 : K) := by
            have hmap : some s.a = some (1 : K) := by
              simpa [h_get] using h_simple n
            exact Option.some.inj hmap
          rw [partialNumeratorsProd_succ_some g n s h_get]
          rw [partialNumeratorsProd_one g h_simple n, hs, mul_one]

/-- Closed form of the determinant in the simple case. -/
theorem det_continuantMatrix_simple (g : GenContFract K) (n : ℕ)
    (h_simple : ∀ m, (g.s.get? m).map (·.a) = some (1 : K))
    (hn : ∀ m < n, (g.s.get? m).isSome) :
    (continuantMatrix g n).det = (-1 : K)^(n + 1) := by
  rw [det_continuantMatrix g n hn, partialNumeratorsProd_one g h_simple, mul_one]

/-! ## GL(2, K) modular group lift -/

/-- The step matrix lifted to `GL(2, K)`. -/
def stepMatrixGL (b : K) : Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mk'' (stepMatrix 1 b) (by
    have h_det : (stepMatrix 1 b).det = -1 := by
      simp [stepMatrix, Matrix.det_fin_two]
    rw [h_det]
    exact isUnit_neg_one)

/-- The `GL(2, K)` step matrix has determinant `-1` as a unit. -/
lemma det_stepMatrixGL (b : K) :
    Matrix.GeneralLinearGroup.det (stepMatrixGL b) = (-1 : Kˣ) := by
  apply Units.ext
  simp [stepMatrixGL, stepMatrix, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_mk'', Matrix.det_fin_two]

/-- The continuant matrix lifted to `GL(2, K)`. -/
def continuantMatrixGL (g : GenContFract K)
    (h_simple : ∀ n, (g.s.get? n).map (·.a) = some (1 : K)) (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mk'' (continuantMatrix g n) (by
    have hn : ∀ m < n, (g.s.get? m).isSome := by
      intro m hm
      cases h : g.s.get? m with
      | none =>
          have h_map := h_simple m
          simp [h] at h_map
      | some s =>
          simp
    rw [det_continuantMatrix_simple g n h_simple hn]
    exact (isUnit_neg_one : IsUnit (-1 : K)).pow (n + 1))

/-- The lifted recursion in `GL(2, K)`. -/
theorem continuantMatrixGL_recursion (g : GenContFract K) (n : ℕ)
    (h_simple : ∀ m, (g.s.get? m).map (·.a) = some (1 : K))
    (s : GenContFract.Pair K) (hs : g.s.get? n = some s) :
    continuantMatrixGL g h_simple (n + 1) =
      continuantMatrixGL g h_simple n * stepMatrixGL s.b := by
  apply Units.ext
  have h_sa : s.a = (1 : K) := by
    have h_map := h_simple n
    rw [hs] at h_map
    simpa using h_map
  simpa [continuantMatrixGL, stepMatrixGL, Matrix.GeneralLinearGroup.val_mk'', h_sa]
    using continuantMatrix_recursion g n s hs

/-- The continuant matrix determinant in the lifted `GL(2, K)` form. -/
lemma det_continuantMatrixGL (g : GenContFract K)
    (h_simple : ∀ n, (g.s.get? n).map (·.a) = some (1 : K)) (n : ℕ) :
    Matrix.GeneralLinearGroup.det (continuantMatrixGL g h_simple n) =
      (-1 : Kˣ) ^ (n + 1) := by
  apply Units.ext
  have hn : ∀ m < n, (g.s.get? m).isSome := by
    intro m hm
    have h_map := h_simple m
    cases h_get : g.s.get? m with
    | none =>
        simp [h_get] at h_map
    | some s =>
        simp [h_get]
  simpa [continuantMatrixGL, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_mk'']
    using det_continuantMatrix_simple g n h_simple hn

/-- The lifted determinant flow is multiplicative along one recursion step. -/
theorem continuantMatrixGL_det_flow (g : GenContFract K) (n : ℕ)
    (h_simple : ∀ m, (g.s.get? m).map (·.a) = some (1 : K))
    (s : GenContFract.Pair K) (hs : g.s.get? n = some s) :
    Matrix.GeneralLinearGroup.det (continuantMatrixGL g h_simple (n + 1)) =
      Matrix.GeneralLinearGroup.det (continuantMatrixGL g h_simple n) *
      Matrix.GeneralLinearGroup.det (stepMatrixGL s.b) := by
  rw [continuantMatrixGL_recursion g n h_simple s hs]
  exact map_mul Matrix.GeneralLinearGroup.det _ _

end MITFInvariant
