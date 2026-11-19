/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentGradeTransport
import InfoGeometry.Core.TripotentStarGrading
import InfoGeometry.Modular.GKSLDissipationIdentity
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Nonzero tripotent grades as GKSL carré-du-champ sources

The existing integer adjoint grading identifies degree zero with the
centralizer. This bridge records what a nonzero homogeneous jump contributes
to the existing division-free GKSL product defect: its commutator with the
tripotent observable cannot vanish, and the defect is the corresponding
ordered star-square. The identity is not promoted to strict positivity,
which would require additional order and faithfulness hypotheses.
-/

set_option autoImplicit false

namespace InfoGeometry.Modular.TripotentGradeGKSLDissipation

open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Modular.GKSL
open InfoGeometry.Physics.Algebra
open scoped BigOperators ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A]

omit [StarRing A] in
/-- A nonzero homogeneous operator of nonzero tripotent-adjoint degree does
not commute with the grading operator. -/
theorem lie_ne_zero_of_mem_adGrade_ne_zero {S L : A} {k : ℤ}
    (hL : L ∈ adGrade S k) (hk : k ≠ 0) (hL0 : L ≠ 0) :
    ⁅L, S⁆ ≠ 0 := by
  intro hLie
  have had : S * L - L * S = (k : ℝ) • L := by
    change adLinear S L = (k : ℝ) • L
    exact mem_adGrade_iff.mp hL
  have hcomm : L * S = S * L := sub_eq_zero.mp hLie
  have hsmul : (k : ℝ) • L = 0 := by
    calc
      (k : ℝ) • L = S * L - L * S := had.symm
      _ = 0 := by rw [hcomm]; simp
  rcases smul_eq_zero.mp hsmul with hk0 | hLzero
  · exact (Int.cast_ne_zero.mpr hk) hk0
  · exact hL0 hLzero

/-- Homogeneity supplies a genuine nonzero commutator, while the GKSL defect
identifies its exact ordered Gram contribution. No commutativity or diagonal
representation is used. -/
theorem homogeneous_grade_gksl_carre_du_champ
    {S L : A} {k : ℤ} (hL : L ∈ adGrade S k)
    (hk : k ≠ 0) (hL0 : L ≠ 0) :
    ⁅L, S⁆ ≠ 0 ∧
      dissipatorTerm2 L (star S * S) -
          star (dissipatorTerm2 L S) * S -
          star S * dissipatorTerm2 L S =
        2 * (star ⁅L, S⁆ * ⁅L, S⁆) := by
  exact ⟨lie_ne_zero_of_mem_adGrade_ne_zero hL hk hL0,
    dissipatorTerm2_star_mul_defect L S S⟩

/-- On a concrete complex matrix algebra, a nonzero homogeneous jump of
nonzero grade has a strictly nonzero Hilbert--Schmidt carré-du-champ trace.
The strictness uses the finite matrix trace's faithful Gram form, rather than
an order claim in the ambient abstract star ring. -/
theorem matrix_homogeneous_grade_carre_trace_ne_zero
    {n : ℕ} {S L : Matrix (Fin n) (Fin n) ℂ} {k : ℤ}
    (hL : L ∈ adGrade S k) (hk : k ≠ 0) (hL0 : L ≠ 0) :
    Matrix.trace (star ⁅L, S⁆ * ⁅L, S⁆) ≠ 0 := by
  have hcomm : ⁅L, S⁆ ≠ 0 :=
    lie_ne_zero_of_mem_adGrade_ne_zero hL hk hL0
  intro htrace
  have hz : ⁅L, S⁆ = 0 := by
    apply (Matrix.trace_conjTranspose_mul_self_eq_zero_iff
      (A := ⁅L, S⁆)).mp
    simpa only [Matrix.star_eq_conjTranspose] using htrace
  exact hcomm hz

/-- The same matrix Gram trace is strictly positive in the canonical complex
matrix order. -/
theorem matrix_homogeneous_grade_carre_trace_pos
    {n : ℕ} {S L : Matrix (Fin n) (Fin n) ℂ} {k : ℤ}
    (hL : L ∈ adGrade S k) (hk : k ≠ 0) (hL0 : L ≠ 0) :
    0 < Matrix.trace (star ⁅L, S⁆ * ⁅L, S⁆) := by
  have hnonneg : 0 ≤ Matrix.trace (star ⁅L, S⁆ * ⁅L, S⁆) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.posSemidef_conjTranspose_mul_self ⁅L, S⁆).trace_nonneg
  exact lt_of_le_of_ne hnonneg
    (matrix_homogeneous_grade_carre_trace_ne_zero hL hk hL0).symm

/-- The trace of the full star-product defect is nonzero for a nonzero
nonzero-grade homogeneous matrix jump. This is the trace-level dissipation
certificate corresponding to the exact algebraic identity above. -/
theorem matrix_homogeneous_grade_gksl_defect_trace_ne_zero
    {n : ℕ} {S L : Matrix (Fin n) (Fin n) ℂ} {k : ℤ}
    (hL : L ∈ adGrade S k) (hk : k ≠ 0) (hL0 : L ≠ 0) :
    Matrix.trace (dissipatorTerm2 L (star S * S) -
      star (dissipatorTerm2 L S) * S -
      star S * dissipatorTerm2 L S) ≠ 0 := by
  have htrace := matrix_homogeneous_grade_carre_trace_ne_zero hL hk hL0
  rw [(homogeneous_grade_gksl_carre_du_champ hL hk hL0).2]
  intro hzero
  have hdouble : (2 : ℂ) *
      Matrix.trace (star ⁅L, S⁆ * ⁅L, S⁆) = 0 := by
    simpa only [two_mul, Matrix.trace_add] using hzero
  exact (mul_ne_zero (by norm_num) htrace) hdouble

/-- The trace of the homogeneous matrix carré-du-champ defect is strictly
positive, giving the noncommutative grade obstruction a quantitative scalar
readout in the Hilbert--Schmidt geometry. -/
theorem matrix_homogeneous_grade_gksl_defect_trace_pos
    {n : ℕ} {S L : Matrix (Fin n) (Fin n) ℂ} {k : ℤ}
    (hL : L ∈ adGrade S k) (hk : k ≠ 0) (hL0 : L ≠ 0) :
    0 < Matrix.trace (dissipatorTerm2 L (star S * S) -
      star (dissipatorTerm2 L S) * S -
      star S * dissipatorTerm2 L S) := by
  rw [(homogeneous_grade_gksl_carre_du_champ hL hk hL0).2]
  calc
    0 < (2 : ℂ) * Matrix.trace (star ⁅L, S⁆ * ⁅L, S⁆) :=
      mul_pos (by norm_num) (matrix_homogeneous_grade_carre_trace_pos hL hk hL0)
    _ = Matrix.trace (2 * (star ⁅L, S⁆ * ⁅L, S⁆)) := by
      simp only [two_mul, Matrix.trace_add]

/-- For a self-adjoint tripotent, the commutator Gram square generated by a
homogeneous jump lies in degree zero. Thus dissipation stores the grade
obstruction in the centralizer even though the jump itself has nonzero grade.
-/
theorem homogeneous_grade_gksl_square_mem_centralizer
    [StarModule ℝ A] {S L : A} {k : ℤ}
    (hSstar : star S = S) (hL : L ∈ adGrade S k) :
    Commute S (star ⁅L, S⁆ * ⁅L, S⁆) ∧
      dissipatorTerm2 L (star S * S) -
          star (dissipatorTerm2 L S) * S -
          star S * dissipatorTerm2 L S =
        2 * (star ⁅L, S⁆ * ⁅L, S⁆) := by
  have had : S * L - L * S = (k : ℝ) • L := by
    change adLinear S L = (k : ℝ) • L
    exact mem_adGrade_iff.mp hL
  have hbracket : ⁅L, S⁆ = -((k : ℝ) • L) := by
    rw [Ring.lie_def]
    calc
      L * S - S * L = -(S * L - L * S) := by noncomm_ring
      _ = -((k : ℝ) • L) := by rw [had]
  have hbracketGrade : ⁅L, S⁆ ∈ adGrade S k := by
    rw [hbracket]
    exact (adGrade S k).neg_mem ((adGrade S k).smul_mem (k : ℝ) hL)
  have hstarGrade : star ⁅L, S⁆ ∈ adGrade S (-k) :=
    star_mem_adGrade_neg_of_selfAdjoint hSstar hbracketGrade
  have hcentralizer : Commute S (star ⁅L, S⁆ * ⁅L, S⁆) := by
    apply commute_mul_of_opposite_adGrades (k := -k) hstarGrade
    simpa using hbracketGrade
  exact ⟨hcentralizer,
    dissipatorTerm2_star_mul_defect L S S⟩

/-- A homogeneous jump sends the grading observable itself to degree zero
under the Heisenberg dissipator. The jump has degree `k`, its adjoint has
degree `-k`, and every ordered term in the output therefore has total degree
zero. This identifies the centralizer-valued drift generated by a nonzero
grade without assuming that the jump commutes with the observable. -/
theorem homogeneous_dissipator_preserves_cartan_grade
    [StarModule ℝ A] {S L : A} {k : ℤ}
    (hSstar : star S = S) (hL : L ∈ adGrade S k) :
    dissipatorTerm2 L S ∈ adGrade S 0 := by
  have hS : S ∈ adGrade S 0 := by
    rw [mem_adGrade_iff]
    unfold adOp
    simp
  have hstarL : star L ∈ adGrade S (-k) :=
    star_mem_adGrade_neg_of_selfAdjoint hSstar hL
  have hLL : star L * L ∈ adGrade S 0 := by
    simpa only [neg_add_cancel] using mul_mem_adGrade_add hstarL hL
  have hLSL : star L * S * L ∈ adGrade S 0 := by
    have hfirst : star L * S ∈ adGrade S (-k) := by
      simpa only [add_zero] using mul_mem_adGrade_add hstarL hS
    simpa only [neg_add_cancel] using mul_mem_adGrade_add hfirst hL
  have hLLS : star L * L * S ∈ adGrade S 0 := by
    simpa only [zero_add] using mul_mem_adGrade_add hLL hS
  have hSLL : S * (star L * L) ∈ adGrade S 0 := by
    simpa only [zero_add] using mul_mem_adGrade_add hS hLL
  have hdouble : (2 : A) * (star L * S * L) ∈ adGrade S 0 := by
    have hs := (adGrade S 0).smul_mem (2 : ℝ) hLSL
    have hcast : algebraMap ℝ A (2 : ℝ) = (2 : A) := by
      exact map_ofNat (algebraMap ℝ A) 2
    simpa only [Algebra.smul_def, hcast] using hs
  have hsum : star L * L * S + S * (star L * L) ∈ adGrade S 0 :=
    (adGrade S 0).add_mem hLLS hSLL
  change (2 : A) * (star L * S * L) -
      (star L * L * S + S * (star L * L)) ∈ adGrade S 0
  exact (adGrade S 0).sub_mem hdouble hsum

/-- Finite families of homogeneous jumps, including families with different
grades, have a centralizer-valued Heisenberg drift on the grading observable.
The proof uses the existing direct-sum grading and the finite GKSL owner. -/
theorem finite_homogeneous_dissipator_preserves_cartan_grade
    {ι : Type*} [Fintype ι] [StarModule ℝ A]
    (S : A) (L : ι → A) (hSstar : star S = S)
    (hgrade : ∀ i, ∃ k : ℤ, L i ∈ adGrade S k) :
    gkslDissipator2 L S ∈ adGrade S 0 := by
  unfold gkslDissipator2
  apply (adGrade S 0).sum_mem
  intro i _
  obtain ⟨k, hL⟩ := hgrade i
  exact homogeneous_dissipator_preserves_cartan_grade hSstar hL

/-- For a finite family of homogeneous jumps, the complete multichannel
GKSL carré-du-champ is a finite sum of opposite-grade Gram products. Its
value therefore commutes with the self-adjoint grading operator. The grades
may vary across channels, and no diagonal or scalar representation is used.
-/
theorem finite_homogeneous_gksl_square_mem_centralizer
    {ι : Type*} [Fintype ι] [StarModule ℝ A]
    (S : A) (L : ι → A) (hSstar : star S = S)
    (hgrade : ∀ i, ∃ k : ℤ, L i ∈ adGrade S k) :
    Commute S (∑ i, star ⁅L i, S⁆ * ⁅L i, S⁆) ∧
      gkslDissipator2 L (star S * S) -
          star (gkslDissipator2 L S) * S -
          star S * gkslDissipator2 L S =
        ∑ i, 2 * (star ⁅L i, S⁆ * ⁅L i, S⁆) := by
  have hterm : ∀ i, Commute S (star ⁅L i, S⁆ * ⁅L i, S⁆) := by
    intro i
    obtain ⟨k, hL⟩ := hgrade i
    exact (homogeneous_grade_gksl_square_mem_centralizer hSstar hL).1
  refine ⟨?_, gkslDissipator2_star_mul_defect L S S⟩
  change S * (∑ i, star ⁅L i, S⁆ * ⁅L i, S⁆) =
    (∑ i, star ⁅L i, S⁆ * ⁅L i, S⁆) * S
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => (hterm i).eq)

/-- A nonzero homogeneous jump of nonzero grade cannot leave both a grading
observable and its quadratic statistic fixed under the Heisenberg
dissipator. Thus, if the first moment is stationary, motion must appear in
the second-moment layer. This full matrix-algebra statement is detected by
the faithful trace of the ordered carré-du-champ Gram term. -/
theorem homogeneous_jump_forces_second_moment_motion
    {n : ℕ} {S L : Matrix (Fin n) (Fin n) ℂ} {k : ℤ}
    (hL : L ∈ adGrade S k) (hk : k ≠ 0) (hL0 : L ≠ 0)
    (hfirst : dissipatorTerm2 L S = 0) :
    dissipatorTerm2 L (star S * S) ≠ 0 := by
  intro hsecond
  have hidentity := dissipatorTerm2_star_mul_defect L S S
  rw [hfirst, hsecond] at hidentity
  have hgram : 2 * (star ⁅L, S⁆ * ⁅L, S⁆) = 0 := by
    simpa using hidentity.symm
  have hdouble : (2 : ℂ) *
      Matrix.trace (star ⁅L, S⁆ * ⁅L, S⁆) = 0 := by
    calc
      (2 : ℂ) * Matrix.trace (star ⁅L, S⁆ * ⁅L, S⁆) =
          Matrix.trace (2 * (star ⁅L, S⁆ * ⁅L, S⁆)) := by
            simp only [two_mul, Matrix.trace_add]
      _ = 0 := by rw [hgram]; simp
  exact (mul_ne_zero (by norm_num)
    (matrix_homogeneous_grade_carre_trace_ne_zero hL hk hL0)) hdouble

/-- The same grade-generation conclusion holds for a finite family of active
homogeneous jumps, even when their grades differ: the first and quadratic
statistics cannot both be fixed by the summed Heisenberg dissipator. The
proof uses positivity term by term, so contributions from distinct channels
cannot cancel in the carré-du-champ trace. -/
theorem finite_homogeneous_jumps_forces_second_moment_motion
    {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {S : Matrix (Fin n) (Fin n) ℂ} (L : ι → Matrix (Fin n) (Fin n) ℂ)
    (hgrade : ∀ i, ∃ k : ℤ, k ≠ 0 ∧ L i ∈ adGrade S k ∧ L i ≠ 0)
    (hfirst : gkslDissipator2 L S = 0) :
    gkslDissipator2 L (star S * S) ≠ 0 := by
  intro hsecond
  have hidentity := gkslDissipator2_star_mul_defect L S S
  rw [hfirst, hsecond] at hidentity
  have hsum : (∑ i, 2 * (star ⁅L i, S⁆ * ⁅L i, S⁆)) = 0 := by
    simpa using hidentity.symm
  have htraceZero :
      Matrix.trace (∑ i, 2 * (star ⁅L i, S⁆ * ⁅L i, S⁆)) = 0 := by
    rw [hsum]
    simp
  rw [Matrix.trace_sum] at htraceZero
  have htermPos (i : ι) :
      0 < Matrix.trace (2 * (star ⁅L i, S⁆ * ⁅L i, S⁆)) := by
    obtain ⟨k, hk, hLi, hLi0⟩ := hgrade i
    calc
      0 < (2 : ℂ) * Matrix.trace (star ⁅L i, S⁆ * ⁅L i, S⁆) :=
        mul_pos (by norm_num)
          (matrix_homogeneous_grade_carre_trace_pos hLi hk hLi0)
      _ = Matrix.trace (2 * (star ⁅L i, S⁆ * ⁅L i, S⁆)) := by
        simp only [two_mul, Matrix.trace_add]
  have hsumPos :
      0 < ∑ i, Matrix.trace (2 * (star ⁅L i, S⁆ * ⁅L i, S⁆)) :=
    Finset.sum_pos (fun i _ => htermPos i) Finset.univ_nonempty
  exact (ne_of_gt hsumPos) htraceZero

end InfoGeometry.Modular.TripotentGradeGKSLDissipation
