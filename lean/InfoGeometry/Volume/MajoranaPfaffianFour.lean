import InfoGeometry.Volume.OrientedPfaffian
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Volume.MajoranaPfaffianFour

open InfoGeometry.Volume.OrientedPfaffian

/-!
# The four-mode Majorana Pfaffian

For a real skew matrix on four labelled modes, the three perfect matchings of
`K₄` are `(01)(23)`, `(02)(13)`, and `(03)(12)`.  This file records the
corresponding signed polynomial explicitly.  The statement is deliberately
kept at the finite algebraic level: it does not identify a Pfaffian with a
quantum expectation value without a separate Wick/Gaussian-state carrier.
-/

abbrev Mat4 := InfoGeometry.Algebra.FiniteSpin.Mat4R

def skewFourByFour (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) : Mat4 :=
  !![0, a₀₁, a₀₂, a₀₃;
     -a₀₁, 0, a₁₂, a₁₃;
     -a₀₂, -a₁₂, 0, a₂₃;
     -a₀₃, -a₁₃, -a₂₃, 0]

def matching01_23 (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) : ℝ :=
  a₀₁ * a₂₃

def matching02_13 (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) : ℝ :=
  -(a₀₂ * a₁₃)

def matching03_12 (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) : ℝ :=
  a₀₃ * a₁₂

def majoranaPfaffianFour
    (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) : ℝ :=
  matching01_23 a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ +
    matching02_13 a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ +
    matching03_12 a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃

def matching0123 : PerfectMatching 2 where
  partner := ![1, 0, 3, 2]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

def matching0213 : PerfectMatching 2 where
  partner := ![2, 3, 0, 1]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

def matching0312 : PerfectMatching 2 where
  partner := ![3, 2, 1, 0]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

private theorem matching_two_cases (M : PerfectMatching 2) :
    M = matching0123 ∨ M = matching0213 ∨ M = matching0312 := by
  have h0 := M.fixed_free 0
  generalize h : M.partner 0 = p
  fin_cases p
  · exact False.elim (h0 h)
  · have h10 : M.partner 1 = 0 := by
      simpa [h] using M.involutive 0
    have h2ne0 : M.partner 2 ≠ 0 := by
      intro h20
      exact (by decide : (2 : Fin 4) ≠ 1)
        (M.partner_injective (by simpa [h20, h10]))
    have h2ne1 : M.partner 2 ≠ 1 := by
      intro h21
      exact (by decide : (2 : Fin 4) ≠ 0)
        (M.partner_injective (by simpa [h21, h]))
    have h2ne2 := M.fixed_free 2
    generalize h2 : M.partner 2 = q
    fin_cases q
    · exact False.elim (h2ne0 h2)
    · exact False.elim (h2ne1 h2)
    · exact False.elim (h2ne2 h2)
    · have h32 : M.partner 3 = 2 := by
        simpa [h2] using M.involutive 2
      left
      cases M with
      | mk p hp hf =>
        congr
        funext i
        fin_cases i
        · simpa using h
        · simpa using h10
        · simpa using h2
        · simpa using h32
  · have h20 : M.partner 2 = 0 := by
      simpa [h] using M.involutive 0
    have h31ne0 : M.partner 3 ≠ 0 := by
      intro h31
      exact (by decide : (3 : Fin 4) ≠ 2)
        (M.partner_injective (by simpa [h31, h20]))
    have h31ne2 : M.partner 3 ≠ 2 := by
      intro h32
      exact (by decide : (3 : Fin 4) ≠ 0)
        (M.partner_injective (by simpa [h32, h]))
    have h31ne3 := M.fixed_free 3
    generalize h31eq : M.partner 3 = q
    fin_cases q
    · exact False.elim (h31ne0 h31eq)
    · right
      left
      have h13 : M.partner 1 = 3 := by
        simpa [h31eq] using M.involutive 3
      cases M with
      | mk p hp hf =>
        congr
        funext i
        fin_cases i
        · simpa using h
        · simpa using h13
        · simpa using h20
        · simpa using h31eq
    · exact False.elim (h31ne2 h31eq)
    · exact False.elim (h31ne3 h31eq)
  · have h30 : M.partner 3 = 0 := by
      simpa [h] using M.involutive 0
    have h21ne0 : M.partner 2 ≠ 0 := by
      intro h21
      exact (by decide : (2 : Fin 4) ≠ 3)
        (M.partner_injective (by simpa [h21, h30]))
    have h21ne2 := M.fixed_free 2
    have h21ne3 : M.partner 2 ≠ 3 := by
      intro h21
      exact (by decide : (2 : Fin 4) ≠ 0)
        (M.partner_injective (by simpa [h21, h]))
    generalize h21eq : M.partner 2 = q
    fin_cases q
    · exact False.elim (h21ne0 h21eq)
    · right
      right
      have h12 : M.partner 1 = 2 := by
        simpa [h21eq] using M.involutive 2
      cases M with
      | mk p hp hf =>
        congr
        funext i
        fin_cases i
        · simpa using h
        · simpa using h12
        · simpa using h21eq
        · simpa using h30
    · exact False.elim (h21ne2 h21eq)
    · exact False.elim (h21ne3 h21eq)

private theorem matching0123_leftEndpoints :
    matching0123.leftEndpoints = ({0, 2} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> simp [matching0123, PerfectMatching.leftEndpoints]

private theorem matching0213_leftEndpoints :
    matching0213.leftEndpoints = ({0, 1} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> simp [matching0213, PerfectMatching.leftEndpoints]

private theorem matching0312_leftEndpoints :
    matching0312.leftEndpoints = ({0, 1} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> simp [matching0312, PerfectMatching.leftEndpoints]

private theorem matching0123_crossingPairs :
    matching0123.crossingPairs = ∅ := by
  ext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [matching0123, PerfectMatching.crossingPairs]

private theorem matching0213_crossingPairs :
    matching0213.crossingPairs = ({(0, 1)} : Finset (Fin 4 × Fin 4)) := by
  unfold PerfectMatching.crossingPairs
  rw [matching0213_leftEndpoints]
  ext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [matching0213, PerfectMatching.crossingPairs,
      matching0213_leftEndpoints]

private theorem matching0312_crossingPairs :
    matching0312.crossingPairs = ∅ := by
  ext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [matching0312, PerfectMatching.crossingPairs]

theorem orientedPfaffian_two_eq_majoranaPfaffianFour
    (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) :
    orientedPfaffian 2 (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) =
      majoranaPfaffianFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ := by
  classical
  rw [orientedPfaffian]
  have huniv : (Finset.univ : Finset (PerfectMatching 2)) =
      {matching0123, matching0213, matching0312} := by
    ext M
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact matching_two_cases M
  rw [huniv]
  have hAB : matching0123 ≠ matching0213 := by
    intro h
    have h0 := congrArg (fun M : PerfectMatching 2 => M.partner 0) h
    simp [matching0123, matching0213] at h0
  have hAC : matching0123 ≠ matching0312 := by
    intro h
    have h0 := congrArg (fun M : PerfectMatching 2 => M.partner 0) h
    simp [matching0123, matching0312] at h0
  have hBC : matching0213 ≠ matching0312 := by
    intro h
    have h0 := congrArg (fun M : PerfectMatching 2 => M.partner 0) h
    simp [matching0213, matching0312] at h0
  rw [Finset.sum_insert (by simp [hAB, hAC]),
    Finset.sum_insert (by simp [hBC]), Finset.sum_singleton]
  unfold PerfectMatching.matchingWeight PerfectMatching.matchingSign
    PerfectMatching.crossingNumber
  rw [matching0123_leftEndpoints, matching0213_leftEndpoints,
    matching0312_leftEndpoints, matching0123_crossingPairs,
    matching0213_crossingPairs, matching0312_crossingPairs]
  simp [majoranaPfaffianFour, matching01_23, matching02_13, matching03_12,
    PerfectMatching.matchingSign, PerfectMatching.crossingNumber,
    PerfectMatching.crossingPairs, PerfectMatching.matchingWeight,
    matching0123, matching0213, matching0312, skewFourByFour]
  ring

theorem skewFourByFour_isSkew
    (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) :
    IsSkew (m := 2) (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [skewFourByFour, Matrix.transpose_apply]

theorem majoranaPfaffianFour_eq_three_matchings
    (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) :
    majoranaPfaffianFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ =
      a₀₁ * a₂₃ - a₀₂ * a₁₃ + a₀₃ * a₁₂ := by
  simp [majoranaPfaffianFour, matching01_23, matching02_13, matching03_12]
  ring

theorem majoranaPfaffianFour_matrix_formula
    (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ) :
    majoranaPfaffianFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ =
      (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) 0 1 *
        (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) 2 3 -
      (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) 0 2 *
        (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) 1 3 +
      (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) 0 3 *
        (skewFourByFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃) 1 2 := by
  simp [majoranaPfaffianFour, matching01_23, matching02_13, matching03_12,
    skewFourByFour]
  ring

theorem majoranaPfaffianFour_zero_of_zero_matching_data
    (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : ℝ)
    (h₀₁ : a₀₁ = 0) (h₀₂ : a₀₂ = 0) (h₀₃ : a₀₃ = 0) :
    majoranaPfaffianFour a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ = 0 := by
  rw [majoranaPfaffianFour_eq_three_matchings, h₀₁, h₀₂, h₀₃]
  ring

end InfoGeometry.Volume.MajoranaPfaffianFour
