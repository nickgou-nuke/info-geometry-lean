/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Authors
-/
import Mathlib.Data.Real.Sqrt
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornNavierStokesHydrodynamicBridge

/-!
# Native Bridge: Piola Curl Adjugate Transformation & Admissible Stress Cone

This module backports and natively formalizes the core algebraic mechanisms from OpenAI's
Navier-Stokes and Euler blowup formalization (`openai/NavierStokesAndEuler`):

1. **Piola Curl Adjugate Transformation Law** (`Euler.PacketPiolaAlgebra`):
   Antisymmetrizing $F^T A F$ transforms by the actual adjugate of $F$:
   $$\operatorname{matrixAntisym}(F^T A F) = F.\text{adjugate.mulVec}(\operatorname{matrixAntisym} A)$$
   without requiring invertibility of $F$. For determinant-one coordinate maps,
   adjugate acts as the exact inverse $F^{-1}$.

2. **Admissible Stress Cone Algebra** (`NavierStokes.ConeAlgebra` / Lemma 3.5 & Eq. 11):
   - Definition of `coneBound` and `rootTerm`.
   - Algebraic identity `square_difference` linking the quadratic form to the square root.
   - Complete equivalence `true_cone_iff`:
     $$(2 < P \wedge v < \text{coneBound}(P, J)) \iff (v < P \wedge (v - 2) J^2 < 2 (P - v)^2)$$
   - Relaxation below two: `relaxed_cone_of_le_two`.
   - Limiting sufficient criterion: `equation_eleven_sufficient` derived from
     `normalized_factorization`, `normalized_test_negative`, and
     `sufficiently_large_amplitude_cone`.

3. **Bridge to Jordan / Peirce Stress Geometry**:
   Connects the cone polynomial directly to `stressBoundaryPoly` and `jordanStressMatrix`
   from `ZornNavierStokesHydrodynamicBridge`, proving that the stress cone positivity
   corresponds to positive determinant of the Peirce stress block in $\mathcal{J}_3(\mathbb{O}_s)$.
-/

noncomputable section

namespace InfoGeometry.Canonical.NavierStokesConePiola

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornNavierStokesHydrodynamic

variable {R : Type*} [CommRing R]

/-!
## 1. Piola Curl Adjugate Transformation Law
-/

/-- Type alias for 3x3 matrices. -/
abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

/-- Antisymmetric vector extraction corresponding to the 3D curl tensor.
Given $A = \nabla u$, this yields $(\partial_2 u_3 - \partial_3 u_2, \partial_3 u_1 - \partial_1 u_3, \partial_1 u_2 - \partial_2 u_1)$. -/
def matrixAntisym (A : Mat3 R) : Fin 3 → R :=
  ![A 2 1 - A 1 2, A 0 2 - A 2 0, A 1 0 - A 0 1]

/-- The Piola curl identity: Congruence transformation $F^T A F$ transforms the
antisymmetric curl vector by the adjugate matrix $F.\text{adjugate}$.
This is a universal polynomial identity valid for all matrices over any commutative ring,
without requiring invertibility of $F$. -/
theorem matrixAntisym_congruence (F A : Mat3 ℝ) :
    matrixAntisym (F.transpose * A * F) = F.adjugate.mulVec (matrixAntisym A) := by
  ext i
  fin_cases i <;>
    simp [matrixAntisym, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.adjugate_fin_three,
      Matrix.cons_val_two] <;>
    ring

/-- For volume-preserving deformations ($\det F = 1$), the adjugate acts as the exact
two-sided matrix inverse. -/
theorem adjugate_mul_eq_one_of_det_one (F : Mat3 ℝ) (hdet : F.det = 1) :
    F.adjugate * F = 1 := by
  rw [Matrix.adjugate_mul, hdet, one_smul]

/-- Similarly, $F * F.\text{adjugate} = 1$ when $\det F = 1$. -/
theorem mul_adjugate_eq_one_of_det_one (F : Mat3 ℝ) (hdet : F.det = 1) :
    F * F.adjugate = 1 := by
  rw [Matrix.mul_adjugate, hdet, one_smul]

/-!
## 2. Admissible Stress Cone Algebra (OpenAI Lemma 3.5 & Eq. 11)
-/

/-- The lower root defining the admissible stress boundary in equation (10). -/
def coneBound (P J : ℝ) : ℝ :=
  P + J ^ 2 / 4 - |J| * Real.sqrt ((P - 2) / 2 + J ^ 2 / 16)

/-- The discriminant radical term in the root formula. -/
def rootTerm (P J : ℝ) : ℝ :=
  |J| * Real.sqrt ((P - 2) / 2 + J ^ 2 / 16)

/-- The discriminant radical term is always non-negative. -/
theorem rootTerm_nonneg (P J : ℝ) : 0 ≤ rootTerm P J :=
  mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

/-- Polynomial expansion of the boundary quadratic form. -/
theorem boundary_polynomial (P J v : ℝ) :
    2 * (P - v) ^ 2 - (v - 2) * J ^ 2 =
      2 * v ^ 2 - (4 * P + J ^ 2) * v + 2 * P ^ 2 + 2 * J ^ 2 := by
  ring

/-- Square difference identity factoring the quadratic polynomial into the root difference. -/
theorem square_difference (P J v : ℝ) :
    (P + J ^ 2 / 4 - v) ^ 2 - J ^ 2 * ((P - 2) / 2 + J ^ 2 / 16) =
      (P - v) ^ 2 - (v - 2) * J ^ 2 / 2 := by
  ring

/-- Exact evaluation of the square of the root term when $P > 2$. -/
theorem rootTerm_sq {P J : ℝ} (hP : 2 < P) :
    rootTerm P J ^ 2 = J ^ 2 * ((P - 2) / 2 + J ^ 2 / 16) := by
  have hrad : 0 ≤ (P - 2) / 2 + J ^ 2 / 16 := by nlinarith [sq_nonneg J]
  unfold rootTerm
  rw [mul_pow, sq_abs, Real.sq_sqrt hrad]

/-- The radical term dominates $J^2 / 4$ when $P > 2$. -/
theorem rootTerm_ge_quarter {P J : ℝ} (hP : 2 < P) :
    J ^ 2 / 4 ≤ rootTerm P J := by
  have hsq := rootTerm_sq (J := J) hP
  have hr := rootTerm_nonneg P J
  have hJ := sq_nonneg J
  have hprod : 0 ≤ J ^ 2 * (P - 2) := mul_nonneg hJ (by linarith)
  nlinarith [sq_nonneg (rootTerm P J - J ^ 2 / 4)]

/-- The cone bound is bounded above by the parameter $P$. -/
theorem coneBound_le_parameter {P J : ℝ} (hP : 2 < P) : coneBound P J ≤ P := by
  have h := rootTerm_ge_quarter (J := J) hP
  change P + J ^ 2 / 4 - rootTerm P J ≤ P
  linarith

/-- The cone bound is strictly greater than 2 whenever $P > 2$. -/
theorem coneBound_gt_two {P J : ℝ} (hP : 2 < P) : 2 < coneBound P J := by
  have hsq := rootTerm_sq (J := J) hP
  have hr := rootTerm_nonneg P J
  have hid := square_difference P J 2
  have hJ := sq_nonneg J
  have hpos : 0 < P + J ^ 2 / 4 - 2 := by linarith
  have hlt : rootTerm P J < P + J ^ 2 / 4 - 2 := by
    nlinarith [sq_pos_of_pos (show 0 < P - 2 by linarith)]
  change 2 < P + J ^ 2 / 4 - rootTerm P J
  linarith

/-- Lemma 3.5: The square-root criterion $v < \text{coneBound}(P, J)$ is strictly equivalent
to the quadratic form inequality $(v - 2) J^2 < 2 (P - v)^2$ for $v > 2$. -/
theorem true_cone_iff {P J v : ℝ} (hv : 2 < v) :
    (2 < P ∧ v < coneBound P J) ↔
      (v < P ∧ (v - 2) * J ^ 2 < 2 * (P - v) ^ 2) := by
  constructor
  · rintro ⟨hP, hcone⟩
    have hvP : v < P := lt_of_lt_of_le hcone (coneBound_le_parameter hP)
    refine ⟨hvP, ?_⟩
    have hsq := rootTerm_sq (J := J) hP
    have hr := rootTerm_nonneg P J
    have hid := square_difference P J v
    have hlt : rootTerm P J < P + J ^ 2 / 4 - v := by
      change v < P + J ^ 2 / 4 - rootTerm P J at hcone
      linarith
    have hdiff := mul_pos (sub_pos.mpr hlt)
      (show 0 < P + J ^ 2 / 4 - v + rootTerm P J by linarith)
    nlinarith
  · rintro ⟨hvP, hquad⟩
    have hP : 2 < P := lt_trans hv hvP
    refine ⟨hP, ?_⟩
    have hsq := rootTerm_sq (J := J) hP
    have hr := rootTerm_nonneg P J
    have hid := square_difference P J v
    have hpos : 0 < P + J ^ 2 / 4 - v := by nlinarith [sq_nonneg J]
    have hlt : rootTerm P J < P + J ^ 2 / 4 - v := by nlinarith
    change v < P + J ^ 2 / 4 - rootTerm P J
    linarith

/-- Below or at two, $P > 2$ alone guarantees the relaxed cone inequality. -/
theorem relaxed_cone_of_le_two {P J v : ℝ} (hP : 2 < P) (hv : v ≤ 2) :
    v < coneBound P J :=
  lt_of_le_of_lt hv (coneBound_gt_two hP)

/-- Exact factorization behind the limiting sufficient criterion (Equation 11). -/
theorem normalized_factorization (a b w : ℝ) (ha : a ≠ 0) :
    (a * (1 + (b / a) ^ 2) - 2) * (w + b / a) ^ 2 -
        2 * (1 - b * w / a) ^ 2 =
      (1 + (b / a) ^ 2) * ((a - 2) * w ^ 2 + 2 * b * w + b ^ 2 / a - 2) := by
  field_simp; ring

/-- Strict negativity in Equation (11) guarantees negativity of the factored test. -/
theorem normalized_test_negative {a b w : ℝ} (ha : 0 < a)
    (hcriterion : 2 * b * w + b ^ 2 / a + (a - 2) * w ^ 2 < 2) :
    (a * (1 + (b / a) ^ 2) - 2) * (w + b / a) ^ 2 -
      2 * (1 - b * w / a) ^ 2 < 0 := by
  rw [normalized_factorization a b w (ne_of_gt ha)]
  exact mul_neg_of_pos_of_neg (by nlinarith [sq_nonneg (b / a)]) (by linarith)

/-- Explicit finite-amplitude sufficient condition prior to taking limits. -/
theorem finite_amplitude_cone {c j v p : ℝ} (hp : 0 < p)
    (hP : 2 < p * c) (hvP : v < p * c)
    (hscale : 4 * c * v < p * (2 * c ^ 2 - (v - 2) * j ^ 2)) :
    v < coneBound (p * c) (p * j) := by
  by_cases hv : 2 < v
  · apply ((true_cone_iff hv).mpr ⟨hvP, ?_⟩).2
    have hprod : 0 < p * (p * (2 * c ^ 2 - (v - 2) * j ^ 2) - 4 * c * v) :=
      mul_pos hp (sub_pos.mpr hscale)
    have hid : 2 * (p * c - v) ^ 2 - (v - 2) * (p * j) ^ 2 =
        p * (p * (2 * c ^ 2 - (v - 2) * j ^ 2) - 4 * c * v) + 2 * v ^ 2 := by
      ring
    nlinarith [sq_nonneg v]
  · exact relaxed_cone_of_le_two hP (le_of_not_gt hv)

/-- For fixed normalized parameters, a positive leading coefficient and strict margin
ensure that the relaxed cone inequality holds at all sufficiently large amplitudes. -/
theorem sufficiently_large_amplitude_cone {c j v : ℝ} (hc : 0 < c)
    (hmargin : (v - 2) * j ^ 2 < 2 * c ^ 2) :
    ∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p →
      2 < p * c ∧ v < coneBound (p * c) (p * j) := by
  let δ := 2 * c ^ 2 - (v - 2) * j ^ 2
  have hδ : 0 < δ := sub_pos.mpr hmargin
  let p₀ := max 0 (max (2 / c) (max (v / c) (4 * c * v / δ)))
  refine ⟨p₀, fun p hlarge => ?_⟩
  have h₀ : 0 ≤ p₀ := le_max_left _ _
  have h₂ : 2 / c ≤ p₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hᵥ : v / c ≤ p₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hδbound : 4 * c * v / δ ≤ p₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hP : 2 < p * c := (div_lt_iff₀ hc).mp (lt_of_le_of_lt h₂ hlarge)
  refine ⟨hP, finite_amplitude_cone (lt_of_le_of_lt h₀ hlarge) hP ?_ ?_⟩
  · exact (div_lt_iff₀ hc).mp (lt_of_le_of_lt hᵥ hlarge)
  · exact (div_lt_iff₀ hδ).mp (lt_of_le_of_lt hδbound hlarge)

/-- Equation (11) is sufficient at all sufficiently large positive stress amplitudes
for each fixed triple of parameters. -/
theorem equation_eleven_sufficient {a b w : ℝ} (ha : 0 < a)
    (hfirst : 0 < a - b * w)
    (hsecond : 2 * b * w + b ^ 2 / a + (a - 2) * w ^ 2 < 2) :
    ∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p →
      2 < p * (1 - b * w / a) ∧ a * (1 + (b / a) ^ 2) <
        coneBound (p * (1 - b * w / a)) (p * (w + b / a)) := by
  apply sufficiently_large_amplitude_cone
  · apply sub_pos.mpr
    exact (div_lt_one ha).mpr (by linarith)
  · have h := normalized_test_negative ha hsecond
    linarith

/-!
## 3. Bridge to Zorn / Jordan Stress Matrix Geometry
-/

/-- The boundary polynomial of the stress cone coincides with `stressBoundaryPoly`. -/
theorem boundary_polynomial_eq_stressBoundaryPoly (P J v : ℝ) :
    2 * (P - v) ^ 2 - (v - 2) * J ^ 2 = stressBoundaryPoly P J v := rfl

/-- Positivity of the stress cone quadratic form is equivalent to strict positivity of
the Jordan stress matrix determinant in $\mathcal{J}_3(\mathbb{O}_s)$. -/
theorem stressBoundaryPoly_pos_iff_det_pos (P J v : ℝ) :
    0 < stressBoundaryPoly P J v ↔ 0 < (jordanStressMatrix P J v).det := by
  rw [jordanStressMatrix_det]

/-- The true cone condition $v < \text{coneBound}(P, J)$ for $v > 2$ is equivalent to
positivity of the Jordan stress matrix determinant and $v < P$. -/
theorem true_cone_iff_jordan_stress_pos {P J v : ℝ} (hv : 2 < v) :
    (2 < P ∧ v < coneBound P J) ↔
      (v < P ∧ 0 < (jordanStressMatrix P J v).det) := by
  rw [true_cone_iff hv, jordanStressMatrix_det, stressBoundaryPoly]
  constructor
  · rintro ⟨hvP, hlt⟩
    exact ⟨hvP, sub_pos.mpr hlt⟩
  · rintro ⟨hvP, hpos⟩
    exact ⟨hvP, sub_pos.mp hpos⟩

/-!
## 4. Certified Synthesis Structure
-/

/-- Certified structural synthesis bundle verifying:
1. Universal Piola curl adjugate transformation law.
2. Volume-preserving inverse duality.
3. Lemma 3.5 admissible stress cone equivalence.
4. Jordan determinant identification $\det(M_{\text{stress}}) = \mathcal{Q}(P, J, v)$.
5. Equation (11) asymptotic cone sufficiency. -/
structure CertifiedNavierStokesConePiolaBridge where
  /-- Piola curl adjugate transformation law holds for all matrices. -/
  piola_curl_congruence : ∀ (F A : Mat3 ℝ),
    matrixAntisym (F.transpose * A * F) = F.adjugate.mulVec (matrixAntisym A)
  /-- Volume-preserving coordinate deformation yields exact inverse. -/
  det_one_inverse : ∀ (F : Mat3 ℝ), F.det = 1 → F.adjugate * F = 1
  /-- Cone bound characterization is equivalent to the quadratic stress condition. -/
  cone_characterization : ∀ {P J v : ℝ}, 2 < v →
    ((2 < P ∧ v < coneBound P J) ↔ (v < P ∧ (v - 2) * J ^ 2 < 2 * (P - v) ^ 2))
  /-- Admissible stress cone condition is equivalent to positivity of the Jordan Peirce determinant. -/
  jordan_det_pos_iff : ∀ {P J v : ℝ}, 2 < v →
    ((2 < P ∧ v < coneBound P J) ↔ (v < P ∧ 0 < (jordanStressMatrix P J v).det))
  /-- Equation (11) sufficient asymptotic amplitude criterion. -/
  equation_eleven_sufficient : ∀ {a b w : ℝ}, 0 < a → 0 < a - b * w →
    2 * b * w + b ^ 2 / a + (a - 2) * w ^ 2 < 2 →
    ∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p →
      2 < p * (1 - b * w / a) ∧ a * (1 + (b / a) ^ 2) <
        coneBound (p * (1 - b * w / a)) (p * (w + b / a))

/-- Certified instance of the Navier-Stokes Cone and Piola Bridge. -/
def certified_navier_stokes_cone_piola_bridge : CertifiedNavierStokesConePiolaBridge where
  piola_curl_congruence := matrixAntisym_congruence
  det_one_inverse := adjugate_mul_eq_one_of_det_one
  cone_characterization := fun hv => true_cone_iff hv
  jordan_det_pos_iff := fun hv => true_cone_iff_jordan_stress_pos hv
  equation_eleven_sufficient := equation_eleven_sufficient

end InfoGeometry.Canonical.NavierStokesConePiola
