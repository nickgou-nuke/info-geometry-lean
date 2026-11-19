/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Brioschi Quintic Identity from Klein Binary Forms

For the displayed binary forms `F₁₂`, `H₂₀`, and `T₃₀`, this file constructs
the Brioschi polynomial parameter and proves an explicit root identity.
The binary tetrahedral form `t₆` satisfies

`t₆⁵ - 10 F₁₂ t₆³ + 45 F₁₂² t₆ - T₃₀ = 0`.

Consequently `s = t₆ F₁₂² / T₃₀` is a root of
`X⁵ - 10 C X³ + 45 C² X - C²`, where `C = F₁₂⁵ / T₃₀²`. The Klein syzygy
identifies this parameter with `(1 - Z₆₀) / 1728` for
`Z₆₀ = -H₂₀³ / T₃₀²`. These are algebraic identities of binary-form values.
They do not establish the classical Galois resolvent of an arbitrary input
quintic. The explicit Klein orbit tuple is equivariant for the displayed
diagonal generator, and its orbit polynomial equals the displayed Brioschi
quintic when `T₃₀ ≠ 0` and the five indexed roots are distinct. Distinctness
holds on the complement of the zero set of an explicit nonzero slice
polynomial; degenerate edge-zero cases are handled separately. Thus the
generic Brioschi root identification is proved, rather than inferred merely
from cyclic equivariance.

For the source-ordered binary quintic representation, evaluation on the five
projective orbit nodes is surjective on the affine chart `(1,t)` when
`t ≠ 0`, by Lagrange interpolation. Its kernel quotient is therefore
isomorphic to the signed orbit-coordinate representation. Squaring removes
the central spinor sign and gives a degree-five orbit polynomial. For each
eligible Klein parameter, the principal complex square root followed by
explicit Lagrange interpolation defines a source quintic whose evaluation
resolvent is that Brioschi polynomial. This branch-selected construction is
not asserted to be `A₅`-equivariant, nor does it identify the Galois
resolvent of an arbitrary input quintic. The fifth-power central characters also rule out a
nonzero linear intertwiner from the unsquared quintic representation to the
ordinary five-root permutation representation.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent

open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
open Polynomial

/-- The degree-six binary form in the explicit Brioschi root identity. -/
def kleinTetrahedralForm6 (z₁ z₂ : ℂ) : ℂ :=
  z₁ ^ 6 + 2 * z₁ ^ 5 * z₂ - 5 * z₁ ^ 4 * z₂ ^ 2 -
    5 * z₁ ^ 2 * z₂ ^ 4 - 2 * z₁ * z₂ ^ 5 + z₂ ^ 6

/-- The degree-six tetrahedral form is homogeneous of degree six. -/
theorem kleinTetrahedralForm6_homogeneous (c z₁ z₂ : ℂ) :
    kleinTetrahedralForm6 (c * z₁) (c * z₂) =
      c ^ 6 * kleinTetrahedralForm6 z₁ z₂ := by
  simp only [kleinTetrahedralForm6, mul_pow]
  ring

/-- The algebraic identity relating the degree-six tetrahedral form to Klein's
icosahedral forms. -/
theorem kleinTetrahedralForm6_brioschi_identity (z₁ z₂ : ℂ) :
    kleinTetrahedralForm6 z₁ z₂ ^ 5 -
      10 * kleinIcosahedralVertexF z₁ z₂ * kleinTetrahedralForm6 z₁ z₂ ^ 3 +
      45 * kleinIcosahedralVertexF z₁ z₂ ^ 2 * kleinTetrahedralForm6 z₁ z₂ -
      kleinIcosahedralEdgeT z₁ z₂ = 0 := by
  simp [kleinTetrahedralForm6, kleinIcosahedralVertexF, kleinIcosahedralEdgeT]
  ring

/-- The binary-form value `C = F₁₂⁵ / T₃₀²`. -/
def brioschiParameter (z₁ z₂ : ℂ) : ℂ :=
  kleinIcosahedralVertexF z₁ z₂ ^ 5 / kleinIcosahedralEdgeT z₁ z₂ ^ 2

/-- The Brioschi parameter is invariant under nonzero common rescaling of the
binary coordinates wherever the edge denominator is nonzero. -/
theorem brioschiParameter_scale (c z₁ z₂ : ℂ) (hc : c ≠ 0)
    (hT : kleinIcosahedralEdgeT z₁ z₂ ≠ 0) :
    brioschiParameter (c * z₁) (c * z₂) = brioschiParameter z₁ z₂ := by
  unfold brioschiParameter
  rw [kleinIcosahedralVertexF_homog, kleinIcosahedralEdgeT_homog]
  field_simp [hc, hT]

/-- The Brioschi-shaped quintic `X⁵ - 10 C X³ + 45 C² X - C²`. -/
def brioschiResolvent (C : ℂ) : Polynomial ℂ :=
  X ^ 5 - Polynomial.C (10 * C) * X ^ 3 +
    Polynomial.C (45 * C ^ 2) * X - Polynomial.C (C ^ 2)

/-- The displayed Brioschi polynomial is monic of degree five. The lower
terms have degree at most three, so they cannot alter its leading term. -/
theorem brioschiResolvent_isMonicOfDegree (C : ℂ) :
    Polynomial.IsMonicOfDegree (brioschiResolvent C) 5 := by
  let q : Polynomial ℂ :=
    Polynomial.C (10 * C) * X ^ 3 -
      Polynomial.C (45 * C ^ 2) * X + Polynomial.C (C ^ 2)
  have hsub : (Polynomial.C (10 * C) * X ^ 3 -
      Polynomial.C (45 * C ^ 2) * X).natDegree ≤ 3 := by
    calc
      _ ≤ max 3 1 := Polynomial.natDegree_sub_le_of_le
        (Polynomial.natDegree_C_mul_X_pow_le (10 * C) 3)
        (by simpa only [pow_one] using
          Polynomial.natDegree_C_mul_X_pow_le (45 * C ^ 2) 1)
      _ ≤ 3 := by norm_num
  have hq : q.natDegree ≤ 3 := by
    dsimp [q]
    calc
      _ ≤ max 3 0 := Polynomial.natDegree_add_le_of_le hsub (by simp)
      _ ≤ 3 := by norm_num
  have hq_lt : q.natDegree < 5 := lt_of_le_of_lt hq (by norm_num)
  have hmain : Polynomial.IsMonicOfDegree (X ^ 5 : Polynomial ℂ) 5 :=
    Polynomial.isMonicOfDegree_X_pow ℂ 5
  convert hmain.sub hq_lt using 1
  dsimp [brioschiResolvent, q]
  ring

/-- The explicit rational function `s = t₆ F₁₂² / T₃₀` is a root of the
Brioschi-shaped polynomial by the binary-form syzygy. This pointwise root
identity alone does not prove a five-root orbit or a Galois resolvent. -/
theorem brioschiResolvent_has_klein_root {z₁ z₂ : ℂ}
    (hT : kleinIcosahedralEdgeT z₁ z₂ ≠ 0) :
    Polynomial.eval
        (kleinTetrahedralForm6 z₁ z₂ * kleinIcosahedralVertexF z₁ z₂ ^ 2 /
          kleinIcosahedralEdgeT z₁ z₂)
        (brioschiResolvent (brioschiParameter z₁ z₂)) = 0 := by
  simp only [brioschiResolvent, eval_sub, eval_add, eval_mul, eval_pow,
    eval_C, eval_X]
  have hT6 := kleinTetrahedralForm6_brioschi_identity z₁ z₂
  unfold brioschiParameter
  field_simp [hT]
  linear_combination (kleinIcosahedralVertexF z₁ z₂ ^ 10) * hT6

/-- The Brioschi parameter is the normalized icosahedral quotient parameter
`(1 - Z₆₀) / 1728`, with `Z₆₀ = -H₂₀³/T₃₀²`. -/
theorem brioschiParameter_eq_icosahedral_quotient {z₁ z₂ : ℂ}
    (hT : kleinIcosahedralEdgeT z₁ z₂ ≠ 0) :
    brioschiParameter z₁ z₂ =
      (1 - (-(kleinIcosahedralFaceH z₁ z₂ ^ 3 /
        kleinIcosahedralEdgeT z₁ z₂ ^ 2))) / 1728 := by
  have hsyzygy := klein_icosahedral_syzygy_1728 z₁ z₂
  unfold brioschiParameter
  field_simp [hT]
  rw [sub_neg_eq_add, hsyzygy]
  ring

/-- The Brioschi parameter is the reciprocal of `1728` plus Klein's
projective binary-form ratio `-H^3/F^5`. This is an algebraic identification
of two invariant coordinates on the binary-form chart; it does not identify
that chart with the analytic modular curve or assert equality with `j`. -/
theorem brioschiParameter_eq_inv_add_kleinBinaryFormRatio {z₁ z₂ : ℂ}
    (hF : kleinIcosahedralVertexF z₁ z₂ ≠ 0)
    (hT : kleinIcosahedralEdgeT z₁ z₂ ≠ 0) :
    brioschiParameter z₁ z₂ =
      (1728 + kleinBinaryFormRatio z₁ z₂)⁻¹ := by
  have hF5 : kleinIcosahedralVertexF z₁ z₂ ^ 5 ≠ 0 := pow_ne_zero 5 hF
  have hT2 : kleinIcosahedralEdgeT z₁ z₂ ^ 2 ≠ 0 := pow_ne_zero 2 hT
  have hsyzygy := klein_icosahedral_syzygy_1728 z₁ z₂
  have hratio_den :
      (1728 + kleinBinaryFormRatio z₁ z₂) *
          kleinIcosahedralVertexF z₁ z₂ ^ 5 =
        kleinIcosahedralEdgeT z₁ z₂ ^ 2 := by
    calc
      (1728 + kleinBinaryFormRatio z₁ z₂) *
          kleinIcosahedralVertexF z₁ z₂ ^ 5 =
          1728 * kleinIcosahedralVertexF z₁ z₂ ^ 5 -
            kleinIcosahedralFaceH z₁ z₂ ^ 3 := by
        unfold kleinBinaryFormRatio
        field_simp [hF5]
        ring
      _ = kleinIcosahedralEdgeT z₁ z₂ ^ 2 := by
        calc
          1728 * kleinIcosahedralVertexF z₁ z₂ ^ 5 -
              kleinIcosahedralFaceH z₁ z₂ ^ 3 =
              (kleinIcosahedralEdgeT z₁ z₂ ^ 2 +
                kleinIcosahedralFaceH z₁ z₂ ^ 3) -
                kleinIcosahedralFaceH z₁ z₂ ^ 3 := by rw [← hsyzygy]
          _ = kleinIcosahedralEdgeT z₁ z₂ ^ 2 := by ring
  have hden : 1728 + kleinBinaryFormRatio z₁ z₂ ≠ 0 := by
    intro hz
    have hzero : kleinIcosahedralEdgeT z₁ z₂ ^ 2 = 0 := by
      rw [← hratio_den, hz]
      ring
    rw [pow_two] at hzero
    exact hT (mul_self_eq_zero.mp hzero)
  unfold brioschiParameter
  field_simp [hT2, hden]
  rw [← hratio_den]
  ring

/-- One step of the diagonal order-ten binary action, expressed on the
projective coordinates used by the Klein invariant owner. -/
def kleinOrderFiveStep (z : ℂ × ℂ) : ℂ × ℂ :=
  (kleinBinaryStandardGenA 0 0 * z.1, kleinBinaryStandardGenA 1 1 * z.2)

/-- The point obtained after `n` applications of the diagonal generator. -/
def kleinOrderFiveIterate (n : ℕ) (z : ℂ × ℂ) : ℂ × ℂ :=
  Nat.rec z (fun _ p => kleinOrderFiveStep p) n

@[simp] theorem kleinOrderFiveIterate_zero (z : ℂ × ℂ) :
    kleinOrderFiveIterate 0 z = z := rfl

@[simp] theorem kleinOrderFiveIterate_succ (n : ℕ) (z : ℂ × ℂ) :
    kleinOrderFiveIterate (n + 1) z = kleinOrderFiveStep (kleinOrderFiveIterate n z) := rfl

private theorem kleinOrderFiveIterate_coordinates (n : ℕ) (z : ℂ × ℂ) :
    kleinOrderFiveIterate n z =
      ((kleinBinaryStandardGenA 0 0) ^ n * z.1,
       (kleinBinaryStandardGenA 1 1) ^ n * z.2) := by
  induction n with
  | zero => simp [kleinOrderFiveIterate]
  | succ n ih =>
      rw [kleinOrderFiveIterate_succ, ih]
      simp only [kleinOrderFiveStep, pow_succ]
      congr 1 <;> ring

/-- The diagonal-generator iterate commutes with common scalar rescaling of
the binary coordinates. -/
theorem kleinOrderFiveIterate_scale (n : ℕ) (c : ℂ) (z : ℂ × ℂ) :
    kleinOrderFiveIterate n (c * z.1, c * z.2) =
      (c * (kleinOrderFiveIterate n z).1,
       c * (kleinOrderFiveIterate n z).2) := by
  simp only [kleinOrderFiveIterate_coordinates]
  congr 1 <;> ring

private theorem kleinOrderFiveIterate_five_is_central (z : ℂ × ℂ) :
    kleinOrderFiveIterate 5 z = (-z.1, -z.2) := by
  rcases kleinBinaryStandardGenA_eigenvalues_fifth_power with ⟨hα, hβ⟩
  rw [kleinOrderFiveIterate_coordinates]
  simp [hα, hβ]

private theorem kleinTetrahedralForm6_neg (z₁ z₂ : ℂ) :
    kleinTetrahedralForm6 (-z₁) (-z₂) = kleinTetrahedralForm6 z₁ z₂ := by
  unfold kleinTetrahedralForm6
  ring

/-- The degree-12 and degree-30 displayed forms are fixed along iterates of
the diagonal generator, by the generator-invariance theorem in the imported
owner. This statement does not assert invariance under all of `A₅`. -/
theorem kleinForms_invariant_on_orderFiveIterate (n : ℕ) (z : ℂ × ℂ) :
    kleinIcosahedralVertexF (kleinOrderFiveIterate n z).1
        (kleinOrderFiveIterate n z).2 = kleinIcosahedralVertexF z.1 z.2 ∧
    kleinIcosahedralEdgeT (kleinOrderFiveIterate n z).1
        (kleinOrderFiveIterate n z).2 = kleinIcosahedralEdgeT z.1 z.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [kleinOrderFiveIterate_succ]
      rcases kleinBinaryForms_invariant_under_standardGenA
          (kleinOrderFiveIterate n z).1 (kleinOrderFiveIterate n z).2 with
        ⟨hF, _, hT⟩
      exact ⟨hF.trans ih.1, hT.trans ih.2⟩

/-- The first five iterate values of the degree-six form, normalized to the
Brioschi-shaped polynomial. Distinctness is not part of this definition. -/
def kleinBrioschiOrbitRootNat (z : ℂ × ℂ) (n : ℕ) : ℂ :=
  let p := kleinOrderFiveIterate n z
  kleinTetrahedralForm6 p.1 p.2 * kleinIcosahedralVertexF z.1 z.2 ^ 2 /
    kleinIcosahedralEdgeT z.1 z.2

/-- The normalized rational orbit root is invariant under nonzero common
rescaling of its binary coordinates, wherever the edge denominator is
nonzero. -/
theorem kleinBrioschiOrbitRootNat_scale (n : ℕ) (c : ℂ) (z : ℂ × ℂ)
    (hc : c ≠ 0) (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0) :
    kleinBrioschiOrbitRootNat (c * z.1, c * z.2) n =
      kleinBrioschiOrbitRootNat z n := by
  unfold kleinBrioschiOrbitRootNat
  rw [kleinOrderFiveIterate_scale]
  dsimp
  rw [kleinTetrahedralForm6_homogeneous,
    kleinIcosahedralVertexF_homog, kleinIcosahedralEdgeT_homog]
  field_simp [hc, hT]

def brioschiSliceF : Polynomial ℂ :=
  X * (1 + 11 * X ^ 5 - X ^ 10)

def brioschiSliceT : Polynomial ℂ :=
  1 + 522 * (X ^ 5 - X ^ 25) -
    10005 * (X ^ 10 + X ^ 20) + X ^ 30

def brioschiSliceT6 : Polynomial ℂ :=
  1 + 2 * X - 5 * X ^ 2 - 5 * X ^ 4 - 2 * X ^ 5 + X ^ 6

def brioschiSliceT6Shift : Polynomial ℂ :=
  Polynomial.C (kleinBinaryStandardGenA 0 0 ^ 6) +
    Polynomial.C (2 * kleinBinaryStandardGenA 0 0 ^ 5 *
      kleinBinaryStandardGenA 1 1) * X -
    Polynomial.C (5 * kleinBinaryStandardGenA 0 0 ^ 4 *
      kleinBinaryStandardGenA 1 1 ^ 2) * X ^ 2 -
    Polynomial.C (5 * kleinBinaryStandardGenA 0 0 ^ 2 *
      kleinBinaryStandardGenA 1 1 ^ 4) * X ^ 4 -
    Polynomial.C (2 * kleinBinaryStandardGenA 0 0 *
      kleinBinaryStandardGenA 1 1 ^ 5) * X ^ 5 +
    Polynomial.C (kleinBinaryStandardGenA 1 1 ^ 6) * X ^ 6

/-- The degree-six form evaluated along the `k`-th generator translate of the
slice `(1,t)`, kept as a polynomial in the slice parameter. -/
def brioschiSliceOrbitT6 (k : Fin 5) : Polynomial ℂ :=
  let α := kleinBinaryStandardGenA 0 0
  let β := kleinBinaryStandardGenA 1 1
  let αk := α ^ k.val
  let βk := β ^ k.val
  Polynomial.C (αk ^ 6) +
    Polynomial.C (2 * αk ^ 5 * βk) * X -
    Polynomial.C (5 * αk ^ 4 * βk ^ 2) * X ^ 2 -
    Polynomial.C (5 * αk ^ 2 * βk ^ 4) * X ^ 4 -
    Polynomial.C (2 * αk * βk ^ 5) * X ^ 5 +
    Polynomial.C (βk ^ 6) * X ^ 6

/-- Evaluation of the orbit numerator polynomial agrees with the owned
degree-six form at the corresponding iterate. -/
theorem brioschiSliceOrbitT6_eval (k : Fin 5) (t : ℂ) :
    (brioschiSliceOrbitT6 k).eval t =
      kleinTetrahedralForm6
        ((kleinBinaryStandardGenA 0 0) ^ k.val)
        ((kleinBinaryStandardGenA 1 1) ^ k.val * t) := by
  simp [brioschiSliceOrbitT6, kleinTetrahedralForm6]
  ring

private theorem kleinBeta_ne_neg_one :
    kleinBinaryStandardGenA 1 1 ≠ -1 := by
  intro hneg
  have hre := congrArg Complex.re hneg
  simp [kleinBinaryStandardGenA] at hre
  have hφ : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hφeq : Real.goldenRatio / 2 = -1 := by
    simpa [Real.goldenRatio] using hre
  linarith

/-- The negative of the second diagonal eigenvalue is a nontrivial fifth
root of unity. -/
private theorem kleinBeta_phase_fifth_power :
    (-kleinBinaryStandardGenA 1 1) ^ 5 = 1 := by
  rw [neg_pow, kleinBinaryStandardGenA_eigenvalues_fifth_power.2]
  norm_num

private theorem kleinBeta_phase_ne_one :
    -kleinBinaryStandardGenA 1 1 ≠ 1 := by
  intro h
  apply kleinBeta_ne_neg_one
  calc
    kleinBinaryStandardGenA 1 1 = -(-kleinBinaryStandardGenA 1 1) := by ring
    _ = -1 := by rw [h]

private theorem kleinBeta_phase_pow_ne_one {d : ℕ}
    (hd0 : 0 < d) (hd5 : d < 5) :
    (-kleinBinaryStandardGenA 1 1) ^ d ≠ 1 := by
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by
    have := hd0
    have := hd5
    omega
  rcases hd with rfl | rfl | rfl | rfl
  · simpa using kleinBeta_phase_ne_one
  · intro h2
    have h5eq : (-kleinBinaryStandardGenA 1 1) ^ 5 =
        -kleinBinaryStandardGenA 1 1 := by
      have h3eq : (-kleinBinaryStandardGenA 1 1) ^ 3 =
          -kleinBinaryStandardGenA 1 1 := by
        calc
          (-kleinBinaryStandardGenA 1 1) ^ 3 =
              (-kleinBinaryStandardGenA 1 1) ^ 2 *
                (-kleinBinaryStandardGenA 1 1) := by ring
          _ = -kleinBinaryStandardGenA 1 1 := by rw [h2]; simp
      calc
        (-kleinBinaryStandardGenA 1 1) ^ 5 =
            (-kleinBinaryStandardGenA 1 1) ^ 2 *
              (-kleinBinaryStandardGenA 1 1) ^ 3 := by ring
        _ = -kleinBinaryStandardGenA 1 1 := by rw [h2, h3eq]; ring
    have hphase : -kleinBinaryStandardGenA 1 1 = 1 :=
      h5eq.symm.trans kleinBeta_phase_fifth_power
    exact kleinBeta_phase_ne_one hphase
  · intro h3
    have h5eq : (-kleinBinaryStandardGenA 1 1) ^ 5 =
        (-kleinBinaryStandardGenA 1 1) ^ 2 := by
      calc
        (-kleinBinaryStandardGenA 1 1) ^ 5 =
            (-kleinBinaryStandardGenA 1 1) ^ 2 *
              (-kleinBinaryStandardGenA 1 1) ^ 3 := by ring
        _ = (-kleinBinaryStandardGenA 1 1) ^ 2 := by rw [h3]; ring
    have h2 : (-kleinBinaryStandardGenA 1 1) ^ 2 = 1 :=
      h5eq.symm.trans kleinBeta_phase_fifth_power
    have hphase : -kleinBinaryStandardGenA 1 1 = 1 := by
      calc
        -kleinBinaryStandardGenA 1 1 =
            (-kleinBinaryStandardGenA 1 1) ^ 2 *
              (-kleinBinaryStandardGenA 1 1) := by rw [h2]; simp
        _ = (-kleinBinaryStandardGenA 1 1) ^ 3 := by ring
        _ = 1 := h3
    exact kleinBeta_phase_ne_one hphase
  · intro h4
    have h5eq : (-kleinBinaryStandardGenA 1 1) ^ 5 =
        -kleinBinaryStandardGenA 1 1 := by
      calc
        (-kleinBinaryStandardGenA 1 1) ^ 5 =
            (-kleinBinaryStandardGenA 1 1) ^ 1 *
              (-kleinBinaryStandardGenA 1 1) ^ 4 := by ring
        _ = -kleinBinaryStandardGenA 1 1 := by rw [h4]; ring
    have hphase : -kleinBinaryStandardGenA 1 1 = 1 :=
      h5eq.symm.trans kleinBeta_phase_fifth_power
    exact kleinBeta_phase_ne_one hphase

private theorem coeff_C_pow_zero (x : ℂ) (n : ℕ) :
    (Polynomial.C x ^ n).coeff 0 = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.mul_coeff_zero, ih]
      simp [pow_succ]

/-- The linear coefficient of the `k`th slice polynomial records the
corresponding power of the nontrivial fifth root `-β`. -/
theorem brioschiSliceOrbitT6_coeff_one (k : Fin 5) :
    (brioschiSliceOrbitT6 k).coeff 1 =
      2 * (-kleinBinaryStandardGenA 1 1) ^ k.val := by
  have hα5 := kleinBinaryStandardGenA_eigenvalues_fifth_power.1
  have hcoeff : (brioschiSliceOrbitT6 k).coeff 1 =
      2 * (kleinBinaryStandardGenA 0 0 ^ 5) ^ k.val *
        kleinBinaryStandardGenA 1 1 ^ k.val := by
    simp only [brioschiSliceOrbitT6, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_C_succ,
      Polynomial.coeff_C_mul_X_pow]
    norm_num
    rw [← pow_mul, coeff_C_pow_zero, coeff_C_pow_zero,
      Nat.mul_comm k.val 5, pow_mul]
  rw [hcoeff]
  calc
    2 * (kleinBinaryStandardGenA 0 0 ^ 5) ^ k.val *
        kleinBinaryStandardGenA 1 1 ^ k.val =
      2 * (kleinBinaryStandardGenA 0 0 ^ 5 *
        kleinBinaryStandardGenA 1 1) ^ k.val := by rw [mul_pow]; ring
    _ = 2 * (-kleinBinaryStandardGenA 1 1) ^ k.val := by rw [hα5]; ring

private theorem kleinBeta_phase_pow_injective (i j : Fin 5)
    (h : (-kleinBinaryStandardGenA 1 1) ^ i.val =
      (-kleinBinaryStandardGenA 1 1) ^ j.val) : i = j := by
  by_contra hij
  have hγ0 : -kleinBinaryStandardGenA 1 1 ≠ 0 := by
    intro hz
    have := kleinBeta_phase_fifth_power
    rw [hz] at this
    norm_num at this
  rcases lt_or_gt_of_ne hij with hij | hji
  · let d := j.val - i.val
    have hd0 : 0 < d := by dsimp [d]; omega
    have hd5 : d < 5 := by dsimp [d]; omega
    have hsplit : j.val = i.val + d := by dsimp [d]; omega
    have hpow :
        (-kleinBinaryStandardGenA 1 1) ^ i.val =
          (-kleinBinaryStandardGenA 1 1) ^ i.val *
            (-kleinBinaryStandardGenA 1 1) ^ d := by
      rw [← pow_add, ← hsplit]
      exact h
    have hpow' : 1 = (-kleinBinaryStandardGenA 1 1) ^ d :=
      mul_left_cancel₀ (pow_ne_zero _ hγ0) (by simpa using hpow)
    exact (kleinBeta_phase_pow_ne_one hd0 hd5) hpow'.symm
  · let d := i.val - j.val
    have hd0 : 0 < d := by dsimp [d]; omega
    have hd5 : d < 5 := by dsimp [d]; omega
    have hsplit : i.val = j.val + d := by dsimp [d]; omega
    have hpow :
        (-kleinBinaryStandardGenA 1 1) ^ j.val =
          (-kleinBinaryStandardGenA 1 1) ^ j.val *
            (-kleinBinaryStandardGenA 1 1) ^ d := by
      rw [← pow_add, ← hsplit]
      exact h.symm
    have hpow' : 1 = (-kleinBinaryStandardGenA 1 1) ^ d :=
      mul_left_cancel₀ (pow_ne_zero _ hγ0) (by simpa using hpow)
    exact (kleinBeta_phase_pow_ne_one hd0 hd5) hpow'.symm

/-- The five degree-six orbit polynomials are pairwise distinct, detected by
their linear coefficients. -/
theorem brioschiSliceOrbitT6_injective :
    Function.Injective brioschiSliceOrbitT6 := by
  intro i j hij
  apply kleinBeta_phase_pow_injective i j
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 1) hij
  rw [brioschiSliceOrbitT6_coeff_one, brioschiSliceOrbitT6_coeff_one] at hcoeff
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hcoeff

private def brioschiSliceDistinctPairSet : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter fun ij => ij.1 ≠ ij.2

private def brioschiSliceDistinctnessPolynomial : Polynomial ℂ :=
  Finset.prod brioschiSliceDistinctPairSet
    (fun ij => brioschiSliceOrbitT6 ij.1 - brioschiSliceOrbitT6 ij.2) *
    brioschiSliceF * brioschiSliceT

/-- These slice polynomials are exactly the restrictions of the owned Klein
forms and the degree-six root form to `(1,t)` and its diagonal-generator
translate. -/
theorem brioschiSlice_eval (t : ℂ) :
    brioschiSliceF.eval t = kleinIcosahedralVertexF 1 t ∧
    brioschiSliceT.eval t = kleinIcosahedralEdgeT 1 t ∧
    brioschiSliceT6.eval t = kleinTetrahedralForm6 1 t ∧
    brioschiSliceT6Shift.eval t =
      kleinTetrahedralForm6 (kleinBinaryStandardGenA 0 0)
        (kleinBinaryStandardGenA 1 1 * t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [brioschiSliceF, kleinIcosahedralVertexF]
  · simp [brioschiSliceT, kleinIcosahedralEdgeT]
    ring
  · simp [brioschiSliceT6, kleinTetrahedralForm6]
  · simp [brioschiSliceT6Shift, kleinTetrahedralForm6,
      kleinBinaryStandardGenA]
    ring

/-- On the slice, each rational orbit root is the evaluation of its explicit
degree-six orbit polynomial times the common Klein normalization. -/
theorem kleinBrioschiOrbitRootNat_slice (k : Fin 5) (t : ℂ) :
    kleinBrioschiOrbitRootNat (1, t) k.val =
      (brioschiSliceOrbitT6 k).eval t * (brioschiSliceF.eval t) ^ 2 /
        (brioschiSliceT.eval t) := by
  rw [kleinBrioschiOrbitRootNat, kleinOrderFiveIterate_coordinates,
    brioschiSliceOrbitT6_eval k t]
  simp [brioschiSlice_eval]

private theorem brioschiSliceT6_difference_ne_zero :
    brioschiSliceT6 - brioschiSliceT6Shift ≠ 0 := by
  intro h
  have heval := congrArg (fun p : Polynomial ℂ => p.eval 0) h
  have hα5 : (kleinBinaryStandardGenA 0 0) ^ 5 = -1 :=
    kleinBinaryStandardGenA_eigenvalues_fifth_power.1
  have hα_ne : kleinBinaryStandardGenA 0 0 ≠ -1 := by
    intro hneg
    have hre := congrArg Complex.re hneg
    simp [kleinBinaryStandardGenA] at hre
    have hφ : 0 < Real.goldenRatio := Real.goldenRatio_pos
    have hφeq : Real.goldenRatio / 2 = -1 := by
      simpa [Real.goldenRatio] using hre
    linarith
  have hα6 : kleinBinaryStandardGenA 0 0 ^ 6 ≠ 1 := by
    intro h6
    have hmul : kleinBinaryStandardGenA 0 0 * (-1) = 1 := by
      calc
        kleinBinaryStandardGenA 0 0 * (-1) =
            kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 0 0 ^ 5 := by rw [hα5]
        _ = kleinBinaryStandardGenA 0 0 ^ 6 := by ring
        _ = 1 := h6
    have hneg : kleinBinaryStandardGenA 0 0 = -1 := by
      calc
        kleinBinaryStandardGenA 0 0 = -(kleinBinaryStandardGenA 0 0 * (-1)) := by ring
        _ = -1 := by rw [hmul]
    exact hα_ne hneg
  simp [brioschiSliceT6, brioschiSliceT6Shift] at heval
  exact hα6 (sub_eq_zero.mp heval).symm

private theorem brioschiSliceF_ne_zero : brioschiSliceF ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
  norm_num [brioschiSliceF] at hcoeff

private theorem brioschiSliceT_ne_zero : brioschiSliceT ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
  norm_num [brioschiSliceT] at hcoeff

/-- The common slice polynomial whose nonvanishing ensures a nonzero
denominator and pairwise distinct normalized roots is nonzero. -/
theorem brioschiSliceDistinctnessPolynomial_ne_zero :
    brioschiSliceDistinctnessPolynomial ≠ 0 := by
  have hpairs :
      Finset.prod brioschiSliceDistinctPairSet
        (fun ij => brioschiSliceOrbitT6 ij.1 - brioschiSliceOrbitT6 ij.2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ij hij
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_filter.mp hij).2 (brioschiSliceOrbitT6_injective heq)
  unfold brioschiSliceDistinctnessPolynomial
  exact mul_ne_zero (mul_ne_zero hpairs brioschiSliceF_ne_zero)
    brioschiSliceT_ne_zero

/-- Along the slice `(1,t)`, the numerator separating the first two orbit
roots is a nonzero polynomial. -/
theorem kleinBrioschiFirstRootDifference_numerator_ne_zero :
    brioschiSliceF ^ 2 * (brioschiSliceT6 - brioschiSliceT6Shift) *
      brioschiSliceT ≠ 0 := by
  have hF2 : brioschiSliceF ^ 2 ≠ 0 := pow_ne_zero 2 brioschiSliceF_ne_zero
  have hleft : brioschiSliceF ^ 2 *
      (brioschiSliceT6 - brioschiSliceT6Shift) ≠ 0 :=
    mul_ne_zero hF2 brioschiSliceT6_difference_ne_zero
  exact mul_ne_zero hleft brioschiSliceT_ne_zero

/-- There are slice parameters where the vertex factor, edge factor, and
first-root separating numerator are all nonzero. In particular, the
root-separating condition is not vacuous. -/
theorem exists_brioschiSlice_parameter_separating_first_roots :
    ∃ t : ℂ, brioschiSliceF.eval t ≠ 0 ∧ brioschiSliceT.eval t ≠ 0 ∧
      (brioschiSliceT6.eval t - brioschiSliceT6Shift.eval t) ≠ 0 := by
  let p := brioschiSliceF ^ 2 * (brioschiSliceT6 - brioschiSliceT6Shift) *
    brioschiSliceT
  have hp : p ≠ 0 := by
    simpa [p] using kleinBrioschiFirstRootDifference_numerator_ne_zero
  have hcard : p.natDegree < Cardinal.mk ℂ :=
    lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.aleph0_le_mk ℂ)
  obtain ⟨t, ht⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card p hp hcard
  have hpeval : brioschiSliceF.eval t ^ 2 *
        (brioschiSliceT6.eval t - brioschiSliceT6Shift.eval t) *
          brioschiSliceT.eval t ≠ 0 := by
      simpa [p, Polynomial.eval_mul, Polynomial.eval_pow] using ht
  refine ⟨t, ?_, ?_, ?_⟩
  · intro hF
    apply hpeval
    simp [hF]
  · intro hT
    apply hpeval
    simp [hT]
  · exact fun hD => hpeval (by simp [hD])

def kleinBrioschiOrbitRoot (z : ℂ × ℂ) (k : Fin 5) : ℂ :=
  kleinBrioschiOrbitRootNat z k.val

/-- At `(1, 0)`, all five listed roots vanish. This is a degeneration of the
root construction, so injectivity cannot hold on the whole coordinate space. -/
theorem kleinBrioschiOrbitRoot_degenerate (n : ℕ) :
    kleinBrioschiOrbitRootNat (1, 0) n = 0 := by
  simp [kleinBrioschiOrbitRootNat, kleinIcosahedralVertexF,
    kleinIcosahedralEdgeT]


private theorem kleinOrderFiveIterate_shift (z : ℂ × ℂ) (n : ℕ) :
    kleinOrderFiveIterate n (kleinOrderFiveStep z) =
      kleinOrderFiveIterate (n + 1) z := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        kleinOrderFiveIterate (n + 1) (kleinOrderFiveStep z) =
            kleinOrderFiveStep (kleinOrderFiveIterate n (kleinOrderFiveStep z)) := rfl
        _ = kleinOrderFiveStep (kleinOrderFiveIterate (n + 1) z) := by rw [ih]
        _ = kleinOrderFiveIterate (n + 1 + 1) z := rfl

private theorem kleinBrioschiOrbitRootNat_step (z : ℂ × ℂ) (n : ℕ) :
    kleinBrioschiOrbitRootNat (kleinOrderFiveStep z) n =
      kleinBrioschiOrbitRootNat z (n + 1) := by
  rcases kleinBinaryForms_invariant_under_standardGenA z.1 z.2 with
    ⟨hF, _, hTstep⟩
  unfold kleinBrioschiOrbitRootNat
  rw [kleinOrderFiveIterate_shift]
  simp only [kleinOrderFiveStep]
  rw [hF, hTstep]

private theorem kleinBrioschiOrbitRootNat_period (z : ℂ × ℂ) :
    kleinBrioschiOrbitRootNat z 5 = kleinBrioschiOrbitRootNat z 0 := by
  rw [kleinBrioschiOrbitRootNat, kleinBrioschiOrbitRootNat,
    kleinOrderFiveIterate_five_is_central, kleinOrderFiveIterate_zero,
    kleinTetrahedralForm6_neg]

def kleinResolventCycleSucc (k : Fin 5) : Fin 5 :=
  ⟨(k.val + 1) % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The binary generator acts on the five indexed root expressions by the
source-order cyclic shift. This is the representation-to-resolvent bridge. -/
theorem kleinBrioschiOrbitRoot_equivariant (z : ℂ × ℂ) (k : Fin 5) :
    kleinBrioschiOrbitRoot (kleinOrderFiveStep z) k =
      kleinBrioschiOrbitRoot z (kleinResolventCycleSucc k) := by
  fin_cases k
  · simpa [kleinBrioschiOrbitRoot, kleinResolventCycleSucc] using
      kleinBrioschiOrbitRootNat_step z 0
  · simpa [kleinBrioschiOrbitRoot, kleinResolventCycleSucc] using
      kleinBrioschiOrbitRootNat_step z 1
  · simpa [kleinBrioschiOrbitRoot, kleinResolventCycleSucc] using
      kleinBrioschiOrbitRootNat_step z 2
  · simpa [kleinBrioschiOrbitRoot, kleinResolventCycleSucc] using
      kleinBrioschiOrbitRootNat_step z 3
  · rw [kleinBrioschiOrbitRoot, kleinResolventCycleSucc]
    change kleinBrioschiOrbitRootNat (kleinOrderFiveStep z) 4 =
      kleinBrioschiOrbitRootNat z 0
    rw [kleinBrioschiOrbitRootNat_step z 4,
      kleinBrioschiOrbitRootNat_period]

/-- On the slice `(1,t)`, the difference of the first two actual orbit roots
is the slice numerator divided by the invariant edge form. -/
theorem kleinBrioschiOrbitRootNat_first_difference (t : ℂ) :
    kleinBrioschiOrbitRootNat (1, t) 0 -
      kleinBrioschiOrbitRootNat (1, t) 1 =
      (brioschiSliceT6.eval t - brioschiSliceT6Shift.eval t) *
        brioschiSliceF.eval t ^ 2 / brioschiSliceT.eval t := by
  have hs := brioschiSlice_eval t
  simp only [kleinBrioschiOrbitRootNat, kleinOrderFiveIterate_zero,
    kleinOrderFiveIterate_succ, kleinOrderFiveIterate_zero,
    kleinOrderFiveStep] at *
  rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
  ring_nf

/-- The first two entries of the nonlinear root tuple are distinct at some
point where the edge form is nonzero. This proves the cyclic orbit is not
identically collapsed along the slice. -/
theorem exists_kleinBrioschiOrbitRootNat_first_difference_ne :
    ∃ t : ℂ, kleinIcosahedralEdgeT 1 t ≠ 0 ∧
      kleinBrioschiOrbitRootNat (1, t) 0 ≠
        kleinBrioschiOrbitRootNat (1, t) 1 := by
  obtain ⟨t, hF, hT, hD⟩ := exists_brioschiSlice_parameter_separating_first_roots
  have hs := brioschiSlice_eval t
  have hT' : kleinIcosahedralEdgeT 1 t ≠ 0 := by
    intro ht
    apply hT
    rw [hs.2.1, ht]
  have hdiff := kleinBrioschiOrbitRootNat_first_difference t
  refine ⟨t, hT', ?_⟩
  intro heq
  have hval : (brioschiSliceT6.eval t - brioschiSliceT6Shift.eval t) *
      brioschiSliceF.eval t ^ 2 / brioschiSliceT.eval t = 0 := by
    rw [← hdiff, sub_eq_zero.mpr heq]
  have hnum : (brioschiSliceT6.eval t - brioschiSliceT6Shift.eval t) *
      brioschiSliceF.eval t ^ 2 = 0 := (div_eq_zero_iff).mp hval |>.resolve_right hT
  rcases mul_eq_zero.mp hnum with hD' | hF'
  · exact hD hD'
  · exact (pow_ne_zero 2 hF) hF'

/-- The ordered five-root tuple attached to a binary coordinate pair. -/
def kleinBrioschiRootTuple (z : ℂ × ℂ) : Fin 5 → ℂ :=
  kleinBrioschiOrbitRoot z

/-- The full five-root tuple is projectively invariant wherever the common
edge denominator is nonzero. -/
theorem kleinBrioschiRootTuple_scale (c : ℂ) (z : ℂ × ℂ)
    (hc : c ≠ 0) (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0) :
    kleinBrioschiRootTuple (c * z.1, c * z.2) =
      kleinBrioschiRootTuple z := by
  funext k
  simpa [kleinBrioschiRootTuple, kleinBrioschiOrbitRoot] using
    kleinBrioschiOrbitRootNat_scale k.val c z hc hT

/-- There is a parameter on the slice `(1,t)` for which the denominator is
nonzero and all five explicit normalized orbit roots are pairwise distinct. -/
theorem exists_brioschiSlice_parameter_with_injective_root_tuple :
    ∃ t : ℂ, kleinIcosahedralEdgeT 1 t ≠ 0 ∧
      Function.Injective (kleinBrioschiRootTuple (1, t)) := by
  let p := brioschiSliceDistinctnessPolynomial
  have hp : p ≠ 0 := by
    simpa [p] using brioschiSliceDistinctnessPolynomial_ne_zero
  have hcard : p.natDegree < Cardinal.mk ℂ :=
    lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.aleph0_le_mk ℂ)
  obtain ⟨t, ht⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card p hp hcard
  have hEval :
      (Finset.prod brioschiSliceDistinctPairSet fun ij =>
        (brioschiSliceOrbitT6 ij.1 - brioschiSliceOrbitT6 ij.2).eval t) *
        brioschiSliceF.eval t * brioschiSliceT.eval t ≠ 0 := by
    simpa [p, brioschiSliceDistinctnessPolynomial, Polynomial.eval_mul,
      Polynomial.eval_prod] using ht
  rcases mul_ne_zero_iff.mp hEval with ⟨hprodF, hT⟩
  rcases mul_ne_zero_iff.mp hprodF with ⟨hprod, hF⟩
  have hpair : ∀ ij ∈ brioschiSliceDistinctPairSet,
      (brioschiSliceOrbitT6 ij.1 - brioschiSliceOrbitT6 ij.2).eval t ≠ 0 := by
    intro ij hij hzero
    apply hprod
    exact Finset.prod_eq_zero hij hzero
  have hTactual : kleinIcosahedralEdgeT 1 t ≠ 0 := by
    intro hz
    apply hT
    rw [(brioschiSlice_eval t).2.1, hz]
  have hinj : Function.Injective (kleinBrioschiRootTuple (1, t)) := by
    intro i j hij
    by_contra hne
    have hnum := hpair (i, j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    have hroots : kleinBrioschiOrbitRootNat (1, t) i.val =
        kleinBrioschiOrbitRootNat (1, t) j.val := by
      simpa [kleinBrioschiRootTuple, kleinBrioschiOrbitRoot] using hij
    rw [kleinBrioschiOrbitRootNat_slice i t,
      kleinBrioschiOrbitRootNat_slice j t] at hroots
    have hscaled := hroots
    field_simp [hT] at hscaled
    have hpoly : (brioschiSliceOrbitT6 i).eval t =
        (brioschiSliceOrbitT6 j).eval t := hscaled
    rw [Polynomial.eval_sub] at hnum
    exact hnum (sub_eq_zero.mpr hpoly)
  exact ⟨t, hTactual, hinj⟩

/-- At every point of the slice where the explicit separation polynomial is
nonzero, the denominator is nonzero and the five normalized roots are
pairwise distinct. -/
theorem kleinBrioschiRootTuple_injective_of_slice_distinctness
    (t : ℂ)
    (hsep : brioschiSliceDistinctnessPolynomial.eval t ≠ 0) :
    kleinIcosahedralEdgeT 1 t ≠ 0 ∧
      Function.Injective (kleinBrioschiRootTuple (1, t)) := by
  have hEval :
      (Finset.prod brioschiSliceDistinctPairSet fun ij =>
        (brioschiSliceOrbitT6 ij.1 - brioschiSliceOrbitT6 ij.2).eval t) *
        brioschiSliceF.eval t * brioschiSliceT.eval t ≠ 0 := by
    simpa [brioschiSliceDistinctnessPolynomial, Polynomial.eval_mul,
      Polynomial.eval_prod] using hsep
  rcases mul_ne_zero_iff.mp hEval with ⟨hprodF, hT⟩
  rcases mul_ne_zero_iff.mp hprodF with ⟨hprod, hF⟩
  have hpair : ∀ ij ∈ brioschiSliceDistinctPairSet,
      (brioschiSliceOrbitT6 ij.1 - brioschiSliceOrbitT6 ij.2).eval t ≠ 0 := by
    intro ij hij hzero
    apply hprod
    exact Finset.prod_eq_zero hij hzero
  have hTactual : kleinIcosahedralEdgeT 1 t ≠ 0 := by
    intro hz
    apply hT
    rw [(brioschiSlice_eval t).2.1, hz]
  have hinj : Function.Injective (kleinBrioschiRootTuple (1, t)) := by
    intro i j hij
    by_contra hne
    have hnum := hpair (i, j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    have hroots : kleinBrioschiOrbitRootNat (1, t) i.val =
        kleinBrioschiOrbitRootNat (1, t) j.val := by
      simpa [kleinBrioschiRootTuple, kleinBrioschiOrbitRoot] using hij
    rw [kleinBrioschiOrbitRootNat_slice i t,
      kleinBrioschiOrbitRootNat_slice j t] at hroots
    have hscaled := hroots
    field_simp [hT] at hscaled
    rw [Polynomial.eval_sub] at hnum
    exact hnum (sub_eq_zero.mpr hscaled)
  exact ⟨hTactual, hinj⟩

/-- The root tuple is not globally injective: at `(1, 0)` its entries at
indices zero and one already coincide. -/
theorem kleinBrioschiRootTuple_not_injective_degenerate :
    ¬ Function.Injective (kleinBrioschiRootTuple (1, 0)) := by
  intro hinj
  have heq : kleinBrioschiRootTuple (1, 0) 0 =
      kleinBrioschiRootTuple (1, 0) 1 := by
    simp [kleinBrioschiRootTuple, kleinBrioschiOrbitRoot,
      kleinBrioschiOrbitRoot_degenerate]
  have hidx := hinj heq
  norm_num at hidx


/-- The actual rational root tuple is equivariant for the checked diagonal
generator, with the ordinary cyclic permutation action on its five entries.
This is a nonlinear coordinate-to-root map, not a linear identification of
the binary-quintic coefficient representation with the permutation module. -/
theorem kleinBrioschiRootTuple_equivariant (z : ℂ × ℂ) :
    kleinBrioschiRootTuple (kleinOrderFiveStep z) =
      fun k => kleinBrioschiRootTuple z (kleinResolventCycleSucc k) := by
  funext k
  exact kleinBrioschiOrbitRoot_equivariant z k

/-- Index obtained by advancing `k` by `n` places in the five-cycle. -/
def kleinResolventCycleIterate (n : ℕ) (k : Fin 5) : Fin 5 :=
  ⟨(k.val + n) % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Iterating the binary generator advances the five root coordinates by the
same cyclic amount. -/
theorem kleinBrioschiRootTuple_iterate_equivariant (n : ℕ) (z : ℂ × ℂ) :
    kleinBrioschiRootTuple (kleinOrderFiveIterate n z) =
      fun k => kleinBrioschiRootTuple z (kleinResolventCycleIterate n k) := by
  induction n with
  | zero =>
      funext k
      apply congrArg (kleinBrioschiRootTuple z)
      apply Fin.ext
      simp [kleinResolventCycleIterate]
      omega
  | succ n ih =>
      funext k
      rw [kleinOrderFiveIterate_succ, kleinBrioschiRootTuple_equivariant]
      rw [ih]
      apply congrArg (kleinBrioschiRootTuple z)
      apply Fin.ext
      simp [kleinResolventCycleIterate, kleinResolventCycleSucc]
      omega

/-- The monic orbit polynomial attached to the Klein projective five-root map.
Repeated values are retained with their orbit multiplicity; no generic
distinctness assumption is hidden in this construction. -/
def kleinBrioschiOrbitPolynomial (z : ℂ × ℂ) : Polynomial ℂ :=
  ∏ k : Fin 5, (X - Polynomial.C (kleinBrioschiRootTuple z k))

/-- The orbit product is invariant under nonzero common rescaling whenever
the edge denominator is nonzero. -/
theorem kleinBrioschiOrbitPolynomial_scale (c : ℂ) (z : ℂ × ℂ)
    (hc : c ≠ 0) (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0) :
    kleinBrioschiOrbitPolynomial (c * z.1, c * z.2) =
      kleinBrioschiOrbitPolynomial z := by
  simp only [kleinBrioschiOrbitPolynomial,
    kleinBrioschiRootTuple_scale c z hc hT]

/-- At `(1, 0)`, the orbit product and Brioschi polynomial agree even though
the indexed roots coincide: both polynomials are `X^5`. -/
theorem kleinBrioschiOrbitPolynomial_eq_resolvent_degenerate :
    kleinBrioschiOrbitPolynomial (1, 0) =
      brioschiResolvent (brioschiParameter 1 0) := by
  have hroot : ∀ k : Fin 5, kleinBrioschiRootTuple (1, 0) k = 0 := by
    intro k
    simp [kleinBrioschiRootTuple, kleinBrioschiOrbitRoot,
      kleinBrioschiOrbitRoot_degenerate]
  simp [kleinBrioschiOrbitPolynomial, hroot, brioschiResolvent,
    brioschiParameter, kleinIcosahedralVertexF, kleinIcosahedralEdgeT]

/-- When the edge form vanishes, the totalized rational root expressions and
the Brioschi parameter both reduce to zero. Thus the orbit product still
agrees with the Brioschi polynomial on the denominator-zero locus; the
nonzero-denominator hypothesis is needed only for the syzygy-based root
argument, not for this degenerate case. -/
theorem kleinBrioschiOrbitPolynomial_eq_resolvent_of_edge_zero
    (z : ℂ × ℂ) (hT : kleinIcosahedralEdgeT z.1 z.2 = 0) :
    kleinBrioschiOrbitPolynomial z =
      brioschiResolvent (brioschiParameter z.1 z.2) := by
  have hroot : ∀ k : Fin 5, kleinBrioschiRootTuple z k = 0 := by
    intro k
    simp [kleinBrioschiRootTuple, kleinBrioschiOrbitRoot,
      kleinBrioschiOrbitRootNat, hT]
  simp [kleinBrioschiOrbitPolynomial, hroot, brioschiResolvent,
    brioschiParameter, hT]

/-- On the other coordinate axis `(0,1)`, the vertex form vanishes and all
five normalized orbit values are zero, so the orbit product is again `X⁵`.
This records the point at infinity omitted by the affine slice `(1,t)`. -/
theorem kleinBrioschiOrbitPolynomial_eq_resolvent_vertical_axis :
    kleinBrioschiOrbitPolynomial (0, 1) =
      brioschiResolvent (brioschiParameter 0 1) := by
  have hroot : ∀ k : Fin 5, kleinBrioschiRootTuple (0, 1) k = 0 := by
    intro k
    simp [kleinBrioschiRootTuple, kleinBrioschiOrbitRoot,
      kleinBrioschiOrbitRootNat, kleinOrderFiveIterate_coordinates,
      kleinIcosahedralVertexF]
  simp [kleinBrioschiOrbitPolynomial, hroot, brioschiResolvent,
    brioschiParameter, kleinIcosahedralVertexF, kleinIcosahedralEdgeT]

/-- The vertical projective axis consists of nondegenerate scalar copies of
`(0,1)` and inherits its exact orbit-polynomial identity. -/
theorem kleinBrioschiOrbitPolynomial_eq_resolvent_on_vertical_axis
    (z₂ : ℂ) (hz₂ : z₂ ≠ 0) :
    kleinBrioschiOrbitPolynomial (0, z₂) =
      brioschiResolvent (brioschiParameter 0 z₂) := by
  have hT : kleinIcosahedralEdgeT (0 : ℂ) (1 : ℂ) ≠ 0 := by
    simp [kleinIcosahedralEdgeT]
  calc
    kleinBrioschiOrbitPolynomial (0, z₂) =
        kleinBrioschiOrbitPolynomial (z₂ * 0, z₂ * 1) := by simp
    _ = kleinBrioschiOrbitPolynomial (0, 1) :=
      kleinBrioschiOrbitPolynomial_scale z₂ (0, 1) hz₂ hT
    _ = brioschiResolvent (brioschiParameter 0 1) :=
      kleinBrioschiOrbitPolynomial_eq_resolvent_vertical_axis
    _ = brioschiResolvent (brioschiParameter 0 z₂) := by
      simpa using congrArg brioschiResolvent
        (brioschiParameter_scale z₂ (0 : ℂ) 1 hz₂ hT).symm

/-- The orbit polynomial is monic, since it is the product of five monic
linear factors. -/
theorem kleinBrioschiOrbitPolynomial_monic (z : ℂ × ℂ) :
    (kleinBrioschiOrbitPolynomial z).Monic := by
  unfold kleinBrioschiOrbitPolynomial
  exact Polynomial.monic_prod_X_sub_C (kleinBrioschiRootTuple z) Finset.univ

/-- Every indexed orbit value is a root of the orbit polynomial, including
when some orbit values coincide. -/
theorem kleinBrioschiOrbitPolynomial_root (z : ℂ × ℂ) (k : Fin 5) :
    Polynomial.eval (kleinBrioschiRootTuple z k)
      (kleinBrioschiOrbitPolynomial z) = 0 := by
  classical
  unfold kleinBrioschiOrbitPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp

/-- The binary generator permutes the five Klein orbit factors, so their
constructed polynomial is invariant under the generator. -/
theorem kleinBrioschiOrbitPolynomial_invariant (z : ℂ × ℂ) :
    kleinBrioschiOrbitPolynomial (kleinOrderFiveStep z) =
      kleinBrioschiOrbitPolynomial z := by
  classical
  unfold kleinBrioschiOrbitPolynomial
  rw [kleinBrioschiRootTuple_equivariant z]
  have hbij : Function.Bijective kleinResolventCycleSucc := by
    constructor
    · intro a b hab
      apply Fin.ext
      have hval := congrArg Fin.val hab
      simp [kleinResolventCycleSucc] at hval
      omega
    · intro b
      refine ⟨⟨(b.val + 4) % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      apply Fin.ext
      simp [kleinResolventCycleSucc]
      omega
  exact Fintype.prod_bijective kleinResolventCycleSucc hbij
    (fun k => X - Polynomial.C (kleinBrioschiRootTuple z
      (kleinResolventCycleSucc k)))
    (fun k => X - Polynomial.C (kleinBrioschiRootTuple z k))
    (by intro k; rfl)

/-- The source carrier of binary quintic coefficients in the monomial basis
`z₁^(5-j) z₂^j`, of dimension six. The checked order-ten generator acts
diagonally by its monomial weights. -/
abbrev BinaryQuinticCoefficientSpace := Fin 6 → ℂ

private def binaryQuinticWeight (j : Fin 6) : ℂ :=
  kleinBinaryStandardGenA 0 0 ^ (5 - j.val) *
    kleinBinaryStandardGenA 1 1 ^ j.val

/-- Linear action of the binary order-ten generator on quintic coefficients. -/
def binaryQuinticGenerator : BinaryQuinticCoefficientSpace →ₗ[ℂ]
    BinaryQuinticCoefficientSpace where
  toFun v j := binaryQuinticWeight j * v j
  map_add' v w := by
    funext j
    simp [binaryQuinticWeight, mul_add]
  map_smul' c v := by
    funext j
    simp [binaryQuinticWeight, mul_assoc, mul_comm]

/-- The ordinary five-root permutation carrier. -/
abbrev BrioschiRootCoordinateSpace := Fin 5 → ℂ

/-- Generator action on an ordered five-root coordinate vector, by the same
successor permutation that acts on `kleinBrioschiRootTuple`. -/
def brioschiRootCycle : BrioschiRootCoordinateSpace →ₗ[ℂ]
    BrioschiRootCoordinateSpace where
  toFun q k := q (kleinResolventCycleSucc k)
  map_add' q r := by
    funext k
    rfl
  map_smul' c q := by
    funext k
    rfl

private theorem binaryQuinticWeight_fifth (j : Fin 6) :
    binaryQuinticWeight j ^ 5 = -1 := by
  rcases kleinBinaryStandardGenA_eigenvalues_fifth_power with ⟨hα, hβ⟩
  let α := kleinBinaryStandardGenA 0 0
  let β := kleinBinaryStandardGenA 1 1
  have hα' : α ^ 5 = -1 := hα
  have hβ' : β ^ 5 = -1 := hβ
  have hpow (a : ℂ) (n : ℕ) : (a ^ n) ^ 5 = (a ^ 5) ^ n := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  unfold binaryQuinticWeight
  have hj : 5 - j.val + j.val = 5 := Nat.sub_add_cancel (by omega)
  calc
    (α ^ (5 - j.val) * β ^ j.val) ^ 5 =
        (α ^ (5 - j.val)) ^ 5 * (β ^ j.val) ^ 5 := by rw [mul_pow]
    _ = (α ^ 5) ^ (5 - j.val) * (β ^ 5) ^ j.val := by rw [hpow, hpow]
    _ = (-1 : ℂ) ^ (5 - j.val) * (-1) ^ j.val := by rw [hα', hβ']
    _ = -1 := by rw [← pow_add, hj]; norm_num

/-- The binary quintic coefficient representation retains the nontrivial
central spinor action: the fifth power of the lifted generator is `-I`. -/
theorem binaryQuinticGenerator_fifth (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticGenerator (binaryQuinticGenerator
      (binaryQuinticGenerator (binaryQuinticGenerator
        (binaryQuinticGenerator v)))) = -v := by
  funext j
  change binaryQuinticWeight j * (binaryQuinticWeight j *
    (binaryQuinticWeight j * (binaryQuinticWeight j *
      (binaryQuinticWeight j * v j)))) = -v j
  calc
    binaryQuinticWeight j * (binaryQuinticWeight j *
        (binaryQuinticWeight j * (binaryQuinticWeight j *
          (binaryQuinticWeight j * v j)))) =
        binaryQuinticWeight j ^ 5 * v j := by ring
    _ = -v j := by rw [binaryQuinticWeight_fifth]; ring

/-- Evaluate a source-ordered binary quintic
`∑ j, v j * z₁^(5-j) * z₂^j` on a binary coordinate pair. -/
def binaryQuinticEval (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) : ℂ :=
  ∑ j : Fin 6, v j * z.1 ^ (5 - j.val) * z.2 ^ j.val

/-- The diagonal generator on quintic coefficients is the pullback action on
evaluation: evaluating the transformed form at `z` is evaluating the original
form at the transformed binary point. -/
theorem binaryQuinticGenerator_eval (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) :
    binaryQuinticEval (binaryQuinticGenerator v) z =
      binaryQuinticEval v (kleinOrderFiveStep z) := by
  change (∑ j : Fin 6,
      (kleinBinaryStandardGenA 0 0 ^ (5 - j.val) *
        kleinBinaryStandardGenA 1 1 ^ j.val * v j) *
        z.1 ^ (5 - j.val) * z.2 ^ j.val) =
    ∑ j : Fin 6, v j *
      (kleinBinaryStandardGenA 0 0 * z.1) ^ (5 - j.val) *
      (kleinBinaryStandardGenA 1 1 * z.2) ^ j.val
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [mul_pow, mul_pow]
  ring

/-- Evaluate a degree-at-most-five polynomial represented in the source
monomial coefficient convention at a specified affine point. -/
def binaryQuinticAffineEvaluation (nodes : Fin 5 → ℂ) :
    BinaryQuinticCoefficientSpace →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun v i := ∑ j : Fin 6, v j * nodes i ^ j.val
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [RingHom.id_apply]
    ring

/-- Coefficient vector of a polynomial in the `z₁^(5-j) z₂^j` basis after
restricting to the affine chart `z₁ = 1`. -/
private def polynomialToBinaryQuinticCoefficients (p : Polynomial ℂ) :
    BinaryQuinticCoefficientSpace :=
  fun j => p.coeff j.val

/-- On polynomials of degree below six, the coefficient-vector affine
evaluation agrees with ordinary polynomial evaluation. -/
private theorem binaryQuinticAffineEvaluation_polynomial
    (nodes : Fin 5 → ℂ) (p : Polynomial ℂ) (hp : p.degree < 6) :
    binaryQuinticAffineEvaluation nodes
        (polynomialToBinaryQuinticCoefficients p) = fun i => p.eval (nodes i) := by
  funext i
  rw [binaryQuinticAffineEvaluation, Polynomial.eval_eq_sum]
  exact Polynomial.sum_fin (fun n a => a * (nodes i) ^ n)
    (by intro n; simp) hp

/-- Mathlib's principal complex square root is a specified square root on all
of `ℂ`, including zero. -/
private theorem complexSqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [sqrt_eq_exp hz]
    calc
      Complex.exp (Complex.log z / 2) ^ 2 =
          Complex.exp (Complex.log z / 2 + Complex.log z / 2) := by
            rw [pow_two, ← Complex.exp_add]
      _ = Complex.exp (Complex.log z) := by congr 1 <;> ring
      _ = z := Complex.exp_log hz

/-- The explicit Lagrange interpolant, expressed in the source-ordered
binary-quintic coefficient convention. This fixes a definite coefficient
vector for each node/target pair instead of merely asserting that one exists. -/
def binaryQuinticAffineEvaluationInterpolant
    (nodes : Fin 5 → ℂ) (target : Fin 5 → ℂ) :
    BinaryQuinticCoefficientSpace :=
  polynomialToBinaryQuinticCoefficients
    (Lagrange.interpolate Finset.univ nodes target)

/-- The explicit Lagrange coefficient vector evaluates to the prescribed
five values whenever the nodes are distinct. -/
theorem binaryQuinticAffineEvaluation_interpolant_spec
    (nodes : Fin 5 → ℂ) (hnodes : Function.Injective nodes)
    (target : Fin 5 → ℂ) :
    binaryQuinticAffineEvaluation nodes
      (binaryQuinticAffineEvaluationInterpolant nodes target) = target := by
  let p := Lagrange.interpolate Finset.univ nodes target
  have hdeg5 : p.degree < (5 : WithBot ℕ) := by
    simpa [p] using
      (Lagrange.degree_interpolate_lt (s := Finset.univ) (v := nodes)
        (r := target) hnodes.injOn)
  have hdeg6 : p.degree < 6 := lt_trans hdeg5 (by norm_num)
  change binaryQuinticAffineEvaluation nodes
    (polynomialToBinaryQuinticCoefficients p) = target
  rw [binaryQuinticAffineEvaluation_polynomial nodes p hdeg6]
  funext i
  exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := nodes)
    (r := target) hnodes.injOn (Finset.mem_univ i)

/-- Restricting a homogeneous quintic to the affine chart `z₁ = 1` gives
the coefficient-vector evaluation used for interpolation. -/
private theorem binaryQuinticEval_affine
    (v : BinaryQuinticCoefficientSpace) (t : ℂ) :
    binaryQuinticEval v (1, t) =
      ∑ j : Fin 6, v j * t ^ j.val := by
  unfold binaryQuinticEval
  apply Finset.sum_congr rfl
  intro j hj
  simp

/-- Lagrange interpolation makes the affine coefficient-evaluation map onto
whenever its five nodes are pairwise distinct. -/
theorem binaryQuinticAffineEvaluation_surjective
    (nodes : Fin 5 → ℂ) (hnodes : Function.Injective nodes) :
    Function.Surjective (binaryQuinticAffineEvaluation nodes) := by
  intro y
  exact ⟨binaryQuinticAffineEvaluationInterpolant nodes y,
    binaryQuinticAffineEvaluation_interpolant_spec nodes hnodes y⟩

/-- On the chart `(1,t)` with `t ≠ 0`, the five projective points generated
by the owner's diagonal order-five action have distinct affine ratios. The
proof uses the actual diagonal eigenvalues: their ratio has exact order five. -/
theorem kleinOrderFiveAffineOrbit_nodes_injective {t : ℂ} (ht : t ≠ 0) :
    Function.Injective (fun k : Fin 5 =>
      (kleinOrderFiveIterate k.val (1, t)).2 /
        (kleinOrderFiveIterate k.val (1, t)).1) := by
  let α := kleinBinaryStandardGenA 0 0
  let β := kleinBinaryStandardGenA 1 1
  let r : ℂ := β / α
  rcases kleinBinaryStandardGenA_eigenvalues_fifth_power with ⟨hα5, hβ5⟩
  change α ^ 5 = -1 at hα5
  change β ^ 5 = -1 at hβ5
  have hα : α ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : 5 ≠ 0)] at hα5
    norm_num at hα5
  have hβ : β ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : 5 ≠ 0)] at hβ5
    norm_num at hβ5
  have hφ : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  have hq2 : Real.sqrt (Real.goldenRatio ^ 2 + 1) ^ 2 =
      Real.goldenRatio ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hqpos : 0 ≤ Real.sqrt (Real.goldenRatio ^ 2 + 1) := Real.sqrt_nonneg _
  have hqgt : 1 < Real.sqrt (Real.goldenRatio ^ 2 + 1) := by
    by_contra h
    have hle : Real.sqrt (Real.goldenRatio ^ 2 + 1) ≤ 1 := le_of_not_gt h
    have hφsq : 1 < Real.goldenRatio ^ 2 := by nlinarith
    nlinarith
  have hparam : 0 < kleinBinaryBasisAlpha := by
    dsimp [kleinBinaryBasisAlpha]
    exact div_pos (sub_pos.mpr hqgt) Real.goldenRatio_pos
  have hαβ : α ≠ β := by
    intro hab
    have him := congrArg Complex.im hab
    simp [α, β, kleinBinaryStandardGenA] at him
    have hφ' : 1 < (1 + Real.sqrt 5) / 2 := by simpa [Real.goldenRatio] using hφ
    nlinarith [hparam, hφ']
  have hrne : r ≠ 1 := by
    intro hr
    have hdiv : β / α = 1 := by simpa [r] using hr
    have hab : β = α := (div_eq_one_iff_eq hα).mp hdiv
    exact hαβ hab.symm
  have hr5 : r ^ 5 = 1 := by
    dsimp [r]
    rw [div_pow, hβ5, hα5]
    norm_num
  have hr0 : r ≠ 0 := div_ne_zero hβ hα
  let u : ℂˣ := Units.mk0 r hr0
  have hu5 : u ^ 5 = 1 := by
    apply Units.ext
    simpa [u] using hr5
  have hu_ne : u ≠ 1 := by
    intro hu
    have hval := congrArg (fun x : ℂˣ => (x : ℂ)) hu
    have : r = 1 := by simpa [u] using hval
    exact hrne this
  have hPrime : Nat.Prime 5 := by norm_num
  letI : Fact (Nat.Prime 5) := ⟨hPrime⟩
  have huOrder : orderOf u = 5 := orderOf_eq_prime hu5 hu_ne
  have hnode_formula (k : Fin 5) :
      (kleinOrderFiveIterate k.val (1, t)).2 /
        (kleinOrderFiveIterate k.val (1, t)).1 = r ^ k.val * t := by
    rw [kleinOrderFiveIterate_coordinates]
    dsimp [α, β, r]
    field_simp [hα]
    ring
  intro i j hij
  have hpows : r ^ i.val = r ^ j.val := by
    apply mul_right_cancel₀ ht
    calc
      r ^ i.val * t =
          (kleinOrderFiveIterate i.val (1, t)).2 /
            (kleinOrderFiveIterate i.val (1, t)).1 := (hnode_formula i).symm
      _ = (kleinOrderFiveIterate j.val (1, t)).2 /
            (kleinOrderFiveIterate j.val (1, t)).1 := hij
      _ = r ^ j.val * t := hnode_formula j
  have hunitPowers : u ^ i.val = u ^ j.val := by
    apply Units.ext
    simpa [u] using hpows
  have hi : i.val ∈ Set.Iio (orderOf u) := by
    rw [huOrder]
    exact i.isLt
  have hj : j.val ∈ Set.Iio (orderOf u) := by
    rw [huOrder]
    exact j.isLt
  have hval := (pow_injOn_Iio_orderOf (x := u)) hi hj hunitPowers
  exact Fin.ext hval

/-- Every first coordinate on the diagonal-generator orbit of `(1,t)` is
nonzero, since the first diagonal eigenvalue has fifth power `-1`. -/
theorem kleinOrderFiveAffineOrbit_first_ne_zero (t : ℂ) (k : Fin 5) :
    (kleinOrderFiveIterate k.val (1, t)).1 ≠ 0 := by
  rcases kleinBinaryStandardGenA_eigenvalues_fifth_power with ⟨hα5, _⟩
  have hα0 : kleinBinaryStandardGenA 0 0 ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : 5 ≠ 0)] at hα5
    norm_num at hα5
  rw [kleinOrderFiveIterate_coordinates]
  simp only [mul_one]
  exact pow_ne_zero _ hα0

/-- The odd-degree binary quintic evaluated along the five projective
order-five translates, with the alternating trivialization that converts the
central spinor sign into a uniform signed cyclic shift. -/
def binaryQuinticSignedOrbit (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (k : Fin 5) : ℂ :=
  (-1 : ℂ) ^ k.val *
    binaryQuinticEval v (kleinOrderFiveIterate k.val z)

/-- Odd homogeneous quintic evaluation changes sign under the central
spinor action `z ↦ -z`. -/
private theorem binaryQuinticEval_scale (v : BinaryQuinticCoefficientSpace)
    (c : ℂ) (z : ℂ × ℂ) :
    binaryQuinticEval v (c * z.1, c * z.2) = c ^ 5 * binaryQuinticEval v z := by
  unfold binaryQuinticEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hdeg : 5 - j.val + j.val = 5 := by omega
  calc
    v j * (c * z.1) ^ (5 - j.val) * (c * z.2) ^ j.val =
        c ^ 5 * (v j * z.1 ^ (5 - j.val) * z.2 ^ j.val) := by
      rw [mul_pow, mul_pow]
      calc
        v j * (c ^ (5 - j.val) * z.1 ^ (5 - j.val)) *
            (c ^ j.val * z.2 ^ j.val) =
            (c ^ (5 - j.val) * c ^ j.val) *
              (v j * z.1 ^ (5 - j.val) * z.2 ^ j.val) := by ring
        _ = c ^ 5 * (v j * z.1 ^ (5 - j.val) * z.2 ^ j.val) := by
          rw [← pow_add, hdeg]

private theorem binaryQuinticEval_neg (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) : binaryQuinticEval v (-z.1, -z.2) =
      -binaryQuinticEval v z := by
  have hpair : (-z.1, -z.2) = ((-1 : ℂ) * z.1, (-1 : ℂ) * z.2) := by
    simp
  rw [hpair, binaryQuinticEval_scale]
  norm_num

/-- Evaluation of a binary quintic on the order-five orbit intertwines its
order-ten coefficient action with the signed five-cycle. The alternating
factor is essential: the fifth power of the spinor generator acts by `-1` on
degree-five forms. -/
theorem binaryQuinticSignedOrbit_equivariant
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    binaryQuinticSignedOrbit (binaryQuinticGenerator v) z =
      fun k => -binaryQuinticSignedOrbit v z (kleinResolventCycleSucc k) := by
  funext k
  fin_cases k
  · simp only [binaryQuinticSignedOrbit, kleinResolventCycleSucc,
      binaryQuinticGenerator_eval]
    norm_num [kleinOrderFiveIterate_succ]
  · simp only [binaryQuinticSignedOrbit, kleinResolventCycleSucc,
      binaryQuinticGenerator_eval]
    rw [← kleinOrderFiveIterate_succ 1 z]
    norm_num
  · simp only [binaryQuinticSignedOrbit, kleinResolventCycleSucc,
      binaryQuinticGenerator_eval]
    rw [← kleinOrderFiveIterate_succ 2 z]
    norm_num
  · simp only [binaryQuinticSignedOrbit, kleinResolventCycleSucc,
      binaryQuinticGenerator_eval]
    rw [← kleinOrderFiveIterate_succ 3 z]
    norm_num
  · simp only [binaryQuinticSignedOrbit, kleinResolventCycleSucc,
      binaryQuinticGenerator_eval]
    rw [← kleinOrderFiveIterate_succ 4 z,
      kleinOrderFiveIterate_five_is_central, binaryQuinticEval_neg]
    norm_num

/-- The signed five-cycle representation, retaining the central `-1` on
degree-five data. -/
def binaryQuinticSignedCycle : BrioschiRootCoordinateSpace →ₗ[ℂ]
    BrioschiRootCoordinateSpace where
  toFun q k := -q (kleinResolventCycleSucc k)
  map_add' q r := by
    funext k
    simp only [Pi.add_apply]
    ring
  map_smul' c q := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Apply the signed cycle five times. -/
def binaryQuinticSignedCycleFive (q : BrioschiRootCoordinateSpace) :
    BrioschiRootCoordinateSpace :=
  binaryQuinticSignedCycle (binaryQuinticSignedCycle
    (binaryQuinticSignedCycle (binaryQuinticSignedCycle
      (binaryQuinticSignedCycle q))))

/-- The signed five-cycle has the same central character as the binary
quintic representation: its fifth power is negation. -/
theorem binaryQuinticSignedCycle_fifth (q : BrioschiRootCoordinateSpace) :
    binaryQuinticSignedCycleFive q = -q := by
  funext k
  fin_cases k <;> norm_num [binaryQuinticSignedCycleFive,
    binaryQuinticSignedCycle, kleinResolventCycleSucc]

/-- The signed five-cycle has period ten. -/
theorem binaryQuinticSignedCycle_tenth (q : BrioschiRootCoordinateSpace) :
    binaryQuinticSignedCycleFive (binaryQuinticSignedCycleFive q) = q := by
  have h5 := binaryQuinticSignedCycle_fifth q
  have h5neg := binaryQuinticSignedCycle_fifth (-q)
  simp only [neg_neg] at h5neg
  calc
    binaryQuinticSignedCycleFive (binaryQuinticSignedCycleFive q) =
        binaryQuinticSignedCycleFive (-q) := by rw [h5]
    _ = q := h5neg

/-- Evaluation on the selected Klein orbit is a complex-linear map from the
six-dimensional source-ordered binary-quintic coefficient space to the
five-dimensional signed orbit-coordinate space. -/
def binaryQuinticOrbitEvaluation (z : ℂ × ℂ) :
    BinaryQuinticCoefficientSpace →ₗ[ℂ] BrioschiRootCoordinateSpace where
  toFun v k := binaryQuinticSignedOrbit v z k
  map_add' v w := by
    funext k
    simp only [binaryQuinticSignedOrbit, binaryQuinticEval, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c v := by
    funext k
    simp only [binaryQuinticSignedOrbit, binaryQuinticEval, Pi.smul_apply,
      smul_eq_mul]
    calc
      (-1 : ℂ) ^ k.val * (∑ j : Fin 6,
          c * v j * (kleinOrderFiveIterate k.val z).1 ^ (5 - j.val) *
            (kleinOrderFiveIterate k.val z).2 ^ j.val) =
          (-1 : ℂ) ^ k.val * (c * ∑ j : Fin 6,
            v j * (kleinOrderFiveIterate k.val z).1 ^ (5 - j.val) *
              (kleinOrderFiveIterate k.val z).2 ^ j.val) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = c * ((-1 : ℂ) ^ k.val * ∑ j : Fin 6,
            v j * (kleinOrderFiveIterate k.val z).1 ^ (5 - j.val) *
              (kleinOrderFiveIterate k.val z).2 ^ j.val) := by ring

/-- If the five orbit points lie in one affine chart and have distinct chart
coordinates, evaluation of binary quintics on that orbit is onto the signed
five-coordinate representation. The chart scalars are nonzero weights, so
they do not change surjectivity. -/
theorem binaryQuinticOrbitEvaluation_surjective_of_affine_chart
    (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1)) :
    Function.Surjective (binaryQuinticOrbitEvaluation z) := by
  let nodes : Fin 5 → ℂ := fun k =>
    (kleinOrderFiveIterate k.val z).2 / (kleinOrderFiveIterate k.val z).1
  let weights : Fin 5 → ℂ := fun k =>
    (-1 : ℂ) ^ k.val * (kleinOrderFiveIterate k.val z).1 ^ 5
  intro y
  have hweights : ∀ k : Fin 5, weights k ≠ 0 := by
    intro k
    have hpow : (kleinOrderFiveIterate k.val z).1 ^ 5 ≠ 0 :=
      pow_ne_zero 5 (hfirst k)
    dsimp [weights]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hpow
  let scaledTarget : Fin 5 → ℂ := fun k => y k / weights k
  obtain ⟨v, hv⟩ :=
    (binaryQuinticAffineEvaluation_surjective nodes hnodes) scaledTarget
  refine ⟨v, ?_⟩
  funext k
  have hpoint : kleinOrderFiveIterate k.val z =
      ((kleinOrderFiveIterate k.val z).1,
       (kleinOrderFiveIterate k.val z).1 * nodes k) := by
    apply Prod.ext
    · rfl
    ·
      change (kleinOrderFiveIterate k.val z).2 =
        (kleinOrderFiveIterate k.val z).1 *
          ((kleinOrderFiveIterate k.val z).2 /
            (kleinOrderFiveIterate k.val z).1)
      field_simp [hfirst k]
  have heval : binaryQuinticEval v (kleinOrderFiveIterate k.val z) =
      (kleinOrderFiveIterate k.val z).1 ^ 5 *
        binaryQuinticAffineEvaluation nodes v k := by
    rw [hpoint]
    have hscaled := binaryQuinticEval_scale v
      (kleinOrderFiveIterate k.val z).1 (1, nodes k)
    have haff : binaryQuinticAffineEvaluation nodes v k =
        ∑ j : Fin 6, v j * nodes k ^ j.val := by
      simp [binaryQuinticAffineEvaluation]
    rw [haff]
    simpa [binaryQuinticEval_affine, nodes] using hscaled
  change (-1 : ℂ) ^ k.val *
    binaryQuinticEval v (kleinOrderFiveIterate k.val z) = y k
  rw [heval, congrFun hv k]
  dsimp [scaledTarget, weights]
  field_simp [hweights k, hfirst k]

/-- Explicit source-ordered coefficient vector interpolating an arbitrary
signed orbit target. The affine ratios and homogeneous weights are those of
the actual Klein orbit nodes. -/
def binaryQuinticOrbitEvaluationInterpolant (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (target : Fin 5 → ℂ) : BinaryQuinticCoefficientSpace :=
  let nodes : Fin 5 → ℂ := fun k =>
    (kleinOrderFiveIterate k.val z).2 / (kleinOrderFiveIterate k.val z).1
  let weights : Fin 5 → ℂ := fun k =>
    (-1 : ℂ) ^ k.val * (kleinOrderFiveIterate k.val z).1 ^ 5
  binaryQuinticAffineEvaluationInterpolant nodes
    (fun k => target k / weights k)

/-- The explicit orbit interpolant realizes its target under the signed
evaluation map. -/
theorem binaryQuinticOrbitEvaluationInterpolant_spec (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (target : Fin 5 → ℂ) :
    binaryQuinticOrbitEvaluation z
      (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target) = target := by
  let nodes : Fin 5 → ℂ := fun k =>
    (kleinOrderFiveIterate k.val z).2 / (kleinOrderFiveIterate k.val z).1
  let weights : Fin 5 → ℂ := fun k =>
    (-1 : ℂ) ^ k.val * (kleinOrderFiveIterate k.val z).1 ^ 5
  let scaledTarget : Fin 5 → ℂ := fun k => target k / weights k
  have hweights : ∀ k : Fin 5, weights k ≠ 0 := by
    intro k
    dsimp [weights]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero 5 (hfirst k))
  have hAffine := binaryQuinticAffineEvaluation_interpolant_spec
    nodes hnodes scaledTarget
  ext k
  have hpoint : kleinOrderFiveIterate k.val z =
      ((kleinOrderFiveIterate k.val z).1,
       (kleinOrderFiveIterate k.val z).1 * nodes k) := by
    apply Prod.ext
    · rfl
    · change (kleinOrderFiveIterate k.val z).2 =
        (kleinOrderFiveIterate k.val z).1 *
          ((kleinOrderFiveIterate k.val z).2 /
            (kleinOrderFiveIterate k.val z).1)
      field_simp [hfirst k]
  have heval : binaryQuinticEval
      (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target)
      (kleinOrderFiveIterate k.val z) =
      (kleinOrderFiveIterate k.val z).1 ^ 5 *
        binaryQuinticAffineEvaluation nodes
          (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target) k := by
    rw [hpoint]
    have hscaled := binaryQuinticEval_scale
      (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target)
      (kleinOrderFiveIterate k.val z).1 (1, nodes k)
    have haff : binaryQuinticAffineEvaluation nodes
        (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target) k =
        ∑ j : Fin 6,
          (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target) j *
            nodes k ^ j.val := by
      simp [binaryQuinticAffineEvaluation]
    rw [haff]
    simpa [binaryQuinticEval_affine, nodes] using hscaled
  have hAffineK := congrFun hAffine k
  change binaryQuinticAffineEvaluation nodes
      (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target) k =
    scaledTarget k at hAffineK
  change (-1 : ℂ) ^ k.val *
    binaryQuinticEval
      (binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes target)
      (kleinOrderFiveIterate k.val z) = target k
  rw [heval, hAffineK]
  dsimp [scaledTarget, weights]
  field_simp [hweights k, hfirst k]

/-- The binary-quintic orbit evaluation is onto the signed five-orbit space
on the explicit affine chart `(1,t)` for every nonzero `t`. -/
theorem binaryQuinticOrbitEvaluation_surjective_affine_chart
    {t : ℂ} (ht : t ≠ 0) :
    Function.Surjective (binaryQuinticOrbitEvaluation (1, t)) := by
  apply binaryQuinticOrbitEvaluation_surjective_of_affine_chart (1, t)
  · exact kleinOrderFiveAffineOrbit_first_ne_zero t
  · exact kleinOrderFiveAffineOrbit_nodes_injective ht

/-- On an orbit satisfying the affine-chart hypotheses, the quotient of the
binary-quintic coefficient representation by the kernel of orbit evaluation
is linearly equivalent to the signed five-orbit representation. -/
noncomputable def binaryQuinticOrbitQuotientEquiv (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1)) :
    (BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) ≃ₗ[ℂ]
        BrioschiRootCoordinateSpace :=
  (binaryQuinticOrbitEvaluation z).quotKerEquivOfSurjective
    (binaryQuinticOrbitEvaluation_surjective_of_affine_chart z hfirst hnodes)

/-- The quotient equivalence sends a coefficient class to its signed orbit
evaluation; this identifies the concrete quotient map, not merely the two
vector-space dimensions. -/
theorem binaryQuinticOrbitQuotientEquiv_apply_mk
    (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (v : BinaryQuinticCoefficientSpace) :
    (binaryQuinticOrbitQuotientEquiv z hfirst hnodes
      (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace) =
        binaryQuinticOrbitEvaluation z v := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (f := binaryQuinticOrbitEvaluation z)
    (binaryQuinticOrbitEvaluation_surjective_of_affine_chart z hfirst hnodes) v

/-- Concrete first-isomorphism equivalence for the actual Klein orbit of
`(1,t)`, with the distinctness and chart nonvanishing discharged from `t ≠ 0`. -/
noncomputable def binaryQuinticAffineOrbitQuotientEquiv {t : ℂ} (ht : t ≠ 0) :
    (BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation (1, t))) ≃ₗ[ℂ]
        BrioschiRootCoordinateSpace :=
  binaryQuinticOrbitQuotientEquiv (1, t)
    (kleinOrderFiveAffineOrbit_first_ne_zero t)
    (kleinOrderFiveAffineOrbit_nodes_injective ht)

/-- The explicit affine-chart quotient equivalence evaluates a coefficient
class at the five signed Klein orbit points. -/
theorem binaryQuinticAffineOrbitQuotientEquiv_apply_mk {t : ℂ} (ht : t ≠ 0)
    (v : BinaryQuinticCoefficientSpace) :
    (binaryQuinticAffineOrbitQuotientEquiv ht
      (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace) =
        binaryQuinticOrbitEvaluation (1, t) v := by
  exact binaryQuinticOrbitQuotientEquiv_apply_mk (1, t)
    (kleinOrderFiveAffineOrbit_first_ne_zero t)
    (kleinOrderFiveAffineOrbit_nodes_injective ht) v

/-- The coefficient representation and signed orbit-coordinate representation
are intertwined by evaluation. -/
theorem binaryQuinticOrbitEvaluation_intertwines
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticOrbitEvaluation z (binaryQuinticGenerator v) =
      binaryQuinticSignedCycle (binaryQuinticOrbitEvaluation z v) := by
  funext k
  exact congrFun (binaryQuinticSignedOrbit_equivariant v z) k

/-- The source generator descends to the quotient by the orbit-evaluation
kernel. This is the representation induced on the five-dimensional quotient,
constructed from the actual coefficient generator rather than postulated by
transport. -/
noncomputable def binaryQuinticOrbitQuotientGenerator (z : ℂ × ℂ) :
    (BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) →ₗ[ℂ]
        (BinaryQuinticCoefficientSpace ⧸
          LinearMap.ker (binaryQuinticOrbitEvaluation z)) := by
  let K := LinearMap.ker (binaryQuinticOrbitEvaluation z)
  refine K.liftQ (K.mkQ.comp binaryQuinticGenerator) ?_
  intro v hv
  have hgen : binaryQuinticGenerator v ∈ K := by
    change binaryQuinticOrbitEvaluation z (binaryQuinticGenerator v) = 0
    rw [binaryQuinticOrbitEvaluation_intertwines]
    have hv' : binaryQuinticOrbitEvaluation z v = 0 := by
      exact LinearMap.mem_ker.mp hv
    rw [hv']
    simp
  change K.mkQ (binaryQuinticGenerator v) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hgen

/-- On quotient classes represented by a quintic coefficient vector, the
induced generator is precisely the source generator followed by quotienting. -/
@[simp]
theorem binaryQuinticOrbitQuotientGenerator_apply_mk
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticOrbitQuotientGenerator z
      (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (binaryQuinticGenerator v) := by
  simp [binaryQuinticOrbitQuotientGenerator]

/-- The first-isomorphism equivalence conjugates the induced quotient action
to the signed order-ten orbit-coordinate action. -/
theorem binaryQuinticOrbitQuotientEquiv_intertwines
    (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) :
    binaryQuinticOrbitQuotientEquiv z hfirst hnodes
        (binaryQuinticOrbitQuotientGenerator z q) =
      binaryQuinticSignedCycle
        (binaryQuinticOrbitQuotientEquiv z hfirst hnodes q) := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  rw [binaryQuinticOrbitQuotientGenerator_apply_mk,
    binaryQuinticOrbitQuotientEquiv_apply_mk,
    binaryQuinticOrbitEvaluation_intertwines,
    binaryQuinticOrbitQuotientEquiv_apply_mk]

/-- On the explicit `(1,t)` chart, the quotient representation is conjugate to
the signed cyclic coordinate representation. -/
theorem binaryQuinticAffineOrbitQuotientEquiv_intertwines {t : ℂ} (ht : t ≠ 0)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation (1, t))) :
    binaryQuinticAffineOrbitQuotientEquiv ht
        (binaryQuinticOrbitQuotientGenerator (1, t) q) =
      binaryQuinticSignedCycle
        (binaryQuinticAffineOrbitQuotientEquiv ht q) := by
  simpa [binaryQuinticAffineOrbitQuotientEquiv] using
    (binaryQuinticOrbitQuotientEquiv_intertwines (1, t)
      (kleinOrderFiveAffineOrbit_first_ne_zero t)
      (kleinOrderFiveAffineOrbit_nodes_injective ht) q)

/-- Squaring the signed evaluation tuple removes the central spinor sign and
produces an ordinary cyclic five-tuple. -/
def binaryQuinticResolventTuple (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) (k : Fin 5) : ℂ :=
  binaryQuinticSignedOrbit v z k ^ 2

/-- The squared quintic evaluation tuple is equivariant for the ordinary
source-ordered five-cycle. It removes the central sign from the evaluation
coordinates, allowing a degree-five orbit polynomial to be formed. -/
theorem binaryQuinticResolventTuple_equivariant
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    binaryQuinticResolventTuple (binaryQuinticGenerator v) z =
      fun k => binaryQuinticResolventTuple v z (kleinResolventCycleSucc k) := by
  funext k
  have h := congrFun (binaryQuinticSignedOrbit_equivariant v z) k
  simp only [binaryQuinticResolventTuple]
  rw [h]
  ring

/-- The degree-five orbit polynomial obtained from squared
source-ordered quintic evaluations on the chosen Klein orbit. -/
def binaryQuinticEvaluationResolvent (v : BinaryQuinticCoefficientSpace)
    (z : ℂ × ℂ) : Polynomial ℂ :=
  ∏ k : Fin 5, (X - Polynomial.C (binaryQuinticResolventTuple v z k))

/-- Uniform scaling of the six binary-quintic coefficients scales each signed
orbit evaluation by the same scalar, and therefore scales each squared
resolvent coordinate by its square. This is the coefficient-scaling action;
it is distinct from dilating the roots of a polynomial. -/
theorem binaryQuinticResolventTuple_smul (c : ℂ)
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    binaryQuinticResolventTuple (c • v) z =
      fun k => c ^ 2 * binaryQuinticResolventTuple v z k := by
  funext k
  have hEval := congrFun ((binaryQuinticOrbitEvaluation z).map_smul c v) k
  change binaryQuinticSignedOrbit (c • v) z k =
    c * binaryQuinticSignedOrbit v z k at hEval
  simp only [binaryQuinticResolventTuple]
  rw [hEval]
  ring

/-- Exact coefficient-scaling law for the monic evaluation resolvent. Its
roots scale by `c²`; hence uniform coefficient scaling does not leave this
monic polynomial unchanged in general. The formula records the actual
projective weight behavior without identifying it with root dilation. -/
theorem binaryQuinticEvaluationResolvent_smul (c : ℂ)
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    binaryQuinticEvaluationResolvent (c • v) z =
      ∏ k : Fin 5,
        (X - Polynomial.C (c ^ 2 * binaryQuinticResolventTuple v z k)) := by
  unfold binaryQuinticEvaluationResolvent
  rw [binaryQuinticResolventTuple_smul]

/-- The evaluation resolvent is monic of degree five, with multiplicities
retained when orbit values coincide. -/
theorem binaryQuinticEvaluationResolvent_monic
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    (binaryQuinticEvaluationResolvent v z).Monic := by
  unfold binaryQuinticEvaluationResolvent
  exact Polynomial.monic_prod_X_sub_C (binaryQuinticResolventTuple v z) Finset.univ

/-- The evaluation resolvent is the orbit polynomial of the squared
coordinates of the quotient class under `binaryQuinticOrbitQuotientEquiv`.
This is the precise representation-to-resolvent identification: the signed
linear quotient is squared to remove the central spinor sign, then its five
coordinates are assembled into the monic orbit polynomial. -/
theorem binaryQuinticEvaluationResolvent_eq_quotient_orbit_polynomial
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1)) :
    binaryQuinticEvaluationResolvent v z =
      ∏ k : Fin 5, (X - Polynomial.C
        (((binaryQuinticOrbitQuotientEquiv z hfirst hnodes
          (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace) k) ^ 2)) := by
  have hcoord :
      (binaryQuinticOrbitQuotientEquiv z hfirst hnodes
        (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace) =
        binaryQuinticSignedOrbit v z := by
    rw [binaryQuinticOrbitQuotientEquiv_apply_mk]
    rfl
  unfold binaryQuinticEvaluationResolvent binaryQuinticResolventTuple
  rw [hcoord]

/-- On the actual affine chart `(1,t)` with `t ≠ 0`, the constructed
degree-five evaluation resolvent is exactly the orbit polynomial of the
squared coordinates of the canonical quotient class. -/
theorem binaryQuinticEvaluationResolvent_eq_affine_quotient_orbit_polynomial
    {t : ℂ} (ht : t ≠ 0) (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticEvaluationResolvent v (1, t) =
      ∏ k : Fin 5, (X - Polynomial.C
        (((binaryQuinticAffineOrbitQuotientEquiv ht
          (Submodule.Quotient.mk v) : BrioschiRootCoordinateSpace) k) ^ 2)) := by
  simpa [binaryQuinticAffineOrbitQuotientEquiv] using
    (binaryQuinticEvaluationResolvent_eq_quotient_orbit_polynomial v (1, t)
      (kleinOrderFiveAffineOrbit_first_ne_zero t)
      (kleinOrderFiveAffineOrbit_nodes_injective ht))

/-- The resolvent polynomial attached directly to a class in the five-dimensional
quotient of the binary-quintic representation.  Unlike the later existence
construction by interpolation, this definition is canonical once the Klein
orbit and its evaluation-kernel quotient have been fixed. -/
def binaryQuinticOrbitQuotientResolvent (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) : Polynomial ℂ :=
  ∏ k : Fin 5, (X - Polynomial.C
    (((binaryQuinticOrbitQuotientEquiv z hfirst hnodes q :
      BrioschiRootCoordinateSpace) k) ^ 2))

/-- On a quotient class represented by a source-ordered quintic, the
quotient-level construction is exactly its evaluation resolvent.  In
particular, the resolvent is independent of the chosen representative. -/
theorem binaryQuinticOrbitQuotientResolvent_apply_mk
    (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticOrbitQuotientResolvent z hfirst hnodes
        (Submodule.Quotient.mk v) = binaryQuinticEvaluationResolvent v z := by
  unfold binaryQuinticOrbitQuotientResolvent binaryQuinticEvaluationResolvent
    binaryQuinticResolventTuple
  rw [binaryQuinticOrbitQuotientEquiv_apply_mk]
  simp [binaryQuinticOrbitEvaluation]

/-- Each squared orbit evaluation is a root of the constructed evaluation
resolvent, including at degenerate orbits where factors repeat. -/
theorem binaryQuinticEvaluationResolvent_root
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) (k : Fin 5) :
    Polynomial.eval (binaryQuinticResolventTuple v z k)
      (binaryQuinticEvaluationResolvent v z) = 0 := by
  classical
  unfold binaryQuinticEvaluationResolvent
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp

/-- The evaluation resolvent is invariant under the order-ten generator on
the binary quintic coefficients; the central sign disappears after squaring. -/
theorem binaryQuinticEvaluationResolvent_invariant
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    binaryQuinticEvaluationResolvent (binaryQuinticGenerator v) z =
      binaryQuinticEvaluationResolvent v z := by
  classical
  unfold binaryQuinticEvaluationResolvent
  rw [binaryQuinticResolventTuple_equivariant]
  have hbij : Function.Bijective kleinResolventCycleSucc := by
    constructor
    · intro a b hab
      apply Fin.ext
      have hval := congrArg Fin.val hab
      simp [kleinResolventCycleSucc] at hval
      omega
    · intro b
      refine ⟨⟨(b.val + 4) % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      apply Fin.ext
      simp [kleinResolventCycleSucc]
      omega
  exact Fintype.prod_bijective kleinResolventCycleSucc hbij
    (fun k => X - Polynomial.C (binaryQuinticResolventTuple v z
      (kleinResolventCycleSucc k)))
    (fun k => X - Polynomial.C (binaryQuinticResolventTuple v z k))
    (by intro k; rfl)

/-- The quotient-level quintic resolvent is invariant under the operator
induced by the binary order-ten generator.  The signed quotient coordinates
are squared, so the central sign disappears and the ordinary five-cycle
only permutes the factors. -/
theorem binaryQuinticOrbitQuotientResolvent_invariant
    (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker (binaryQuinticOrbitEvaluation z)) :
    binaryQuinticOrbitQuotientResolvent z hfirst hnodes
        (binaryQuinticOrbitQuotientGenerator z q) =
      binaryQuinticOrbitQuotientResolvent z hfirst hnodes q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  rw [binaryQuinticOrbitQuotientGenerator_apply_mk,
    binaryQuinticOrbitQuotientResolvent_apply_mk,
    binaryQuinticOrbitQuotientResolvent_apply_mk,
    binaryQuinticEvaluationResolvent_invariant]

/-- The ordinary five-cycle on root coordinates has fifth power equal to the
identity, so the central element acts trivially on this permutation carrier. -/
theorem brioschiRootCycle_fifth (q : BrioschiRootCoordinateSpace) :
    brioschiRootCycle (brioschiRootCycle
      (brioschiRootCycle (brioschiRootCycle (brioschiRootCycle q)))) = q := by
  funext k
  fin_cases k <;> norm_num [brioschiRootCycle, kleinResolventCycleSucc]

/-- There is no nonzero complex-linear intertwiner from the binary quintic
coefficient representation to the ordinary five-root permutation
representation. Their fifth powers have opposite central characters. This
rules out the proposed *linear* representation identification while leaving
the explicit nonlinear equivariant root tuple intact. -/
theorem no_linear_intertwiner_binaryQuintic_to_brioschiRoots
    (f : BinaryQuinticCoefficientSpace →ₗ[ℂ] BrioschiRootCoordinateSpace)
    (hintertwine : ∀ v, f (binaryQuinticGenerator v) =
      brioschiRootCycle (f v)) : f = 0 := by
  apply LinearMap.ext
  intro v
  funext k
  have hiter :
      f (binaryQuinticGenerator (binaryQuinticGenerator
        (binaryQuinticGenerator (binaryQuinticGenerator
          (binaryQuinticGenerator v))))) =
      brioschiRootCycle (brioschiRootCycle (brioschiRootCycle
        (brioschiRootCycle (brioschiRootCycle (f v))))) := by
    calc
      f (binaryQuinticGenerator (binaryQuinticGenerator
          (binaryQuinticGenerator (binaryQuinticGenerator
            (binaryQuinticGenerator v)))) ) =
          brioschiRootCycle (f (binaryQuinticGenerator (binaryQuinticGenerator
            (binaryQuinticGenerator (binaryQuinticGenerator v))))) := hintertwine _
      _ = brioschiRootCycle (brioschiRootCycle
          (f (binaryQuinticGenerator (binaryQuinticGenerator
            (binaryQuinticGenerator v))))) := by rw [hintertwine]
      _ = brioschiRootCycle (brioschiRootCycle (brioschiRootCycle
          (f (binaryQuinticGenerator (binaryQuinticGenerator v))))) := by rw [hintertwine]
      _ = brioschiRootCycle (brioschiRootCycle (brioschiRootCycle
          (brioschiRootCycle (f (binaryQuinticGenerator v))))) := by rw [hintertwine]
      _ = brioschiRootCycle (brioschiRootCycle (brioschiRootCycle
          (brioschiRootCycle (brioschiRootCycle (f v))))) := by rw [hintertwine]
  rw [binaryQuinticGenerator_fifth, map_neg, brioschiRootCycle_fifth] at hiter
  have hk : -(f v k) = f v k := by simpa using congrFun hiter k
  have hsum : f v k + f v k = 0 := by
    nth_rewrite 2 [← hk]
    simp
  have htwo : (2 : ℂ) * f v k = 0 := by rw [two_mul]; exact hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Each of the five listed iterate values is a root of the same
Brioschi-shaped quintic. This does not assert the values are pairwise
distinct or form the complete Galois orbit. -/
theorem kleinBrioschiOrbitRoot_is_root (z : ℂ × ℂ) (k : Fin 5)
    (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0) :
    Polynomial.eval (kleinBrioschiOrbitRoot z k)
      (brioschiResolvent (brioschiParameter z.1 z.2)) = 0 := by
  let p := kleinOrderFiveIterate k.val z
  have hinv := kleinForms_invariant_on_orderFiveIterate k.val z
  have hTp : kleinIcosahedralEdgeT p.1 p.2 ≠ 0 := by
    rw [hinv.2]
    exact hT
  have hroot := brioschiResolvent_has_klein_root hTp
  simpa [kleinBrioschiOrbitRoot, kleinBrioschiOrbitRootNat, p,
    brioschiParameter, hinv.1, hinv.2] using hroot

/-- When the five explicit orbit values are distinct, their monic orbit
polynomial is exactly the displayed Brioschi quintic. The distinctness
hypothesis is stated explicitly rather than inferred from cyclic equivariance. -/
theorem kleinBrioschiOrbitPolynomial_eq_resolvent_of_injective
    (z : ℂ × ℂ) (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0)
    (hinj : Function.Injective (kleinBrioschiRootTuple z)) :
    kleinBrioschiOrbitPolynomial z =
      brioschiResolvent (brioschiParameter z.1 z.2) := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (kleinBrioschiOrbitPolynomial z -
      brioschiResolvent (brioschiParameter z.1 z.2)) hinj
  · intro k
    rw [Polynomial.eval_sub, kleinBrioschiOrbitPolynomial_root z k]
    have hr := kleinBrioschiOrbitRoot_is_root z k hT
    simpa [kleinBrioschiRootTuple] using hr
  · have hOrbit : Polynomial.IsMonicOfDegree (kleinBrioschiOrbitPolynomial z) 5 := by
      constructor
      · simp [kleinBrioschiOrbitPolynomial]
      · exact kleinBrioschiOrbitPolynomial_monic z
    exact (hOrbit.natDegree_sub_lt (by norm_num)
      (brioschiResolvent_isMonicOfDegree _)).trans_eq
      (by norm_num)

/-- The Brioschi orbit polynomial is realized by the squared evaluation
resolvent of a source-ordered binary quintic. Here the principal complex
square root selects one definite lift of each of the five root values; the
resulting construction is explicit but is not claimed to be `A₅`-equivariant. -/
def binaryQuinticBrioschiPreimage (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1)) : BinaryQuinticCoefficientSpace :=
  binaryQuinticOrbitEvaluationInterpolant z hfirst hnodes
    (fun k => Complex.sqrt (kleinBrioschiRootTuple z k))

/-- The explicit principal-root interpolation has exactly the Brioschi orbit
polynomial as its squared evaluation resolvent. -/
theorem binaryQuinticBrioschiPreimage_spec (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1)) :
    binaryQuinticEvaluationResolvent
        (binaryQuinticBrioschiPreimage z hfirst hnodes) z =
      kleinBrioschiOrbitPolynomial z := by
  have heval := binaryQuinticOrbitEvaluationInterpolant_spec z hfirst hnodes
    (fun k => Complex.sqrt (kleinBrioschiRootTuple z k))
  have htuple : binaryQuinticResolventTuple
      (binaryQuinticBrioschiPreimage z hfirst hnodes) z =
      kleinBrioschiRootTuple z := by
    funext k
    change binaryQuinticSignedOrbit
        (binaryQuinticBrioschiPreimage z hfirst hnodes) z k ^ 2 = _
    have hk := congrFun heval k
    change binaryQuinticSignedOrbit
        (binaryQuinticBrioschiPreimage z hfirst hnodes) z k = _ at hk
    rw [hk]
    exact complexSqrt_sq (kleinBrioschiRootTuple z k)
  unfold binaryQuinticEvaluationResolvent kleinBrioschiOrbitPolynomial
  rw [htuple]

/-- Existential form of the explicit construction, retained for consumers
that need only a witness. -/
theorem exists_binaryQuinticEvaluationResolvent_eq_kleinBrioschiOrbitPolynomial
    (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1)) :
    ∃ v : BinaryQuinticCoefficientSpace,
      binaryQuinticEvaluationResolvent v z = kleinBrioschiOrbitPolynomial z := by
  exact ⟨binaryQuinticBrioschiPreimage z hfirst hnodes,
    binaryQuinticBrioschiPreimage_spec z hfirst hnodes⟩

/-- Under the generic hypotheses making the five Brioschi orbit values
distinct and roots of the displayed Brioschi quintic, that quintic is the
evaluation resolvent of some binary-quintic coefficient vector.  The vector
is noncanonical: it is obtained by square-root choices and interpolation. -/
theorem exists_binaryQuinticEvaluationResolvent_eq_brioschiResolvent
    (z : ℂ × ℂ) (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (hnodes : Function.Injective
      (fun k : Fin 5 => (kleinOrderFiveIterate k.val z).2 /
        (kleinOrderFiveIterate k.val z).1))
    (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0)
    (hinj : Function.Injective (kleinBrioschiRootTuple z)) :
    ∃ v : BinaryQuinticCoefficientSpace,
      binaryQuinticEvaluationResolvent v z =
        brioschiResolvent (brioschiParameter z.1 z.2) := by
  obtain ⟨v, hv⟩ :=
    exists_binaryQuinticEvaluationResolvent_eq_kleinBrioschiOrbitPolynomial
      z hfirst hnodes
  exact ⟨v, hv.trans
    (kleinBrioschiOrbitPolynomial_eq_resolvent_of_injective z hT hinj)⟩

/-- There is a nondegenerate affine specialization and a source-ordered
binary-quintic coefficient vector whose evaluation resolvent is exactly the
displayed Brioschi quintic.  The vector is obtained noncanonically by
interpolating square roots of the five explicit orbit roots. -/
theorem exists_brioschi_evaluation_resolvent_specialization :
    ∃ t : ℂ, ∃ v : BinaryQuinticCoefficientSpace,
      kleinIcosahedralEdgeT 1 t ≠ 0 ∧
      Function.Injective (kleinBrioschiRootTuple (1, t)) ∧
      binaryQuinticEvaluationResolvent v (1, t) =
        brioschiResolvent (brioschiParameter 1 t) := by
  obtain ⟨t, hT, hinj⟩ :=
    exists_brioschiSlice_parameter_with_injective_root_tuple
  have ht : t ≠ 0 := by
    intro hzero
    subst t
    exact kleinBrioschiRootTuple_not_injective_degenerate hinj
  obtain ⟨v, hv⟩ := exists_binaryQuinticEvaluationResolvent_eq_brioschiResolvent
    (1, t) (kleinOrderFiveAffineOrbit_first_ne_zero t)
    (kleinOrderFiveAffineOrbit_nodes_injective ht) hT hinj
  exact ⟨t, v, hT, hinj, hv⟩

/-- The slice separation polynomial is an explicit sufficient genericity
condition for identifying the Klein orbit polynomial with the Brioschi
quintic. -/
theorem kleinBrioschiOrbitPolynomial_eq_resolvent_of_slice_distinctness
    (t : ℂ)
    (hsep : brioschiSliceDistinctnessPolynomial.eval t ≠ 0) :
    kleinBrioschiOrbitPolynomial (1, t) =
      brioschiResolvent (brioschiParameter 1 t) := by
  obtain ⟨hT, hinj⟩ := kleinBrioschiRootTuple_injective_of_slice_distinctness t hsep
  exact kleinBrioschiOrbitPolynomial_eq_resolvent_of_injective (1, t) hT hinj

/-- The nonzero separation polynomial has at least one nonvanishing
specialization on the normalized slice. -/
theorem exists_brioschiSlice_parameter_with_nonzero_separation :
    ∃ t : ℂ, brioschiSliceDistinctnessPolynomial.eval t ≠ 0 := by
  have hp := brioschiSliceDistinctnessPolynomial_ne_zero
  have hcard : brioschiSliceDistinctnessPolynomial.natDegree < Cardinal.mk ℂ :=
    lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.aleph0_le_mk ℂ)
  obtain ⟨t, ht⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card
    brioschiSliceDistinctnessPolynomial hp hcard
  exact ⟨t, ht⟩

/-- Projective transport of the generic slice identity: for every binary
coordinate pair with nonzero first coordinate, nonvanishing of the slice
separation polynomial at `z₂ / z₁` identifies its orbit product with the
Brioschi quintic. -/
theorem kleinBrioschiOrbitPolynomial_eq_resolvent_of_projective_chart
    (z₁ z₂ : ℂ) (hz₁ : z₁ ≠ 0)
    (hsep : brioschiSliceDistinctnessPolynomial.eval (z₂ / z₁) ≠ 0) :
    kleinBrioschiOrbitPolynomial (z₁, z₂) =
      brioschiResolvent (brioschiParameter z₁ z₂) := by
  let t := z₂ / z₁
  have hzt : z₁ * t = z₂ := by
    dsimp [t]
    field_simp [hz₁]
  have hcoords : (z₁ * 1, z₁ * t) = (z₁, z₂) := by
    simp [hzt]
  have hT₀ : kleinIcosahedralEdgeT 1 t ≠ 0 :=
    (kleinBrioschiRootTuple_injective_of_slice_distinctness t hsep).1
  have hOrbitScale : kleinBrioschiOrbitPolynomial (z₁, z₂) =
      kleinBrioschiOrbitPolynomial (1, t) := by
    calc
      kleinBrioschiOrbitPolynomial (z₁, z₂) =
          kleinBrioschiOrbitPolynomial (z₁ * 1, z₁ * t) := by rw [← hcoords]
      _ = kleinBrioschiOrbitPolynomial (1, t) := by
        simpa using kleinBrioschiOrbitPolynomial_scale z₁ (1, t) hz₁ hT₀
  have hParamScale : brioschiParameter z₁ z₂ =
      brioschiParameter 1 t := by
    calc
      brioschiParameter z₁ z₂ = brioschiParameter (z₁ * 1) (z₁ * t) := by
        rw [mul_one, hzt]
      _ = brioschiParameter 1 t := by
        exact brioschiParameter_scale z₁ 1 t hz₁ hT₀
  calc
    kleinBrioschiOrbitPolynomial (z₁, z₂) =
        kleinBrioschiOrbitPolynomial (1, t) := hOrbitScale
    _ = brioschiResolvent (brioschiParameter 1 t) :=
      kleinBrioschiOrbitPolynomial_eq_resolvent_of_slice_distinctness t hsep
    _ = brioschiResolvent (brioschiParameter z₁ z₂) := by rw [← hParamScale]

/-- Every projective chart with nonzero first coordinate contains a point
where the five-root orbit polynomial is exactly the Brioschi resolvent.
The chosen point avoids the finite exceptional set detected by the slice
separation polynomial. -/
theorem exists_projective_chart_resolvent_specialization
    (z₁ : ℂ) (hz₁ : z₁ ≠ 0) :
    ∃ z₂ : ℂ,
      kleinIcosahedralEdgeT z₁ z₂ ≠ 0 ∧
      kleinBrioschiOrbitPolynomial (z₁, z₂) =
        brioschiResolvent (brioschiParameter z₁ z₂) := by
  obtain ⟨t, hsep⟩ := exists_brioschiSlice_parameter_with_nonzero_separation
  have hT₀ : kleinIcosahedralEdgeT 1 t ≠ 0 :=
    (kleinBrioschiRootTuple_injective_of_slice_distinctness t hsep).1
  have hTscale := kleinIcosahedralEdgeT_homog z₁ 1 t
  rw [mul_one] at hTscale
  have hT : kleinIcosahedralEdgeT z₁ (z₁ * t) ≠ 0 := by
    rw [hTscale]
    exact mul_ne_zero (pow_ne_zero 30 hz₁) hT₀
  refine ⟨z₁ * t, hT, ?_⟩
  apply kleinBrioschiOrbitPolynomial_eq_resolvent_of_projective_chart
    z₁ (z₁ * t) hz₁
  have hratio : (z₁ * t) / z₁ = t := by
    field_simp [hz₁]
  simpa [hratio] using hsep

/-- The orbit-polynomial identification holds for all but finitely many
parameters on the slice `(1,t)`. The exceptional set is contained in the
zero set of the explicit nonzero separation polynomial. -/
theorem eventually_kleinBrioschiOrbitPolynomial_eq_resolvent_on_slice :
    ∀ᶠ t : ℂ in Filter.cofinite,
      kleinBrioschiOrbitPolynomial (1, t) =
        brioschiResolvent (brioschiParameter 1 t) := by
  have hevent := Polynomial.eventually_cofinite_not_isRoot
    brioschiSliceDistinctnessPolynomial_ne_zero
  filter_upwards [hevent] with t ht
  apply kleinBrioschiOrbitPolynomial_eq_resolvent_of_slice_distinctness
  exact ht

/-- A concrete nondegenerate specialization of the nonlinear five-root
construction is exactly the Brioschi quintic, with no distinctness hypothesis
left as external input. -/
theorem exists_kleinBrioschiOrbitPolynomial_eq_resolvent_specialization :
    ∃ t : ℂ,
      kleinIcosahedralEdgeT 1 t ≠ 0 ∧
      Function.Injective (kleinBrioschiRootTuple (1, t)) ∧
      kleinBrioschiOrbitPolynomial (1, t) =
        brioschiResolvent (brioschiParameter 1 t) := by
  obtain ⟨t, hT, hinj⟩ :=
    exists_brioschiSlice_parameter_with_injective_root_tuple
  exact ⟨t, hT, hinj,
    kleinBrioschiOrbitPolynomial_eq_resolvent_of_injective (1, t) hT hinj⟩

end InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
