/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The finite split-Clifford/projective matrix bridge

This owner records the concrete real matrix atom behind the Witt basis.  It
proves the nilpotent CAR relations, the complementary coordinate projectors,
the split Cartan action, and its induced dilation on the affine projective
coordinate.  It does not identify a quotient with `ℝP¹` or `ℂP¹`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge

open Matrix

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

def e0 : M2R := !![0, 1; 1, 0]

def e1 : M2R := !![0, 1; -1, 0]

def b : M2R := (1 / 2 : ℝ) • (e0 + e1)

def bdag : M2R := (1 / 2 : ℝ) • (e0 - e1)

def cartan : M2R := e0 * e1

def Pminus : M2R := b * bdag

def Pplus : M2R := bdag * b

theorem e0_sq : e0 * e0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, Matrix.mul_apply, Fin.sum_univ_two]

theorem e1_sq : e1 * e1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem e0_e1_anticomm : e0 * e1 + e1 * e0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem b_sq : b * b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bdag_sq : bdag * bdag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem b_bdag_add_bdag_b : b * bdag + bdag * b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cartan_sq : cartan * cartan = 1 := by
  unfold cartan
  calc
    (e0 * e1) * (e0 * e1) = -(e0 * e0) * (e1 * e1) := by
      have h : e1 * e0 = -(e0 * e1) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [e0, e1, Matrix.mul_apply, Fin.sum_univ_two]
      rw [show (e0 * e1) * (e0 * e1) = e0 * (e1 * e0) * e1 by noncomm_ring, h]
      noncomm_ring
    _ = 1 := by rw [e0_sq, e1_sq]; simp

theorem Pminus_eq_first_coordinate_projector :
    Pminus = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pminus, b, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Pplus_eq_second_coordinate_projector :
    Pplus = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pplus, b, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Pminus_sq : Pminus * Pminus = Pminus := by
  rw [Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Pplus_sq : Pplus * Pplus = Pplus := by
  rw [Pplus_eq_second_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Pminus_add_Pplus : Pminus + Pplus = 1 := by
  rw [Pminus_eq_first_coordinate_projector, Pplus_eq_second_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem cartan_eq_Pplus_sub_Pminus : cartan = Pplus - Pminus := by
  rw [Pplus_eq_second_coordinate_projector, Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, e0, e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem cartan_mul_b : cartan * b = -b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, b, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem b_mul_cartan : b * cartan = b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, b, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cartan_commutator_b : cartan * b - b * cartan = -2 • b := by
  rw [cartan_mul_b, b_mul_cartan]
  module

theorem cartan_mul_bdag : cartan * bdag = bdag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bdag_mul_cartan : bdag * cartan = -bdag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cartan_commutator_bdag : cartan * bdag - bdag * cartan = 2 • bdag := by
  rw [cartan_mul_bdag, bdag_mul_cartan]
  module

/-! ## Homogeneous two-chart projective point (finite matrix scope) -/

/-- The homogeneous Peirce point in the concrete real `2 × 2` matrix carrier.
The coordinates are scalars; this definition does not assert a topology or a
projective quotient construction. -/
def homogeneousPeircePoint (u v : ℝ) : M2R :=
  !![u ^ 2, u * v; u * v, v ^ 2]

/-- The unnormalized homogeneous point satisfies a scaled idempotency law. -/
theorem homogeneousPeircePoint_sq (u v : ℝ) :
    homogeneousPeircePoint u v * homogeneousPeircePoint u v =
      (u ^ 2 + v ^ 2) • homogeneousPeircePoint u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homogeneousPeircePoint, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Swapping the two Peirce sheets exchanges homogeneous coordinates. -/
theorem sheetSwap_homogeneousPeircePoint (u v : ℝ) :
    e0 * homogeneousPeircePoint u v * e0 = homogeneousPeircePoint v u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, homogeneousPeircePoint, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Exact commutator-square readout of the homogeneous point. This is a
finite-dimensional algebraic identity; it does not assert a Fubini–Study
metric on a projective space. -/
theorem homogeneousPeircePoint_commutator_sq (u v : ℝ) :
    (Pminus * homogeneousPeircePoint u v -
      homogeneousPeircePoint u v * Pminus) ^ 2 =
      -((u * v) ^ 2) • (1 : M2R) := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pminus_eq_first_coordinate_projector, homogeneousPeircePoint,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The unnormalized commutator-square readout is homogeneous of degree four
in the coordinate pair. Thus it is a polynomial on representatives, not by
itself a function on projective rays. -/
theorem homogeneousPeircePoint_variance_scale (u v c : ℝ) :
    -(4 : ℝ) •
        ((Pminus * homogeneousPeircePoint (c * u) (c * v) -
          homogeneousPeircePoint (c * u) (c * v) * Pminus) ^ 2) =
      c ^ 4 •
        (-(4 : ℝ) •
          ((Pminus * homogeneousPeircePoint u v -
            homogeneousPeircePoint u v * Pminus) ^ 2)) := by
  rw [homogeneousPeircePoint_commutator_sq, homogeneousPeircePoint_commutator_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply] <;> ring

/-- Affine-chart normalization of the homogeneous Peirce point. It is defined
only as a matrix-valued formula; a projective quotient is not part of this
owner. -/
def normalizedPeircePoint (u v : ℝ) : M2R :=
  (u ^ 2 + v ^ 2)⁻¹ • homogeneousPeircePoint u v

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- On the affine chart `u ≠ 0`, the concrete Peirce Bruhat polynomial with
`P = Pminus`, `U = e0`, `A = (v/u) • e0`, and
`C = (u*v/(u^2+v^2)) • e0` is exactly the normalized matrix point. This is a
matrix identity on an affine chart and does not use a projective quotient. -/
theorem peirceBruhat_affineChart_eq_normalizedPeircePoint
    (u v : ℝ) (hu : u ≠ 0) :
    Pminus + genPhi Pminus ((v / u) • e0)
        ((u * v / (u ^ 2 + v ^ 2)) • e0) -
      genSig Pminus ((v / u) • e0)
        ((u * v / (u ^ 2 + v ^ 2)) • e0) -
      genV Pminus ((v / u) • e0)
        ((u * v / (u ^ 2 + v ^ 2)) • e0) *
          conePlus Pminus ((v / u) • e0) =
      normalizedPeircePoint u v := by
  have hden : u ^ 2 + v ^ 2 ≠ 0 := by
    have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
    have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
    linarith
  let a : ℝ := v / u
  let c : ℝ := u * v / (u ^ 2 + v ^ 2)
  have hplus : conePlus Pminus ((v / u) • e0) = !![0, a; 0, 0] := by
    rw [Pminus_eq_first_coordinate_projector]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, conePlus, e0, Matrix.mul_apply, Matrix.smul_apply,
        Fin.sum_univ_two] <;> ring
  have hminus : coneMinus Pminus ((u * v / (u ^ 2 + v ^ 2)) • e0) =
      !![0, 0; c, 0] := by
    rw [Pminus_eq_first_coordinate_projector]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [c, coneMinus, e0, Matrix.mul_apply, Matrix.smul_apply,
        Fin.sum_univ_two] <;> ring
  have hphi : genPhi Pminus ((v / u) • e0)
      ((u * v / (u ^ 2 + v ^ 2)) • e0) = !![0, a; c, 0] := by
    rw [genPhi, hplus, hminus]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, c]
  have hsig : genSig Pminus ((v / u) • e0)
      ((u * v / (u ^ 2 + v ^ 2)) • e0) =
      !![a * c, 0; 0, -(a * c)] := by
    rw [genSig, hplus, hminus]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, a, c] <;> ring
  have hV : genV Pminus ((v / u) • e0)
      ((u * v / (u ^ 2 + v ^ 2)) • e0) = !![a * c, 0; 0, a * c] := by
    rw [genV, hplus, hminus]
    dsimp [anticomm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, a, c] <;> ring
  rw [hphi, hsig, hV, hplus, Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two,
      normalizedPeircePoint, homogeneousPeircePoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul, ↓reduceIte,
      Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero]
  all_goals field_simp [hu, hden] <;> dsimp [a, c] <;> field_simp [hu, hden] <;> ring

/-- The normalized matrix formula is idempotent. At `(u,v) = (0,0)` both sides
are zero by the field's totalized inverse convention; that point is not a
projective coordinate. -/
theorem normalizedPeircePoint_idempotent (u v : ℝ) :
    normalizedPeircePoint u v * normalizedPeircePoint u v =
      normalizedPeircePoint u v := by
  by_cases hden : u ^ 2 + v ^ 2 = 0
  · have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    subst u
    subst v
    simp [normalizedPeircePoint, homogeneousPeircePoint]
  · have hden' : u ^ 2 + v ^ 2 ≠ 0 := hden
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [normalizedPeircePoint, homogeneousPeircePoint, Matrix.mul_apply,
        Matrix.smul_apply, Fin.sum_univ_two] <;>
      field_simp [hden'] <;> ring

/-- The normalized matrix formula is invariant under exchanging the two
coordinates together with the sheet-swap matrix. -/
theorem sheetSwap_normalizedPeircePoint (u v : ℝ) :
    e0 * normalizedPeircePoint u v * e0 = normalizedPeircePoint v u := by
  have hden : (u ^ 2 + v ^ 2)⁻¹ = (v ^ 2 + u ^ 2)⁻¹ := by congr 1 <;> ring
  rw [normalizedPeircePoint, normalizedPeircePoint, hden]
  calc
    e0 * ((v ^ 2 + u ^ 2)⁻¹ • homogeneousPeircePoint u v) * e0 =
        (v ^ 2 + u ^ 2)⁻¹ •
          (e0 * homogeneousPeircePoint u v * e0) := by
            rw [mul_smul_comm, smul_mul_assoc]
    _ = (v ^ 2 + u ^ 2)⁻¹ • homogeneousPeircePoint v u := by
      rw [sheetSwap_homogeneousPeircePoint]

/-- Nonzero rescaling of a nonzero homogeneous coordinate pair leaves the
normalized matrix unchanged. This is a formula-level scaling law, not a
construction of a projective quotient. -/
theorem normalizedPeircePoint_scale (u v c : ℝ)
    (hc : c ≠ 0) (hs : u ^ 2 + v ^ 2 ≠ 0) :
    normalizedPeircePoint (c * u) (c * v) = normalizedPeircePoint u v := by
  have hden : c ^ 2 * (u ^ 2 + v ^ 2) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc) hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedPeircePoint, homogeneousPeircePoint, Matrix.smul_apply] <;>
    field_simp [hc, hs, hden] <;> ring

/-- Reciprocal affine coordinates give the same normalized matrix whenever
the reciprocal is defined. -/
theorem normalizedPeircePoint_reciprocal_chart (z : ℝ) (hz : z ≠ 0) :
    normalizedPeircePoint 1 z = normalizedPeircePoint z⁻¹ 1 := by
  have hs : (1 : ℝ) ^ 2 + z ^ 2 ≠ 0 := by nlinarith [sq_nonneg z]
  have hc : z⁻¹ ≠ 0 := inv_ne_zero hz
  have h := normalizedPeircePoint_scale 1 z z⁻¹ hc hs
  simpa [inv_mul_cancel₀ hz] using h.symm

/-- Sheet swap implements reciprocal-coordinate inversion on the normalized
affine chart, under the explicit nonzero-coordinate hypothesis. -/
theorem normalizedPeircePoint_mobius_inversion (z : ℝ) (hz : z ≠ 0) :
    normalizedPeircePoint 1 z =
      e0 * normalizedPeircePoint 1 z⁻¹ * e0 := by
  calc
    normalizedPeircePoint 1 z = normalizedPeircePoint z⁻¹ 1 :=
      normalizedPeircePoint_reciprocal_chart z hz
    _ = e0 * normalizedPeircePoint 1 z⁻¹ * e0 := by
      exact (sheetSwap_normalizedPeircePoint 1 z⁻¹).symm

/-- The normalized commutator has the expected reciprocal-denominator square.
At the zero pair, both sides vanish under the totalized inverse convention. -/
theorem normalizedPeircePoint_commutator_sq (u v : ℝ) :
    (Pminus * normalizedPeircePoint u v -
      normalizedPeircePoint u v * Pminus) ^ 2 =
      -(((u * v) / (u ^ 2 + v ^ 2)) ^ 2) • (1 : M2R) := by
  by_cases hden : u ^ 2 + v ^ 2 = 0
  · have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    subst u
    subst v
    simp [normalizedPeircePoint, homogeneousPeircePoint]
  · rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [normalizedPeircePoint, Pminus_eq_first_coordinate_projector,
        homogeneousPeircePoint, Matrix.mul_apply, Matrix.smul_apply,
        Fin.sum_univ_two] <;>
      field_simp [hden] <;> ring

/-- The scalar commutator-square profile is invariant under reciprocal
coordinate exchange. -/
theorem normalizedPeircePoint_profile_swap (u v : ℝ) :
    ((u * v) / (u ^ 2 + v ^ 2)) ^ 2 =
      ((v * u) / (v ^ 2 + u ^ 2)) ^ 2 := by
  ring

/-- The matrix-valued commutator-square readout of the normalized chart.
The coefficient is the finite algebraic variance profile; no metric tensor
or projective-space structure is asserted. -/
theorem normalizedPeircePoint_variance (u v : ℝ) :
    -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint u v -
          normalizedPeircePoint u v * Pminus) ^ 2) =
      (4 * ((u * v) / (u ^ 2 + v ^ 2)) ^ 2) • (1 : M2R) := by
  rw [normalizedPeircePoint_commutator_sq]
  module

/-- Reciprocal coordinate exchange preserves the matrix-valued variance
readout. -/
theorem normalizedPeircePoint_variance_swap (u v : ℝ) :
    -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint u v -
          normalizedPeircePoint u v * Pminus) ^ 2) =
      -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint v u -
          normalizedPeircePoint v u * Pminus) ^ 2) := by
  rw [normalizedPeircePoint_variance, normalizedPeircePoint_variance,
    normalizedPeircePoint_profile_swap]

/-- The normalized commutator-square readout is invariant under nonzero
rescaling of a nonzero coordinate pair. This is the representative-independent
version of the homogeneous degree-four formula. -/
theorem normalizedPeircePoint_variance_scale (u v c : ℝ)
    (hc : c ≠ 0) (hs : u ^ 2 + v ^ 2 ≠ 0) :
    -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint (c * u) (c * v) -
          normalizedPeircePoint (c * u) (c * v) * Pminus) ^ 2) =
      -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint u v -
          normalizedPeircePoint u v * Pminus) ^ 2) := by
  rw [normalizedPeircePoint_scale u v c hc hs]

/-- The commutator-square variance vanishes at the first Peirce anchor. -/
theorem normalizedPeircePoint_variance_first_anchor :
    -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint 1 0 -
          normalizedPeircePoint 1 0 * Pminus) ^ 2) = 0 := by
  rw [normalizedPeircePoint_variance]
  norm_num

/-- The commutator-square variance has unit value at the self-reciprocal
midpoint. -/
theorem normalizedPeircePoint_variance_midpoint_anchor :
    -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint 1 1 -
          normalizedPeircePoint 1 1 * Pminus) ^ 2) = 1 := by
  rw [normalizedPeircePoint_variance]
  norm_num

/-- The commutator-square variance vanishes at the complementary Peirce
anchor. -/
theorem normalizedPeircePoint_variance_second_anchor :
    -(4 : ℝ) •
        ((Pminus * normalizedPeircePoint 0 1 -
          normalizedPeircePoint 0 1 * Pminus) ^ 2) = 0 := by
  rw [normalizedPeircePoint_variance]
  norm_num

/-- The normalized point at the first coordinate anchor is the first Peirce
projector. -/
theorem normalizedPeircePoint_first_anchor :
    normalizedPeircePoint 1 0 = Pminus := by
  rw [Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedPeircePoint, homogeneousPeircePoint] <;> norm_num

/-- The normalized point at the self-reciprocal coordinate is the equal-sheet
projector. -/
theorem normalizedPeircePoint_midpoint_anchor :
    normalizedPeircePoint 1 1 = (1 / 2 : ℝ) • (1 + e0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedPeircePoint, homogeneousPeircePoint, e0] <;> norm_num

/-- The normalized point at the reciprocal endpoint is the complementary
Peirce projector. -/
theorem normalizedPeircePoint_second_anchor :
    normalizedPeircePoint 0 1 = Pplus := by
  rw [Pplus_eq_second_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedPeircePoint, homogeneousPeircePoint] <;> norm_num

end InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge

