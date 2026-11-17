/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesHermitianMatrixBridge
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

/-!
# Reversion norms and current sandwiches in the native real spacetime algebra

The carrier is the existing `HestenesCl14.Cl14`, with its actual Mathlib
Clifford product and reversion. The existing equivalence of the whole even
algebra with the Pauli algebra is used to prove reversion and norm identities;
it does not replace the Clifford carrier by a smaller model.

The real numbers below are the coefficients of `1` and `volumeEven` in the
proved reversion-product decomposition. This file does not introduce a scalar
projection on arbitrary Clifford elements. In particular the scalar coefficient
of `(a + b I) I` is `-b`, since `I * I = -1`.

The current conclusions are algebraic identities. Grade-one identification,
positive observer flux, PDE continuity, and hypersurface integration are
separate statements and are not inferred here from covariance.
-/

noncomputable section

namespace HestenesCurrentAlgebra

open HestenesCl14 HestenesPauliSheetBridge HestenesEvenPauliEquiv
open HestenesKreinMatrixBridge HestenesHermitianAdjoint
open HestenesHermitianMatrixBridge

private theorem adjugate_add_two (A B : HestenesPauliSheetBridge.Sheet) :
    Matrix.adjugate (A + B) = Matrix.adjugate A + Matrix.adjugate B := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two]

private theorem adjugate_paravector (v : V14) :
    Matrix.adjugate (paravector v) = paravectorConj v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, paravector, paravectorConj]

private theorem adjugate_paravectorConj (v : V14) :
    Matrix.adjugate (paravectorConj v) = paravector v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, paravector, paravectorConj]

theorem reverseEven_pair (u v : V14) :
    reverseEven ((CliffordAlgebra.even.ι Q14).bilin u v) =
      (CliffordAlgebra.even.ι Q14).bilin v u := by
  apply Subtype.ext
  change CliffordAlgebra.reverse
      (CliffordAlgebra.ι Q14 u * CliffordAlgebra.ι Q14 v) =
    CliffordAlgebra.ι Q14 v * CliffordAlgebra.ι Q14 u
  simp only [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι]

private theorem clPlusToPauli_reverseEven_pair (u v : V14) :
    clPlusToPauli (reverseEven ((CliffordAlgebra.even.ι Q14).bilin u v)) =
      Matrix.adjugate (clPlusToPauli ((CliffordAlgebra.even.ι Q14).bilin u v)) := by
  rw [reverseEven_pair, clPlusToPauli_on_pair, clPlusToPauli_on_pair,
    Matrix.adjugate_mul_distrib, adjugate_paravectorConj, adjugate_paravector]

/-- Reversion on the entire native even Clifford algebra is transported to
the two-by-two adjugate. No invertibility assumption on the spinor is used. -/
theorem clPlusToPauli_reverseEven (ψ : ClPlus14) :
    clPlusToPauli (reverseEven ψ) = Matrix.adjugate (clPlusToPauli ψ) := by
  rcases ψ with ⟨ψ, hψ⟩
  induction ψ, hψ using CliffordAlgebra.even_induction with
  | algebraMap r =>
      have hr : reverseEven
          (⟨algebraMap ℝ Cl14 r, SetLike.algebraMap_mem_graded _ _⟩ : ClPlus14) =
          algebraMap ℝ ClPlus14 r := by
        apply Subtype.ext
        exact CliffordAlgebra.reverse.commutes r
      have hs :
          (⟨algebraMap ℝ Cl14 r, SetLike.algebraMap_mem_graded _ _⟩ : ClPlus14) =
            algebraMap ℝ ClPlus14 r := rfl
      rw [hr, hs]
      simp only [clPlusToPauli.commutes, Matrix.algebraMap_eq_diagonal]
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.adjugate_fin_two]
  | add x y hx hy ihx ihy =>
      change clPlusToPauli (reverseEven (⟨x, hx⟩ + ⟨y, hy⟩)) =
        Matrix.adjugate (clPlusToPauli (⟨x, hx⟩ + ⟨y, hy⟩))
      rw [reverseEven_add, map_add, map_add, adjugate_add_two, ihx, ihy]
  | ι_mul_ι_mul u v x hx ihx =>
      let p : ClPlus14 := (CliffordAlgebra.even.ι Q14).bilin u v
      let z : ClPlus14 := ⟨x, hx⟩
      change clPlusToPauli (reverseEven (p * z)) =
        Matrix.adjugate (clPlusToPauli (p * z))
      rw [reverseEven_mul, map_mul, map_mul, Matrix.adjugate_mul_distrib,
        ihx, clPlusToPauli_reverseEven_pair]

/-- The scalar coefficient of the native reversion product. -/
def scalarInvariant (ψ : ClPlus14) : ℝ := (clPlusToPauli ψ).det.re

/-- The coefficient of the native pseudoscalar in the reversion product. -/
def pseudoscalarInvariant (ψ : ClPlus14) : ℝ := (clPlusToPauli ψ).det.im

theorem mul_reverseEven_eq_lift (ψ : ClPlus14) :
    ψ * reverseEven ψ = liftComplexCoeff (clPlusToPauli ψ).det 1 := by
  apply clPlusToPauli_injective
  rw [map_mul, clPlusToPauli_reverseEven, clPlusToPauli_liftComplexCoeff, map_one]
  exact Matrix.mul_adjugate _

theorem reverseEven_mul_eq_lift (ψ : ClPlus14) :
    reverseEven ψ * ψ = liftComplexCoeff (clPlusToPauli ψ).det 1 := by
  apply clPlusToPauli_injective
  rw [map_mul, clPlusToPauli_reverseEven, clPlusToPauli_liftComplexCoeff, map_one]
  exact Matrix.adjugate_mul _

/-- Scalar--pseudoscalar decomposition is derived for every even spinor,
including zero divisors. -/
theorem mul_reverseEven_decomposition (ψ : ClPlus14) :
    ψ * reverseEven ψ =
      scalarInvariant ψ • (1 : ClPlus14) + pseudoscalarInvariant ψ • volumeEven := by
  simpa only [liftComplexCoeff, mul_one, scalarInvariant, pseudoscalarInvariant]
    using mul_reverseEven_eq_lift ψ

theorem reverseEven_mul_eq_mul_reverseEven (ψ : ClPlus14) :
    reverseEven ψ * ψ = ψ * reverseEven ψ :=
  (reverseEven_mul_eq_lift ψ).trans (mul_reverseEven_eq_lift ψ).symm

theorem liftComplexCoeff_one_commute (z : ℂ) (ψ : ClPlus14) :
    Commute (liftComplexCoeff z 1) ψ := by
  change liftComplexCoeff z 1 * ψ = ψ * liftComplexCoeff z 1
  apply clPlusToPauli_injective
  simp only [map_mul, clPlusToPauli_liftComplexCoeff, map_one]
  simp [smul_mul_assoc, mul_smul_comm]

theorem liftComplexCoeff_one_mul (z w : ℂ) :
    liftComplexCoeff z 1 * liftComplexCoeff w 1 = liftComplexCoeff (z * w) 1 := by
  apply clPlusToPauli_injective
  simp only [map_mul, clPlusToPauli_liftComplexCoeff, map_one]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem reverseEven_liftComplexCoeff_one (z : ℂ) :
    reverseEven (liftComplexCoeff z 1) = liftComplexCoeff z 1 := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_reverseEven]
  simp only [clPlusToPauli_liftComplexCoeff, map_one]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two]

theorem hestenesAdjoint_liftComplexCoeff_one (z : ℂ) :
    hestenesAdjoint (liftComplexCoeff z 1) = liftComplexCoeff (star z) 1 := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_hestenesAdjoint, clPlusToPauli_liftComplexCoeff,
    clPlusToPauli_liftComplexCoeff, map_one]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

theorem gamma_zero_conjugate_liftComplexCoeff_one (z : ℂ) :
    gamma 0 * (liftComplexCoeff z 1 : Cl14) * gamma 0 =
      (liftComplexCoeff (star z) 1 : Cl14) := by
  have hr := congrArg Subtype.val (reverseEven_liftComplexCoeff_one z)
  have h := congrArg Subtype.val (hestenesAdjoint_liftComplexCoeff_one z)
  change CliffordAlgebra.reverse (liftComplexCoeff z 1 : Cl14) =
    (liftComplexCoeff z 1 : Cl14) at hr
  change gamma 0 * CliffordAlgebra.reverse (liftComplexCoeff z 1 : Cl14) * gamma 0 =
    (liftComplexCoeff (star z) 1 : Cl14) at h
  rwa [hr] at h

theorem gamma_zero_mul_liftComplexCoeff_one (z : ℂ) :
    gamma 0 * (liftComplexCoeff z 1 : Cl14) =
      (liftComplexCoeff (star z) 1 : Cl14) * gamma 0 := by
  have h := congrArg (fun a : Cl14 => a * gamma 0)
    (gamma_zero_conjugate_liftComplexCoeff_one z)
  simpa only [mul_assoc, gamma_zero_sq, mul_one] using h

theorem gamma_three_mul_liftComplexCoeff_one (z : ℂ) :
    gamma 3 * (liftComplexCoeff z 1 : Cl14) =
      (liftComplexCoeff (star z) 1 : Cl14) * gamma 3 := by
  have hγ : gamma 3 = (sigmaEven 2 : Cl14) * gamma 0 := by
    change gamma 3 = (gamma 3 * gamma 0) * gamma 0
    simp only [mul_assoc, gamma_zero_sq, mul_one]
  have hc := congrArg Subtype.val (liftComplexCoeff_one_commute (star z) (sigmaEven 2)).eq
  change (liftComplexCoeff (star z) 1 : Cl14) * (sigmaEven 2 : Cl14) =
    (sigmaEven 2 : Cl14) * (liftComplexCoeff (star z) 1 : Cl14) at hc
  calc
    gamma 3 * (liftComplexCoeff z 1 : Cl14) =
        (sigmaEven 2 : Cl14) * (gamma 0 * (liftComplexCoeff z 1 : Cl14)) := by
      rw [hγ, mul_assoc]
    _ = (sigmaEven 2 : Cl14) * ((liftComplexCoeff (star z) 1 : Cl14) * gamma 0) := by
      rw [gamma_zero_mul_liftComplexCoeff_one]
    _ = ((liftComplexCoeff (star z) 1 : Cl14) * (sigmaEven 2 : Cl14)) * gamma 0 := by
      rw [← mul_assoc, ← hc]
    _ = (liftComplexCoeff (star z) 1 : Cl14) * gamma 3 := by rw [mul_assoc, ← hγ]

theorem liftComplexCoeff_star_mul_self (z : ℂ) :
    liftComplexCoeff (star z) 1 * liftComplexCoeff z 1 =
      (z.re ^ 2 + z.im ^ 2) • (1 : ClPlus14) := by
  rw [liftComplexCoeff_one_mul]
  have hz : star z * z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_apply]
    simp only [pow_two]
  rw [hz]
  simp [liftComplexCoeff]

theorem volumeEven_sq : volumeEven * volumeEven = -(1 : ClPlus14) := by
  apply clPlusToPauli_injective
  rw [map_mul, clPlusToPauli_volumeEven, map_neg, map_one]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_sq]

/-- Multiplication by the pseudoscalar negates its previous coefficient. -/
theorem mul_reverseEven_mul_volumeEven (ψ : ClPlus14) :
    (ψ * reverseEven ψ) * volumeEven =
      (-pseudoscalarInvariant ψ) • (1 : ClPlus14) + scalarInvariant ψ • volumeEven := by
  rw [mul_reverseEven_decomposition, add_mul, smul_mul_assoc, smul_mul_assoc,
    one_mul, volumeEven_sq]
  simp only [smul_neg, neg_smul]
  exact add_comm _ _

/-- The actual Clifford sandwich; the insertion need not be a vector. -/
def sandwich (ψ : ClPlus14) (v : Cl14) : Cl14 :=
  (ψ : Cl14) * v * CliffordAlgebra.reverse (ψ : Cl14)

def diracCurrent (ψ : ClPlus14) : Cl14 := sandwich ψ (gamma 0)

def axialCurrent (ψ : ClPlus14) : Cl14 := sandwich ψ (gamma 3)

/-- Covariance of the sandwich under left spinor multiplication. Rotor
normalization is not needed for this identity. -/
theorem sandwich_mul_left (R ψ : ClPlus14) (v : Cl14) :
    sandwich (R * ψ) v = (R : Cl14) * sandwich ψ v * CliffordAlgebra.reverse (R : Cl14) := by
  change ((R : Cl14) * (ψ : Cl14)) * v *
      CliffordAlgebra.reverse ((R : Cl14) * (ψ : Cl14)) = _
  rw [CliffordAlgebra.reverse.map_mul]
  simp only [sandwich, mul_assoc]

theorem diracCurrent_mul_left (R ψ : ClPlus14) :
    diracCurrent (R * ψ) =
      (R : Cl14) * diracCurrent ψ * CliffordAlgebra.reverse (R : Cl14) :=
  sandwich_mul_left R ψ (gamma 0)

theorem axialCurrent_mul_left (R ψ : ClPlus14) :
    axialCurrent (R * ψ) =
      (R : Cl14) * axialCurrent ψ * CliffordAlgebra.reverse (R : Cl14) :=
  sandwich_mul_left R ψ (gamma 3)

theorem reverse_sandwich_gamma (ψ : ClPlus14) (i : Fin 4) :
    CliffordAlgebra.reverse (sandwich ψ (gamma i)) = sandwich ψ (gamma i) := by
  simp only [sandwich, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_reverse, gamma, CliffordAlgebra.reverse_ι, mul_assoc]

theorem sandwich_gamma_mem_odd (ψ : ClPlus14) (i : Fin 4) :
    sandwich ψ (gamma i) ∈ CliffordAlgebra.evenOdd Q14 1 := by
  have hψ : (ψ : Cl14) ∈ CliffordAlgebra.evenOdd Q14 0 := ψ.2
  have hγ : gamma i ∈ CliffordAlgebra.evenOdd Q14 1 :=
    CliffordAlgebra.ι_mem_evenOdd_one Q14 (basisVec i)
  have hr : CliffordAlgebra.reverse (ψ : Cl14) ∈ CliffordAlgebra.evenOdd Q14 0 :=
    CliffordAlgebra.reverse_mem_evenOdd_iff.mpr hψ
  have hp := SetLike.mul_mem_graded hψ hγ
  have hq := SetLike.mul_mem_graded hp hr
  simpa only [zero_add, add_zero] using hq

/-- The right paravector of the current is the native Hermitian Gram product. -/
theorem diracCurrent_mul_gamma_zero (ψ : ClPlus14) :
    diracCurrent ψ * gamma 0 = (ψ * hestenesAdjoint ψ : ClPlus14) := by
  change ((ψ : Cl14) * gamma 0 * CliffordAlgebra.reverse (ψ : Cl14)) * gamma 0 =
    (ψ : Cl14) * (gamma 0 * CliffordAlgebra.reverse (ψ : Cl14) * gamma 0)
  simp only [mul_assoc]

private theorem sandwich_mul_of_twist (ψ : ClPlus14) (u v : Cl14)
    (hu : u * (liftComplexCoeff (clPlusToPauli ψ).det 1 : Cl14) =
      (liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) * u) :
    sandwich ψ u * sandwich ψ v =
      (liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) *
        (ψ : Cl14) * (u * v) * CliffordAlgebra.reverse (ψ : Cl14) := by
  have hn := congrArg Subtype.val (reverseEven_mul_eq_lift ψ)
  change CliffordAlgebra.reverse (ψ : Cl14) * (ψ : Cl14) =
    (liftComplexCoeff (clPlusToPauli ψ).det 1 : Cl14) at hn
  have hc := congrArg Subtype.val
    (liftComplexCoeff_one_commute (star (clPlusToPauli ψ).det) ψ).eq
  change (liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) * (ψ : Cl14) =
    (ψ : Cl14) * (liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) at hc
  calc
    sandwich ψ u * sandwich ψ v =
        (ψ : Cl14) * u * (CliffordAlgebra.reverse (ψ : Cl14) * (ψ : Cl14)) *
          v * CliffordAlgebra.reverse (ψ : Cl14) := by simp only [sandwich, mul_assoc]
    _ = (ψ : Cl14) *
        (u * (liftComplexCoeff (clPlusToPauli ψ).det 1 : Cl14)) *
          v * CliffordAlgebra.reverse (ψ : Cl14) := by rw [hn, mul_assoc (ψ : Cl14) u]
    _ = (ψ : Cl14) *
        ((liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) * u) *
          v * CliffordAlgebra.reverse (ψ : Cl14) := by rw [hu]
    _ = (liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) *
        (ψ : Cl14) * (u * v) * CliffordAlgebra.reverse (ψ : Cl14) := by
      rw [← mul_assoc (ψ : Cl14), ← hc]
      simp only [mul_assoc]

private theorem norm_factorization (ψ : ClPlus14) :
    (liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) *
        (ψ : Cl14) * CliffordAlgebra.reverse (ψ : Cl14) =
      (scalarInvariant ψ ^ 2 + pseudoscalarInvariant ψ ^ 2) • (1 : Cl14) := by
  have hn := congrArg Subtype.val (mul_reverseEven_eq_lift ψ)
  change (ψ : Cl14) * CliffordAlgebra.reverse (ψ : Cl14) =
    (liftComplexCoeff (clPlusToPauli ψ).det 1 : Cl14) at hn
  rw [mul_assoc, hn]
  exact congrArg Subtype.val (liftComplexCoeff_star_mul_self (clPlusToPauli ψ).det)

/-- The exact Fierz square in the native Clifford algebra. -/
theorem diracCurrent_sq (ψ : ClPlus14) :
    diracCurrent ψ * diracCurrent ψ =
      (scalarInvariant ψ ^ 2 + pseudoscalarInvariant ψ ^ 2) • (1 : Cl14) := by
  rw [diracCurrent, sandwich_mul_of_twist ψ (gamma 0) (gamma 0)
    (gamma_zero_mul_liftComplexCoeff_one _), gamma_zero_sq, mul_one]
  exact norm_factorization ψ

theorem axialCurrent_sq (ψ : ClPlus14) :
    axialCurrent ψ * axialCurrent ψ =
      -((scalarInvariant ψ ^ 2 + pseudoscalarInvariant ψ ^ 2) • (1 : Cl14)) := by
  rw [axialCurrent, sandwich_mul_of_twist ψ (gamma 3) (gamma 3)
    (gamma_three_mul_liftComplexCoeff_one _), gamma_three_sq]
  simpa only [mul_neg, mul_one, neg_mul] using congrArg Neg.neg (norm_factorization ψ)

/-- Orthogonality as an exact vanishing Clifford anticommutator. -/
theorem diracCurrent_axialCurrent_anticomm (ψ : ClPlus14) :
    diracCurrent ψ * axialCurrent ψ + axialCurrent ψ * diracCurrent ψ = 0 := by
  rw [diracCurrent, axialCurrent,
    sandwich_mul_of_twist ψ (gamma 0) (gamma 3) (gamma_zero_mul_liftComplexCoeff_one _),
    sandwich_mul_of_twist ψ (gamma 3) (gamma 0) (gamma_three_mul_liftComplexCoeff_one _)]
  calc
    _ = (liftComplexCoeff (star (clPlusToPauli ψ).det) 1 : Cl14) * (ψ : Cl14) *
        (gamma 0 * gamma 3 + gamma 3 * gamma 0) * CliffordAlgebra.reverse (ψ : Cl14) := by
      noncomm_ring
    _ = 0 := by rw [gamma_anticomm (by decide)]; simp

theorem current_norm_coefficient_nonneg (ψ : ClPlus14) :
    0 ≤ scalarInvariant ψ ^ 2 + pseudoscalarInvariant ψ ^ 2 := by positivity

/-- Normalization of a native even rotor fixes its Pauli determinant. -/
theorem det_eq_one_of_mul_reverseEven_eq_one (R : ClPlus14)
    (hR : R * reverseEven R = 1) : (clPlusToPauli R).det = 1 := by
  have hm := congrArg clPlusToPauli hR
  rw [map_mul, clPlusToPauli_reverseEven, Matrix.mul_adjugate, map_one] at hm
  have h00 := congrArg (fun A : HestenesPauliSheetBridge.Sheet => A 0 0) hm
  simpa using h00

theorem scalarInvariant_mul_left (R ψ : ClPlus14) (hR : R * reverseEven R = 1) :
    scalarInvariant (R * ψ) = scalarInvariant ψ := by
  simp only [scalarInvariant, map_mul, Matrix.det_mul,
    det_eq_one_of_mul_reverseEven_eq_one R hR, one_mul]

theorem pseudoscalarInvariant_mul_left (R ψ : ClPlus14) (hR : R * reverseEven R = 1) :
    pseudoscalarInvariant (R * ψ) = pseudoscalarInvariant ψ := by
  simp only [pseudoscalarInvariant, map_mul, Matrix.det_mul,
    det_eq_one_of_mul_reverseEven_eq_one R hR, one_mul]

/-- Algebraic invariant of normalized left multiplication; no PDE or
statement about time-dependent growth is implicit in this equality. -/
theorem diracCurrent_sq_mul_left (R ψ : ClPlus14) (hR : R * reverseEven R = 1) :
    diracCurrent (R * ψ) * diracCurrent (R * ψ) = diracCurrent ψ * diracCurrent ψ := by
  rw [diracCurrent_sq, diracCurrent_sq, scalarInvariant_mul_left R ψ hR,
    pseudoscalarInvariant_mul_left R ψ hR]

end HestenesCurrentAlgebra

end noncomputable section
