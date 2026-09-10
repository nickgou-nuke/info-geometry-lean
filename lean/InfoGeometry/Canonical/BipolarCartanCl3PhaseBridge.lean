import InfoGeometry.Canonical.BipolarCartanPauliZornRealificationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.GullDoranPseudoscalarBridge
import Mathlib.Tactic

/-!
# Bipolar Cartan phase and the concrete real `Cl(3)` volume axis

Two repository owners use different coordinate orders for the realification of
`ℂ²`:

* `Cl11JordanComplexRealificationBridge` uses
  `(re z₀, re z₁, im z₀, im z₁)`;
* `GullDoranPseudoscalarBridge` uses
  `(re z₀, im z₀, re z₁, im z₁)`.

The explicit involutive permutation below converts between these conventions.
After conjugation by that permutation, the realification of scalar
multiplication by `I` is exactly the concrete real Pauli volume axis

`realSigma1 * realSigma2 * realSigma3 = realPhaseAxis`.

Consequently the compact bipolar Cartan direction is obtained from the
noncompact direction by the action of this concrete square-minus-one volume
axis in the interleaved real coordinates.

This is the exact finite `Cl(3)` matrix statement available in the repository.
It is not yet an identification with the grade-four pseudoscalar of a concrete
`Cl(1,3)` spacetime algebra, nor a construction of a Dirac or Nambu--Krein
module.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! The finite `4 × 4` coordinate computations below are intentionally
    kernel-reduced rather than delegated to an opaque certificate. -/
section

namespace InfoGeometry.Canonical.BipolarCartanCl3PhaseBridge

open scoped Matrix

open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Canonical.BipolarCartanPauliZornRealificationBridge
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open InfoGeometry.Physics.ChiralCausalCone

abbrev Matrix2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev Matrix4R := Matrix (Fin 4) (Fin 4) ℝ

/-- Permutation from block-real coordinates to interleaved complex coordinates. -/
def realificationOrderSwap : Matrix4R :=
  !![(1 : ℝ), 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

/-- The coordinate-order permutation is an involution. -/
@[simp] theorem realificationOrderSwap_sq :
    realificationOrderSwap * realificationOrderSwap = (1 : Matrix4R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realificationOrderSwap, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- Conjugation by an involutive permutation preserves multiplication. -/
theorem orderSwap_conjugation_mul (A B : Matrix4R) :
    realificationOrderSwap * (A * B) * realificationOrderSwap =
      (realificationOrderSwap * A * realificationOrderSwap) *
        (realificationOrderSwap * B * realificationOrderSwap) := by
  calc
    realificationOrderSwap * (A * B) * realificationOrderSwap =
        realificationOrderSwap * A *
          (realificationOrderSwap * realificationOrderSwap) *
          B * realificationOrderSwap := by
      rw [realificationOrderSwap_sq]
      simp [mul_assoc]
    _ =
        (realificationOrderSwap * A * realificationOrderSwap) *
          (realificationOrderSwap * B * realificationOrderSwap) := by
      simp only [mul_assoc]

/-- The two concrete square-minus-one matrices differ only by the explicit
coordinate-order permutation. -/
theorem orderSwap_conjugates_complexStructure_to_realPhaseAxis :
    realificationOrderSwap * complexStructure * realificationOrderSwap =
      realPhaseAxis := by
  rw [complexStructure_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realificationOrderSwap, realPhaseAxis, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- In interleaved coordinates, the scalar complex structure is the concrete
Pauli `Cl(3)` volume product. -/
theorem orderSwap_complexStructure_eq_real_pauli_volume :
    realificationOrderSwap * complexStructure * realificationOrderSwap =
      realSigma1 * realSigma2 * realSigma3 := by
  rw [orderSwap_conjugates_complexStructure_to_realPhaseAxis,
    real_pseudoscalar_eq_phaseAxis]

/-- Ring realification expressed in the interleaved coordinate convention. -/
noncomputable def interleavedRealify (A : Matrix2C) : Matrix4R :=
  realificationOrderSwap * realify A * realificationOrderSwap

/-- The interleaved realification remains multiplicative. -/
theorem interleavedRealify_mul (A B : Matrix2C) :
    interleavedRealify (A * B) =
      interleavedRealify A * interleavedRealify B := by
  unfold interleavedRealify
  rw [realify_mul, orderSwap_conjugation_mul]

/-- The interleaved realification preserves the identity. -/
@[simp] theorem interleavedRealify_one :
    interleavedRealify (1 : Matrix2C) = 1 := by
  unfold interleavedRealify
  rw [realify_one]
  simp [mul_assoc]

/-- Scalar multiplication by `I` becomes the concrete Pauli volume axis. -/
theorem interleavedRealify_complexPhase :
    interleavedRealify ((Complex.I : ℂ) • (1 : Matrix2C)) =
      realPhaseAxis := by
  unfold interleavedRealify
  change realificationOrderSwap * complexStructure * realificationOrderSwap =
    realPhaseAxis
  exact orderSwap_conjugates_complexStructure_to_realPhaseAxis

/-- Interleaved realification of the noncompact Cartan direction. -/
noncomputable def interleavedKboost : Matrix4R :=
  interleavedRealify Kboost

/-- Interleaved realification of the compact Cartan direction. -/
noncomputable def interleavedKcirc : Matrix4R :=
  interleavedRealify Kcirc

/-- The compact Cartan direction is the concrete real phase-axis action on the
noncompact direction. -/
theorem interleavedKcirc_eq_realPhaseAxis_mul_interleavedKboost :
    interleavedKcirc = realPhaseAxis * interleavedKboost := by
  have hscalar :
      ((Complex.I : ℂ) • (1 : Matrix2C)) * Kboost =
        Complex.I • Kboost := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Kboost, σ3c, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply]
  have hK :
      Kcirc = ((Complex.I : ℂ) • (1 : Matrix2C)) * Kboost := by
    rw [hscalar]
    exact Kcirc_eq_I_smul_Kboost
  calc
    interleavedKcirc =
        interleavedRealify
          (((Complex.I : ℂ) • (1 : Matrix2C)) * Kboost) := by
      rw [interleavedKcirc, hK]
    _ = interleavedRealify ((Complex.I : ℂ) • (1 : Matrix2C)) *
        interleavedRealify Kboost := by
      rw [interleavedRealify_mul]
    _ = realPhaseAxis * interleavedKboost := by
      rw [interleavedRealify_complexPhase]
      rfl

/-- Equivalent Pauli-volume form of the compact/noncompact Cartan relation. -/
theorem interleavedKcirc_eq_real_pauli_volume_mul_interleavedKboost :
    interleavedKcirc =
      (realSigma1 * realSigma2 * realSigma3) * interleavedKboost := by
  rw [real_pseudoscalar_eq_phaseAxis]
  exact interleavedKcirc_eq_realPhaseAxis_mul_interleavedKboost

/-- The Pauli volume action used above squares to minus the identity. -/
theorem real_pauli_volume_sq :
    (realSigma1 * realSigma2 * realSigma3) *
        (realSigma1 * realSigma2 * realSigma3) =
      -(1 : Matrix4R) :=
  real_pseudoscalar_sq

/-- Compact finite phase bridge. -/
theorem bipolar_cartan_cl3_phase_packet :
    realificationOrderSwap * realificationOrderSwap = (1 : Matrix4R) ∧
      realificationOrderSwap * complexStructure * realificationOrderSwap =
        realSigma1 * realSigma2 * realSigma3 ∧
      (realSigma1 * realSigma2 * realSigma3) *
          (realSigma1 * realSigma2 * realSigma3) =
        -(1 : Matrix4R) ∧
      interleavedKcirc =
        (realSigma1 * realSigma2 * realSigma3) * interleavedKboost := by
  exact ⟨realificationOrderSwap_sq,
    orderSwap_complexStructure_eq_real_pauli_volume,
    real_pauli_volume_sq,
    interleavedKcirc_eq_real_pauli_volume_mul_interleavedKboost⟩

end InfoGeometry.Canonical.BipolarCartanCl3PhaseBridge

end
