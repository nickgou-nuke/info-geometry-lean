/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Twistor.TwistorKinematicTensor
import InfoGeometry.Twistor.InfinityTwistor

/-! # Finite constituent sums and their mass invariant

The two-constituent determinant is reused from SpinorOuterProduct. Energy
positivity and tensor aggregation use the same lower-spinor data.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorConstituentKinematics

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwistorKinematicTensor
open InfoGeometry.Twistor.SpinorOuterProduct
open InfoGeometry.Twistor.InfinityTwistor
open scoped BigOperators Matrix

abbrev Packet (ι : Type*) := ι → Twistor4

variable {ι : Type*} [Fintype ι]

def totalKinematic (Z : Packet ι) : KinematicMatrix := ∑ i, kinematic (Z i)
def totalMomentum (Z : Packet ι) : ComplexSpacetime := ∑ i, momentum (Z i)

/-- Component matrices of the actual twistor constituents and their infinity raises. -/
def packetMatrix (Z : Packet ι) : Matrix ι Slot ℂ := fun i a => component (Z i) a
def infinityMatrix (Z : Packet ι) : Matrix ι Slot ℂ :=
  packetMatrix (fun i => infinityConjugate (Z i))

theorem packetMatrix_injective : Function.Injective (packetMatrix (ι := ι)) := by
  intro Z W h
  funext i
  apply Prod.ext <;> funext a
  · exact congrFun (congrFun h i) (.inl a)
  · exact congrFun (congrFun h i) (.inr a)

/-- The constituent sum is the symmetric product of two actual rectangular matrices. -/
theorem totalKinematic_matrix (Z : Packet ι) :
    totalKinematic Z = (packetMatrix Z)ᵀ * infinityMatrix Z +
      (infinityMatrix Z)ᵀ * packetMatrix Z := by
  ext a b
  simp only [totalKinematic, Matrix.sum_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [kinematic, symmetricOuter, packetMatrix, infinityMatrix, component]

theorem totalKinematic_symmetric (Z : Packet ι) :
    (totalKinematic Z)ᵀ = totalKinematic Z := by
  rw [totalKinematic, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun i _ => kinematic_symmetric (Z i)

theorem totalMomentum_hermitian (Z : Packet ι) :
    (totalMomentum Z)ᴴ = totalMomentum Z := by
  rw [totalMomentum, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => momentum_hermitian (Z i)

/-- Energy in the unnormalized Pauli convention. -/
def totalEnergy (Z : Packet ι) : ℝ :=
  (∑ i, (Complex.normSq ((Z i).2 0) + Complex.normSq ((Z i).2 1))) / 2

theorem totalEnergy_nonneg (Z : Packet ι) : 0 ≤ totalEnergy Z := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun i _ => add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- The energy is read from precisely the same momentum matrix. -/
theorem trace_totalMomentum (Z : Packet ι) :
    Matrix.trace (totalMomentum Z) = ((2 * totalEnergy Z : ℝ) : ℂ) := by
  rw [totalMomentum, Matrix.trace_sum]
  simp [Matrix.trace, momentum, Matrix.vecMulVec, Fin.sum_univ_two,
    totalEnergy, Complex.normSq_eq_conj_mul_self, Finset.sum_add_distrib]
  ring

/-- The spinor determinant controlling the two-constituent mass. -/
def spinorMinor (pi rho : Spinor2) : ℂ := pi 0 * rho 1 - pi 1 * rho 0

def pairMassSq (Z W : Twistor4) : ℝ := Complex.normSq (spinorMinor Z.2 W.2)

/-- A pair has zero mass exactly when its infinity-twistor pairing vanishes. -/
theorem pairMassSq_zero_iff_infinityTwistor_pairing_zero (Z W : Twistor4) :
    pairMassSq Z W = 0 ↔ infinityTwistor Z W = 0 := by
  rw [pairMassSq, Complex.normSq_eq_zero, infinityTwistor_apply]
  simp [spinorMinor]

/-- If one constituent lies in the radical of the infinity twistor, its pair
with every constituent has zero mass. -/
theorem pairMassSq_eq_zero_of_first_constituent_in_infinity_radical
    (Z W : Twistor4) (hZ : infinityTwistor Z = 0) :
    pairMassSq Z W = 0 := by
  apply (pairMassSq_zero_iff_infinityTwistor_pairing_zero Z W).2
  exact congrArg (fun f : Module.Dual ℂ Twistor4 => f W) hZ

/-- The radical criterion gives the equivalent lower-spinor rank condition. -/
theorem pairMassSq_eq_zero_of_first_lower_spinor_zero
    (Z W : Twistor4) (hZ : Z.2 = 0) : pairMassSq Z W = 0 := by
  apply pairMassSq_eq_zero_of_first_constituent_in_infinity_radical
  exact (infinityTwistor_radical Z).2 hZ

/-- Existing Hermitian-dyad theorem, specialized to the paper's conjugate spinors. -/
theorem pairMomentum_determinant (Z W : Twistor4) :
    (momentum Z + momentum W).det = (pairMassSq Z W : ℂ) := by
  unfold momentum
  have h := det_sum_self_outer (star Z.2) (star W.2)
  simp only [star_star] at h
  rw [h]
  simp [pairMassSq, spinorMinor, Complex.normSq_eq_conj_mul_self]

/-- The total momentum is null exactly when the infinity-twistor pairing of its
two null constituents vanishes. This joins the momentum determinant and the
native degenerate twistor form on the same carrier. -/
theorem pairMomentum_determinant_zero_iff_infinityTwistor_pairing_zero
    (Z W : Twistor4) :
    (momentum Z + momentum W).det = 0 ↔ infinityTwistor Z W = 0 := by
  rw [pairMomentum_determinant]
  constructor
  · intro h
    apply (pairMassSq_zero_iff_infinityTwistor_pairing_zero Z W).mp
    exact_mod_cast h
  · intro h
    have hm := (pairMassSq_zero_iff_infinityTwistor_pairing_zero Z W).mpr h
    exact_mod_cast hm

theorem pairMassSq_nonneg (Z W : Twistor4) : 0 ≤ pairMassSq Z W :=
  Complex.normSq_nonneg _

theorem pairMassSq_pos_iff (Z W : Twistor4) :
    0 < pairMassSq Z W ↔ spinorMinor Z.2 W.2 ≠ 0 :=
  Complex.normSq_pos

theorem pairMassSq_zero_iff (Z W : Twistor4) :
    pairMassSq Z W = 0 ↔ Z.2 0 * W.2 1 = Z.2 1 * W.2 0 := by
  rw [pairMassSq_zero_iff_infinityTwistor_pairing_zero,
    infinityTwistor_apply]
  exact sub_eq_zero

/-- The paper's normalization reads mass squared as twice this determinant. -/
theorem paper_pair_mass (Z W : Twistor4) :
    2 * (momentum Z + momentum W).det = ((2 * pairMassSq Z W : ℝ) : ℂ) := by
  rw [pairMomentum_determinant]
  push_cast
  rfl

/-- Two independent null constituents give a nonzero mass invariant. -/
theorem massive_pair_witness :
    pairMassSq ((0 : Spinor2), ![1, 0]) ((0 : Spinor2), ![0, 1]) = 1 := by
  norm_num [pairMassSq, spinorMinor]

section WittPairingSeparation

open PenroseTwistor PerjesConventions

private theorem isNullTwistor_of_witt_null (Z : Twistor4)
    (hpi : Z.2 ≠ 0) (hnull : wittPair Z Z = 0) :
    IsNullTwistor (wittToDiagonal Z) := by
  constructor
  · intro h
    have hz : Z = 0 := wittToDiagonal.injective (by simpa using h)
    exact hpi (congrArg Prod.snd hz)
  · change (twistorHermitian (wittToDiagonal Z) (wittToDiagonal Z)).re = 0
    rw [diagonal_pairing, hnull]
    simp

/-- Mutually Witt-orthogonal null twistors can have positive constituent
mass. Both lower spinors are nonzero; neither momentum is a zero constituent. -/
theorem null_twistors_witt_orthogonal_positive_mass :
    ∃ Z W : Twistor4,
      IsNullTwistor (wittToDiagonal Z) ∧ IsNullTwistor (wittToDiagonal W) ∧
      Z.2 ≠ 0 ∧ W.2 ≠ 0 ∧ wittPair Z W = 0 ∧ pairMassSq Z W = 1 := by
  let Z : Twistor4 := ((0 : Spinor2), ![1, 0])
  let W : Twistor4 := ((0 : Spinor2), ![0, 1])
  have h0 : (![1, 0] : Spinor2) ≠ 0 := by
    intro h
    have hc := congrFun h 0
    norm_num at hc
  have h1 : (![0, 1] : Spinor2) ≠ 0 := by
    intro h
    have hc := congrFun h 1
    norm_num at hc
  refine ⟨Z, W, ?_, ?_, h0, h1, ?_, ?_⟩
  · exact isNullTwistor_of_witt_null Z h0 (by simp [Z, wittPair])
  · exact isNullTwistor_of_witt_null W h1 (by simp [W, wittPair])
  · simp [Z, W, wittPair]
  · exact massive_pair_witness

/-- Nonzero mutual Witt pairing does not force positive constituent mass,
even for null twistors with two nonzero constituent momenta. -/
theorem null_twistors_witt_pairing_I_zero_mass :
    ∃ Z W : Twistor4,
      IsNullTwistor (wittToDiagonal Z) ∧ IsNullTwistor (wittToDiagonal W) ∧
      Z.2 ≠ 0 ∧ W.2 ≠ 0 ∧ wittPair Z W = Complex.I ∧ pairMassSq Z W = 0 := by
  let Z : Twistor4 := ((0 : Spinor2), ![1, 0])
  let W : Twistor4 := ((![Complex.I, 0] : Spinor2), ![1, 0])
  have h0 : (![1, 0] : Spinor2) ≠ 0 := by
    intro h
    have hc := congrFun h 0
    norm_num at hc
  refine ⟨Z, W, ?_, ?_, h0, h0, ?_, ?_⟩
  · exact isNullTwistor_of_witt_null Z h0 (by simp [Z, wittPair])
  · apply isNullTwistor_of_witt_null W h0
    norm_num [W, wittPair, Fin.sum_univ_two]
  · simp [Z, W, wittPair, Fin.sum_univ_two]
  · norm_num [Z, W, pairMassSq, spinorMinor]

end WittPairingSeparation

end InfoGeometry.Twistor.TwistorConstituentKinematics
