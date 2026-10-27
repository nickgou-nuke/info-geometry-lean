import InfoGeometry.Twistor.TwistorKinematicTensor

/-! # Finite constituent sums and their mass invariant

The two-constituent determinant is reused from SpinorOuterProduct. Energy
positivity and tensor aggregation use the same lower-spinor data.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorConstituentKinematics

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwistorKinematicTensor
open InfoGeometry.Twistor.SpinorOuterProduct
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
  simp [totalKinematic, kinematic, symmetricOuter, packetMatrix, infinityMatrix,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_add_distrib]

theorem totalKinematic_symmetric (Z : Packet ι) :
    (totalKinematic Z)ᵀ = totalKinematic Z := by
  ext a b
  simp only [totalKinematic, Matrix.transpose_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (congrFun (kinematic_symmetric (Z i)) a) b

theorem totalMomentum_hermitian (Z : Packet ι) :
    (totalMomentum Z)ᴴ = totalMomentum Z := by
  ext a b
  simp [totalMomentum, momentum, Matrix.conjTranspose_apply, Matrix.vecMulVec, mul_comm]

/-- Energy in the unnormalized Pauli convention. -/
def totalEnergy (Z : Packet ι) : ℝ :=
  (∑ i, Complex.normSq ((Z i).2 0) + Complex.normSq ((Z i).2 1)) / 2

theorem totalEnergy_nonneg (Z : Packet ι) : 0 ≤ totalEnergy Z := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun i _ => add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- The energy is read from precisely the same momentum matrix. -/
theorem trace_totalMomentum (Z : Packet ι) :
    Matrix.trace (totalMomentum Z) = ((2 * totalEnergy Z : ℝ) : ℂ) := by
  simp [Matrix.trace, totalMomentum, momentum, Matrix.vecMulVec, Fin.sum_univ_two,
    totalEnergy, Complex.normSq_eq_conj_mul_self, Finset.sum_add_distrib]
  push_cast
  ring

/-- The spinor determinant controlling the two-constituent mass. -/
def spinorMinor (pi rho : Spinor2) : ℂ := pi 0 * rho 1 - pi 1 * rho 0

def pairMassSq (Z W : Twistor4) : ℝ := Complex.normSq (spinorMinor Z.2 W.2)

/-- Existing Hermitian-dyad theorem, specialized to the paper's conjugate spinors. -/
theorem pairMomentum_determinant (Z W : Twistor4) :
    (momentum Z + momentum W).det = (pairMassSq Z W : ℂ) := by
  unfold momentum
  have h := det_sum_self_outer (star Z.2) (star W.2)
  simp only [star_star] at h
  rw [h]
  simp [pairMassSq, spinorMinor, Complex.normSq_eq_conj_mul_self]
  ring

theorem pairMassSq_nonneg (Z W : Twistor4) : 0 ≤ pairMassSq Z W :=
  Complex.normSq_nonneg _

theorem pairMassSq_pos_iff (Z W : Twistor4) :
    0 < pairMassSq Z W ↔ spinorMinor Z.2 W.2 ≠ 0 :=
  Complex.normSq_pos

theorem pairMassSq_zero_iff (Z W : Twistor4) :
    pairMassSq Z W = 0 ↔ Z.2 0 * W.2 1 = Z.2 1 * W.2 0 := by
  rw [pairMassSq, Complex.normSq_eq_zero, spinorMinor, sub_eq_zero]

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

end InfoGeometry.Twistor.TwistorConstituentKinematics
