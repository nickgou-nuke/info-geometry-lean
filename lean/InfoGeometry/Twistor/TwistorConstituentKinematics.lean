import InfoGeometry.Twistor.TwistorKinematicTensor
import InfoGeometry.Twistor.SpinorOuterProduct

/-! # Finite constituent kinematics on the existing twistor carrier

The same constituent spinors determine a positive Hermitian momentum matrix
and the symmetric kinematic tensor. The two-constituent determinant theorem
reuses the existing outer-product owner. `pairMassSq` uses the unscaled
Pauli convention; the paper's normalization adapter is in PerjesConventions.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorConstituentKinematics

open Matrix
open scoped BigOperators
open PenroseIncidence TwistorKinematicTensor

variable {ι : Type*} [Fintype ι]

/-- Columns are the actual momentum spinors of the constituents. -/
def spinorColumns (Z : ι → Twistor4) : Matrix (Fin 2) ι ℂ := fun a i => (Z i).2 a

def totalMomentum (Z : ι → Twistor4) : ComplexSpacetime :=
  spinorColumns Z * (spinorColumns Z)ᴴ

def totalKinematic (Z : ι → Twistor4) : KinematicMatrix := ∑ i, kinematic (Z i)

theorem totalMomentum_eq_sum (Z : ι → Twistor4) :
    totalMomentum Z = ∑ i, momentum (Z i) := by
  ext a b
  simp [totalMomentum, spinorColumns, momentum, Matrix.mul_apply, vecMulVec]

theorem totalMomentum_hermitian (Z : ι → Twistor4) :
    (totalMomentum Z)ᴴ = totalMomentum Z := by
  simp [totalMomentum, Matrix.conjTranspose_mul]

/-- Native matrix positive semidefiniteness, not only diagonal nonnegativity. -/
theorem totalMomentum_posSemidef (Z : ι → Twistor4) :
    (totalMomentum Z).PosSemidef := by
  classical
  simpa [totalMomentum] using
    (Matrix.PosSemidef.one (n := ι) (R := ℂ)).mul_mul_conjTranspose_same (spinorColumns Z)

theorem totalKinematic_symmetric (Z : ι → Twistor4) :
    (totalKinematic Z)ᵀ = totalKinematic Z := by
  simp [totalKinematic, kinematic_symmetric]

/-- Momentum readback uses the same constituent family as the kinematic tensor. -/
theorem totalKinematic_momentum_zero (Z : ι → Twistor4) (a : Fin 2) :
    totalKinematic Z (.inr a) (.inl 0) = totalMomentum Z a 1 := by
  rw [totalMomentum_eq_sum]
  simp [totalKinematic, kinematic_momentum_column_zero]

theorem totalKinematic_momentum_one (Z : ι → Twistor4) (a : Fin 2) :
    totalKinematic Z (.inr a) (.inl 1) = -totalMomentum Z a 0 := by
  rw [totalMomentum_eq_sum]
  simp [totalKinematic, kinematic_momentum_column_one]

/-- The determinant minor is the existing infinity contraction. -/
def spinorMinor (Z W : Twistor4) : ℂ := InfinityTwistor.infinityTwistor Z W

def pairMassSq (Z W : Twistor4) : ℝ := Complex.normSq (spinorMinor Z W)

theorem pair_determinant (Z W : Twistor4) :
    (momentum Z + momentum W).det = (pairMassSq Z W : ℂ) := by
  rw [momentum, momentum, SpinorOuterProduct.det_sum_self_outer]
  exact Complex.mul_conj (spinorMinor Z W)

theorem pairMassSq_nonneg (Z W : Twistor4) : 0 ≤ pairMassSq Z W :=
  Complex.normSq_nonneg _

theorem pairMassSq_eq_zero_iff (Z W : Twistor4) :
    pairMassSq Z W = 0 ↔ (Z.2 0 * W.2 1 = Z.2 1 * W.2 0) := by
  rw [pairMassSq, Complex.normSq_eq_zero]
  exact sub_eq_zero

theorem pairMassSq_pos_iff (Z W : Twistor4) :
    0 < pairMassSq Z W ↔ InfinityTwistor.infinityTwistor Z W ≠ 0 := by
  exact Complex.normSq_pos

/-- A single constituent is null even when the full sum is massive. -/
theorem momentum_det_zero (Z : Twistor4) : (momentum Z).det = 0 := by
  simp [momentum, vecMulVec, Matrix.det_fin_two]
  ring

theorem momentum_phase (c : ℂ) (hc : c * star c = 1) (Z : Twistor4) :
    momentum (c • Z) = momentum Z :=
  SpinorOuterProduct.outer_phase_invariant c hc Z.2 Z.2

theorem pairMassSq_translation (X : ComplexSpacetime) (Z W : Twistor4) :
    pairMassSq (InfinityTwistor.translation X Z) (InfinityTwistor.translation X W) =
      pairMassSq Z W := by
  simp [pairMassSq, spinorMinor]

/-- Non-vacuous timelike sum of two distinct rank-one momenta. -/
theorem two_null_constituents_massive :
    ∃ Z W : Twistor4,
      (momentum Z).det = 0 ∧ (momentum W).det = 0 ∧
      momentum Z + momentum W = 1 ∧ pairMassSq Z W = 1 := by
  let Z : Twistor4 := (0, ![1, 0])
  let W : Twistor4 := (0, ![0, 1])
  refine ⟨Z, W, momentum_det_zero Z, momentum_det_zero W, ?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [momentum, vecMulVec, Z, W]
  · norm_num [pairMassSq, spinorMinor, InfinityTwistor.infinityTwistor, Z, W]

end InfoGeometry.Twistor.TwistorConstituentKinematics
