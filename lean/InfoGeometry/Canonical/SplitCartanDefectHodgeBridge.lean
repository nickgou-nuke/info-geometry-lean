import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCartanChiralNilpotentBlock
import InfoGeometry.Canonical.SplitCartanRelativeModularTwoByTwoBridge

/-!
# Defect and Hodge rotation for the finite split-Cartan block

This is a binary split-Cartan specialization.  The scalar defect records the
volume and unimodular shape contributions separately, while the commutator
lemmas expose the finite Hestenes rotation of the centered chiral surprisal.
No general log-determinant theory or modular identification is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCartanDefectHodgeBridge

open InfoGeometry.Canonical.SplitCartanChiralNilpotentBlock
open InfoGeometry.Canonical.SplitCartanRelativeModularTwoByTwoBridge
open InfoGeometry.Physics

def volumeDefect (κ : ℝ) : ℝ :=
  2 * (Real.exp (-κ) - 1 + κ)

def shapeDefect (κ a : ℝ) : ℝ :=
  2 * Real.exp (-κ) * (Real.cosh a - 1)

def operatorDefect (κ a : ℝ) : ℝ :=
  2 * (Real.exp (-κ) * Real.cosh a - 1 + κ)

theorem operatorDefect_eq_volume_shape (κ a : ℝ) :
    operatorDefect κ a = volumeDefect κ + shapeDefect κ a := by
  unfold operatorDefect volumeDefect shapeDefect
  ring

theorem operatorDefect_eq_relativeDensity_trace (κ a : ℝ) :
    operatorDefect κ a =
      Matrix.trace (relativeDensity κ a) - 2 + 2 * κ := by
  have htrace : Matrix.trace (relativeDensity κ a) =
      Real.exp (-(κ + a)) + Real.exp (-(κ - a)) := by
    simp [relativeDensity, Matrix.trace, Fin.sum_univ_two]
  have h₁ : Real.exp (-(κ + a)) =
      Real.exp (-κ) * Real.exp (-a) := by
    rw [show -(κ + a) = -κ + -a by ring, Real.exp_add]
  have h₂ : Real.exp (-(κ - a)) =
      Real.exp (-κ) * Real.exp a := by
    rw [show -(κ - a) = -κ + a by ring, Real.exp_add]
  rw [htrace, h₁, h₂]
  unfold operatorDefect
  rw [Real.cosh_eq]
  ring

theorem volumeDefect_nonneg (κ : ℝ) : 0 ≤ volumeDefect κ := by
  unfold volumeDefect
  have h := Real.add_one_le_exp (-κ)
  linarith

private theorem one_le_cosh (a : ℝ) : 1 ≤ Real.cosh a := by
  rw [Real.cosh_eq]
  have h₁ := Real.add_one_le_exp a
  have h₂ := Real.add_one_le_exp (-a)
  linarith

private theorem one_lt_cosh_of_ne_zero {a : ℝ} (ha : a ≠ 0) :
    1 < Real.cosh a := by
  rw [Real.cosh_eq]
  have h₁ := Real.add_one_lt_exp ha
  have h₂ := Real.add_one_le_exp (-a)
  linarith

theorem shapeDefect_nonneg (κ a : ℝ) : 0 ≤ shapeDefect κ a := by
  unfold shapeDefect
  exact mul_nonneg
    (mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos (-κ))))
    (sub_nonneg.mpr (one_le_cosh a))

theorem volumeDefect_eq_zero_iff (κ : ℝ) :
    volumeDefect κ = 0 ↔ κ = 0 := by
  constructor
  · intro hκ
    by_contra hne
    have hstrict := Real.add_one_lt_exp (neg_ne_zero.mpr hne)
    unfold volumeDefect at hκ
    linarith
  · intro hκ
    subst hκ
    simp [volumeDefect]

theorem shapeDefect_eq_zero_iff (κ a : ℝ) :
    shapeDefect κ a = 0 ↔ a = 0 := by
  constructor
  · intro hshape
    by_contra hne
    have hstrict := one_lt_cosh_of_ne_zero hne
    have hpositive : 0 < shapeDefect κ a := by
      unfold shapeDefect
      exact mul_pos
        (mul_pos (by norm_num) (Real.exp_pos (-κ)))
        (sub_pos.mpr hstrict)
    linarith
  · intro ha
    subst ha
    simp [shapeDefect]

theorem operatorDefect_nonneg (κ a : ℝ) : 0 ≤ operatorDefect κ a := by
  rw [operatorDefect_eq_volume_shape]
  exact add_nonneg (volumeDefect_nonneg κ) (shapeDefect_nonneg κ a)

theorem operatorDefect_eq_zero_iff (κ a : ℝ) :
    operatorDefect κ a = 0 ↔ κ = 0 ∧ a = 0 := by
  constructor
  · intro h
    have hsplit := operatorDefect_eq_volume_shape κ a
    have hv : volumeDefect κ = 0 := by
      nlinarith [volumeDefect_nonneg κ, shapeDefect_nonneg κ a]
    have hs : shapeDefect κ a = 0 := by
      nlinarith [volumeDefect_nonneg κ, shapeDefect_nonneg κ a]
    exact ⟨volumeDefect_eq_zero_iff κ |>.mp hv,
      shapeDefect_eq_zero_iff κ a |>.mp hs⟩
  · rintro ⟨rfl, rfl⟩
    simp [operatorDefect]

theorem relativeSurprisal_scalar_part (κ a : ℝ) :
    ((1 / 2 : ℝ) * Matrix.trace (relativeSurprisal κ a)) •
        (1 : Block) = κ • (1 : Block) := by
  rw [relativeSurprisal_trace]
  have h : (1 / 2 : ℝ) * (2 * κ) = κ := by ring
  rw [h]

theorem relativeSurprisal_centered_readout (κ a : ℝ) :
    relativeSurprisal κ a -
        ((1 / 2 : ℝ) * Matrix.trace (relativeSurprisal κ a)) •
          (1 : Block) = a • gamma := by
  exact relativeSurprisal_centered κ a

theorem relativeSurprisalOperator_eq_relativeSurprisal_of_potential_readout
    (κ a : ℝ)
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin 2))
    (h₀ : InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential
      q q0 0 = κ + a)
    (h₁ : InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential
      q q0 1 = κ - a) :
    InfoGeometry.Canonical.RelativeModularHamiltonian.relativeModularHamiltonianOperator
        q q0 = relativeSurprisal κ a := by
  rw [relativeSurprisalOperator_fin_two_readout]
  ext i j
  fin_cases i <;> fin_cases j
  · change InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential
        q q0 0 = κ + a
    exact h₀
  · rfl
  · rfl
  · change InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential
        q q0 1 = κ - a
    exact h₁

/-! ## Finite Jordan/Lie channels -/

/-- The symmetric Jordan channel of an associative matrix product. -/
noncomputable def jordanChannel (K A : Block) : Block :=
  (2 : ℝ)⁻¹ • (K * A + A * K)

/-- The antisymmetric Lie channel of an associative matrix product. -/
noncomputable def lieChannel (K A : Block) : Block :=
  (2 : ℝ)⁻¹ • (K * A - A * K)

theorem product_eq_jordanChannel_add_lieChannel (K A : Block) :
    K * A = jordanChannel K A + lieChannel K A := by
  unfold jordanChannel lieChannel
  module

theorem kAxis_mul_eq_jordanChannel_add_lieChannel (A : Block) :
    kAxis * A = jordanChannel kAxis A + lieChannel kAxis A := by
  exact product_eq_jordanChannel_add_lieChannel kAxis A

/-! ## Native linear-operator readout -/

abbrev BlockEnd := Module.End ℝ (Fin 2 → ℝ)

noncomputable def matrixEnd (A : Block) : BlockEnd := Matrix.toLin' A

noncomputable def matrixEndAlgEquiv : Block ≃ₐ[ℝ] BlockEnd :=
  Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 2))

@[simp] theorem matrixEndAlgEquiv_apply (A : Block) :
    matrixEndAlgEquiv A = matrixEnd A := by
  rfl

theorem matrixEnd_injective : Function.Injective matrixEnd := by
  intro A B h
  apply matrixEndAlgEquiv.injective
  simpa using h

theorem matrixEnd_mul (A B : Block) :
    matrixEnd (A * B) = matrixEnd A * matrixEnd B := by
  apply LinearMap.ext
  intro x
  simp [matrixEnd, Matrix.toLin'_apply, Module.End.mul_apply]

theorem matrixEnd_product_eq_jordan_add_lie (K A : Block) :
    matrixEnd (K * A) =
      matrixEnd (jordanChannel K A) + matrixEnd (lieChannel K A) := by
  rw [product_eq_jordanChannel_add_lieChannel]
  simp [matrixEnd]

theorem matrixEnd_mul_apply (A B : Block) (x : Fin 2 → ℝ) :
    matrixEnd (A * B) x = matrixEnd A (matrixEnd B x) := by
  rw [matrixEnd_mul]
  rfl

theorem matrixEnd_product_split_apply (K A : Block) (x : Fin 2 → ℝ) :
    matrixEnd K (matrixEnd A x) =
      matrixEnd (jordanChannel K A) x +
        matrixEnd (lieChannel K A) x := by
  have h := congrArg (fun T : BlockEnd => T x)
    (matrixEnd_product_eq_jordan_add_lie K A)
  simpa [matrixEnd_mul, Module.End.mul_apply] using h

theorem jordanChannel_relativeSurprisal (κ a : ℝ) :
    jordanChannel kAxis (relativeSurprisal κ a) = κ • kAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jordanChannel, relativeSurprisal, kAxis, qPlus, qMinus,
      gamma, chiralParity, chiralQPlus, chiralQMinus,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem kAxis_commutator_relativeSurprisal (κ a : ℝ) :
    SplitCartanChiralNilpotentBlock.commutator kAxis (relativeSurprisal κ a) =
      (2 * a) • hodgeDirac := by
  norm_num [SplitCartanChiralNilpotentBlock.commutator, relativeSurprisal,
    hodgeDirac, dirac, kAxis,
    gamma, qPlus, qMinus, chiralParity, chiralQPlus, chiralQMinus,
    Matrix.mul_apply, Fin.sum_univ_two]
  constructor <;> ring

theorem lieChannel_relativeSurprisal (κ a : ℝ) :
    lieChannel kAxis (relativeSurprisal κ a) = a • hodgeDirac := by
  unfold lieChannel
  change (2 : ℝ)⁻¹ •
      SplitCartanChiralNilpotentBlock.commutator
        kAxis (relativeSurprisal κ a) = a • hodgeDirac
  rw [kAxis_commutator_relativeSurprisal]
  module

theorem kAxis_mul_relativeSurprisal_eq_synthesis (κ a : ℝ) :
    kAxis * relativeSurprisal κ a = κ • kAxis + a • hodgeDirac := by
  rw [kAxis_mul_eq_jordanChannel_add_lieChannel,
    jordanChannel_relativeSurprisal, lieChannel_relativeSurprisal]

theorem kAxis_commutator_hodgeDirac :
    SplitCartanChiralNilpotentBlock.commutator kAxis hodgeDirac =
      (-2 : ℝ) • gamma := by
  norm_num [SplitCartanChiralNilpotentBlock.commutator, hodgeDirac, dirac,
    kAxis, gamma, qPlus, qMinus,
    chiralParity, chiralQPlus, chiralQMinus, Matrix.mul_apply,
    Fin.sum_univ_two]

end InfoGeometry.Canonical.SplitCartanDefectHodgeBridge
