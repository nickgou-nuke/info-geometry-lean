/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.WalshCharacterGeometry

/-!
# Real binary electric–magnetic Fourier duality

The existing Walsh matrix on `ι → ZMod 2` squares to the group cardinality
times the identity. Electric projection uses the reciprocal cardinality;
its inverse is the unnormalized Walsh transform. Transpose covariance of
twisted tables therefore gives the two-sided, transposed Fourier duality.

For `ι = Fin 2`, this is the finite real algebra of 't Hooft (1979), (6.3):
sixteen summands and normalization `1 / 4`. The twisted table must first be
Fourier projected in the longitudinal coordinate, which is constructed below.
The full three-coordinate electric normalization is consequently `1 / 8`.
Euclidean covariance is an explicit input, not a proved property of a gauge
theory. No confinement or asymptotic free-energy factorization is asserted.
See `docs/BINARY_FLUX_DUALITY_CONTRACT.md` for the source and scope.
-/

noncomputable section

namespace InfoGeometry.Algebra.BinaryFluxDuality

open scoped BigOperators
open InfoGeometry.LLM.WalshCharacterGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem card_ne_zero : (Fintype.card (ι → ZMod 2) : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero (α := ι → ZMod 2)

/-- Reuse Walsh symmetry and orthogonality to obtain the square law. -/
theorem walshMatrix_square :
    walshMatrix (ι := ι) * walshMatrix =
      (Fintype.card (ι → ZMod 2) : ℝ) • (1 : Matrix _ _ ℝ) := by
  simpa only [walshMatrix_transpose] using walshMatrix_mul_transpose (ι := ι)

/-- The electric-sector convention has reciprocal group-order normalization. -/
def electricTransform (W : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ :=
  (Fintype.card (ι → ZMod 2) : ℝ)⁻¹ • (walshMatrix * W)

/-- Inversion of electric projection has no prefactor. -/
def inverseElectricTransform (Z : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ :=
  walshMatrix * Z

theorem electricTransform_apply (W : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ)
    (e m : ι → ZMod 2) :
    electricTransform W e m =
      (Fintype.card (ι → ZMod 2) : ℝ)⁻¹ *
        ∑ k, walshCharacter e k * W k m := by
  simp only [electricTransform, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    walshMatrix, walshCharacter_symmetric]

@[simp] theorem inverseElectricTransform_electricTransform
    (W : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) :
    inverseElectricTransform (electricTransform W) = W := by
  unfold inverseElectricTransform electricTransform
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, walshMatrix_square,
    Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ card_ne_zero, one_smul]

@[simp] theorem electricTransform_inverseElectricTransform
    (Z : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) :
    electricTransform (inverseElectricTransform Z) = Z := by
  unfold inverseElectricTransform electricTransform
  rw [← Matrix.mul_assoc, walshMatrix_square, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, inv_mul_cancel₀ card_ne_zero, one_smul]

/-- The symplectic binary Fourier duality includes a transpose of the input. -/
def fluxDuality :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ →ₗ[ℝ]
      Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ where
  toFun Z := (Fintype.card (ι → ZMod 2) : ℝ)⁻¹ •
    (walshMatrix * Z.transpose * walshMatrix)
  map_add' X Y := by
    simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' c Z := by
    simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      RingHom.id_apply]
    exact smul_comm _ _ _

/-- The duality is obtained by undoing electric projection, transposing,
and projecting again. -/
theorem fluxDuality_eq_electricTransform
    (Z : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) :
    fluxDuality Z = electricTransform (inverseElectricTransform Z).transpose := by
  change _ = (Fintype.card (ι → ZMod 2) : ℝ)⁻¹ •
    (walshMatrix * (walshMatrix * Z).transpose)
  rw [Matrix.transpose_mul, walshMatrix_transpose, ← Matrix.mul_assoc]
  rfl

/-- The actual finite transform is an involution; no physical covariance
assumption is needed for this algebraic identity. -/
theorem fluxDuality_involutive : Function.Involutive (fluxDuality (ι := ι)) := by
  intro Z
  rw [fluxDuality_eq_electricTransform, fluxDuality_eq_electricTransform,
    inverseElectricTransform_electricTransform, Matrix.transpose_transpose,
    electricTransform_inverseElectricTransform]

/-- Native linear equivalence supplied by the proved involution. -/
def fluxDualityEquiv :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ ≃ₗ[ℝ]
      Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ :=
  LinearEquiv.ofInvolutive fluxDuality fluxDuality_involutive

/-- Fourier inversion turns an explicitly supplied transpose covariance
of twisted tables into flux duality of their projected tables. -/
theorem electricTransform_eq_fluxDuality_of_transpose
    (W W' : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ)
    (hW : W = W'.transpose) :
    electricTransform W = fluxDuality (electricTransform W') := by
  rw [fluxDuality_eq_electricTransform, inverseElectricTransform_electricTransform, hW]

/-- Entrywise normalization and ordering: the input is read at `(l,k)`. -/
theorem fluxDuality_apply (Z : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ)
    (e m : ι → ZMod 2) :
    fluxDuality Z e m =
      (Fintype.card (ι → ZMod 2) : ℝ)⁻¹ *
        ∑ k, ∑ l, walshCharacter e k * walshCharacter m l * Z l k := by
  change (Fintype.card (ι → ZMod 2) : ℝ)⁻¹ *
    ((walshMatrix * Z.transpose * walshMatrix :
      Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) e m) = _
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, walshMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [walshCharacter_symmetric k e]
  exact mul_right_comm _ _ _

/-- Project in the third electric coordinate before treating the two
transverse coordinates. The longitudinal magnetic coordinate is fixed. -/
def longitudinalProjection (e₃ : ZMod 2)
    (W : ZMod 2 → Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ :=
  (1 / 2 : ℝ) • ∑ k₃, binarySign (e₃ * k₃) • W k₃

omit [Fintype ι] [DecidableEq ι] in
/-- The source rotation fixes the third coordinates, so the longitudinal
Fourier projection preserves its supplied transpose covariance. -/
theorem longitudinalProjection_transpose_covariant (e₃ : ZMod 2)
    (W W' : ZMod 2 → Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ)
    (hW : ∀ k₃, W k₃ = (W' k₃).transpose) :
    longitudinalProjection e₃ W = (longitudinalProjection e₃ W').transpose := by
  simp only [longitudinalProjection, Matrix.transpose_smul, Matrix.transpose_sum, hW]

/-- The finite algebraic implication (6.2) → (6.3), retaining the
longitudinal electric projection rather than fixing a twist coordinate. -/
theorem projected_electricTransform_eq_fluxDuality (e₃ : ZMod 2)
    (W W' : ZMod 2 → Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ)
    (hW : ∀ k₃, W k₃ = (W' k₃).transpose) :
    electricTransform (longitudinalProjection e₃ W) =
      fluxDuality (electricTransform (longitudinalProjection e₃ W')) :=
  electricTransform_eq_fluxDuality_of_transpose _ _
    (longitudinalProjection_transpose_covariant e₃ W W' hW)

/-- Four transverse labels, hence sixteen pairs in the duality sum. -/
theorem transverse_card : Fintype.card (Fin 2 → ZMod 2) = 4 := by
  norm_num [Fintype.card_fun]

/-- The N = 2 specialization of the source's transverse duality kernel. -/
theorem transverse_fluxDuality_apply
    (Z : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℝ)
    (e m : Fin 2 → ZMod 2) :
    fluxDuality Z e m =
      (1 / 4 : ℝ) *
        ∑ k, ∑ l, walshCharacter e k * walshCharacter m l * Z l k := by
  rw [fluxDuality_apply, transverse_card]
  norm_num

/-- The two transverse coordinates and the projected longitudinal coordinate
give the full eight-term electric projection with normalization `1 / 8`. -/
theorem transverse_projected_electricTransform_apply
    (W : ZMod 2 → Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℝ)
    (e₃ : ZMod 2) (e m : Fin 2 → ZMod 2) :
    electricTransform (longitudinalProjection e₃ W) e m =
      (1 / 8 : ℝ) * ∑ k₃, ∑ k,
        binarySign (e₃ * k₃) * walshCharacter e k * W k₃ k m := by
  rw [electricTransform_apply, transverse_card]
  simp only [longitudinalProjection, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k₃ _
  apply Finset.sum_congr rfl
  intro k _
  ring

end InfoGeometry.Algebra.BinaryFluxDuality
