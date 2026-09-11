import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The normalized axial grading in the circular Peirce basis

This owner packages one half of the native commutator with the distinguished
split axis.  It is a linear operator on the full alternative carrier; no
associativity of the carrier is used or asserted.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CanonicalZorn :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

def axialWeight : Fin 8 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => -1
  | 6 => -1
  | 7 => -1
  | _ => 0

noncomputable def axialGrading : Module.End ℝ CanonicalZorn :=
  (1 / 2 : ℝ) • ellCommutator

theorem axialGrading_basis (i : Fin 8) :
    axialGrading (circularPeirceBasis i) =
      axialWeight i • circularPeirceBasis i := by
  fin_cases i
  · change axialGrading (circularPeirceBasis 0) = axialWeight 0 • circularPeirceBasis 0
    rw [circularPeirceBasis_zero, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_uPlus]
    simp only [axialWeight, smul_zero, zero_smul]
  · change axialGrading (circularPeirceBasis 1) = axialWeight 1 • circularPeirceBasis 1
    rw [circularPeirceBasis_one, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_rootPlus]
    simp only [smul_smul]
    norm_num [axialWeight]
  · change axialGrading (circularPeirceBasis 2) = axialWeight 2 • circularPeirceBasis 2
    rw [circularPeirceBasis_two, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_rootPlus]
    simp only [smul_smul]
    norm_num [axialWeight]
  · change axialGrading (circularPeirceBasis 3) = axialWeight 3 • circularPeirceBasis 3
    rw [circularPeirceBasis_three, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_rootPlus]
    simp only [smul_smul]
    norm_num [axialWeight]
  · change axialGrading (circularPeirceBasis 4) = axialWeight 4 • circularPeirceBasis 4
    rw [circularPeirceBasis_four, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_uMinus]
    simp only [axialWeight, smul_zero, zero_smul]
  · change axialGrading (circularPeirceBasis 5) = axialWeight 5 • circularPeirceBasis 5
    rw [circularPeirceBasis_five, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_rootMinus]
    simp only [smul_smul]
    norm_num [axialWeight]
  · change axialGrading (circularPeirceBasis 6) = axialWeight 6 • circularPeirceBasis 6
    rw [circularPeirceBasis_six, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_rootMinus]
    simp only [smul_smul]
    norm_num [axialWeight]
  · change axialGrading (circularPeirceBasis 7) = axialWeight 7 • circularPeirceBasis 7
    rw [circularPeirceBasis_seven, axialGrading]
    simp only [LinearMap.smul_apply]
    rw [ellCommutator_rootMinus]
    simp only [smul_smul]
    norm_num [axialWeight]

theorem axialGrading_tripotent : axialGrading ^ 3 = axialGrading := by
  apply circularPeirceBasis.ext
  intro i
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply]
  simp only [axialGrading_basis, map_smul]
  fin_cases i <;> norm_num [axialWeight]

noncomputable def axialProjectorPlus : Module.End ℝ CanonicalZorn :=
  (1 / 2 : ℝ) • (axialGrading + axialGrading ^ 2)

noncomputable def axialProjectorZero : Module.End ℝ CanonicalZorn :=
  LinearMap.id - axialGrading ^ 2

noncomputable def axialProjectorMinus : Module.End ℝ CanonicalZorn :=
  (1 / 2 : ℝ) • (axialGrading ^ 2 - axialGrading)

theorem axialProjectors_add_eq_id :
    axialProjectorPlus + axialProjectorZero + axialProjectorMinus =
      (LinearMap.id : CanonicalZorn →ₗ[ℝ] CanonicalZorn) := by
  change
    (1 / 2 : ℝ) •
        (axialGrading + axialGrading ^ 2) +
      ((LinearMap.id : Module.End ℝ CanonicalZorn) - axialGrading ^ 2) +
      (1 / 2 : ℝ) • (axialGrading ^ 2 - axialGrading) =
    (LinearMap.id : Module.End ℝ CanonicalZorn)
  noncomm_ring
  module

theorem axialProjectors_sub_eq_axialGrading :
    axialProjectorPlus - axialProjectorMinus = axialGrading := by
  change
    (1 / 2 : ℝ) • (axialGrading + axialGrading ^ 2) -
        (1 / 2 : ℝ) • (axialGrading ^ 2 - axialGrading) =
      axialGrading
  module

theorem axialProjectors_add_nonzero_eq_axialGrading_sq :
    axialProjectorPlus + axialProjectorMinus = axialGrading ^ 2 := by
  change
    (1 / 2 : ℝ) • (axialGrading + axialGrading ^ 2) +
        (1 / 2 : ℝ) • (axialGrading ^ 2 - axialGrading) =
      axialGrading ^ 2
  module

theorem axialProjectorPlus_basis (i : Fin 8) :
    axialProjectorPlus (circularPeirceBasis i) =
      ((axialWeight i + (axialWeight i) ^ 2) / 2) •
        circularPeirceBasis i := by
  have h₂ : (axialGrading ^ 2) (circularPeirceBasis i) =
      (axialWeight i) ^ 2 • circularPeirceBasis i := by
    rw [pow_two, Module.End.mul_apply, axialGrading_basis, map_smul,
      axialGrading_basis, smul_smul, pow_two]
  change (1 / 2 : ℝ) •
      (axialGrading (circularPeirceBasis i) +
        (axialGrading ^ 2) (circularPeirceBasis i)) = _
  rw [axialGrading_basis, h₂]
  module

theorem axialProjectorZero_basis (i : Fin 8) :
    axialProjectorZero (circularPeirceBasis i) =
      (1 - (axialWeight i) ^ 2) • circularPeirceBasis i := by
  have h₂ : (axialGrading ^ 2) (circularPeirceBasis i) =
      (axialWeight i) ^ 2 • circularPeirceBasis i := by
    rw [pow_two, Module.End.mul_apply, axialGrading_basis, map_smul,
      axialGrading_basis, smul_smul, pow_two]
  change circularPeirceBasis i -
      (axialGrading ^ 2) (circularPeirceBasis i) = _
  rw [h₂]
  module

theorem axialProjectorMinus_basis (i : Fin 8) :
    axialProjectorMinus (circularPeirceBasis i) =
      (((axialWeight i) ^ 2 - axialWeight i) / 2) •
        circularPeirceBasis i := by
  have h₂ : (axialGrading ^ 2) (circularPeirceBasis i) =
      (axialWeight i) ^ 2 • circularPeirceBasis i := by
    rw [pow_two, Module.End.mul_apply, axialGrading_basis, map_smul,
      axialGrading_basis, smul_smul, pow_two]
  change (1 / 2 : ℝ) •
      ((axialGrading ^ 2) (circularPeirceBasis i) -
        axialGrading (circularPeirceBasis i)) = _
  rw [h₂, axialGrading_basis]
  module

theorem axialProjectors_apply_add (X : CanonicalZorn) :
    axialProjectorPlus X + axialProjectorZero X + axialProjectorMinus X = X := by
  exact congrArg (fun T : Module.End ℝ CanonicalZorn => T X)
    axialProjectors_add_eq_id

def axialProjectorPlusWeight (i : Fin 8) : ℝ :=
  (axialWeight i + (axialWeight i) ^ 2) / 2

def axialProjectorZeroWeight (i : Fin 8) : ℝ :=
  1 - (axialWeight i) ^ 2

def axialProjectorMinusWeight (i : Fin 8) : ℝ :=
  ((axialWeight i) ^ 2 - axialWeight i) / 2

theorem axialGrading_mul_axialProjectorPlus :
    axialGrading * axialProjectorPlus = axialProjectorPlus := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorPlus_basis, map_smul,
    axialGrading_basis]
  fin_cases i <;> norm_num [axialProjectorPlusWeight, axialWeight]

theorem axialGrading_mul_axialProjectorZero :
    axialGrading * axialProjectorZero = 0 := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorZero_basis, map_smul,
    axialGrading_basis]
  fin_cases i <;> norm_num [axialProjectorZeroWeight, axialWeight]

theorem axialGrading_mul_axialProjectorMinus :
    axialGrading * axialProjectorMinus =
      -axialProjectorMinus := by
  apply circularPeirceBasis.ext
  intro i
  change axialGrading (axialProjectorMinus (circularPeirceBasis i)) =
    -axialProjectorMinus (circularPeirceBasis i)
  rw [axialProjectorMinus_basis, map_smul,
    axialGrading_basis]
  fin_cases i <;> norm_num [axialProjectorMinusWeight, axialWeight]

theorem axialProjectorPlus_idempotent :
    axialProjectorPlus * axialProjectorPlus = axialProjectorPlus := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorPlus_basis, map_smul,
    axialProjectorPlus_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorPlusWeight, axialWeight]

theorem axialProjectorZero_idempotent :
    axialProjectorZero * axialProjectorZero = axialProjectorZero := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorZero_basis, map_smul,
    axialProjectorZero_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorZeroWeight, axialWeight]

theorem axialProjectorMinus_idempotent :
    axialProjectorMinus * axialProjectorMinus = axialProjectorMinus := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorMinus_basis, map_smul,
    axialProjectorMinus_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorMinusWeight, axialWeight]

theorem axialProjectorPlus_mul_zero :
    axialProjectorPlus * axialProjectorZero = 0 := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorZero_basis, map_smul,
    axialProjectorPlus_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorPlusWeight,
    axialProjectorZeroWeight, axialWeight]

theorem axialProjectorZero_mul_plus :
    axialProjectorZero * axialProjectorPlus = 0 := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorPlus_basis, map_smul,
    axialProjectorZero_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorPlusWeight,
    axialProjectorZeroWeight, axialWeight]

theorem axialProjectorPlus_mul_minus :
    axialProjectorPlus * axialProjectorMinus = 0 := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorMinus_basis, map_smul,
    axialProjectorPlus_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorPlusWeight,
    axialProjectorMinusWeight, axialWeight]

theorem axialProjectorMinus_mul_plus :
    axialProjectorMinus * axialProjectorPlus = 0 := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorPlus_basis, map_smul,
    axialProjectorMinus_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorPlusWeight,
    axialProjectorMinusWeight, axialWeight]

theorem axialProjectorZero_mul_minus :
    axialProjectorZero * axialProjectorMinus = 0 := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorMinus_basis, map_smul,
    axialProjectorZero_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorZeroWeight,
    axialProjectorMinusWeight, axialWeight]

theorem axialProjectorMinus_mul_zero :
    axialProjectorMinus * axialProjectorZero = 0 := by
  apply circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, axialProjectorZero_basis, map_smul,
    axialProjectorMinus_basis, smul_smul]
  fin_cases i <;> norm_num [axialProjectorZeroWeight,
    axialProjectorMinusWeight, axialWeight]

noncomputable def axialProjectorPlusCoordinate : Module.End ℝ Coordinate :=
  coordinateEquiv.toLinearMap.comp
    (axialProjectorPlus.comp coordinateEquiv.symm.toLinearMap)

noncomputable def axialProjectorZeroCoordinate : Module.End ℝ Coordinate :=
  coordinateEquiv.toLinearMap.comp
    (axialProjectorZero.comp coordinateEquiv.symm.toLinearMap)

noncomputable def axialProjectorMinusCoordinate : Module.End ℝ Coordinate :=
  coordinateEquiv.toLinearMap.comp
    (axialProjectorMinus.comp coordinateEquiv.symm.toLinearMap)

@[simp] theorem axialProjectorPlusCoordinate_apply (x : Coordinate) :
    axialProjectorPlusCoordinate x =
      coordinateEquiv (axialProjectorPlus (coordinateEquiv.symm x)) := by
  rfl

@[simp] theorem axialProjectorZeroCoordinate_apply (x : Coordinate) :
    axialProjectorZeroCoordinate x =
      coordinateEquiv (axialProjectorZero (coordinateEquiv.symm x)) := by
  rfl

@[simp] theorem axialProjectorMinusCoordinate_apply (x : Coordinate) :
    axialProjectorMinusCoordinate x =
      coordinateEquiv (axialProjectorMinus (coordinateEquiv.symm x)) := by
  rfl

theorem axialProjectorPlusCoordinate_on_single (i : Fin 8) :
    axialProjectorPlusCoordinate (Pi.single i (1 : ℝ)) =
      axialProjectorPlusWeight i • (Pi.single i (1 : ℝ) : Coordinate) := by
  rw [axialProjectorPlusCoordinate_apply, coordinateEquiv_symm_single,
    ← circularPeirceBasis_apply i, axialProjectorPlus_basis,
    coordinateEquiv.map_smul,
    circularPeirceBasis_apply, coordinateEquiv_apply_frame]
  rfl

theorem axialProjectorZeroCoordinate_on_single (i : Fin 8) :
    axialProjectorZeroCoordinate (Pi.single i (1 : ℝ)) =
      axialProjectorZeroWeight i • (Pi.single i (1 : ℝ) : Coordinate) := by
  rw [axialProjectorZeroCoordinate_apply, coordinateEquiv_symm_single,
    ← circularPeirceBasis_apply i, axialProjectorZero_basis,
    coordinateEquiv.map_smul,
    circularPeirceBasis_apply, coordinateEquiv_apply_frame]
  rfl

theorem axialProjectorMinusCoordinate_on_single (i : Fin 8) :
    axialProjectorMinusCoordinate (Pi.single i (1 : ℝ)) =
      axialProjectorMinusWeight i • (Pi.single i (1 : ℝ) : Coordinate) := by
  rw [axialProjectorMinusCoordinate_apply, coordinateEquiv_symm_single,
    ← circularPeirceBasis_apply i, axialProjectorMinus_basis,
    coordinateEquiv.map_smul,
    circularPeirceBasis_apply, coordinateEquiv_apply_frame]
  rfl

theorem coordinateOperatorMatrix_eq_diagonal
    (T : Module.End ℝ Coordinate) (w : Fin 8 → ℝ)
    (hT : ∀ j : Fin 8,
      T (Pi.single j (1 : ℝ) : Coordinate) =
        w j • (Pi.single j (1 : ℝ) : Coordinate)) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) T =
      Matrix.diagonal w := by
  ext i j
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, hT]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, Matrix.diagonal]
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

noncomputable def axialProjectorPlusMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    axialProjectorPlusCoordinate

noncomputable def axialProjectorZeroMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    axialProjectorZeroCoordinate

noncomputable def axialProjectorMinusMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    axialProjectorMinusCoordinate

theorem axialProjectorPlusMatrix_eq_diagonal :
    axialProjectorPlusMatrix = Matrix.diagonal axialProjectorPlusWeight := by
  exact coordinateOperatorMatrix_eq_diagonal _ _
    axialProjectorPlusCoordinate_on_single

theorem axialProjectorZeroMatrix_eq_diagonal :
    axialProjectorZeroMatrix = Matrix.diagonal axialProjectorZeroWeight := by
  exact coordinateOperatorMatrix_eq_diagonal _ _
    axialProjectorZeroCoordinate_on_single

theorem axialProjectorMinusMatrix_eq_diagonal :
    axialProjectorMinusMatrix = Matrix.diagonal axialProjectorMinusWeight := by
  exact coordinateOperatorMatrix_eq_diagonal _ _
    axialProjectorMinusCoordinate_on_single

noncomputable def axialFlowCoordinate (t : ℝ) : Module.End ℝ Coordinate where
  toFun x := fun i => Real.exp (t * axialWeight i) * x i
  map_add' := by
    intro x y
    funext i
    simp only [Pi.add_apply, mul_add]
  map_smul' := by
    intro c x
    funext i
    change Real.exp (t * axialWeight i) * (c * x i) =
      c * (Real.exp (t * axialWeight i) * x i)
    ring

@[simp] theorem axialFlowCoordinate_apply (t : ℝ) (x : Coordinate)
    (i : Fin 8) :
    axialFlowCoordinate t x i = Real.exp (t * axialWeight i) * x i := by
  rfl

theorem axialFlowCoordinate_on_single (t : ℝ) (i : Fin 8) :
    axialFlowCoordinate t (Pi.single i (1 : ℝ)) =
      Real.exp (t * axialWeight i) • (Pi.single i (1 : ℝ) : Coordinate) := by
  funext j
  simp [axialFlowCoordinate, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem axialFlowCoordinate_zero :
    axialFlowCoordinate 0 = (LinearMap.id : Coordinate →ₗ[ℝ] Coordinate) := by
  ext x i
  simp [axialFlowCoordinate]

theorem axialFlowCoordinate_add (s t : ℝ) :
      axialFlowCoordinate (s + t) =
      axialFlowCoordinate s * axialFlowCoordinate t := by
  apply LinearMap.ext
  intro x
  funext i
  change Real.exp ((s + t) * axialWeight i) * x i =
    Real.exp (s * axialWeight i) *
      (Real.exp (t * axialWeight i) * x i)
  rw [add_mul, Real.exp_add]
  ring

noncomputable def axialFlow (t : ℝ) : Module.End ℝ CanonicalZorn :=
  coordinateEquiv.symm.toLinearMap.comp
    ((axialFlowCoordinate t).comp coordinateEquiv.toLinearMap)

@[simp] theorem axialFlow_apply (t : ℝ) (X : CanonicalZorn) :
    axialFlow t X =
      coordinateEquiv.symm (axialFlowCoordinate t (coordinateEquiv X)) := by
  rfl

theorem coordinateEquiv_axialFlow_apply (t : ℝ) (X : CanonicalZorn)
    (i : Fin 8) :
    coordinateEquiv (axialFlow t X) i =
      Real.exp (t * axialWeight i) * coordinateEquiv X i := by
  rw [axialFlow_apply, coordinateEquiv.apply_symm_apply,
    axialFlowCoordinate_apply]

theorem axialFlow_zero_apply (X : CanonicalZorn) :
    axialFlow 0 X = X := by
  apply coordinateEquiv.injective
  funext i
  rw [coordinateEquiv_axialFlow_apply]
  simp

theorem axialFlow_add_apply (s t : ℝ) (X : CanonicalZorn) :
    axialFlow (s + t) X = axialFlow s (axialFlow t X) := by
  apply coordinateEquiv.injective
  funext i
  rw [coordinateEquiv_axialFlow_apply,
    coordinateEquiv_axialFlow_apply, coordinateEquiv_axialFlow_apply,
    add_mul, Real.exp_add]
  ring

theorem axialFlow_basis (t : ℝ) (i : Fin 8) :
    axialFlow t (circularPeirceBasis i) =
      Real.exp (t * axialWeight i) • circularPeirceBasis i := by
  apply coordinateEquiv.injective
  funext j
  rw [coordinateEquiv_axialFlow_apply, circularPeirceBasis_apply,
    coordinateEquiv_apply_frame]
  simp only [Pi.single_apply]
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem axialGrading_mul_axialFlow (t : ℝ) :
    axialGrading * axialFlow t = axialFlow t * axialGrading := by
  apply circularPeirceBasis.ext
  intro i
  change axialGrading (axialFlow t (circularPeirceBasis i)) =
    axialFlow t (axialGrading (circularPeirceBasis i))
  rw [axialFlow_basis, map_smul, axialGrading_basis,
    map_smul, axialFlow_basis]
  module

theorem axialFlow_mul_axialProjectorPlus (t : ℝ) :
    axialFlow t * axialProjectorPlus =
      axialProjectorPlus * axialFlow t := by
  apply circularPeirceBasis.ext
  intro i
  change axialFlow t (axialProjectorPlus (circularPeirceBasis i)) =
    axialProjectorPlus (axialFlow t (circularPeirceBasis i))
  rw [axialProjectorPlus_basis, map_smul, axialFlow_basis,
    map_smul, axialProjectorPlus_basis]
  module

theorem axialFlow_mul_axialProjectorZero (t : ℝ) :
    axialFlow t * axialProjectorZero =
      axialProjectorZero * axialFlow t := by
  apply circularPeirceBasis.ext
  intro i
  change axialFlow t (axialProjectorZero (circularPeirceBasis i)) =
    axialProjectorZero (axialFlow t (circularPeirceBasis i))
  rw [axialProjectorZero_basis, map_smul, axialFlow_basis,
    map_smul, axialProjectorZero_basis]
  module

theorem axialFlow_mul_axialProjectorMinus (t : ℝ) :
    axialFlow t * axialProjectorMinus =
      axialProjectorMinus * axialFlow t := by
  apply circularPeirceBasis.ext
  intro i
  change axialFlow t (axialProjectorMinus (circularPeirceBasis i)) =
    axialProjectorMinus (axialFlow t (circularPeirceBasis i))
  rw [axialProjectorMinus_basis, map_smul, axialFlow_basis,
    map_smul, axialProjectorMinus_basis]
  module

noncomputable def axialFlowMatrix (t : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (axialFlowCoordinate t)

theorem axialFlowMatrix_eq_diagonal (t : ℝ) :
    axialFlowMatrix t =
      Matrix.diagonal (fun i => Real.exp (t * axialWeight i)) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _
    (axialFlowCoordinate_on_single t)

noncomputable def axialGradingCoordinate : Module.End ℝ Coordinate :=
  coordinateEquiv.toLinearMap.comp
    (axialGrading.comp coordinateEquiv.symm.toLinearMap)

@[simp] theorem axialGradingCoordinate_apply (x : Coordinate) :
    axialGradingCoordinate x =
      coordinateEquiv (axialGrading (coordinateEquiv.symm x)) := by
  rfl

theorem axialGradingCoordinate_on_single (i : Fin 8) :
    axialGradingCoordinate (Pi.single i (1 : ℝ)) =
      axialWeight i • (Pi.single i (1 : ℝ) : Coordinate) := by
  rw [axialGradingCoordinate_apply, coordinateEquiv_symm_single]
  rw [← circularPeirceBasis_apply i, axialGrading_basis]
  rw [coordinateEquiv.map_smul, circularPeirceBasis_apply,
    coordinateEquiv_apply_frame]

noncomputable def axialGradingMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    axialGradingCoordinate

theorem axialGradingMatrix_apply (i j : Fin 8) :
    axialGradingMatrix i j =
      (axialGradingCoordinate (Pi.single j (1 : ℝ) : Coordinate)) i := by
  rw [axialGradingMatrix, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]

theorem axialGradingMatrix_column (j : Fin 8) :
    (fun i => axialGradingMatrix i j) =
      axialWeight j • (Pi.single j (1 : ℝ) : Coordinate) := by
  funext i
  rw [axialGradingMatrix_apply, axialGradingCoordinate_on_single]

theorem axialGradingMatrix_eq_diagonal :
    axialGradingMatrix = Matrix.diagonal axialWeight := by
  ext i j
  rw [axialGradingMatrix_apply, axialGradingCoordinate_on_single]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Matrix.diagonal]
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

theorem axialGrading_apply_weighted_coordinates (X : CanonicalZorn) :
    axialGrading X =
      ∑ i : Fin 8,
        axialWeight i •
          (coordinateEquiv X i • circularPeirceBasis i) := by
  calc
    axialGrading X =
        axialGrading
          (∑ i : Fin 8,
            circularPeirceBasis.equivFun X i • circularPeirceBasis i) := by
      rw [circularPeirceBasis_sum_repr]
    _ = ∑ i : Fin 8,
        axialWeight i •
          (circularPeirceBasis.equivFun X i • circularPeirceBasis i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, axialGrading_basis]
      simp [smul_smul, mul_comm]
    _ = ∑ i : Fin 8,
      axialWeight i •
          (coordinateEquiv X i • circularPeirceBasis i) := by
      rfl

theorem coordinateEquiv_axialGrading_apply (X : CanonicalZorn) (j : Fin 8) :
    coordinateEquiv (axialGrading X) j =
      axialWeight j * coordinateEquiv X j := by
  rw [axialGrading_apply_weighted_coordinates]
  simp only [map_sum, map_smul, circularPeirceBasis_apply,
    coordinateEquiv_apply_frame]
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

def axialEigenspace (w : ℝ) : Submodule ℝ CanonicalZorn :=
  LinearMap.ker
    (axialGrading - w • (LinearMap.id : CanonicalZorn →ₗ[ℝ] CanonicalZorn))

theorem mem_axialEigenspace_iff (w : ℝ) (X : CanonicalZorn) :
    X ∈ axialEigenspace w ↔ axialGrading X = w • X := by
  constructor
  · intro h
    have hzero :
        (axialGrading -
          w • (LinearMap.id : CanonicalZorn →ₗ[ℝ] CanonicalZorn)) X = 0 := h
    have hsub : axialGrading X =
        (w • (LinearMap.id : CanonicalZorn →ₗ[ℝ] CanonicalZorn)) X :=
      sub_eq_zero.mp hzero
    simpa [LinearMap.smul_apply] using hsub
  · intro h
    have hsub : axialGrading X =
        (w • (LinearMap.id : CanonicalZorn →ₗ[ℝ] CanonicalZorn)) X := by
      simpa [LinearMap.smul_apply] using h
    have hzero :
        (axialGrading -
          w • (LinearMap.id : CanonicalZorn →ₗ[ℝ] CanonicalZorn)) X = 0 :=
      sub_eq_zero.mpr hsub
    exact hzero

theorem axialEigenspace_inf_eq_bot_of_ne (w v : ℝ) (hne : w ≠ v) :
    axialEigenspace w ⊓ axialEigenspace v = ⊥ := by
  apply le_antisymm
  · intro X hX
    rcases hX with ⟨hw, hv⟩
    change X = 0
    have hw' := (mem_axialEigenspace_iff w X).mp hw
    have hv' := (mem_axialEigenspace_iff v X).mp hv
    have hscalar : (w - v) • X = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (hw'.symm.trans hv')
    rcases smul_eq_zero.mp hscalar with hzero | hXzero
    · exact (hne (sub_eq_zero.mp hzero)).elim
    · exact hXzero
  · exact bot_le

theorem axialProjectorPlus_apply_of_mem_axialEigenspace_one
    (X : CanonicalZorn) (hX : X ∈ axialEigenspace 1) :
    axialProjectorPlus X = X := by
  have h : axialGrading X = X := by
    simpa using (mem_axialEigenspace_iff 1 X).mp hX
  have h₂ : (axialGrading ^ 2) X = X := by
    rw [pow_two, Module.End.mul_apply, h]
    exact h
  change (1 / 2 : ℝ) • (axialGrading X + (axialGrading ^ 2) X) = X
  rw [h, h₂]
  module

theorem axialProjectorZero_apply_of_mem_axialEigenspace_zero
    (X : CanonicalZorn) (hX : X ∈ axialEigenspace 0) :
    axialProjectorZero X = X := by
  have h : axialGrading X = 0 := by
    simpa using (mem_axialEigenspace_iff 0 X).mp hX
  have h₂ : (axialGrading ^ 2) X = 0 := by
    rw [pow_two, Module.End.mul_apply, h]
    exact map_zero axialGrading
  change X - (axialGrading ^ 2) X = X
  rw [h₂]
  simp

theorem axialProjectorMinus_apply_of_mem_axialEigenspace_neg_one
    (X : CanonicalZorn) (hX : X ∈ axialEigenspace (-1)) :
    axialProjectorMinus X = X := by
  have h : axialGrading X = -X := by
    simpa using (mem_axialEigenspace_iff (-1) X).mp hX
  have h₂ : (axialGrading ^ 2) X = X := by
    rw [pow_two, Module.End.mul_apply, h]
    rw [map_neg, h, neg_neg]
  change (1 / 2 : ℝ) • ((axialGrading ^ 2) X - axialGrading X) = X
  rw [h, h₂]
  module

theorem axialProjectorPlus_range_le_axialEigenspace_one :
    LinearMap.range axialProjectorPlus ≤ axialEigenspace 1 := by
  rintro X ⟨Y, rfl⟩
  rw [mem_axialEigenspace_iff]
  have h := congrArg (fun T : Module.End ℝ CanonicalZorn => T Y)
    axialGrading_mul_axialProjectorPlus
  change axialGrading (axialProjectorPlus Y) = axialProjectorPlus Y at h
  simpa using h

theorem axialEigenspace_one_le_axialProjectorPlus_range :
    axialEigenspace 1 ≤ LinearMap.range axialProjectorPlus := by
  intro X hX
  exact ⟨X, axialProjectorPlus_apply_of_mem_axialEigenspace_one X hX⟩

theorem axialProjectorPlus_range_eq_axialEigenspace_one :
    LinearMap.range axialProjectorPlus = axialEigenspace 1 := by
  exact le_antisymm axialProjectorPlus_range_le_axialEigenspace_one
    axialEigenspace_one_le_axialProjectorPlus_range

theorem axialProjectorZero_range_le_axialEigenspace_zero :
    LinearMap.range axialProjectorZero ≤ axialEigenspace 0 := by
  rintro X ⟨Y, rfl⟩
  rw [mem_axialEigenspace_iff]
  have h := congrArg (fun T : Module.End ℝ CanonicalZorn => T Y)
    axialGrading_mul_axialProjectorZero
  change axialGrading (axialProjectorZero Y) = 0 at h
  simpa using h

theorem axialEigenspace_zero_le_axialProjectorZero_range :
    axialEigenspace 0 ≤ LinearMap.range axialProjectorZero := by
  intro X hX
  exact ⟨X, axialProjectorZero_apply_of_mem_axialEigenspace_zero X hX⟩

theorem axialProjectorZero_range_eq_axialEigenspace_zero :
    LinearMap.range axialProjectorZero = axialEigenspace 0 := by
  exact le_antisymm axialProjectorZero_range_le_axialEigenspace_zero
    axialEigenspace_zero_le_axialProjectorZero_range

theorem axialProjectorMinus_range_le_axialEigenspace_neg_one :
    LinearMap.range axialProjectorMinus ≤ axialEigenspace (-1) := by
  rintro X ⟨Y, rfl⟩
  rw [mem_axialEigenspace_iff]
  have h := congrArg (fun T : Module.End ℝ CanonicalZorn => T Y)
    axialGrading_mul_axialProjectorMinus
  change axialGrading (axialProjectorMinus Y) =
    -axialProjectorMinus Y at h
  simpa using h

theorem axialEigenspace_neg_one_le_axialProjectorMinus_range :
    axialEigenspace (-1) ≤ LinearMap.range axialProjectorMinus := by
  intro X hX
  exact ⟨X, axialProjectorMinus_apply_of_mem_axialEigenspace_neg_one X hX⟩

theorem axialProjectorMinus_range_eq_axialEigenspace_neg_one :
    LinearMap.range axialProjectorMinus = axialEigenspace (-1) := by
  exact le_antisymm axialProjectorMinus_range_le_axialEigenspace_neg_one
    axialEigenspace_neg_one_le_axialProjectorMinus_range

theorem axialProjectorPlus_apply_mem_axialEigenspace_one (X : CanonicalZorn) :
    axialProjectorPlus X ∈ axialEigenspace 1 := by
  exact axialProjectorPlus_range_le_axialEigenspace_one ⟨X, rfl⟩

theorem axialProjectorZero_apply_mem_axialEigenspace_zero (X : CanonicalZorn) :
    axialProjectorZero X ∈ axialEigenspace 0 := by
  exact axialProjectorZero_range_le_axialEigenspace_zero ⟨X, rfl⟩

theorem axialProjectorMinus_apply_mem_axialEigenspace_neg_one
    (X : CanonicalZorn) :
    axialProjectorMinus X ∈ axialEigenspace (-1) := by
  exact axialProjectorMinus_range_le_axialEigenspace_neg_one ⟨X, rfl⟩

theorem axialSpectralDecomposition (X : CanonicalZorn) :
    X = axialProjectorPlus X + axialProjectorZero X + axialProjectorMinus X := by
  exact (axialProjectors_apply_add X).symm

theorem coordinateEquiv_eq_zero_of_mem_axialEigenspace
    (w : ℝ) (X : CanonicalZorn) (j : Fin 8)
    (hweight : axialWeight j ≠ w)
    (hX : X ∈ axialEigenspace w) :
    coordinateEquiv X j = 0 := by
  have h := (mem_axialEigenspace_iff w X).mp hX
  have hc := congrArg (fun Y : CanonicalZorn => coordinateEquiv Y j) h
  change coordinateEquiv (axialGrading X) j =
    coordinateEquiv (w • X) j at hc
  rw [coordinateEquiv_axialGrading_apply] at hc
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at hc
  have hmul : (axialWeight j - w) * coordinateEquiv X j = 0 := by
    linarith
  rcases mul_eq_zero.mp hmul with hzero | hcoord
  · exact (hweight (sub_eq_zero.mp hzero)).elim
  · exact hcoord

theorem circularPeirceBasis_mem_axialEigenspace (i : Fin 8) :
    circularPeirceBasis i ∈ axialEigenspace (axialWeight i) := by
  rw [mem_axialEigenspace_iff]
  exact axialGrading_basis i

def zeroWeightSubmodule : Submodule ℝ CanonicalZorn :=
  Submodule.span ℝ ({uPlus, uMinus} : Set CanonicalZorn)

def positiveWeightSubmodule : Submodule ℝ CanonicalZorn :=
  Submodule.span ℝ (Set.range (fun i : Fin 3 => rootPlus i))

def negativeWeightSubmodule : Submodule ℝ CanonicalZorn :=
  Submodule.span ℝ (Set.range (fun i : Fin 3 => rootMinus i))

theorem zeroWeightSubmodule_le_axialEigenspace_zero :
    zeroWeightSubmodule ≤ axialEigenspace 0 := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | rfl)
  · simpa [circularPeirceBasis_zero, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (0 : Fin 8)
  · simpa [circularPeirceBasis_four, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (4 : Fin 8)

theorem positiveWeightSubmodule_le_axialEigenspace_one :
    positiveWeightSubmodule ≤ axialEigenspace 1 := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨i, rfl⟩
  fin_cases i
  · simpa [circularPeirceBasis_one, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (1 : Fin 8)
  · simpa [circularPeirceBasis_two, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (2 : Fin 8)
  · simpa [circularPeirceBasis_three, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (3 : Fin 8)

theorem axialEigenspace_one_le_positiveWeightSubmodule :
    axialEigenspace 1 ≤ positiveWeightSubmodule := by
  intro X hX
  rw [← circularPeirceBasis_sum_repr X]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  fin_cases i
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      1 X 0 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 0 • circularPeirceBasis 0 ∈
      positiveWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using positiveWeightSubmodule.zero_mem
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 1 ∈ positiveWeightSubmodule
      rw [circularPeirceBasis_one]
      exact Submodule.subset_span ⟨0, rfl⟩)
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 2 ∈ positiveWeightSubmodule
      rw [circularPeirceBasis_two]
      exact Submodule.subset_span ⟨1, rfl⟩)
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 3 ∈ positiveWeightSubmodule
      rw [circularPeirceBasis_three]
      exact Submodule.subset_span ⟨2, rfl⟩)
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      1 X 4 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 4 • circularPeirceBasis 4 ∈
      positiveWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using positiveWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      1 X 5 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 5 • circularPeirceBasis 5 ∈
      positiveWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using positiveWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      1 X 6 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 6 • circularPeirceBasis 6 ∈
      positiveWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using positiveWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      1 X 7 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 7 • circularPeirceBasis 7 ∈
      positiveWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using positiveWeightSubmodule.zero_mem

theorem axialEigenspace_zero_le_zeroWeightSubmodule :
    axialEigenspace 0 ≤ zeroWeightSubmodule := by
  intro X hX
  rw [← circularPeirceBasis_sum_repr X]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  fin_cases i
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 0 ∈ zeroWeightSubmodule
      rw [circularPeirceBasis_zero]
      exact Submodule.subset_span (by simp))
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      0 X 1 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 1 • circularPeirceBasis 1 ∈ zeroWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using zeroWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      0 X 2 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 2 • circularPeirceBasis 2 ∈ zeroWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using zeroWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      0 X 3 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 3 • circularPeirceBasis 3 ∈ zeroWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using zeroWeightSubmodule.zero_mem
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 4 ∈ zeroWeightSubmodule
      rw [circularPeirceBasis_four]
      exact Submodule.subset_span (by simp))
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      0 X 5 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 5 • circularPeirceBasis 5 ∈ zeroWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using zeroWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      0 X 6 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 6 • circularPeirceBasis 6 ∈ zeroWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using zeroWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      0 X 7 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 7 • circularPeirceBasis 7 ∈ zeroWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using zeroWeightSubmodule.zero_mem

theorem negativeWeightSubmodule_le_axialEigenspace_neg_one :
    negativeWeightSubmodule ≤ axialEigenspace (-1) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨i, rfl⟩
  fin_cases i
  · simpa [circularPeirceBasis_five, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (5 : Fin 8)
  · simpa [circularPeirceBasis_six, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (6 : Fin 8)
  · simpa [circularPeirceBasis_seven, axialWeight] using
      circularPeirceBasis_mem_axialEigenspace (7 : Fin 8)

theorem axialEigenspace_neg_one_le_negativeWeightSubmodule :
    axialEigenspace (-1) ≤ negativeWeightSubmodule := by
  intro X hX
  rw [← circularPeirceBasis_sum_repr X]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  fin_cases i
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      (-1) X 0 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 0 • circularPeirceBasis 0 ∈ negativeWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using negativeWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      (-1) X 1 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 1 • circularPeirceBasis 1 ∈ negativeWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using negativeWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      (-1) X 2 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 2 • circularPeirceBasis 2 ∈ negativeWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using negativeWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      (-1) X 3 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 3 • circularPeirceBasis 3 ∈ negativeWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using negativeWeightSubmodule.zero_mem
  · have hc := coordinateEquiv_eq_zero_of_mem_axialEigenspace
      (-1) X 4 (by norm_num [axialWeight]) hX
    change coordinateEquiv X 4 • circularPeirceBasis 4 ∈ negativeWeightSubmodule
    rw [hc]
    simpa only [zero_smul] using negativeWeightSubmodule.zero_mem
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 5 ∈ negativeWeightSubmodule
      rw [circularPeirceBasis_five]
      exact Submodule.subset_span ⟨0, rfl⟩)
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 6 ∈ negativeWeightSubmodule
      rw [circularPeirceBasis_six]
      exact Submodule.subset_span ⟨1, rfl⟩)
  · exact Submodule.smul_mem _ _ (by
      change circularPeirceBasis 7 ∈ negativeWeightSubmodule
      rw [circularPeirceBasis_seven]
      exact Submodule.subset_span ⟨2, rfl⟩)

theorem zeroWeightSubmodule_eq_axialEigenspace_zero :
    zeroWeightSubmodule = axialEigenspace 0 :=
  le_antisymm zeroWeightSubmodule_le_axialEigenspace_zero
    axialEigenspace_zero_le_zeroWeightSubmodule

theorem positiveWeightSubmodule_eq_axialEigenspace_one :
    positiveWeightSubmodule = axialEigenspace 1 :=
  le_antisymm positiveWeightSubmodule_le_axialEigenspace_one
    axialEigenspace_one_le_positiveWeightSubmodule

theorem negativeWeightSubmodule_eq_axialEigenspace_neg_one :
    negativeWeightSubmodule = axialEigenspace (-1) :=
  le_antisymm negativeWeightSubmodule_le_axialEigenspace_neg_one
    axialEigenspace_neg_one_le_negativeWeightSubmodule

theorem weightSubmodules_sup_eq_top :
    zeroWeightSubmodule ⊔ positiveWeightSubmodule ⊔ negativeWeightSubmodule =
      (⊤ : Submodule ℝ CanonicalZorn) := by
  refine le_antisymm le_top ?_
  rw [← circularPeirceBasis_span_top]
  refine Submodule.span_le.2 ?_
  rintro x ⟨i, rfl⟩
  fin_cases i
  · change circularPeirceBasis 0 ∈ _
    rw [circularPeirceBasis_zero]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.subset_span (by simp)))
  · change circularPeirceBasis 1 ∈ _
    rw [circularPeirceBasis_one]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.subset_span ⟨0, rfl⟩))
  · change circularPeirceBasis 2 ∈ _
    rw [circularPeirceBasis_two]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.subset_span ⟨1, rfl⟩))
  · change circularPeirceBasis 3 ∈ _
    rw [circularPeirceBasis_three]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.subset_span ⟨2, rfl⟩))
  · change circularPeirceBasis 4 ∈ _
    rw [circularPeirceBasis_four]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.subset_span (by simp)))
  · change circularPeirceBasis 5 ∈ _
    rw [circularPeirceBasis_five]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨0, rfl⟩)
  · change circularPeirceBasis 6 ∈ _
    rw [circularPeirceBasis_six]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨1, rfl⟩)
  · change circularPeirceBasis 7 ∈ _
    rw [circularPeirceBasis_seven]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨2, rfl⟩)

theorem axialEigenspaces_sup_eq_top :
    axialEigenspace 0 ⊔ axialEigenspace 1 ⊔ axialEigenspace (-1) =
      (⊤ : Submodule ℝ CanonicalZorn) := by
  rw [← zeroWeightSubmodule_eq_axialEigenspace_zero,
    ← positiveWeightSubmodule_eq_axialEigenspace_one,
    ← negativeWeightSubmodule_eq_axialEigenspace_neg_one]
  exact weightSubmodules_sup_eq_top

theorem axialProjector_ranges_sup_eq_top :
    LinearMap.range axialProjectorZero ⊔
        LinearMap.range axialProjectorPlus ⊔
          LinearMap.range axialProjectorMinus =
      (⊤ : Submodule ℝ CanonicalZorn) := by
  rw [axialProjectorZero_range_eq_axialEigenspace_zero,
    axialProjectorPlus_range_eq_axialEigenspace_one,
    axialProjectorMinus_range_eq_axialEigenspace_neg_one]
  exact axialEigenspaces_sup_eq_top

end InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
