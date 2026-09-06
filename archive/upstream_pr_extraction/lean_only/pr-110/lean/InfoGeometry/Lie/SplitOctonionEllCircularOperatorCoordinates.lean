import InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
import InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
import InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge

/-!
# Operatorial coordinates in the circular Peirce basis

This owner exposes the already-proved `Module.Basis` and axial-flow facts in
the natural eight coordinates.  Every statement is linear-operator algebra on
the full split-octonion carrier; no associativity of its multiplication is
used or asserted.
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates

open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge

abbrev CanonicalZorn :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

theorem circularPeirceBasis_coordinate_expansion (X : CanonicalZorn) :
    X =
      coordinateEquiv X 0 • uPlus +
        coordinateEquiv X 1 • rootPlus 0 +
        coordinateEquiv X 2 • rootPlus 1 +
        coordinateEquiv X 3 • rootPlus 2 +
        coordinateEquiv X 4 • uMinus +
        coordinateEquiv X 5 • rootMinus 0 +
        coordinateEquiv X 6 • rootMinus 1 +
        coordinateEquiv X 7 • rootMinus 2 := by
  calc
    X = ∑ i : Fin 8,
        (circularPeirceBasis.equivFun X i) • circularPeirceBasis i :=
      (circularPeirceBasis_sum_repr X).symm
    _ = _ := by
      rw [Fin.sum_univ_eight]
      simp only [circularPeirceBasis_zero, circularPeirceBasis_one,
        circularPeirceBasis_two, circularPeirceBasis_three,
        circularPeirceBasis_four, circularPeirceBasis_five,
        circularPeirceBasis_six, circularPeirceBasis_seven]
      simp only [coordinateEquiv]

theorem axialFlow_coordinate_expansion (t : ℝ) (X : CanonicalZorn) :
    axialFlow t X =
      ∑ i : Fin 8,
        (Real.exp (t * axialWeight i) * coordinateEquiv X i) •
          circularPeirceBasis i := by
  calc
    axialFlow t X =
        ∑ i : Fin 8, coordinateEquiv (axialFlow t X) i •
          circularPeirceBasis i :=
      (circularPeirceBasis_sum_repr (axialFlow t X)).symm
    _ = ∑ i : Fin 8,
        (Real.exp (t * axialWeight i) * coordinateEquiv X i) •
          circularPeirceBasis i := by
      congr 1
      funext i
      rw [coordinateEquiv_axialFlow_apply]

theorem axialGrading_coordinate_expansion (X : CanonicalZorn) :
    axialGrading X =
      ∑ i : Fin 8,
        (axialWeight i * coordinateEquiv X i) •
          circularPeirceBasis i := by
  calc
    axialGrading X =
        ∑ i : Fin 8, coordinateEquiv (axialGrading X) i •
          circularPeirceBasis i :=
      (circularPeirceBasis_sum_repr (axialGrading X)).symm
    _ = ∑ i : Fin 8,
        (axialWeight i * coordinateEquiv X i) •
          circularPeirceBasis i := by
      congr 1
      funext i
      rw [coordinateEquiv_axialGrading_apply]

theorem ellCommutatorCoordinate_apply_diagonal (x : Coordinate) (i : Fin 8) :
    ellCommutatorCoordinate x i =
      (2 : ℝ) * axialWeight i * x i := by
  have hcomm : ellCommutator = (2 : ℝ) • axialGrading := by
    apply LinearMap.ext
    intro X
    simp [axialGrading]
  rw [ellCommutatorCoordinate_apply, hcomm]
  simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [coordinateEquiv_axialGrading_apply]
  simp only [coordinateEquiv.apply_symm_apply]
  ring

theorem leftCoordinateOperator_uPlus_apply (x : Coordinate) :
    leftCoordinateOperator uPlus x =
      fun i => if i.val < 4 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val < 4 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val < 4
        · simp only [Pi.add_apply, if_pos hi]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val < 4
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi, RingHom.id_apply]
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero,
            RingHom.id_apply] }
  have hT : leftCoordinateOperator uPlus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (uPlus * frame i) =
          if i.val < 4 then Pi.single i 1 else 0 := by
      rw [uPlus_mul_frame]
      fin_cases i
      · simpa [frame] using coordinateEquiv_apply_frame 0
      · simpa [frame] using coordinateEquiv_apply_frame 1
      · simpa [frame] using coordinateEquiv_apply_frame 2
      · simpa [frame] using coordinateEquiv_apply_frame 3
      · simp
      · simp
      · simp
      · simp
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [leftCoordinateOperator_on_frame]
    rw [hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

theorem rightCoordinateOperator_uMinus_apply (x : Coordinate) :
    rightCoordinateOperator uMinus x =
      fun i => if 0 < i.val ∧ i.val < 5 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if 0 < i.val ∧ i.val < 5 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : 0 < i.val ∧ i.val < 5
        · simp only [Pi.add_apply, if_pos hi, add_zero, zero_add]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : 0 < i.val ∧ i.val < 5
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi] <;> rfl
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero] <;> rfl }
  have hT : rightCoordinateOperator uMinus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (frame i * uMinus) =
          if 0 < i.val ∧ i.val < 5 then Pi.single i 1 else 0 := by
      rw [frame_mul_uMinus]
      fin_cases i
      · simp
      · simpa [frame] using coordinateEquiv_apply_frame 1
      · simpa [frame] using coordinateEquiv_apply_frame 2
      · simpa [frame] using coordinateEquiv_apply_frame 3
      · simpa [frame] using coordinateEquiv_apply_frame 4
      · simp
      · simp
      · simp
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [rightCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

theorem leftCoordinateOperator_uMinus_apply (x : Coordinate) :
    leftCoordinateOperator uMinus x =
      fun i => if i.val ≥ 4 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val ≥ 4 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val ≥ 4
        · simp only [Pi.add_apply, if_pos hi, add_zero, zero_add]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val ≥ 4
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi] <;> rfl
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero] <;> rfl }
  have hT : leftCoordinateOperator uMinus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (uMinus * frame i) =
          if i.val ≥ 4 then Pi.single i 1 else 0 := by
      rw [uMinus_mul_frame]
      fin_cases i
      · simp
      · simp
      · simp
      · simp
      · simpa [frame] using coordinateEquiv_apply_frame 4
      · simpa [frame] using coordinateEquiv_apply_frame 5
      · simpa [frame] using coordinateEquiv_apply_frame 6
      · simpa [frame] using coordinateEquiv_apply_frame 7
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [leftCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

theorem rightCoordinateOperator_uPlus_apply (x : Coordinate) :
    rightCoordinateOperator uPlus x =
      fun i => if i.val = 0 ∨ i.val ≥ 5 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val = 0 ∨ i.val ≥ 5 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val = 0 ∨ i.val ≥ 5
        · simp only [Pi.add_apply, if_pos hi, add_zero, zero_add]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val = 0 ∨ i.val ≥ 5
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi] <;> rfl
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero] <;> rfl }
  have hT : rightCoordinateOperator uPlus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (frame i * uPlus) =
          if i.val = 0 ∨ i.val ≥ 5 then Pi.single i 1 else 0 := by
      rw [frame_mul_uPlus]
      fin_cases i
      · simpa [frame] using coordinateEquiv_apply_frame 0
      · simp
      · simp
      · simp
      · simp
      · simpa [frame] using coordinateEquiv_apply_frame 5
      · simpa [frame] using coordinateEquiv_apply_frame 6
      · simpa [frame] using coordinateEquiv_apply_frame 7
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [rightCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

/-- The native Zorn multiplication is represented in the circular coordinates
by the bilinear basis-product kernel.  This is a coordinate expansion only;
it does not reassociate any triple product and does not assert associativity. -/
theorem coordinateEquiv_mul_basis_kernel (X Y : CanonicalZorn) :
    coordinateEquiv (X * Y) =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (coordinateEquiv X i * coordinateEquiv Y j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
  have hX := circularPeirceBasis_sum_repr X
  have hY := circularPeirceBasis_sum_repr Y
  have hX' : ∑ i : Fin 8, coordinateEquiv X i • circularPeirceBasis i = X := by
    simpa [coordinateEquiv] using hX
  have hY' : ∑ i : Fin 8, coordinateEquiv Y i • circularPeirceBasis i = Y := by
    simpa [coordinateEquiv] using hY
  calc
    coordinateEquiv (X * Y) = coordinateEquiv
        ((∑ i : Fin 8, (coordinateEquiv X i) • circularPeirceBasis i) *
          (∑ j : Fin 8, (coordinateEquiv Y j) • circularPeirceBasis j)) := by
      exact congrArg coordinateEquiv
        (congrArg₂ (fun A B : CanonicalZorn => A * B) hX'.symm hY'.symm)
    _ = ∑ i : Fin 8, ∑ j : Fin 8,
        (coordinateEquiv X i * coordinateEquiv Y j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
      have hprod :
          (∑ i : Fin 8, coordinateEquiv X i • circularPeirceBasis i) *
              (∑ j : Fin 8, coordinateEquiv Y j • circularPeirceBasis j) =
              ∑ i : Fin 8, ∑ j : Fin 8,
              (coordinateEquiv X i * coordinateEquiv Y j) •
                (circularPeirceBasis i * circularPeirceBasis j) := by
        change rightMultiplication
          (∑ j : Fin 8, coordinateEquiv Y j • circularPeirceBasis j)
          (∑ i : Fin 8, coordinateEquiv X i • circularPeirceBasis i) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [rightMultiplication_apply]
        change (coordinateEquiv X i • circularPeirceBasis i) *
          (∑ j : Fin 8, coordinateEquiv Y j • circularPeirceBasis j) = _
        rw [← leftMultiplication_apply, map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
          (coordinateEquiv X i • circularPeirceBasis i)
          (coordinateEquiv Y j • circularPeirceBasis j) = _
        rw [zMul_smul_right, zMul_smul_left, smul_smul]
        change _ = (coordinateEquiv X i * coordinateEquiv Y j) •
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
            (circularPeirceBasis i) (circularPeirceBasis j)
        rw [mul_comm]
      rw [hprod, map_sum coordinateEquiv]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_sum coordinateEquiv]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]

theorem leftCoordinateOperator_basis_kernel
    (A : CanonicalZorn) (x : Coordinate) :
    leftCoordinateOperator A x =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (coordinateEquiv A i * x j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
  rw [leftCoordinateOperator_apply]
  rw [coordinateEquiv_mul_basis_kernel]
  simp only [coordinateEquiv.apply_symm_apply]

theorem rightCoordinateOperator_basis_kernel
    (A : CanonicalZorn) (x : Coordinate) :
    rightCoordinateOperator A x =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (x i * coordinateEquiv A j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
  rw [rightCoordinateOperator_apply]
  rw [coordinateEquiv_mul_basis_kernel]
  simp only [coordinateEquiv.apply_symm_apply]

noncomputable def leftCoordinateOperatorMatrix (A : CanonicalZorn) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (leftCoordinateOperator A)

theorem leftCoordinateOperatorMatrix_apply (A : CanonicalZorn)
    (i j : Fin 8) :
    leftCoordinateOperatorMatrix A i j =
      ∑ k : Fin 8, coordinateEquiv A k *
        coordinateEquiv (circularPeirceBasis k * circularPeirceBasis j) i := by
  rw [leftCoordinateOperatorMatrix, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]
  rw [leftCoordinateOperator_on_frame]
  rw [coordinateEquiv_mul_basis_kernel]
  rw [Finset.sum_apply]
  classical
  simp only [circularPeirceBasis_apply]
  simp_rw [coordinateEquiv_apply_frame]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single j]
  · simp [Pi.single_apply, smul_eq_mul]
  · intro c hc hcj
    simp [hcj]
  · simp

noncomputable def rightCoordinateOperatorMatrix (A : CanonicalZorn) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (rightCoordinateOperator A)

theorem rightCoordinateOperatorMatrix_apply (A : CanonicalZorn)
    (i j : Fin 8) :
    rightCoordinateOperatorMatrix A i j =
      ∑ k : Fin 8, coordinateEquiv A k *
        coordinateEquiv (circularPeirceBasis j * circularPeirceBasis k) i := by
  rw [rightCoordinateOperatorMatrix, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]
  rw [rightCoordinateOperator_on_frame]
  rw [coordinateEquiv_mul_basis_kernel]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [coordinateEquiv_apply_frame, Pi.single_apply]
  · intro x hx hxj
    simp [hxj]
  · simp

noncomputable def ellCommutatorCoordinateMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    ellCommutatorCoordinate

theorem ellCommutatorCoordinateMatrix_eq_diagonal :
    ellCommutatorCoordinateMatrix =
      Matrix.diagonal (fun i => (2 : ℝ) * axialWeight i) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    ext i
    rw [ellCommutatorCoordinate_apply_diagonal]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, Matrix.diagonal,
      Matrix.one_apply]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

theorem ellCommutatorCoordinateMatrix_eq_two_axialGradingMatrix :
    ellCommutatorCoordinateMatrix = (2 : ℝ) • axialGradingMatrix := by
  rw [ellCommutatorCoordinateMatrix_eq_diagonal, axialGradingMatrix_eq_diagonal]
  ext i j
  simp [Matrix.diagonal]

noncomputable def leftCoordinateOperatorUPlusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (leftCoordinateOperator uPlus)

theorem leftCoordinateOperatorUPlusMatrix_eq_diagonal :
    leftCoordinateOperatorUPlusMatrix =
      Matrix.diagonal (fun i => if i.val < 4 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [leftCoordinateOperator_uPlus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

noncomputable def rightCoordinateOperatorUMinusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (rightCoordinateOperator uMinus)

theorem rightCoordinateOperatorUMinusMatrix_eq_diagonal :
    rightCoordinateOperatorUMinusMatrix =
      Matrix.diagonal (fun i => if 0 < i.val ∧ i.val < 5 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [rightCoordinateOperator_uMinus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

noncomputable def leftCoordinateOperatorUMinusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (leftCoordinateOperator uMinus)

theorem leftCoordinateOperatorUMinusMatrix_eq_diagonal :
    leftCoordinateOperatorUMinusMatrix =
      Matrix.diagonal (fun i => if i.val ≥ 4 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [leftCoordinateOperator_uMinus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

noncomputable def rightCoordinateOperatorUPlusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (rightCoordinateOperator uPlus)

theorem rightCoordinateOperatorUPlusMatrix_eq_diagonal :
    rightCoordinateOperatorUPlusMatrix =
      Matrix.diagonal (fun i => if i.val = 0 ∨ i.val ≥ 5 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [rightCoordinateOperator_uPlus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

theorem rightCoordinateOperatorUPlusMatrix_add_rightCoordinateOperatorUMinusMatrix :
    rightCoordinateOperatorUPlusMatrix + rightCoordinateOperatorUMinusMatrix =
      (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [rightCoordinateOperatorUPlusMatrix_eq_diagonal,
    rightCoordinateOperatorUMinusMatrix_eq_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    fin_cases i <;> simp [Matrix.diagonal, Matrix.one_apply]
  · simp [Matrix.diagonal, Matrix.one_apply, h]

theorem leftCoordinateOperatorUPlusMatrix_add_leftCoordinateOperatorUMinusMatrix :
    leftCoordinateOperatorUPlusMatrix + leftCoordinateOperatorUMinusMatrix =
      (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [leftCoordinateOperatorUPlusMatrix_eq_diagonal,
    leftCoordinateOperatorUMinusMatrix_eq_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i.val < 4
    · have hge : ¬ 4 ≤ i.val := by omega
      simp [Matrix.diagonal, Matrix.one_apply, hi, hge]
    · have hge : 4 ≤ i.val := by omega
      simp [Matrix.diagonal, Matrix.one_apply, hi, hge]
  · simp [Matrix.diagonal, Matrix.one_apply, h]

theorem axialFlow_mem_axialEigenspace (t w : ℝ) (X : CanonicalZorn)
    (hX : X ∈ axialEigenspace w) :
    axialFlow t X ∈ axialEigenspace w := by
  rw [mem_axialEigenspace_iff] at hX ⊢
  have hcomm := congrArg (fun T : Module.End ℝ CanonicalZorn => T X)
    (axialGrading_mul_axialFlow t)
  have hcomm' : axialGrading (axialFlow t X) =
      axialFlow t (axialGrading X) := by
    simpa only [Module.End.mul_apply] using hcomm
  change axialGrading (axialFlow t X) = w • axialFlow t X
  rw [hcomm']
  rw [hX, map_smul]

end InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
