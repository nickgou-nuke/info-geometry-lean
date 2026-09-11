import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The global circular Peirce basis for the split-octonion carrier

This owner uses the actual complementary idempotents `uPlus` and `uMinus`.
It is distinct from `SplitOctonionCircularPeirceBasis`, whose frame uses the
diagonal `zornPlus` and `zornMinus` convention.  All statements here are
linear-basis statements in the full alternative carrier; no associativity is
assumed.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel

abbrev CanonicalZorn := InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn

/-- Left multiplication by a fixed carrier element, as a native linear
operator on the full nonassociative carrier. -/
noncomputable def leftMultiplication (A : CanonicalZorn) : Module.End ℝ CanonicalZorn where
  toFun X := A * X
  map_add' X Y := by
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul A (X + Y) =
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul A X +
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul A Y
    rw [zMul_add_right]
  map_smul' r X := by
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul A (r • X) =
      r • InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul A X
    rw [zMul_smul_right]

/-- Right multiplication by a fixed carrier element, as a native linear
operator on the full nonassociative carrier. -/
noncomputable def rightMultiplication (A : CanonicalZorn) : Module.End ℝ CanonicalZorn where
  toFun X := X * A
  map_add' X Y := by
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (X + Y) A =
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X A +
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul Y A
    rw [zMul_add_left]
  map_smul' r X := by
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (r • X) A =
      r • InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X A
    rw [zMul_smul_left]

@[simp] theorem leftMultiplication_apply (A X : CanonicalZorn) :
    leftMultiplication A X = A * X := rfl

@[simp] theorem rightMultiplication_apply (A X : CanonicalZorn) :
    rightMultiplication A X = X * A := rfl

theorem ellLeftMul_eq_leftMultiplication :
    ellLeftMul = leftMultiplication lUnit := by
  apply LinearMap.ext
  intro X
  rw [ellLeftMul_apply, leftMultiplication_apply]

theorem ellCommutator_eq_left_sub_right :
    ellCommutator = leftMultiplication lUnit - rightMultiplication lUnit := by
  apply LinearMap.ext
  intro X
  rfl

/-- The ordered circular Peirce frame with the genuine `uPlus/uMinus` projectors. -/
def frame : Fin 8 → CanonicalZorn
  | 0 => uPlus
  | 1 => rootPlus 0
  | 2 => rootPlus 1
  | 3 => rootPlus 2
  | 4 => uMinus
  | 5 => rootMinus 0
  | 6 => rootMinus 1
  | 7 => rootMinus 2
  | _ => 0

lemma frame_zero :
    frame 0 = (1 / 2 : ℝ) • (ellWeightBasisReal 3 + ellWeightBasisReal 4) := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis, uPlus]

lemma frame_four :
    frame 4 = (1 / 2 : ℝ) • (ellWeightBasisReal 3 - ellWeightBasisReal 4) := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis, uMinus]

lemma frame_one : frame 1 = ellWeightBasisReal 5 := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis]

lemma frame_two : frame 2 = ellWeightBasisReal 6 := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis]

lemma frame_three : frame 3 = ellWeightBasisReal 7 := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis]

lemma frame_five : frame 5 = ellWeightBasisReal 0 := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis]

lemma frame_six : frame 6 = ellWeightBasisReal 1 := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis]

lemma frame_seven : frame 7 = ellWeightBasisReal 2 := by
  rw [ellWeightBasisReal_apply]
  simp [frame, ellWeightBasis]

/-- Coordinates of an element in the circular Peirce frame. -/
def coord (X : CanonicalZorn) : Fin 8 → ℝ :=
  let c := ellWeightBasisReal.equivFun X
  fun i => match i with
    | 0 => c 3 + c 4
    | 1 => c 5
    | 2 => c 6
    | 3 => c 7
    | 4 => c 3 - c 4
    | 5 => c 0
    | 6 => c 1
    | 7 => c 2
    | _ => 0

theorem sum_coord_smul_frame (X : CanonicalZorn) :
    ∑ i : Fin 8, coord X i • frame i = X := by
  have h := ellWeightBasisReal.sum_equivFun X
  rw [Fin.sum_univ_eight] at h ⊢
  rw [show frame 0 = _ from frame_zero, show frame 4 = _ from frame_four]
  rw [frame_one, frame_two, frame_three, frame_five, frame_six, frame_seven]
  calc
    _ = ∑ i : Fin 8, (ellWeightBasisReal.equivFun X i) • ellWeightBasisReal i := by
      simp only [coord, Fin.sum_univ_eight]
      module
    _ = X := by simpa [Fin.sum_univ_eight] using h

theorem linearIndependent_frame : LinearIndependent ℝ frame := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let q : Fin 8 → ℝ := fun j => match j with
    | 0 => g 5
    | 1 => g 6
    | 2 => g 7
    | 3 => (g 0 + g 4) / 2
    | 4 => (g 0 - g 4) / 2
    | 5 => g 1
    | 6 => g 2
    | 7 => g 3
    | _ => 0
  have hq : ∑ j : Fin 8, q j • ellWeightBasisReal j = 0 := by
    have h := hg
    simp only [Fin.sum_univ_eight, frame_zero, frame_one, frame_two, frame_three,
      frame_four, frame_five, frame_six, frame_seven] at h
    rw [Fin.sum_univ_eight]
    simp only [q]
    convert h using 1 <;> module
  have hqall := (Fintype.linearIndependent_iff.mp
    ellWeightBasisReal.linearIndependent) q hq
  have h0 := hqall 0
  have h1 := hqall 1
  have h2 := hqall 2
  have h3 := hqall 3
  have h4 := hqall 4
  have h5 := hqall 5
  have h6 := hqall 6
  have h7 := hqall 7
  fin_cases i <;> simp [q] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢ <;> linarith

/-- The genuine circular Peirce basis of the full split-octonion carrier. -/
noncomputable def circularPeirceBasis : Module.Basis (Fin 8) ℝ CanonicalZorn :=
  Module.Basis.mk linearIndependent_frame (by
    intro X _
    rw [← sum_coord_smul_frame X]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp] theorem circularPeirceBasis_apply (i : Fin 8) :
    circularPeirceBasis i = frame i := by
  exact Module.Basis.mk_apply _ _ _

theorem circularPeirceBasis_sum_repr (X : CanonicalZorn) :
    ∑ i : Fin 8, (circularPeirceBasis.equivFun X i) • circularPeirceBasis i = X := by
  exact circularPeirceBasis.sum_equivFun X

theorem circularPeirceBasis_equivFun_symm_coord (X : CanonicalZorn) :
    circularPeirceBasis.equivFun.symm (coord X) = X := by
  rw [circularPeirceBasis.equivFun_symm_apply]
  simpa only [circularPeirceBasis_apply] using sum_coord_smul_frame X

theorem coord_eq_circularPeirceBasis_equivFun (X : CanonicalZorn) :
    coord X = circularPeirceBasis.equivFun X := by
  have h := congrArg circularPeirceBasis.equivFun
    (circularPeirceBasis_equivFun_symm_coord X)
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem circularPeirceBasis_linearIndependent :
    LinearIndependent ℝ (circularPeirceBasis : Fin 8 → CanonicalZorn) :=
  circularPeirceBasis.linearIndependent

theorem circularPeirceBasis_span_top :
    Submodule.span ℝ (Set.range (circularPeirceBasis : Fin 8 → CanonicalZorn)) = ⊤ :=
  circularPeirceBasis.span_eq

theorem circularPeirceBasis_ne_zero (i : Fin 8) :
    circularPeirceBasis i ≠ 0 :=
  circularPeirceBasis.linearIndependent.ne_zero i

theorem circularPeirceBasis_zero : circularPeirceBasis 0 = uPlus := by
  simp [circularPeirceBasis_apply, frame]

theorem circularPeirceBasis_one : circularPeirceBasis 1 = rootPlus 0 := by
  simp [circularPeirceBasis_apply, frame]

theorem circularPeirceBasis_two : circularPeirceBasis 2 = rootPlus 1 := by
  simp [circularPeirceBasis_apply, frame]

theorem circularPeirceBasis_three : circularPeirceBasis 3 = rootPlus 2 := by
  simp [circularPeirceBasis_apply, frame]

theorem circularPeirceBasis_four : circularPeirceBasis 4 = uMinus := by
  simp [circularPeirceBasis_apply, frame]

theorem circularPeirceBasis_five : circularPeirceBasis 5 = rootMinus 0 := by
  simp [circularPeirceBasis_apply, frame]

theorem circularPeirceBasis_six : circularPeirceBasis 6 = rootMinus 1 := by
  simp [circularPeirceBasis_apply, frame]

theorem circularPeirceBasis_seven : circularPeirceBasis 7 = rootMinus 2 := by
  simp [circularPeirceBasis_apply, frame]

theorem rootPlus_parenthesized_recovery (a : Fin 3) :
    (uPlus * rootPlus a) * uMinus = rootPlus a := by
  rw [uPlus_mul_rootPlus, rootPlus_mul_uMinus]

theorem rootMinus_parenthesized_recovery (a : Fin 3) :
    (uMinus * rootMinus a) * uPlus = rootMinus a := by
  rw [uMinus_mul_rootMinus, rootMinus_mul_uPlus]

theorem uPlus_mul_frame (i : Fin 8) :
    uPlus * frame i =
      match i with
      | 0 => uPlus
      | 1 => rootPlus 0
      | 2 => rootPlus 1
      | 3 => rootPlus 2
      | 4 => 0
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | _ => 0 := by
  fin_cases i
  · simpa [frame] using uPlus_sq
  · simpa [frame] using uPlus_mul_rootPlus 0
  · simpa [frame] using uPlus_mul_rootPlus 1
  · simpa [frame] using uPlus_mul_rootPlus 2
  · simpa [frame] using uPlus_mul_uMinus
  · simpa [frame] using uPlus_mul_rootMinus 0
  · simpa [frame] using uPlus_mul_rootMinus 1
  · simpa [frame] using uPlus_mul_rootMinus 2

theorem uMinus_mul_frame (i : Fin 8) :
    uMinus * frame i =
      match i with
      | 0 => 0
      | 1 => 0
      | 2 => 0
      | 3 => 0
      | 4 => uMinus
      | 5 => rootMinus 0
      | 6 => rootMinus 1
      | 7 => rootMinus 2
      | _ => 0 := by
  fin_cases i
  · simpa [frame] using uMinus_mul_uPlus
  · simpa [frame] using uMinus_mul_rootPlus 0
  · simpa [frame] using uMinus_mul_rootPlus 1
  · simpa [frame] using uMinus_mul_rootPlus 2
  · simpa [frame] using uMinus_sq
  · simpa [frame] using uMinus_mul_rootMinus 0
  · simpa [frame] using uMinus_mul_rootMinus 1
  · simpa [frame] using uMinus_mul_rootMinus 2

theorem frame_mul_uPlus (i : Fin 8) :
    frame i * uPlus =
      match i with
      | 0 => uPlus
      | 1 => 0
      | 2 => 0
      | 3 => 0
      | 4 => 0
      | 5 => rootMinus 0
      | 6 => rootMinus 1
      | 7 => rootMinus 2
      | _ => 0 := by
  fin_cases i
  · simpa [frame] using uPlus_sq
  · simpa [frame] using rootPlus_mul_uPlus 0
  · simpa [frame] using rootPlus_mul_uPlus 1
  · simpa [frame] using rootPlus_mul_uPlus 2
  · simpa [frame] using uMinus_mul_uPlus
  · simpa [frame] using rootMinus_mul_uPlus 0
  · simpa [frame] using rootMinus_mul_uPlus 1
  · simpa [frame] using rootMinus_mul_uPlus 2

theorem frame_mul_uMinus (i : Fin 8) :
    frame i * uMinus =
      match i with
      | 0 => 0
      | 1 => rootPlus 0
      | 2 => rootPlus 1
      | 3 => rootPlus 2
      | 4 => uMinus
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | _ => 0 := by
  fin_cases i
  · simpa [frame] using uPlus_mul_uMinus
  · simpa [frame] using rootPlus_mul_uMinus 0
  · simpa [frame] using rootPlus_mul_uMinus 1
  · simpa [frame] using rootPlus_mul_uMinus 2
  · simpa [frame] using uMinus_sq
  · simpa [frame] using rootMinus_mul_uMinus 0
  · simpa [frame] using rootMinus_mul_uMinus 1
  · simpa [frame] using rootMinus_mul_uMinus 2

theorem leftMultiplication_uPlus_frame (i : Fin 8) :
    leftMultiplication uPlus (frame i) =
      match i with
      | 0 => uPlus
      | 1 => rootPlus 0
      | 2 => rootPlus 1
      | 3 => rootPlus 2
      | 4 => 0
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | _ => 0 := by
  simpa only [leftMultiplication_apply] using uPlus_mul_frame i

theorem leftMultiplication_uMinus_frame (i : Fin 8) :
    leftMultiplication uMinus (frame i) =
      match i with
      | 0 => 0
      | 1 => 0
      | 2 => 0
      | 3 => 0
      | 4 => uMinus
      | 5 => rootMinus 0
      | 6 => rootMinus 1
      | 7 => rootMinus 2
      | _ => 0 := by
  simpa only [leftMultiplication_apply] using uMinus_mul_frame i

theorem rightMultiplication_uPlus_frame (i : Fin 8) :
    rightMultiplication uPlus (frame i) =
      match i with
      | 0 => uPlus
      | 1 => 0
      | 2 => 0
      | 3 => 0
      | 4 => 0
      | 5 => rootMinus 0
      | 6 => rootMinus 1
      | 7 => rootMinus 2
      | _ => 0 := by
  simpa only [rightMultiplication_apply] using frame_mul_uPlus i

theorem rightMultiplication_uMinus_frame (i : Fin 8) :
    rightMultiplication uMinus (frame i) =
      match i with
      | 0 => 0
      | 1 => rootPlus 0
      | 2 => rootPlus 1
      | 3 => rootPlus 2
      | 4 => uMinus
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | _ => 0 := by
  simpa only [rightMultiplication_apply] using frame_mul_uMinus i

theorem ellCommutator_uPlus :
    ellCommutator uPlus = 0 := by
  unfold ellCommutator uPlus
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit
      ((1 / 2 : ℝ) • (1 + lUnit)) -
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
      ((1 / 2 : ℝ) • (1 + lUnit)) lUnit = 0
  rw [zMul_smul_right, zMul_smul_left, zMul_add_right, zMul_add_left,
    one_zMul, zMul_one, l_sq]
  module

theorem ellCommutator_uMinus :
    ellCommutator uMinus = 0 := by
  unfold ellCommutator uMinus
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit
      ((1 / 2 : ℝ) • (1 - lUnit)) -
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
      ((1 / 2 : ℝ) • (1 - lUnit)) lUnit = 0
  rw [zMul_smul_right, zMul_smul_left, zMul_sub_right, zMul_sub_left,
    one_zMul, zMul_one, l_sq]
  module

theorem ellCommutator_frame_one :
    ellCommutator (frame 1) = (2 : ℝ) • frame 1 := by
  change ellCommutator (rootPlus 0) = (2 : ℝ) • rootPlus 0
  exact ellCommutator_rootPlus 0

theorem ellCommutator_frame_two :
    ellCommutator (frame 2) = (2 : ℝ) • frame 2 := by
  change ellCommutator (rootPlus 1) = (2 : ℝ) • rootPlus 1
  exact ellCommutator_rootPlus 1

theorem ellCommutator_frame_three :
    ellCommutator (frame 3) = (2 : ℝ) • frame 3 := by
  change ellCommutator (rootPlus 2) = (2 : ℝ) • rootPlus 2
  exact ellCommutator_rootPlus 2

theorem ellCommutator_frame_five :
    ellCommutator (frame 5) = (-2 : ℝ) • frame 5 := by
  change ellCommutator (rootMinus 0) = (-2 : ℝ) • rootMinus 0
  exact ellCommutator_rootMinus 0

theorem ellCommutator_frame_six :
    ellCommutator (frame 6) = (-2 : ℝ) • frame 6 := by
  change ellCommutator (rootMinus 1) = (-2 : ℝ) • rootMinus 1
  exact ellCommutator_rootMinus 1

theorem ellCommutator_frame_seven :
    ellCommutator (frame 7) = (-2 : ℝ) • frame 7 := by
  change ellCommutator (rootMinus 2) = (-2 : ℝ) • rootMinus 2
  exact ellCommutator_rootMinus 2

abbrev Coordinate : Type := InfoGeometry.Algebra.FiniteSpin.Vec8R

noncomputable def coordinateEquiv : CanonicalZorn ≃ₗ[ℝ] Coordinate :=
  circularPeirceBasis.equivFun

@[simp] theorem coordinateEquiv_apply_frame (i : Fin 8) :
    coordinateEquiv (frame i) = Pi.single i 1 := by
  ext j
  change (circularPeirceBasis.repr (frame i)) j = _
  have h := Module.Basis.equivFun_self circularPeirceBasis i j
  rw [circularPeirceBasis_apply] at h
  by_cases hij : i = j
  · subst j
    simpa using h
  · have hji : j ≠ i := Ne.symm hij
    simpa [hij, hji, Pi.single_apply] using h

@[simp] theorem coordinateEquiv_symm_single (i : Fin 8) :
    coordinateEquiv.symm (Pi.single i 1) = frame i := by
  apply coordinateEquiv.injective
  rw [coordinateEquiv_apply_frame, coordinateEquiv.apply_symm_apply]

noncomputable def leftCoordinateOperator (A : CanonicalZorn) :
    Module.End ℝ Coordinate where
  toFun x := coordinateEquiv (leftMultiplication A (coordinateEquiv.symm x))
  map_add' x y := by
    simp only [coordinateEquiv.symm.map_add, (leftMultiplication A).map_add,
      coordinateEquiv.map_add]
  map_smul' r x := by
    simp only [coordinateEquiv.symm.map_smul, (leftMultiplication A).map_smul,
      coordinateEquiv.map_smul]
    simp only [RingHom.id_apply]

noncomputable def rightCoordinateOperator (A : CanonicalZorn) :
    Module.End ℝ Coordinate where
  toFun x := coordinateEquiv (rightMultiplication A (coordinateEquiv.symm x))
  map_add' x y := by
    simp only [coordinateEquiv.symm.map_add, (rightMultiplication A).map_add,
      coordinateEquiv.map_add]
  map_smul' r x := by
    simp only [coordinateEquiv.symm.map_smul, (rightMultiplication A).map_smul,
      coordinateEquiv.map_smul]
    simp only [RingHom.id_apply]

@[simp] theorem leftCoordinateOperator_apply (A : CanonicalZorn) (x : Coordinate) :
    leftCoordinateOperator A x =
      coordinateEquiv (A * coordinateEquiv.symm x) := by
  rfl

@[simp] theorem rightCoordinateOperator_apply (A : CanonicalZorn) (x : Coordinate) :
    rightCoordinateOperator A x =
      coordinateEquiv (coordinateEquiv.symm x * A) := by
  rfl

theorem leftCoordinateOperator_on_frame (A : CanonicalZorn) (i : Fin 8) :
    leftCoordinateOperator A (Pi.single i 1) =
      coordinateEquiv (A * frame i) := by
  rw [leftCoordinateOperator_apply, coordinateEquiv_symm_single]

theorem rightCoordinateOperator_on_frame (A : CanonicalZorn) (i : Fin 8) :
    rightCoordinateOperator A (Pi.single i 1) =
      coordinateEquiv (frame i * A) := by
  rw [rightCoordinateOperator_apply, coordinateEquiv_symm_single]

theorem leftCoordinateOperator_uPlus_on_frame (i : Fin 8) :
    leftCoordinateOperator uPlus (Pi.single i 1) =
      coordinateEquiv (match i with
        | 0 => uPlus
        | 1 => rootPlus 0
        | 2 => rootPlus 1
        | 3 => rootPlus 2
        | 4 => 0
        | 5 => 0
        | 6 => 0
        | 7 => 0
        | _ => 0) := by
  rw [leftCoordinateOperator_on_frame]
  exact congrArg coordinateEquiv (uPlus_mul_frame i)

theorem rightCoordinateOperator_uMinus_on_frame (i : Fin 8) :
    rightCoordinateOperator uMinus (Pi.single i 1) =
      coordinateEquiv (match i with
        | 0 => 0
        | 1 => rootPlus 0
        | 2 => rootPlus 1
        | 3 => rootPlus 2
        | 4 => uMinus
        | 5 => 0
        | 6 => 0
        | 7 => 0
        | _ => 0) := by
  rw [rightCoordinateOperator_on_frame]
  exact congrArg coordinateEquiv (frame_mul_uMinus i)

theorem leftCoordinateOperator_uMinus_on_frame (i : Fin 8) :
    leftCoordinateOperator uMinus (Pi.single i 1) =
      coordinateEquiv (match i with
        | 0 => 0
        | 1 => 0
        | 2 => 0
        | 3 => 0
        | 4 => uMinus
        | 5 => rootMinus 0
        | 6 => rootMinus 1
        | 7 => rootMinus 2
        | _ => 0) := by
  rw [leftCoordinateOperator_on_frame]
  exact congrArg coordinateEquiv (uMinus_mul_frame i)

theorem rightCoordinateOperator_uPlus_on_frame (i : Fin 8) :
    rightCoordinateOperator uPlus (Pi.single i 1) =
      coordinateEquiv (match i with
        | 0 => uPlus
        | 1 => 0
        | 2 => 0
        | 3 => 0
        | 4 => 0
        | 5 => rootMinus 0
        | 6 => rootMinus 1
        | 7 => rootMinus 2
        | _ => 0) := by
  rw [rightCoordinateOperator_on_frame]
  exact congrArg coordinateEquiv (frame_mul_uPlus i)

noncomputable def ellCommutatorCoordinate : Module.End ℝ Coordinate where
  toFun x := coordinateEquiv (ellCommutator (coordinateEquiv.symm x))
  map_add' x y := by
    rw [coordinateEquiv.symm.map_add, map_add ellCommutator,
      coordinateEquiv.map_add]
  map_smul' r x := by
    rw [coordinateEquiv.symm.map_smul, map_smul ellCommutator,
      coordinateEquiv.map_smul]
    simp only [RingHom.id_apply]

@[simp] theorem ellCommutatorCoordinate_apply (x : Coordinate) :
    ellCommutatorCoordinate x =
      coordinateEquiv (ellCommutator (coordinateEquiv.symm x)) := by
  rfl

theorem ellCommutatorCoordinate_eq_left_sub_right :
    ellCommutatorCoordinate =
      leftCoordinateOperator lUnit - rightCoordinateOperator lUnit := by
  apply LinearMap.ext
  intro x
  change coordinateEquiv (ellCommutator (coordinateEquiv.symm x)) =
    coordinateEquiv (leftMultiplication lUnit (coordinateEquiv.symm x)) -
      coordinateEquiv (rightMultiplication lUnit (coordinateEquiv.symm x))
  calc
    coordinateEquiv (ellCommutator (coordinateEquiv.symm x)) =
        coordinateEquiv ((leftMultiplication lUnit - rightMultiplication lUnit)
          (coordinateEquiv.symm x)) := by
      rw [ellCommutator_eq_left_sub_right]
    _ = coordinateEquiv (leftMultiplication lUnit (coordinateEquiv.symm x)) -
        coordinateEquiv (rightMultiplication lUnit (coordinateEquiv.symm x)) := by
      exact coordinateEquiv.map_sub _ _

theorem ellCommutatorCoordinate_on_frame (i : Fin 8) :
    ellCommutatorCoordinate (Pi.single i 1) =
      coordinateEquiv (ellCommutator (frame i)) := by
  rw [ellCommutatorCoordinate_apply, coordinateEquiv_symm_single]

theorem ellCommutatorCoordinate_frame_action (i : Fin 8) :
    ellCommutatorCoordinate (Pi.single i 1) =
      coordinateEquiv (match i with
        | 0 => 0
        | 1 => (2 : ℝ) • rootPlus 0
        | 2 => (2 : ℝ) • rootPlus 1
        | 3 => (2 : ℝ) • rootPlus 2
        | 4 => 0
        | 5 => (-2 : ℝ) • rootMinus 0
        | 6 => (-2 : ℝ) • rootMinus 1
        | 7 => (-2 : ℝ) • rootMinus 2
        | _ => 0) := by
  rw [ellCommutatorCoordinate_on_frame]
  fin_cases i
  · change coordinateEquiv (ellCommutator uPlus) = coordinateEquiv 0
    rw [ellCommutator_uPlus]
  · change coordinateEquiv (ellCommutator (rootPlus 0)) =
      coordinateEquiv ((2 : ℝ) • rootPlus 0)
    rw [ellCommutator_rootPlus]
  · change coordinateEquiv (ellCommutator (rootPlus 1)) =
      coordinateEquiv ((2 : ℝ) • rootPlus 1)
    rw [ellCommutator_rootPlus]
  · change coordinateEquiv (ellCommutator (rootPlus 2)) =
      coordinateEquiv ((2 : ℝ) • rootPlus 2)
    rw [ellCommutator_rootPlus]
  · change coordinateEquiv (ellCommutator uMinus) = coordinateEquiv 0
    rw [ellCommutator_uMinus]
  · change coordinateEquiv (ellCommutator (rootMinus 0)) =
      coordinateEquiv ((-2 : ℝ) • rootMinus 0)
    rw [ellCommutator_rootMinus]
  · change coordinateEquiv (ellCommutator (rootMinus 1)) =
      coordinateEquiv ((-2 : ℝ) • rootMinus 1)
    rw [ellCommutator_rootMinus]
  · change coordinateEquiv (ellCommutator (rootMinus 2)) =
      coordinateEquiv ((-2 : ℝ) • rootMinus 2)
    rw [ellCommutator_rootMinus]

end InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
