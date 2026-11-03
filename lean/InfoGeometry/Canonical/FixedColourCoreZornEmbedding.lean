/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ThreeColorFixedCoreSuperLie
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorZornGaugeCovariance
import InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading

/-!
# Fixed-colour matrix core inside the native operator-valued Zorn carrier

The fixed-colour associative core is represented by `BdGBlock A`.  This file
embeds it into the native operator-valued Zorn coordinates and proves the
actual multiplication compatibility.  No associative or Lie structure is
installed on the full native carrier.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics
open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A] [Algebra ℝ A]

def fixedColourEmbedding (k : Fin 3) (X : FixedColourCore A) :
    OperatorZornMatrix A :=
  ⟨X 0 0, X 1 1,
    operatorColourUnit k (X 0 1),
    operatorColourUnit k (X 1 0)⟩

@[simp] theorem operatorColourUnit_cross_same (k : Fin 3) (a b : A) :
    operatorCross (operatorColourUnit k a)
        (operatorColourUnit k b) = 0 := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      NCZornElement.zornCross]

@[simp] theorem fixedColourEmbedding_zero (k : Fin 3) :
    fixedColourEmbedding k (0 : FixedColourCore A) = 0 := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext i
    change (if i = k then (0 : A) else 0) = 0
    simp
  · funext i
    change (if i = k then (0 : A) else 0) = 0
    simp

/-- The fixed-colour carrier map preserves addition in the native Zorn
coordinates. -/
theorem fixedColourEmbedding_add (k : Fin 3) (X Y : FixedColourCore A) :
    fixedColourEmbedding k (X + Y) =
      fixedColourEmbedding k X + fixedColourEmbedding k Y := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorColourUnit, hk]
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorColourUnit, hk]

/-- The fixed-colour map is injective: all four BdG matrix entries are
recoverable from the two diagonal Zorn coordinates and the selected colour
coordinates. -/
theorem fixedColourEmbedding_injective (k : Fin 3) :
    Function.Injective (fixedColourEmbedding (A := A) k) := by
  intro X Y h
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrArg NCZornElement.n_plus h
  · have hs := congrArg (fun Z : OperatorZornMatrix A => Z.sigma_plus k) h
    simpa [fixedColourEmbedding, operatorColourUnit] using hs
  · have hs := congrArg (fun Z : OperatorZornMatrix A => Z.sigma_minus k) h
    simpa [fixedColourEmbedding, operatorColourUnit] using hs
  · exact congrArg NCZornElement.n_minus h

private theorem if_mul_add_mul_same (p : Prop) [Decidable p]
    (a b c d : A) :
    (if p then a * b + c * d else 0) =
      (if p then a * b else 0) + (if p then c * d else 0) := by
  by_cases hp : p <;> simp [hp]

private theorem if_mul_add_mul_swapped (p : Prop) [Decidable p]
    (a b c d : A) :
    (if p then a * b + c * d else 0) =
      (if p then c * d else 0) + (if p then a * b else 0) := by
  by_cases hp : p <;> simp [hp, add_comm]

theorem fixedColourEmbedding_mul (k : Fin 3) (X Y : FixedColourCore A) :
    fixedColourEmbedding k (X * Y) =
      operatorZornMul (fixedColourEmbedding k X)
        (fixedColourEmbedding k Y) := by
  apply operatorZornMatrix_ext
  · simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
      Matrix.mul_apply, Fin.sum_univ_two,
      operatorDot_colourUnit_same]
  · simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
      Matrix.mul_apply, Fin.sum_univ_two,
      operatorDot_colourUnit_same]
    <;> abel
  · funext i
    fin_cases i
    all_goals
      simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
        operatorCross, operatorColourUnit, Matrix.mul_apply,
        Fin.sum_univ_two]
      <;> apply if_mul_add_mul_same
  · funext i
    fin_cases i
    all_goals
      simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
        operatorCross, operatorColourUnit, Matrix.mul_apply,
        Fin.sum_univ_two]
      <;> apply if_mul_add_mul_swapped

/-- The fixed-colour embedding commutes with coefficient transport.  In
particular, coefficientwise transport along a finite-stage bonding map gives
the same Zorn element as first transporting the BdG matrix and then embedding
it. -/
theorem mapCoefficients_fixedColourEmbedding
    {C : Type*} [Ring C] [Algebra ℝ C]
    (f : A →+* C) (k : Fin 3) (X : FixedColourCore A) :
    InfoGeometry.Canonical.OperatorZornGaugeCovariance.mapCoefficients f
        (fixedColourEmbedding k X) =
      fixedColourEmbedding (A := C) k (f.mapMatrix X) := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext i
    by_cases hk : i = k <;>
      simp [InfoGeometry.Canonical.OperatorZornGaugeCovariance.mapCoefficients,
        InfoGeometry.Canonical.OperatorZornRepresentationCurvatureBridge.mapOperatorVector,
        fixedColourEmbedding, operatorColourUnit, Matrix.map_apply, hk]
  · funext i
    by_cases hk : i = k <;>
      simp [InfoGeometry.Canonical.OperatorZornGaugeCovariance.mapCoefficients,
        InfoGeometry.Canonical.OperatorZornRepresentationCurvatureBridge.mapOperatorVector,
        fixedColourEmbedding, operatorColourUnit, Matrix.map_apply, hk]

/-- The ordered kinetic--mass commutator defect is natural under coefficient
maps after passage through the fixed-colour Zorn embedding.  This applies in
particular to each finite-stage bonding homomorphism. -/
theorem mapCoefficients_fixedColour_mass_anomaly
    {C : Type*} [Ring C] [Algebra ℝ C]
    (f : A →+* C) (k : Fin 3) (D M : A) :
    InfoGeometry.Canonical.OperatorZornGaugeCovariance.mapCoefficients f
        (fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)) =
      fixedColourEmbedding (A := C) k
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly (f D) (f M)) := by
  rw [mapCoefficients_fixedColourEmbedding]
  apply operatorZornMatrix_ext
  · simp [fixedColourEmbedding,
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly, RingHom.mapMatrix_apply]
  · simp [fixedColourEmbedding,
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly, RingHom.mapMatrix_apply]
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorColourUnit,
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly, RingHom.mapMatrix_apply, hk]
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorColourUnit,
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly, RingHom.mapMatrix_apply, hk]

/-- The actual massive BdG operator is natural under coefficient transport
through the fixed-colour Zorn realization. Thus a stage bonding homomorphism
may be applied either before or after constructing and embedding the mass
operator. -/
theorem mapCoefficients_fixedColour_massiveBdG
    {C : Type*} [Ring C] [Algebra ℝ C]
    [StarRing A] [StarRing C]
    (f : A →+* C) (k : Fin 3) (D M : A) :
    InfoGeometry.Canonical.OperatorZornGaugeCovariance.mapCoefficients f
        (fixedColourEmbedding k (InfoGeometry.Physics.massiveBdGHamiltonian D M)) =
      fixedColourEmbedding (A := C) k
        (InfoGeometry.Physics.massiveBdGHamiltonian (f D) (f M)) := by
  rw [mapCoefficients_fixedColourEmbedding]
  apply operatorZornMatrix_ext
  · simp [fixedColourEmbedding, InfoGeometry.Physics.massiveBdGHamiltonian,
      RingHom.mapMatrix_apply]
  · simp [fixedColourEmbedding, InfoGeometry.Physics.massiveBdGHamiltonian,
      RingHom.mapMatrix_apply]
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorColourUnit,
        InfoGeometry.Physics.massiveBdGHamiltonian, RingHom.mapMatrix_apply, hk]
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorColourUnit,
        InfoGeometry.Physics.massiveBdGHamiltonian, RingHom.mapMatrix_apply, hk]

/-- The matrix chiral commutator is supported exactly on the two off-diagonal
channels, with opposite orientations. -/
theorem chiralGrading_commutator_entries (X : FixedColourCore A) :
    InfoGeometry.Physics.chiralGrading * X - X * InfoGeometry.Physics.chiralGrading =
      !![0, X 0 1 + X 0 1; -(X 1 0 + X 1 0), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.chiralGrading, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, sub_eq_add_neg, add_assoc]

/-- The native Zorn tripotent action on the fixed-colour matrix core is the
integral form of the BdG chiral commutator.  The factor `2` is retained on the
matrix side, so this identity is valid without inverting `2` in the coefficient
ring.  It gives an operation-preserving map from the BdG carrier into the
actual operator-valued Zorn carrier. -/
theorem ncZornTripotent_fixedColourEmbedding_intertwines_chiral_commutator
    (k : Fin 3) (X : FixedColourCore A) :
    InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornTripotent
          (fixedColourEmbedding k X) +
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornTripotent
          (fixedColourEmbedding k X) =
      fixedColourEmbedding k
        (InfoGeometry.Physics.chiralGrading * X -
          X * InfoGeometry.Physics.chiralGrading) := by
  rw [chiralGrading_commutator_entries]
  rw [InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornTripotent_apply]
  apply operatorZornMatrix_ext
  · simp [InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornTripotent_apply,
      fixedColourEmbedding, operatorZornCoordinates]
  · simp [InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornTripotent_apply,
      fixedColourEmbedding, operatorZornCoordinates]
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorZornCoordinates, operatorColourUnit, hk]
  · funext i
    by_cases hk : i = k <;>
      simp [fixedColourEmbedding, operatorZornCoordinates, operatorColourUnit, hk]

/-- The massive BdG square defect induces all five grade actions of left
multiplication in the native Zorn decomposition. The extreme grades are the
cross actions; the adjacent grades retain the dot and coefficient actions; the
middle grade vanishes. Both ordered coefficient commutators remain explicit. -/
theorem massiveBdG_anomaly_fixedColour_all_Zorn_grades
    (k : Fin 3) (D M : A) (Y : OperatorZornMatrix A) :
    InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
        (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M))) 0 Y =
      operatorZornCoordinates 0 0 0
        (NCZornElement.zornCross
          (operatorColourUnit k (D * M - M * D)) Y.sigma_plus) ∧
    InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
        (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M))) 1 Y =
      operatorZornCoordinates 0
        (NCZornElement.zornDot
          (operatorColourUnit k (M * D - D * M)) Y.sigma_plus) 0
        (fun i => operatorColourUnit k (M * D - D * M) i * Y.n_plus) ∧
    InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
        (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M))) 2 Y =
      operatorZornCoordinates 0 0 (fun _ => 0) (fun _ => 0) ∧
    InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
        (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M))) 3 Y =
      operatorZornCoordinates
        (NCZornElement.zornDot
          (operatorColourUnit k (D * M - M * D)) Y.sigma_minus) 0
        (fun i => operatorColourUnit k (D * M - M * D) i * Y.n_minus) 0 ∧
    InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
        (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M))) 4 Y =
      operatorZornCoordinates 0 0
        (fun i => -NCZornElement.zornCross
          (operatorColourUnit k (M * D - D * M)) Y.sigma_minus i) 0 := by
  rcases InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul_fiveComponent_explicit
      (fixedColourEmbedding k
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)) Y with
    ⟨hNegTwo, hNegOne, hZero, hPosOne, hPosTwo⟩
  exact ⟨by simpa [fixedColourEmbedding,
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using hNegTwo,
    by simpa [fixedColourEmbedding,
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using hNegOne,
    by simpa [fixedColourEmbedding,
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using hZero,
    by simpa [fixedColourEmbedding,
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using hPosOne,
    by simpa [fixedColourEmbedding,
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using hPosTwo⟩

/-- The off-diagonal entries detect the ordered kinetic--mass commutator in
the BdG square anomaly. -/
theorem massiveBdG_anomaly_ne_zero_iff_operators_do_not_commute (D M : A) :
    InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M ≠ 0 ↔ D * M ≠ M * D := by
  constructor
  · intro hAnomaly hDM
    apply hAnomaly
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Physics.massiveBdGCommutatorAnomaly, hDM]
  · intro hDM hAnomaly
    have h01 := congrArg (fun X : FixedColourCore A => X 0 1) hAnomaly
    apply hDM
    have hEntry : D * M - M * D = 0 := by
      simpa [InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using h01
    exact sub_eq_zero.mp hEntry

/-- The BdG interaction anomaly is nonzero exactly when its native Zorn left
multiplication has a nonzero component in the exhaustive five-grade
decomposition.  This detects the anomaly in the actual Zorn operator
representation, including all grades that can arise from its dot and cross
actions. -/
theorem massiveBdG_anomaly_nonzero_iff_some_Zorn_grade_nonzero
    (k : Fin 3) (D M : A) :
    D * M ≠ M * D ↔
      ∃ d : Fin 5,
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
          (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
            (fixedColourEmbedding k
              (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M))) d ≠ 0 := by
  constructor
  · intro hDM
    have hAnomaly : InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M ≠ 0 :=
      (massiveBdG_anomaly_ne_zero_iff_operators_do_not_commute D M).2 hDM
    have hLeft : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
        (fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)) ≠ 0 := by
      intro hz
      have hZero : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
          (0 : OperatorZornMatrix A) = 0 := by
        apply LinearMap.ext
        intro Y
        simp [InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul_apply]
      have hElement : fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) = 0 :=
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul_injective
          (hz.trans hZero.symm)
      have hCore : InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M = 0 :=
        fixedColourEmbedding_injective k (by
          calc
            fixedColourEmbedding k
                (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) = 0 := hElement
            _ = fixedColourEmbedding k 0 := (fixedColourEmbedding_zero k).symm)
      exact hAnomaly hCore
    by_contra hGrades
    push Not at hGrades
    have hSum :=
      InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent_sum
        (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)))
    simp [hGrades] at hSum
    exact hLeft hSum.symm
  · rintro ⟨d, hd⟩ hDM
    have hAnomaly : InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M = 0 := by
      by_contra h
      exact (massiveBdG_anomaly_ne_zero_iff_operators_do_not_commute D M).mp h hDM
    have hEmbedded : fixedColourEmbedding k
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) = 0 := by
      rw [hAnomaly]
      exact fixedColourEmbedding_zero k
    have hLeft : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul
        (fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)) = 0 := by
      rw [hEmbedded]
      apply LinearMap.ext
      intro Y
      simp [InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornLeftMul_apply]
    apply hd
    rw [hLeft]
    fin_cases d <;>
      simp [InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent,
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornBlock]

/-- The full massive BdG square, not only its commutator defect, transports
through the multiplicative fixed-colour embedding into the native Zorn
product. The two summands retain the ordered diagonal terms and the
particle--hole-odd commutator anomaly. -/
theorem massiveBdG_square_fixedColour_operator_decomposition [StarRing A]
    (k : Fin 3) (D M : A) :
    operatorZornMul
        (fixedColourEmbedding k (InfoGeometry.Physics.massiveBdGHamiltonian D M))
        (fixedColourEmbedding k (InfoGeometry.Physics.massiveBdGHamiltonian D M)) =
      fixedColourEmbedding k
        (InfoGeometry.Physics.massiveBdGSquareEven D M +
          InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) := by
  rw [← fixedColourEmbedding_mul k
    (InfoGeometry.Physics.massiveBdGHamiltonian D M)
    (InfoGeometry.Physics.massiveBdGHamiltonian D M)]
  rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_split]

/-- The hole-reflected anomaly cancels the original anomaly after transport
into the fixed-colour Zorn operator carrier. This uses the actual Zorn product
twice, so the statement records the compatibility of the embedding with
composition as well as the matrix Andreev reflection law. -/
theorem massiveBdG_andreev_anomaly_cancels_in_fixedColour_Zorn [StarRing A]
    (k : Fin 3) (D M : A) :
    fixedColourEmbedding k (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) +
      operatorZornMul
        (operatorZornMul
          (fixedColourEmbedding k InfoGeometry.Physics.andreevSwap)
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)))
        (fixedColourEmbedding k InfoGeometry.Physics.andreevSwap) = 0 := by
  have hReflected :
      operatorZornMul
          (operatorZornMul
            (fixedColourEmbedding k InfoGeometry.Physics.andreevSwap)
            (fixedColourEmbedding k
              (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)))
          (fixedColourEmbedding k InfoGeometry.Physics.andreevSwap) =
        fixedColourEmbedding k
          (InfoGeometry.Physics.andreevSwap *
            InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M *
            InfoGeometry.Physics.andreevSwap) := by
    rw [← fixedColourEmbedding_mul k InfoGeometry.Physics.andreevSwap
      (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)]
    rw [← fixedColourEmbedding_mul k
      (InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M)
      InfoGeometry.Physics.andreevSwap]
  calc
    _ = fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) +
        fixedColourEmbedding k
          (InfoGeometry.Physics.andreevSwap *
            InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M *
            InfoGeometry.Physics.andreevSwap) := by rw [hReflected]
    _ = fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M +
            InfoGeometry.Physics.andreevSwap *
              InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M *
              InfoGeometry.Physics.andreevSwap) :=
      (fixedColourEmbedding_add k _ _).symm
    _ = 0 := by
      rw [InfoGeometry.Physics.andreev_reflect_mass_commutator_anomaly]
      simp [fixedColourEmbedding_zero]

end InfoGeometry.Canonical
