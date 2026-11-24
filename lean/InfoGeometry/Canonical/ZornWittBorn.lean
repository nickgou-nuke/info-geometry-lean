/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl44VolumeElement
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Native real Zorn transport of the four-mode Witt and Born operators

The diagonal `(4,4)` quadratic form is identified with the existing Zorn norm
through the existing quaternion-coordinate equivalence. The universal
Clifford isometry then transports the existing normalized Witt generators
into the existing real doubled Zorn representation.

The Born element is the ordered product of the four negative generators.
Its square and conjugation laws are first proved in the native Clifford
algebra, then transported by the actual algebra homomorphism. No new Zorn
product, gamma family, or creation/annihilation family is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.ZornWittBorn

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.Cl44VolumeElement
open InfoGeometry.Clifford.KoszulFoundation
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

private def quaternionCoordinateEquiv :
    (Fin 4 → ℝ) ≃ₗ[ℝ] QuaternionCoordinates :=
  (LinearEquiv.funCongrLeft ℝ ℝ (finSuccEquiv 3).symm).trans
    (LinearEquiv.piOptionEquivProd ℝ)

/-- Native finite-function equivalences split eight coordinates into the two
existing scalar/vector quaternion-coordinate copies. -/
def splitCoordinateEquiv : (Fin 8 → ℝ) ≃ₗ[ℝ] CartesianCoordinates :=
  (LinearEquiv.funCongrLeft ℝ ℝ
    (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8)).trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) ℝ ℝ).trans
        (quaternionCoordinateEquiv.prodCongr quaternionCoordinateEquiv))

@[simp] theorem splitCoordinateEquiv_apply (v : Fin 8 → ℝ) :
    splitCoordinateEquiv v =
      ((v 0, ![v 1, v 2, v 3]), (v 4, ![v 5, v 6, v 7])) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl

/-- The diagonal split form is exactly the native reduced Zorn norm in the
existing Cartesian coordinates. -/
def splitZornIsometry : splitQ44.IsometryEquiv (zornNorm (R := ℝ)) where
  toLinearEquiv := splitCoordinateEquiv.trans cartesianZornLinearEquiv
  map_app' v := by
    change zornNormFun (cartesianZornLinearEquiv (splitCoordinateEquiv v)) = splitQ44 v
    change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
      (cartesianZornLinearEquiv (splitCoordinateEquiv v)) = splitQ44 v
    rw [detZ_cartesianZornLinearEquiv, splitCoordinateEquiv_apply, splitQ44_apply]
    change
      (v 0) ^ 2 + (v 1 * v 1 + v 2 * v 2 + v 3 * v 3) -
          ((v 4) ^ 2 + (v 5 * v 5 + v 6 * v 6 + v 7 * v 7)) =
        v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3 -
          (v 4 * v 4 + v 5 * v 5 + v 6 * v 6 + v 7 * v 7)
    ring

/-- Explicit oriented coordinate readout of the proved quadratic isometry. -/
@[simp] theorem splitZornIsometry_apply (v : Fin 8 → ℝ) :
    splitZornIsometry v =
      { a := v 0 + v 4
        b := v 0 - v 4
        x := ![v 1 + v 5, v 2 + v 6, v 3 + v 7]
        y := ![v 5 - v 1, v 6 - v 2, v 7 - v 3] } := by
  change cartesianZornLinearEquiv (splitCoordinateEquiv v) = _
  rw [splitCoordinateEquiv_apply, cartesianZornLinearEquiv_apply]
  apply ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

@[simp] theorem splitZornIsometry_eVec_zero :
    splitZornIsometry (eVec 0) = (1 : ZornMatrix ℝ) := by
  rw [splitZornIsometry_apply]
  apply ZornMatrix.ext
  · simp [eVec]
  · simp [eVec]
  · funext i
    fin_cases i <;> simp [eVec]
  · funext i
    fin_cases i <;> simp [eVec]

@[simp] theorem splitZornIsometry_eVec_succ (i : Fin 3) :
    splitZornIsometry (eVec i.succ) = chiralUpperBasis i - chiralLowerBasis i := by
  rw [splitZornIsometry_apply]
  fin_cases i <;> ext j <;> (try fin_cases j) <;>
    simp [eVec, chiralUpperBasis, chiralLowerBasis]

@[simp] theorem splitZornIsometry_fVec_zero :
    splitZornIsometry (fVec 0) = zornPlus - zornMinus := by
  rw [splitZornIsometry_apply]
  apply ZornMatrix.ext
  · simp [fVec, zornPlus, zornMinus]
  · simp [fVec, zornPlus, zornMinus]
  · funext i
    fin_cases i <;> simp [fVec, zornPlus, zornMinus]
  · funext i
    fin_cases i <;> simp [fVec, zornPlus, zornMinus]

@[simp] theorem splitZornIsometry_fVec_succ (i : Fin 3) :
    splitZornIsometry (fVec i.succ) = chiralUpperBasis i + chiralLowerBasis i := by
  rw [splitZornIsometry_apply]
  fin_cases i <;> ext j <;> (try fin_cases j) <;>
    simp [fVec, chiralUpperBasis, chiralLowerBasis]

/-- The proved quadratic isometry induces an actual Clifford algebra
equivalence, rather than a comparison of dimensions. -/
def cl44ToZorn : Cl44 ≃ₐ[ℝ] CliffordAlgebra (zornNorm (R := ℝ)) :=
  CliffordAlgebra.equivOfIsometry splitZornIsometry

/-- The original real doubled Zorn action, precomposed with the proved
Clifford coordinate equivalence. -/
def cl44Representation : Cl44 →ₐ[ℝ] Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  (zornCliffordRepresentation (R := ℝ)).comp cl44ToZorn.toAlgHom

@[simp] theorem cl44Representation_ι (v : Fin 8 → ℝ) :
    cl44Representation (CliffordAlgebra.ι splitQ44 v) =
      diracGammaLinear (splitZornIsometry v) := by
  change zornCliffordRepresentation
    (CliffordAlgebra.map splitZornIsometry.toIsometry
      (CliffordAlgebra.ι splitQ44 v)) = _
  rw [CliffordAlgebra.map_apply_ι, zornCliffordRepresentation_ι]
  rfl

/-- The existing annihilation generator retains its factor `1/2` under the
native Zorn representation. -/
theorem cl44Representation_a (i : Fin 4) :
    cl44Representation (a i) = (1 / 2 : ℝ) •
      (diracGammaLinear (splitZornIsometry (eVec i)) +
        diracGammaLinear (splitZornIsometry (fVec i))) := by
  simp only [InfoGeometry.Clifford.Cl44Witt.a, aVec, map_smul, map_add,
    cl44Representation_ι]

/-- The existing creation generator uses the same factor `1/2` on the
difference of the signed Clifford generators. -/
theorem cl44Representation_adag (i : Fin 4) :
    cl44Representation (adag i) = (1 / 2 : ℝ) •
      (diracGammaLinear (splitZornIsometry (eVec i)) -
        diracGammaLinear (splitZornIsometry (fVec i))) := by
  simp only [adag, adagVec, map_smul, map_sub, cl44Representation_ι]

theorem cl44Representation_a_sq_zero (i : Fin 4) :
    cl44Representation (a i) * cl44Representation (a i) = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg cl44Representation (a_sq_zero i)

theorem cl44Representation_adag_sq_zero (i : Fin 4) :
    cl44Representation (adag i) * cl44Representation (adag i) = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg cl44Representation (adag_sq_zero i)

/-- The mixed anticommutator is the identity exactly on the diagonal, on
the full existing sixteen-dimensional real module. -/
theorem cl44Representation_witt_CAR (i j : Fin 4) :
    cl44Representation (a i) * cl44Representation (adag j) +
        cl44Representation (adag j) * cl44Representation (a i) =
      if i = j then 1 else 0 := by
  simpa only [map_add, map_mul, map_one, map_zero, apply_ite] using
    congrArg cl44Representation (witt_CAR i j)

theorem cl44Representation_annihilation_anticomm (i j : Fin 4) :
    cl44Representation (a i) * cl44Representation (a j) +
        cl44Representation (a j) * cl44Representation (a i) = 0 := by
  simpa only [map_add, map_mul, map_zero] using
    congrArg cl44Representation (witt_annihilation_anticomm i j)

theorem cl44Representation_creation_anticomm (i j : Fin 4) :
    cl44Representation (adag i) * cl44Representation (adag j) +
        cl44Representation (adag j) * cl44Representation (adag i) = 0 := by
  simpa only [map_add, map_mul, map_zero] using
    congrArg cl44Representation (witt_creation_anticomm i j)

/-- The ordered product of the four existing negative Clifford generators. -/
def bornElement : Cl44 :=
  cliffordVolumeElement splitQ44 [fVec 0, fVec 1, fVec 2, fVec 3]

theorem bornElement_ordered_product : bornElement = f 0 * f 1 * f 2 * f 3 := by
  simp [bornElement, cliffordVolumeElement, f, mul_assoc]

private theorem negative_pairwise :
    [fVec 0, fVec 1, fVec 2, fVec 3].Pairwise
      (QuadraticMap.IsOrtho splitQ44) := by
  norm_num [List.pairwise_cons, QuadraticMap.IsOrtho, fVec, splitQ44_apply]

/-- Four negative squares and six pairwise interchanges give square `+1`. -/
theorem bornElement_sq : bornElement * bornElement = 1 := by
  rw [bornElement, cliffordVolumeElement_sq_of_pairwise _ negative_pairwise]
  norm_num [cliffordVolumeSquareScalar, fVec, splitQ44_apply]

private def positiveElement : Cl44 :=
  cliffordVolumeElement splitQ44 [eVec 0, eVec 1, eVec 2, eVec 3]

private theorem positive_pairwise :
    [eVec 0, eVec 1, eVec 2, eVec 3].Pairwise
      (QuadraticMap.IsOrtho splitQ44) := by
  norm_num [List.pairwise_cons, QuadraticMap.IsOrtho, eVec, splitQ44_apply]

private theorem positiveElement_sq : positiveElement * positiveElement = 1 := by
  rw [positiveElement, cliffordVolumeElement_sq_of_pairwise _ positive_pairwise]
  norm_num [cliffordVolumeSquareScalar, eVec, splitQ44_apply]

private theorem volumeElement_eq_positive_mul_born :
    volumeElement = positiveElement * bornElement := by
  simp [volumeElement, volumeVectorList, volumeVector,
    positiveElement, bornElement, cliffordVolumeElement, mul_assoc]

/-- The four-negative product commutes with every positive generator. -/
theorem bornElement_mul_e (i : Fin 4) : bornElement * e i = e i * bornElement := by
  have horth : ∀ w ∈ [fVec 0, fVec 1, fVec 2, fVec 3],
      QuadraticMap.IsOrtho splitQ44 (eVec i) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    all_goals fin_cases i <;>
      norm_num [QuadraticMap.IsOrtho, eVec, fVec, splitQ44_apply]
  have h := clifford_anticommute_listProduct (Q := splitQ44)
    (eVec i) [fVec 0, fVec 1, fVec 2, fVec 3] horth
  simpa [bornElement, cliffordVolumeElement, e, pow_succ] using h.symm

private theorem positiveElement_mul_f (i : Fin 4) :
    positiveElement * f i = f i * positiveElement := by
  have horth : ∀ w ∈ [eVec 0, eVec 1, eVec 2, eVec 3],
      QuadraticMap.IsOrtho splitQ44 (fVec i) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    all_goals fin_cases i <;>
      norm_num [QuadraticMap.IsOrtho, eVec, fVec, splitQ44_apply]
  have h := clifford_anticommute_listProduct (Q := splitQ44)
    (fVec i) [eVec 0, eVec 1, eVec 2, eVec 3] horth
  simpa [positiveElement, cliffordVolumeElement, f, pow_succ] using h.symm

/-- Anticommutation with the negative generators follows from the existing
oriented volume theorem and cancellation by its positive four-factor part. -/
theorem bornElement_mul_f (i : Fin 4) :
    bornElement * f i = -(f i * bornElement) := by
  have hunit : IsUnit positiveElement :=
    ⟨⟨positiveElement, positiveElement, positiveElement_sq, positiveElement_sq⟩, rfl⟩
  apply hunit.mul_left_cancel
  calc
    positiveElement * (bornElement * f i) = (positiveElement * bornElement) * f i :=
      (mul_assoc _ _ _).symm
    _ = -(f i * (positiveElement * bornElement)) := by
      simpa only [volumeElement_eq_positive_mul_born] using volumeElement_anticommutes_f i
    _ = positiveElement * (-(f i * bornElement)) := by
      rw [mul_neg]
      congr 1
      rw [← mul_assoc, ← positiveElement_mul_f i, mul_assoc]

theorem bornElement_e_born (i : Fin 4) : bornElement * e i * bornElement = e i := by
  rw [bornElement_mul_e, mul_assoc, bornElement_sq, mul_one]

theorem bornElement_f_born (i : Fin 4) : bornElement * f i * bornElement = -f i := by
  rw [bornElement_mul_f, neg_mul, mul_assoc, bornElement_sq, mul_one]

/-- Ordinary conjugation by the actual four-negative product exchanges the
existing normalized Witt families, without an additional sign. -/
theorem bornElement_a_born (i : Fin 4) : bornElement * a i * bornElement = adag i := by
  have ha : a i = (1 / 2 : ℝ) • (e i + f i) := by
    simp only [InfoGeometry.Clifford.Cl44Witt.a, aVec, e, f, map_smul, map_add]
  have hadag : adag i = (1 / 2 : ℝ) • (e i - f i) := by
    simp only [adag, adagVec, e, f, map_smul, map_sub]
  rw [ha, hadag, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    bornElement_e_born, bornElement_f_born, ← sub_eq_add_neg]

theorem bornElement_adag_born (i : Fin 4) : bornElement * adag i * bornElement = a i := by
  calc
    bornElement * adag i * bornElement =
        bornElement * (bornElement * a i * bornElement) * bornElement := by
      rw [bornElement_a_born]
    _ = (bornElement * bornElement) * a i * (bornElement * bornElement) := by
      simp only [mul_assoc]
    _ = a i := by simp only [bornElement_sq, one_mul, mul_one]

/-- The represented Born operator is an involution on the original real
doubled Zorn module. -/
theorem cl44Representation_born_sq :
    cl44Representation bornElement * cl44Representation bornElement = 1 := by
  simpa only [map_mul, map_one] using congrArg cl44Representation bornElement_sq

theorem cl44Representation_born_a_born (i : Fin 4) :
    cl44Representation bornElement * cl44Representation (a i) *
        cl44Representation bornElement = cl44Representation (adag i) := by
  simpa only [map_mul] using congrArg cl44Representation (bornElement_a_born i)

theorem cl44Representation_born_adag_born (i : Fin 4) :
    cl44Representation bornElement * cl44Representation (adag i) *
        cl44Representation bornElement = cl44Representation (a i) := by
  simpa only [map_mul] using congrArg cl44Representation (bornElement_adag_born i)

end InfoGeometry.Canonical.ZornWittBorn
