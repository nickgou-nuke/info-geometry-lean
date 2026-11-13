/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FreedKleinRepresentation
import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.Geometry.KleinPinGradedDirac
import InfoGeometry.OperatorAlgebra.GradedMatrixMorita
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Concrete smooth Klein sectors in graded matrix Morita coordinates

The volume of the actual Klein Clifford representation exchanges the two
smooth equivariance sectors and squares to minus one. It therefore identifies
`S₊ × S₋` with `Fin 2 → S₊` by `(ψ₊,ψ₋) ↦ (ψ₊,-K ψ₋)`.

Native endomorphism-matrix equivalence retains the full generally
noncommutative coefficient algebra `End ℝ S₊`. In these coordinates the actual
odd geometric Dirac operator is `[[0,-A],[-A,0]]`, with `A = K D` the already
constructed same-sector suspended Dirac operator. Multiplication by the
negative swap head gives `diag(A,A)`, so its actual corner is `A`.

The smooth carrier is an actual object of the existing graded matrix Morita
category. Its corner, unit, and counit are the native constructions. The odd
Dirac operator is represented as an element of the full matrix algebra; it is
not asserted to be linear or superlinear for every coefficient operator.
No Hilbert completion, Sobolev domain, analytic Morita equivalence, or Fredholm
assertion is inferred from this smooth algebraic construction.
-/

noncomputable section

open CategoryTheory
open scoped Matrix Matrix.Module ContDiff

namespace InfoGeometry.Geometry.KleinPinSmoothMorita

open InfoGeometry.Geometry.KleinPinDirac
open InfoGeometry.Clifford.FreedKleinRepresentation
open InfoGeometry.Topology.KleinAssociatedSpinors
open InfoGeometry.Topology.KleinCliffordPinLift
open InfoGeometry.Topology.KleinDeckRepresentation
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita

/-- Multiplication by the actual Clifford volume on smooth equivariant fields. -/
def volumeSmoothLinear (sector : Bool) :
    smoothSections sector →ₗ[ℝ] smoothSections (!sector) where
  toFun ψ :=
    ⟨⟨fun p => volumeAction (ψ.val.val p), by
        intro g p
        change volumeAction (ψ.val.val (deckAction g p)) =
          monodromy (!sector) g (volumeAction (ψ.val.val p))
        rw [ψ.val.property g p, volumeAction_monodromy]⟩,
      volumeAction.contDiff.comp (smoothSection_contDiff sector ψ)⟩
  map_add' ψ χ := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact volumeAction.map_add _ _
  map_smul' r ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact volumeAction.map_smul r _

@[simp] theorem volumeSmoothLinear_apply (sector : Bool)
    (ψ : smoothSections sector) (p : PlanePoint) :
    (volumeSmoothLinear sector ψ).val.val p = volumeAction (ψ.val.val p) := rfl

@[simp] theorem volumeSmoothLinear_false_true (ψ : smoothSections false) :
    volumeSmoothLinear true (volumeSmoothLinear false ψ) = -ψ := by
  apply Subtype.ext
  apply Subtype.ext
  funext p
  exact volumeAction_sq _

@[simp] theorem volumeSmoothLinear_true_false (ψ : smoothSections true) :
    volumeSmoothLinear false (volumeSmoothLinear true ψ) = -ψ := by
  apply Subtype.ext
  apply Subtype.ext
  funext p
  exact volumeAction_sq _

/-- The inverse is multiplication by the negative volume, on the other sector. -/
def volumeEquiv : smoothSections false ≃ₗ[ℝ] smoothSections true where
  toFun := volumeSmoothLinear false
  invFun ψ := -(volumeSmoothLinear true ψ)
  left_inv ψ := by simp
  right_inv ψ := by simp
  map_add' := (volumeSmoothLinear false).map_add
  map_smul' := (volumeSmoothLinear false).map_smul

@[simp] theorem volumeEquiv_apply (ψ : smoothSections false) :
    volumeEquiv ψ = volumeSmoothLinear false ψ := rfl

@[simp] theorem volumeEquiv_symm_apply (ψ : smoothSections true) :
    volumeEquiv.symm ψ = -(volumeSmoothLinear true ψ) := rfl

/-- Differentiation of a constant volume action and Clifford anticommutation
produce the sign in the concrete reduction. -/
theorem dirac_volume (ψ : PlanePoint → Spinor)
    (hψ : Differentiable ℝ ψ) (p : PlanePoint) :
    dirac (volumeAction ∘ ψ) p = -(volumeAction (dirac ψ p)) := by
  have hf : fderiv ℝ (volumeAction ∘ ψ) p =
      volumeAction.comp (fderiv ℝ ψ p) :=
    (volumeAction.hasFDerivAt.comp p (hψ p).hasFDerivAt).fderiv
  simp only [dirac, hf, ContinuousLinearMap.comp_apply]
  ext i
  fin_cases i <;> simp [gammaX_apply, gammaY_apply, volumeAction_apply]

/-- This commutation equation holds on the actual smooth sections. -/
theorem dirac_volume_smooth (ψ : smoothSections false) :
    diracSmoothLinear true (volumeSmoothLinear false ψ) =
      -(volumeSmoothLinear true (diracSmoothLinear false ψ)) := by
  apply Subtype.ext
  apply Subtype.ext
  funext p
  exact dirac_volume _ (smoothSection_differentiable false ψ) p

/-- The existing suspended operator is the actual volume-composed source
Dirac operator on the positive smooth sector. -/
theorem suspendedDirac_factor (ψ : smoothSections false) :
    suspendedDiracSmoothLinear false ψ =
      volumeSmoothLinear true (diracSmoothLinear false ψ) := by
  apply Subtype.ext
  apply Subtype.ext
  funext p
  exact suspendedDirac_eq_volume_dirac _ p

/-- Concrete Morita coordinates, retaining the two actual smooth domains. -/
def sectorCoordinates : TotalSections ≃ₗ[ℝ] (Fin 2 → smoothSections false) where
  toFun ψ := ![ψ.1, volumeEquiv.symm ψ.2]
  invFun v := (v 0, volumeEquiv (v 1))
  left_inv ψ := by simp
  right_inv v := by
    funext i
    fin_cases i
    · rfl
    · exact volumeEquiv.symm_apply_apply (v 1)
  map_add' ψ χ := by
    funext i
    fin_cases i
    · rfl
    · exact volumeEquiv.symm.map_add ψ.2 χ.2
  map_smul' r ψ := by
    funext i
    fin_cases i
    · rfl
    · exact volumeEquiv.symm.map_smul r ψ.2

@[simp] theorem sectorCoordinates_zero (ψ : TotalSections) :
    sectorCoordinates ψ 0 = ψ.1 := rfl

@[simp] theorem sectorCoordinates_one (ψ : TotalSections) :
    sectorCoordinates ψ 1 = volumeEquiv.symm ψ.2 := rfl

@[simp] theorem sectorCoordinates_symm_apply (v : Fin 2 → smoothSections false) :
    sectorCoordinates.symm v = (v 0, volumeEquiv (v 1)) := rfl

/-- The concrete domain grading agrees with the existing native Morita grading. -/
theorem sectorCoordinates_grading (ψ : TotalSections) :
    sectorCoordinates (grading ψ) =
      vectorGrade (AddMonoidHom.id (smoothSections false)) (sectorCoordinates ψ) := by
  ext i
  fin_cases i <;> simp [grading, vectorGrade]

/-- The entire concrete differential operator, before taking any corner. -/
theorem sectorCoordinates_dirac (v : Fin 2 → smoothSections false) :
    sectorCoordinates (gradedDirac (sectorCoordinates.symm v)) =
      ![-(suspendedDiracSmoothLinear false (v 1)),
        -(suspendedDiracSmoothLinear false (v 0))] := by
  funext i
  fin_cases i
  · change diracSmoothLinear true (volumeSmoothLinear false (v 1)) =
      -(suspendedDiracSmoothLinear false (v 1))
    rw [dirac_volume_smooth, ← suspendedDirac_factor]
  · change -(volumeSmoothLinear true (diracSmoothLinear false (v 0))) =
      -(suspendedDiracSmoothLinear false (v 0))
    rw [← suspendedDirac_factor]

/-- The full coefficient algebra consists of all real linear operators on
one concrete smooth sector; it is not assumed commutative. -/
abbrev Coeff := Module.End ℝ (smoothSections false)

/-- Native endomorphism-matrix equivalence after the concrete domain equivalence. -/
def operatorMatrix : Module.End ℝ TotalSections ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) Coeff :=
  (sectorCoordinates.conjAlgEquiv ℝ).trans
    (endVecAlgEquivMatrixEnd (Fin 2) ℝ ℝ (smoothSections false))

/-- Each entry is an actual operator corner, with the injection and projection
specified by the concrete coordinates. -/
theorem operatorMatrix_apply (T : Module.End ℝ TotalSections)
    (i j : Fin 2) (ψ : smoothSections false) :
    operatorMatrix T i j ψ =
      sectorCoordinates (T (sectorCoordinates.symm (Pi.single j ψ))) i := rfl

/-- The complete noncommutative operator matrix of the geometric Dirac operator. -/
theorem operatorMatrix_dirac :
    operatorMatrix gradedDirac =
      !![0, -suspendedDiracSmoothLinear false;
         -suspendedDiracSmoothLinear false, 0] := by
  ext i j ψ
  rw [operatorMatrix_apply, sectorCoordinates_dirac]
  fin_cases i <;> fin_cases j <;> simp

/-- In the same coordinates the geometric grading is the standard head parity. -/
theorem operatorMatrix_grading : operatorMatrix grading = !![1, 0; 0, -1] := by
  ext i j ψ
  rw [operatorMatrix_apply, sectorCoordinates_grading,
    sectorCoordinates.apply_symm_apply]
  fin_cases i <;> fin_cases j <;> simp [vectorGrade]

/-- Conjugation by the independently constructed geometric grading is the
existing matrix parity on every operator, retaining all coefficient entries. -/
theorem operatorMatrix_parity (T : Module.End ℝ TotalSections) :
    operatorMatrix (grading * T * grading) =
      matrixGrade (RingEquiv.refl Coeff) (operatorMatrix T) := by
  rw [map_mul, map_mul, operatorMatrix_grading, matrixGrade_eq_parity_conj]
  change !![1, 0; 0, -1] * operatorMatrix T * !![1, 0; 0, -1] =
    !![1, 0; 0, -1] * (operatorMatrix T).map id * !![1, 0; 0, -1]
  rw [Matrix.map_id]

/-- Evaluation of arbitrary operator-valued matrices on the original smooth domain. -/
def matrixAction : Matrix (Fin 2) (Fin 2) Coeff →ₐ[ℝ] Module.End ℝ TotalSections :=
  operatorMatrix.symm.toAlgHom

@[simp] theorem operatorMatrix_matrixAction (M : Matrix (Fin 2) (Fin 2) Coeff) :
    operatorMatrix (matrixAction M) = M := operatorMatrix.apply_symm_apply M

/-- Evaluation in coordinates retains the order of every coefficient operator. -/
theorem sectorCoordinates_matrixAction (M : Matrix (Fin 2) (Fin 2) Coeff)
    (ψ : TotalSections) :
    sectorCoordinates (matrixAction M ψ) =
      fun i => M i 0 (sectorCoordinates ψ 0) + M i 1 (sectorCoordinates ψ 1) := by
  change sectorCoordinates
    (sectorCoordinates.symm
      ((endVecAlgEquivMatrixEnd (Fin 2) ℝ ℝ (smoothSections false)).symm M
        (sectorCoordinates ψ))) = _
  rw [sectorCoordinates.apply_symm_apply]
  funext i
  change (∑ j : Fin 2, M i j (sectorCoordinates ψ j)) =
    M i 0 (sectorCoordinates ψ 0) + M i 1 (sectorCoordinates ψ 1)
  exact Fin.sum_univ_two (fun j : Fin 2 => M i j (sectorCoordinates ψ j))

/-- Full operator-valued matrix evaluation intertwines the actual native
matrix module action. -/
theorem sectorCoordinates_matrixAction_smul (M : Matrix (Fin 2) (Fin 2) Coeff)
    (ψ : TotalSections) :
    sectorCoordinates (matrixAction M ψ) = M • sectorCoordinates ψ := by
  rw [sectorCoordinates_matrixAction]
  funext i
  change M i 0 (sectorCoordinates ψ 0) + M i 1 (sectorCoordinates ψ 1) =
    ∑ j : Fin 2, M i j (sectorCoordinates ψ j)
  exact (Fin.sum_univ_two (fun j : Fin 2 => M i j (sectorCoordinates ψ j))).symm

/-- The first diagonal matrix unit is exactly the positive-sector projection. -/
theorem matrixAction_corner (ψ : TotalSections) :
    matrixAction (Matrix.single (0 : Fin 2) 0 (1 : Coeff)) ψ = (ψ.1, 0) := by
  apply sectorCoordinates.injective
  rw [sectorCoordinates_matrixAction]
  ext i
  fin_cases i <;> simp [Matrix.single]

/-- The negative swap is a concrete odd head operator on the two smooth sectors. -/
def negativeSwap : Module.End ℝ TotalSections := matrixAction !![0, -1; -1, 0]

@[simp] theorem operatorMatrix_negativeSwap :
    operatorMatrix negativeSwap = !![0, -1; -1, 0] := operatorMatrix_matrixAction _

/-- The compensating head is an involution on the concrete smooth domain. -/
theorem negativeSwap_sq : negativeSwap * negativeSwap = 1 := by
  apply operatorMatrix.injective
  rw [map_mul, operatorMatrix_negativeSwap, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The compensating head is odd for the geometric sector grading. -/
theorem negativeSwap_odd : grading * negativeSwap = -(negativeSwap * grading) := by
  apply operatorMatrix.injective
  rw [map_mul, map_neg, map_mul, operatorMatrix_grading, operatorMatrix_negativeSwap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The geometric operator is recovered from the diagonal lift of the
same-sector suspended operator by the explicit head factor. -/
theorem negativeSwap_dirac_matrix :
    operatorMatrix (negativeSwap * gradedDirac) =
      !![suspendedDiracSmoothLinear false, 0;
         0, suspendedDiracSmoothLinear false] := by
  rw [map_mul, operatorMatrix_dirac]
  rw [show operatorMatrix negativeSwap = !![0, -1; -1, 0] from
    operatorMatrix_matrixAction _]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact reconstruction of the original odd differential operator from
its head-compensated coefficient and the concrete split head. -/
theorem gradedDirac_reconstruction :
    gradedDirac = negativeSwap * matrixAction
      !![suspendedDiracSmoothLinear false, 0;
         0, suspendedDiracSmoothLinear false] := by
  have h : negativeSwap * gradedDirac = matrixAction
      !![suspendedDiracSmoothLinear false, 0;
         0, suspendedDiracSmoothLinear false] := by
    apply operatorMatrix.injective
    rw [negativeSwap_dirac_matrix, operatorMatrix_matrixAction]
  calc
    gradedDirac = (negativeSwap * negativeSwap) * gradedDirac := by
      rw [negativeSwap_sq, one_mul]
    _ = negativeSwap * (negativeSwap * gradedDirac) := mul_assoc _ _ _
    _ = _ := by rw [h]

/-- The uncompensated diagonal corner of an odd operator vanishes. -/
theorem dirac_diagonal_corner : operatorMatrix gradedDirac 0 0 = 0 := by
  rw [operatorMatrix_dirac]
  rfl

/-- The actual head-compensated Morita corner is the existing nonzero
same-sector suspended geometric operator. -/
theorem compensated_dirac_corner :
    operatorMatrix (negativeSwap * gradedDirac) 0 0 =
      suspendedDiracSmoothLinear false := by
  rw [negativeSwap_dirac_matrix]
  rfl

/-- The same-sector operator is a nonzero element of the full coefficient algebra. -/
theorem suspendedOperator_ne_zero : suspendedDiracSmoothLinear false ≠ 0 := by
  intro h
  have hv := congrArg
    (fun T : Coeff => (T cosineSmoothSection).val.val (1 / 4, 0)) h
  apply suspendedDirac_cosineField_nonzero
  simpa [suspendedDiracSmoothLinear, suspendedDiracSection,
    cosineSmoothSection, cosineSection] using hv

/-- The upper corner matrix over the full concrete coefficient algebra. -/
def upperCornerMatrix : Matrix (Fin 2) (Fin 2) Coeff := Matrix.single 0 1 1

/-- The lower corner matrix over the full concrete coefficient algebra. -/
def lowerCornerMatrix : Matrix (Fin 2) (Fin 2) Coeff := Matrix.single 1 0 1

/-- The actual coefficient-valued corner matrices do not commute. -/
theorem cornerMatrices_noncomm :
    upperCornerMatrix * lowerCornerMatrix ≠ lowerCornerMatrix * upperCornerMatrix := by
  let : Nontrivial Coeff :=
    ⟨⟨suspendedDiracSmoothLinear false, 0, suspendedOperator_ne_zero⟩⟩
  exact matrix_units_noncomm (A := Coeff)

/-- The concrete matrix representation has genuinely noncommuting operators. -/
theorem matrixAction_units_noncomm :
    matrixAction upperCornerMatrix * matrixAction lowerCornerMatrix ≠
      matrixAction lowerCornerMatrix * matrixAction upperCornerMatrix := by
  intro h
  apply cornerMatrices_noncomm
  have hm := congrArg operatorMatrix h
  simpa only [map_mul, operatorMatrix_matrixAction] using hm

/-- The existing faithful standard split-Clifford head now acts on the
particular doubled smooth Klein domain, with the full operator tail retained. -/
def cliffordHeadRepresentation :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 →ₐ[ℝ]
      Module.End ℝ TotalSections :=
  matrixAction.comp ((Algebra.ofId ℝ Coeff).mapMatrix.comp
    InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv.toAlgHom)

/-- The compensating odd head is minus the actual represented positive
split-Clifford generator. -/
theorem cliffordHead_positive :
    cliffordHeadRepresentation
      (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) =
      -negativeSwap := by
  apply operatorMatrix.injective
  rw [map_neg]
  change operatorMatrix (matrixAction
    ((Algebra.ofId ℝ Coeff).mapMatrix
      (InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0))))) =
    -(operatorMatrix (matrixAction !![0, -1; -1, 0]))
  rw [operatorMatrix_matrixAction, operatorMatrix_matrixAction,
    InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv_iota_pos]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Clifford.Cl11Matrix.J1, AlgHom.mapMatrix_apply]

/-- The geometric grading is the represented ordered split-Clifford volume. -/
theorem cliffordHead_volume :
    cliffordHeadRepresentation InfoGeometry.Clifford.Cl11Matrix.J1_cl = grading := by
  apply operatorMatrix.injective
  rw [operatorMatrix_grading]
  change operatorMatrix (matrixAction
    ((Algebra.ofId ℝ Coeff).mapMatrix
      (InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv
        InfoGeometry.Clifford.Cl11Matrix.J1_cl))) = _
  rw [operatorMatrix_matrixAction,
    InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv_J1_cl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Clifford.Cl11Matrix.Eplus, AlgHom.mapMatrix_apply]

/-- Canonical grading of the represented split Clifford head is implemented
by the actual geometric grading on the smooth domain. -/
theorem cliffordHead_grading (x : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) :
    cliffordHeadRepresentation (CliffordAlgebra.involute x) =
      grading * cliffordHeadRepresentation x * grading := by
  rw [InfoGeometry.Clifford.Cl11GradedMorita.involute_eq_J1_cl_conj,
    map_mul, map_mul, cliffordHead_volume]

/-- The concrete coefficient module, with its identity grading. -/
def coefficientObject : GradedModuleCat (RingEquiv.refl Coeff) where
  V := ModuleCat.of Coeff (smoothSections false)
  grade := AddMonoidHom.id _
  grade_smul _ _ := rfl
  grade_sq _ := rfl

section ConcreteModule

local instance : Module (Matrix (Fin 2) (Fin 2) Coeff) TotalSections :=
  Module.compHom TotalSections matrixAction.toRingHom

/-- The existing doubled smooth domain, with the constructed full matrix
coefficient action and its independently defined geometric grading. -/
def concreteObject : GradedModuleCat (matrixGrade (RingEquiv.refl Coeff)) where
  V := ModuleCat.of (Matrix (Fin 2) (Fin 2) Coeff) TotalSections
  grade := grading.toAddMonoidHom
  grade_smul M ψ := by
    apply sectorCoordinates.injective
    change sectorCoordinates (grading (matrixAction M ψ)) =
      sectorCoordinates (matrixAction (matrixGrade (RingEquiv.refl Coeff) M) (grading ψ))
    rw [sectorCoordinates_grading, sectorCoordinates_matrixAction_smul,
      sectorCoordinates_matrixAction_smul, sectorCoordinates_grading]
    exact (liftObj (RingEquiv.refl Coeff) coefficientObject).grade_smul M
      (sectorCoordinates ψ)
  grade_sq ψ := by
    exact LinearMap.congr_fun grading_sq ψ

/-- The concrete geometric domain is isomorphic to native graded Morita
induction on its genuine positive smooth sector. -/
def concreteCoordinatesIso :
    concreteObject ≅ liftObj (RingEquiv.refl Coeff) coefficientObject :=
  GradedModuleCat.isoOfUnderlying
    (LinearEquiv.toModuleIso
      { toFun := sectorCoordinates
        invFun := sectorCoordinates.symm
        left_inv := sectorCoordinates.symm_apply_apply
        right_inv := sectorCoordinates.apply_symm_apply
        map_add' := sectorCoordinates.map_add
        map_smul' := by
          intro M ψ
          exact sectorCoordinates_matrixAction_smul M ψ })
    sectorCoordinates_grading

/-- The actual corner of the concrete smooth module is the original smooth
sector, through the established native Morita reduction and unit. -/
def concreteCornerIso :
    reduceObj (RingEquiv.refl Coeff) concreteObject ≅ coefficientObject :=
  (reduce (RingEquiv.refl Coeff)).mapIso concreteCoordinatesIso ≪≫
    ((matrixEquivalence (RingEquiv.refl Coeff)).unitIso.app coefficientObject).symm

/-- Native induction of the concrete corner reconstructs the full smooth
module, with an even counit. -/
def concreteReconstructionIso :
    liftObj (RingEquiv.refl Coeff) (reduceObj (RingEquiv.refl Coeff) concreteObject) ≅
      concreteObject :=
  (matrixEquivalence (RingEquiv.refl Coeff)).counitIso.app concreteObject

end ConcreteModule

end InfoGeometry.Geometry.KleinPinSmoothMorita

end
