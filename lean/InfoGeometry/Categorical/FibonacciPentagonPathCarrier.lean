import InfoGeometry.Categorical.FibonacciFourAnyonCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciBraidedCategory
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The five-edge path carrier for the Fibonacci pentagon

The low-anyon owner already provides five matrices on the common `Basis6`
carrier.  This file gives those five positions an explicit finite index.  It
is path data only: no pentagon equality is asserted here.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonPathCarrier

open InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
open InfoGeometry.Categorical.FibonacciFourAnyonCarrier
open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData

inductive PentagonEdge : Type
  | edge₁ | edge₂ | edge₃ | edge₄ | edge₅
  deriving DecidableEq, Repr

inductive PentagonVertex : Type
  | vertex₁ | vertex₂ | vertex₃ | vertex₄ | vertex₅
  deriving DecidableEq, Repr

noncomputable def fourTau :
    InfoGeometry.Categorical.FibonacciHomSpace.FibCat :=
  Finsupp.single FibSimple.tau 1

noncomputable def parenthesizedObject : PentagonVertex →
    InfoGeometry.Categorical.FibonacciHomSpace.FibCat
  | .vertex₁ => fibTensorObj (fibTensorObj (fibTensorObj fourTau fourTau) fourTau) fourTau
  | .vertex₂ => fibTensorObj (fibTensorObj fourTau fourTau) (fibTensorObj fourTau fourTau)
  | .vertex₃ => fibTensorObj (fibTensorObj fourTau (fibTensorObj fourTau fourTau)) fourTau
  | .vertex₄ => fibTensorObj fourTau (fibTensorObj (fibTensorObj fourTau fourTau) fourTau)
  | .vertex₅ => fibTensorObj fourTau (fibTensorObj fourTau (fibTensorObj fourTau fourTau))

theorem parenthesizedObject_eq_vertex₁ (v : PentagonVertex) :
    parenthesizedObject v = parenthesizedObject .vertex₁ := by
  cases v <;> simp [parenthesizedObject, fourTau, fibTensorObj] <;> ext s <;>
    cases s <;> simp [fibTensorObj] <;> ring

theorem parenthesizedObject_counts (v : PentagonVertex) :
    parenthesizedObject v FibSimple.unit = 2 ∧
      parenthesizedObject v FibSimple.tau = 3 := by
  cases v <;> simp [parenthesizedObject, fourTau, fibTensorObj]

theorem parenthesizedObject_total_channel_count (v : PentagonVertex) :
    parenthesizedObject v FibSimple.unit +
        parenthesizedObject v FibSimple.tau = 5 := by
  rw [(parenthesizedObject_counts v).1, (parenthesizedObject_counts v).2]

theorem basis6_card : Fintype.card Basis6 = 5 := by
  simp [Basis6]

/-- A noncanonical cardinality transport from the formal channel count to the
finite `Basis6` carrier.  This is not a choice of fusion basis. -/
noncomputable def parenthesizedChannelEquiv (v : PentagonVertex) :
    Fin (parenthesizedObject v FibSimple.unit +
      parenthesizedObject v FibSimple.tau) ≃ Basis6 :=
  Equiv.cast (congrArg Fin (parenthesizedObject_total_channel_count v))

theorem parenthesizedChannelEquiv_source (v : PentagonVertex) :
    (parenthesizedChannelEquiv v).toFun =
      (Equiv.cast (congrArg Fin (parenthesizedObject_total_channel_count v))).toFun :=
  rfl

abbrev PathCarrier := Basis6 → ℂ

def edgeSource : PentagonEdge → PentagonVertex
  | .edge₁ => .vertex₁
  | .edge₂ => .vertex₂
  | .edge₃ => .vertex₃
  | .edge₄ => .vertex₄
  | .edge₅ => .vertex₅

def edgeTarget : PentagonEdge → PentagonVertex
  | .edge₁ => .vertex₂
  | .edge₂ => .vertex₃
  | .edge₃ => .vertex₄
  | .edge₄ => .vertex₅
  | .edge₅ => .vertex₁

theorem edge_target_source_cycle (e : PentagonEdge) :
    edgeTarget e ≠ edgeSource e := by
  cases e <;> decide

theorem edge_source_target_cover (v : PentagonVertex) :
    ∃ e, edgeSource e = v ∧ edgeTarget e ≠ v := by
  cases v with
  | vertex₁ => exact ⟨.edge₁, rfl, by decide⟩
  | vertex₂ => exact ⟨.edge₂, rfl, by decide⟩
  | vertex₃ => exact ⟨.edge₃, rfl, by decide⟩
  | vertex₄ => exact ⟨.edge₄, rfl, by decide⟩
  | vertex₅ => exact ⟨.edge₅, rfl, by decide⟩

noncomputable def parenthesizedObjectIso (e : PentagonEdge) :
    parenthesizedObject (edgeSource e) ≅ parenthesizedObject (edgeTarget e) :=
  CategoryTheory.eqToIso (by
    rw [parenthesizedObject_eq_vertex₁ (edgeSource e),
      parenthesizedObject_eq_vertex₁ (edgeTarget e)])

noncomputable def edgeMatrix (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B : BBlockEntries) : Matrix Basis6 Basis6 ℂ :=
  match e with
  | .edge₁ => pi6_b1 qNeg4 q3
  | .edge₂ => pi6_b2 q3 B
  | .edge₃ => pi6_b3 qNeg4 q3 B
  | .edge₄ => pi6_b4 q3 B
  | .edge₅ => pi6_b5 qNeg4 q3

noncomputable def edgeLinearMap (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B : BBlockEntries) : PathCarrier →ₗ[ℂ] PathCarrier :=
  Matrix.toLin' (edgeMatrix e qNeg4 q3 B)

theorem edgeLinearMap_apply (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B : BBlockEntries) (x : PathCarrier) :
    edgeLinearMap e qNeg4 q3 B x =
      Matrix.mulVec (edgeMatrix e qNeg4 q3 B) x := by
  rfl

theorem edgeLinearMap_comp (e₁ e₂ : PentagonEdge) (qNeg4 q3 : ℂ)
    (B : BBlockEntries) :
    (edgeLinearMap e₁ qNeg4 q3 B).comp
        (edgeLinearMap e₂ qNeg4 q3 B) =
      Matrix.toLin'
        (edgeMatrix e₁ qNeg4 q3 B * edgeMatrix e₂ qNeg4 q3 B) := by
  simp [edgeLinearMap, Matrix.toLin'_mul]

noncomputable def edgeInverseMatrix (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries) : Matrix Basis6 Basis6 ℂ :=
  match e with
  | .edge₁ => pi6_b1 qNeg4⁻¹ q3⁻¹
  | .edge₂ => pi6_b2 q3⁻¹ Binv
  | .edge₃ => pi6_b3 qNeg4⁻¹ q3⁻¹ Binv
  | .edge₄ => pi6_b4 q3⁻¹ Binv
  | .edge₅ => pi6_b5 qNeg4⁻¹ q3⁻¹

theorem edgeMatrix_mul_inverse (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    edgeMatrix e qNeg4 q3 B * edgeInverseMatrix e qNeg4 q3 B Binv = 1 := by
  cases e with
  | edge₁ =>
    exact endpointOne_matrix_mul_inverse qNeg4 q3 hqNeg4 hq3
  | edge₂ =>
    exact middleTwo_matrix_mul_inverse q3 B Binv hB hq3
  | edge₃ =>
    exact middleThree_matrix_mul_inverse qNeg4 q3 B Binv hB hqNeg4 hq3
  | edge₄ =>
    exact middleFour_matrix_mul_inverse q3 B Binv hB hq3
  | edge₅ =>
    exact endpointFive_matrix_mul_inverse qNeg4 q3 hqNeg4 hq3

noncomputable def edgeInverseLinearMap (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries) : PathCarrier →ₗ[ℂ] PathCarrier :=
  Matrix.toLin' (edgeInverseMatrix e qNeg4 q3 B Binv)

theorem edgeLinearMap_comp_inverse (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (edgeLinearMap e qNeg4 q3 B).comp
        (edgeInverseLinearMap e qNeg4 q3 B Binv) =
      LinearMap.id := by
  rw [show (edgeLinearMap e qNeg4 q3 B).comp
      (edgeInverseLinearMap e qNeg4 q3 B Binv) =
      Matrix.toLin' (edgeMatrix e qNeg4 q3 B *
        edgeInverseMatrix e qNeg4 q3 B Binv) by
    simp [edgeLinearMap, edgeInverseLinearMap, Matrix.toLin'_mul]]
  rw [edgeMatrix_mul_inverse e qNeg4 q3 B Binv hB hqNeg4 hq3]
  ext x i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem edgeInverse_comp_linearMap (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (edgeInverseLinearMap e qNeg4 q3 B Binv).comp
        (edgeLinearMap e qNeg4 q3 B) =
      LinearMap.id := by
  cases e with
  | edge₁ =>
    rw [show (edgeInverseLinearMap .edge₁ qNeg4 q3 B Binv).comp
        (edgeLinearMap .edge₁ qNeg4 q3 B) =
        Matrix.toLin' (pi6_b1 qNeg4⁻¹ q3⁻¹ * pi6_b1 qNeg4 q3) by
      simp [edgeLinearMap, edgeInverseLinearMap, edgeMatrix,
        edgeInverseMatrix]]
    have hm : pi6_b1 qNeg4⁻¹ q3⁻¹ * pi6_b1 qNeg4 q3 = 1 := by
      simpa only [inv_inv] using
        (endpointOne_matrix_mul_inverse qNeg4⁻¹ q3⁻¹
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3))
    rw [hm]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

  | edge₂ =>
    rw [show (edgeInverseLinearMap .edge₂ qNeg4 q3 B Binv).comp
        (edgeLinearMap .edge₂ qNeg4 q3 B) =
        Matrix.toLin' (pi6_b2 q3⁻¹ Binv * pi6_b2 q3 B) by
      simp [edgeLinearMap, edgeInverseLinearMap, edgeMatrix, edgeInverseMatrix,
        Matrix.toLin'_mul]]
    rw [middleTwo_matrix_inverse_mul q3 B Binv hBinv hq3]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  | edge₃ =>
    rw [show (edgeInverseLinearMap .edge₃ qNeg4 q3 B Binv).comp
        (edgeLinearMap .edge₃ qNeg4 q3 B) =
        Matrix.toLin' (pi6_b3 qNeg4⁻¹ q3⁻¹ Binv *
          pi6_b3 qNeg4 q3 B) by
      simp [edgeLinearMap, edgeInverseLinearMap, edgeMatrix, edgeInverseMatrix,
        Matrix.toLin'_mul]]
    rw [middleThree_matrix_inverse_mul qNeg4 q3 B Binv hBinv hqNeg4 hq3]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  | edge₄ =>
    rw [show (edgeInverseLinearMap .edge₄ qNeg4 q3 B Binv).comp
        (edgeLinearMap .edge₄ qNeg4 q3 B) =
        Matrix.toLin' (pi6_b4 q3⁻¹ Binv * pi6_b4 q3 B) by
      simp [edgeLinearMap, edgeInverseLinearMap, edgeMatrix, edgeInverseMatrix,
        Matrix.toLin'_mul]]
    rw [middleFour_matrix_inverse_mul q3 B Binv hBinv hq3]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  | edge₅ =>
    rw [show (edgeInverseLinearMap .edge₅ qNeg4 q3 B Binv).comp
        (edgeLinearMap .edge₅ qNeg4 q3 B) =
        Matrix.toLin' (pi6_b5 qNeg4⁻¹ q3⁻¹ * pi6_b5 qNeg4 q3) by
      simp [edgeLinearMap, edgeInverseLinearMap, edgeMatrix,
        edgeInverseMatrix]]
    have hm : pi6_b5 qNeg4⁻¹ q3⁻¹ * pi6_b5 qNeg4 q3 = 1 := by
      simpa only [inv_inv] using
        (endpointFive_matrix_mul_inverse qNeg4⁻¹ q3⁻¹
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3))
    rw [hm]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

noncomputable def edgeLinearEquiv (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    PathCarrier ≃ₗ[ℂ] PathCarrier :=
  LinearEquiv.ofLinear
    (edgeLinearMap e qNeg4 q3 B)
    (edgeInverseLinearMap e qNeg4 q3 B Binv)
    (edgeLinearMap_comp_inverse e qNeg4 q3 B Binv hB hqNeg4 hq3)
    (edgeInverse_comp_linearMap e qNeg4 q3 B Binv hBinv hqNeg4 hq3)

theorem edgeLinearEquiv_apply (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) (x : PathCarrier) :
    edgeLinearEquiv e qNeg4 q3 B Binv hB hBinv hqNeg4 hq3 x =
      Matrix.mulVec (edgeMatrix e qNeg4 q3 B) x := by
  rfl

noncomputable def edgeModuleIso (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ PathCarrier ≅ ModuleCat.of ℂ PathCarrier :=
  (edgeLinearEquiv e qNeg4 q3 B Binv hB hBinv hqNeg4 hq3).toModuleIso

theorem edgeModuleIso_hom (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (edgeModuleIso e qNeg4 q3 B Binv hB hBinv hqNeg4 hq3).hom =
      ModuleCat.ofHom (Matrix.toLin' (edgeMatrix e qNeg4 q3 B)) := by
  rfl

theorem edgeMatrix_edge₁ (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeMatrix .edge₁ qNeg4 q3 B = pi6_b1 qNeg4 q3 := by
  rfl

theorem edgeMatrix_edge₂ (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeMatrix .edge₂ qNeg4 q3 B = pi6_b2 q3 B := by
  rfl

theorem edgeMatrix_edge₃ (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeMatrix .edge₃ qNeg4 q3 B = pi6_b3 qNeg4 q3 B := by
  rfl

theorem edgeMatrix_edge₄ (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeMatrix .edge₄ qNeg4 q3 B = pi6_b4 q3 B := by
  rfl

theorem edgeMatrix_edge₅ (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeMatrix .edge₅ qNeg4 q3 B = pi6_b5 qNeg4 q3 := by
  rfl

end InfoGeometry.Categorical.FibonacciPentagonPathCarrier
