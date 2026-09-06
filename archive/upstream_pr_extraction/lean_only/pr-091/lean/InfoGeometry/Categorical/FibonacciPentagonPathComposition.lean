import InfoGeometry.Categorical.FibonacciPentagonPathCarrier

/-!
# Composition of finite Fibonacci pentagon paths

The pentagon path carrier supplies five individual edge matrices.  This file
adds only their finite-word composition API.  It does not identify the two
pentagon paths or assert the nontrivial Fibonacci pentagon equation.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonPathComposition

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
open InfoGeometry.Categorical.FibonacciPentagonPathCarrier

abbrev PathMatrix := Matrix Basis6 Basis6 ℂ

noncomputable def edgeWordMatrix
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    List PentagonEdge → PathMatrix
  | [] => 1
  | e :: es => edgeMatrix e qNeg4 q3 B * edgeWordMatrix qNeg4 q3 B es

noncomputable def edgeWordLinearMap
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    List PentagonEdge → PathCarrier →ₗ[ℂ] PathCarrier
  | es => Matrix.toLin' (edgeWordMatrix qNeg4 q3 B es)

noncomputable def edgeWordInverseMatrix
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries) :
    List PentagonEdge → PathMatrix
  | [] => 1
  | e :: es =>
      edgeWordInverseMatrix qNeg4 q3 B Binv es *
        edgeInverseMatrix e qNeg4 q3 B Binv

noncomputable def edgeWordInverseLinearMap
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries) :
    List PentagonEdge → PathCarrier →ₗ[ℂ] PathCarrier
  | es => Matrix.toLin' (edgeWordInverseMatrix qNeg4 q3 B Binv es)

@[simp] theorem edgeWordMatrix_nil
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeWordMatrix qNeg4 q3 B [] = 1 := rfl

@[simp] theorem edgeWordMatrix_cons
    (e : PentagonEdge) (es : List PentagonEdge)
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeWordMatrix qNeg4 q3 B (e :: es) =
      edgeMatrix e qNeg4 q3 B * edgeWordMatrix qNeg4 q3 B es := rfl

theorem edgeWordLinearMap_apply
    (es : List PentagonEdge) (qNeg4 q3 : ℂ) (B : BBlockEntries)
    (x : PathCarrier) :
    edgeWordLinearMap qNeg4 q3 B es x =
      Matrix.mulVec (edgeWordMatrix qNeg4 q3 B es) x := by
  rfl

theorem edgeLinearMap_comp_edgeWordLinearMap
    (e : PentagonEdge) (es : List PentagonEdge)
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    (edgeLinearMap e qNeg4 q3 B).comp
        (edgeWordLinearMap qNeg4 q3 B es) =
      Matrix.toLin' (edgeWordMatrix qNeg4 q3 B (e :: es)) := by
  simp [edgeLinearMap, edgeWordLinearMap, edgeWordMatrix,
    Matrix.toLin'_mul]

theorem edgeWordLinearMap_nil
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeWordLinearMap qNeg4 q3 B [] = LinearMap.id := by
  ext x i
  simp [edgeWordLinearMap, edgeWordMatrix, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]

theorem edgeWordMatrix_append
    (xs ys : List PentagonEdge) (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeWordMatrix qNeg4 q3 B (xs ++ ys) =
      edgeWordMatrix qNeg4 q3 B xs * edgeWordMatrix qNeg4 q3 B ys := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
      simp only [List.cons_append, edgeWordMatrix_cons, ih, mul_assoc]

theorem edgeWordMatrix_mul_inverse
    (xs : List PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    edgeWordMatrix qNeg4 q3 B xs *
        edgeWordInverseMatrix qNeg4 q3 B Binv xs = 1 := by
  induction xs with
  | nil => simp [edgeWordMatrix, edgeWordInverseMatrix]
  | cons e es ih =>
      rw [edgeWordMatrix_cons, edgeWordInverseMatrix]
      calc
        (edgeMatrix e qNeg4 q3 B * edgeWordMatrix qNeg4 q3 B es) *
            (edgeWordInverseMatrix qNeg4 q3 B Binv es *
              edgeInverseMatrix e qNeg4 q3 B Binv) =
            edgeMatrix e qNeg4 q3 B *
              (edgeWordMatrix qNeg4 q3 B es *
                edgeWordInverseMatrix qNeg4 q3 B Binv es) *
              edgeInverseMatrix e qNeg4 q3 B Binv := by
                simp only [mul_assoc]
        _ = edgeMatrix e qNeg4 q3 B *
              (1 : PathMatrix) *
              edgeInverseMatrix e qNeg4 q3 B Binv := by rw [ih]
        _ = 1 := by
          rw [mul_one, edgeMatrix_mul_inverse e qNeg4 q3 B Binv hB
            hqNeg4 hq3]

theorem edgeInverseMatrix_mul_edgeMatrix
    (e : PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    edgeInverseMatrix e qNeg4 q3 B Binv *
        edgeMatrix e qNeg4 q3 B = 1 := by
  cases e with
  | edge₁ =>
      simpa [edgeMatrix, edgeInverseMatrix, inv_inv] using
        (edgeMatrix_mul_inverse (.edge₁) qNeg4⁻¹ q3⁻¹ Binv B hBinv
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3))
  | edge₂ =>
      simpa [edgeMatrix, edgeInverseMatrix, inv_inv] using
        (edgeMatrix_mul_inverse (.edge₂) qNeg4⁻¹ q3⁻¹ Binv B hBinv
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3))
  | edge₃ =>
      simpa [edgeMatrix, edgeInverseMatrix, inv_inv] using
        (edgeMatrix_mul_inverse (.edge₃) qNeg4⁻¹ q3⁻¹ Binv B hBinv
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3))
  | edge₄ =>
      simpa [edgeMatrix, edgeInverseMatrix, inv_inv] using
        (edgeMatrix_mul_inverse (.edge₄) qNeg4⁻¹ q3⁻¹ Binv B hBinv
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3))
  | edge₅ =>
      simpa [edgeMatrix, edgeInverseMatrix, inv_inv] using
        (edgeMatrix_mul_inverse (.edge₅) qNeg4⁻¹ q3⁻¹ Binv B hBinv
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3))

theorem edgeWordInverseMatrix_mul
    (xs : List PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    edgeWordInverseMatrix qNeg4 q3 B Binv xs *
        edgeWordMatrix qNeg4 q3 B xs = 1 := by
  induction xs with
  | nil => simp [edgeWordMatrix, edgeWordInverseMatrix]
  | cons e es ih =>
      rw [edgeWordMatrix_cons, edgeWordInverseMatrix]
      calc
        (edgeWordInverseMatrix qNeg4 q3 B Binv es *
            edgeInverseMatrix e qNeg4 q3 B Binv) *
            (edgeMatrix e qNeg4 q3 B *
              edgeWordMatrix qNeg4 q3 B es) =
            edgeWordInverseMatrix qNeg4 q3 B Binv es *
              (edgeInverseMatrix e qNeg4 q3 B Binv *
                edgeMatrix e qNeg4 q3 B) *
              edgeWordMatrix qNeg4 q3 B es := by
                simp only [mul_assoc]
        _ = edgeWordInverseMatrix qNeg4 q3 B Binv es *
              (1 : PathMatrix) *
              edgeWordMatrix qNeg4 q3 B es := by
                rw [edgeInverseMatrix_mul_edgeMatrix e qNeg4 q3 B Binv
                  hBinv hqNeg4 hq3]
        _ = 1 := by
          rw [mul_one, ih]

theorem edgeWordLinearMap_comp_inverse
    (xs : List PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (edgeWordLinearMap qNeg4 q3 B xs).comp
        (edgeWordInverseLinearMap qNeg4 q3 B Binv xs) =
      LinearMap.id := by
  rw [show (edgeWordLinearMap qNeg4 q3 B xs).comp
      (edgeWordInverseLinearMap qNeg4 q3 B Binv xs) =
      Matrix.toLin' (edgeWordMatrix qNeg4 q3 B xs *
        edgeWordInverseMatrix qNeg4 q3 B Binv xs) by
    simp [edgeWordLinearMap, edgeWordInverseLinearMap, Matrix.toLin'_mul]]
  rw [edgeWordMatrix_mul_inverse xs qNeg4 q3 B Binv hB hqNeg4 hq3]
  ext x i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem edgeWordInverse_comp_linearMap
    (xs : List PentagonEdge) (qNeg4 q3 : ℂ)
    (B Binv : BBlockEntries)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (edgeWordInverseLinearMap qNeg4 q3 B Binv xs).comp
        (edgeWordLinearMap qNeg4 q3 B xs) =
      LinearMap.id := by
  rw [show (edgeWordInverseLinearMap qNeg4 q3 B Binv xs).comp
      (edgeWordLinearMap qNeg4 q3 B xs) =
      Matrix.toLin' (edgeWordInverseMatrix qNeg4 q3 B Binv xs *
        edgeWordMatrix qNeg4 q3 B xs) by
    simp [edgeWordLinearMap, edgeWordInverseLinearMap, Matrix.toLin'_mul]]
  rw [edgeWordInverseMatrix_mul xs qNeg4 q3 B Binv hBinv hqNeg4 hq3]
  ext x i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem edgeWordLinearMap_append
    (xs ys : List PentagonEdge) (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    (edgeWordLinearMap qNeg4 q3 B xs).comp
        (edgeWordLinearMap qNeg4 q3 B ys) =
      edgeWordLinearMap qNeg4 q3 B (xs ++ ys) := by
  simp [edgeWordLinearMap, Matrix.toLin'_mul, edgeWordMatrix_append]

/- The finite matrix and linear-map presentations of a word carry exactly
the same equality information.  This is the readout used by a future
pentagon proof: the remaining content is the explicit matrix identity, not
an untyped equality of path carriers. -/
theorem edgeWordMatrix_eq_iff_edgeWordLinearMap_eq
    (xs ys : List PentagonEdge) (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    edgeWordMatrix qNeg4 q3 B xs = edgeWordMatrix qNeg4 q3 B ys ↔
      edgeWordLinearMap qNeg4 q3 B xs =
        edgeWordLinearMap qNeg4 q3 B ys := by
  constructor
  · intro h
    simp [edgeWordLinearMap, h]
  · intro h
    apply Matrix.toLin'.injective
    simpa [edgeWordLinearMap] using h

end InfoGeometry.Categorical.FibonacciPentagonPathComposition
