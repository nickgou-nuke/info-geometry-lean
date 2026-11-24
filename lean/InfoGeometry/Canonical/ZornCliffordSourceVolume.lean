/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordKleinHierarchy
import InfoGeometry.Algebra.ZornChiralOperatorReconstruction

/-!
# The source-ordered eight-generator real Dirac volume

The order is `(1, q₁, q₂, q₃, q₄, q₅, q₆, q₇)`, where the first three
imaginary vectors are `Vᵢ-Uᵢ`, the next three are `Uᵢ+Vᵢ`, and
`q₇=E₂₂-E₁₁`.  On the real sixteen-dimensional Dirac module this ordered
product acts as **minus** the chirality operator.

The proof reduces each single gamma to its two-block action and then uses
the existing seven-generator left-operator volume theorem.  It does not
reassociate octonion products or expand eight nested Zorn products.  The
square theorem below concerns the represented operator.  It does not infer
injectivity of the full Clifford representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornClifford

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

private def sourceImaginaryZorn : Fin 7 → VZ :=
  ![-InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal
      (InfoGeometry.Algebra.ZornVec3.basis 0)
      (-InfoGeometry.Algebra.ZornVec3.basis 0),
    -InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal
      (InfoGeometry.Algebra.ZornVec3.basis 1)
      (-InfoGeometry.Algebra.ZornVec3.basis 1),
    -InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal
      (InfoGeometry.Algebra.ZornVec3.basis 2)
      (-InfoGeometry.Algebra.ZornVec3.basis 2),
    InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal
      (InfoGeometry.Algebra.ZornVec3.basis 0)
      (InfoGeometry.Algebra.ZornVec3.basis 0),
    InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal
      (InfoGeometry.Algebra.ZornVec3.basis 1)
      (InfoGeometry.Algebra.ZornVec3.basis 1),
    InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal
      (InfoGeometry.Algebra.ZornVec3.basis 2)
      (InfoGeometry.Algebra.ZornVec3.basis 2),
    -InfoGeometry.Algebra.ZornVectorMatrix.diagonal 1 (-1)]

/-- The seven imaginary source vectors in the real Clifford vector carrier. -/
def sourceImaginaryVector (i : Fin 7) : ZornMatrix ℝ :=
  canonicalVectorEquiv.symm (sourceImaginaryZorn i)

private def sourceLeftOperator : Fin 7 → Module.End ℝ VZ :=
  ![-InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaMinus
      (InfoGeometry.Algebra.ZornVec3.basis 0),
    -InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaMinus
      (InfoGeometry.Algebra.ZornVec3.basis 1),
    -InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaMinus
      (InfoGeometry.Algebra.ZornVec3.basis 2),
    InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaPlus
      (InfoGeometry.Algebra.ZornVec3.basis 0),
    InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaPlus
      (InfoGeometry.Algebra.ZornVec3.basis 1),
    InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaPlus
      (InfoGeometry.Algebra.ZornVec3.basis 2),
    -InfoGeometry.Algebra.L_map (R := ℝ)
      (InfoGeometry.Algebra.ZornVectorMatrix.diagonal 1 (-1))]

private theorem sourceLeftOperator_apply (i : Fin 7) (z : VZ) :
    sourceLeftOperator i z =
      InfoGeometry.Algebra.ZornVectorMatrix.mul (sourceImaginaryZorn i) z := by
  fin_cases i <;>
    simp [sourceLeftOperator, sourceImaginaryZorn,
      InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaMinus,
      InfoGeometry.Algebra.ZornVectorMatrix.leftMajoranaPlus,
      InfoGeometry.Algebra.L_map,
      InfoGeometry.Algebra.ZornVectorMatrix.neg_mul]

private theorem sourceImaginaryZorn_conj (i : Fin 7) :
    InfoGeometry.Algebra.ZornVectorMatrix.conj (sourceImaginaryZorn i) =
      -(sourceImaginaryZorn i) := by
  fin_cases i <;> ext k <;>
    simp [sourceImaginaryZorn, InfoGeometry.Algebra.ZornVectorMatrix.conj,
      InfoGeometry.Algebra.ZornVectorMatrix.neg,
      InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal,
      InfoGeometry.Algebra.ZornVectorMatrix.diagonal]

/-- The seven source vectors have norm signs `(+,+,+,-,-,-,-)`. -/
theorem sourceImaginaryVector_norm (i : Fin 7) :
    zornNorm (sourceImaginaryVector i) = if i.val < 3 then 1 else -1 := by
  rw [zornNorm_eq_vectorNorm]
  simp only [sourceImaginaryVector, Equiv.apply_symm_apply]
  fin_cases i <;>
    norm_num [sourceImaginaryZorn, InfoGeometry.Algebra.ZornVectorMatrix.norm,
      InfoGeometry.Algebra.ZornVectorMatrix.neg,
      InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal,
      InfoGeometry.Algebra.ZornVectorMatrix.diagonal,
      InfoGeometry.Algebra.ZornVec3.dot,
      InfoGeometry.Algebra.ZornVec3.basis, Fin.sum_univ_three]

private def diracVectorReadbackEquiv :
    DiracSpinor16 (R := ℝ) ≃ VZ × VZ :=
  canonicalVectorEquiv.prodCongr canonicalVectorEquiv

private theorem sourceGamma_readback (i : Fin 7)
    (Ψ : DiracSpinor16 (R := ℝ)) :
    diracVectorReadbackEquiv (diracGammaLinear (sourceImaginaryVector i) Ψ) =
      (sourceLeftOperator i (diracVectorReadbackEquiv Ψ).2,
        -sourceLeftOperator i (diracVectorReadbackEquiv Ψ).1) := by
  rcases Ψ with ⟨s, t⟩
  change (canonicalVectorEquiv (diracGamma (sourceImaginaryVector i) (s, t)).1,
      canonicalVectorEquiv (diracGamma (sourceImaginaryVector i) (s, t)).2) = _
  rw [diracGamma_vectorReadback]
  simp only [sourceImaginaryVector, Equiv.apply_symm_apply]
  rw [sourceImaginaryZorn_conj,
    show (-sourceImaginaryZorn i : VZ) =
      InfoGeometry.Algebra.ZornVectorMatrix.neg (sourceImaginaryZorn i) from rfl,
    InfoGeometry.Algebra.ZornVectorMatrix.neg_mul]
  simp only [sourceLeftOperator_apply]
  rfl

private theorem unitGamma_readback (Ψ : DiracSpinor16 (R := ℝ)) :
    diracVectorReadbackEquiv (diracGammaLinear (1 : ZornMatrix ℝ) Ψ) =
      ((diracVectorReadbackEquiv Ψ).2, (diracVectorReadbackEquiv Ψ).1) := by
  have hc : zornConj (1 : ZornMatrix ℝ) = 1 := by
    ext i <;> simp [zornConj]
  rcases Ψ with ⟨s, t⟩
  change (canonicalVectorEquiv ((1 : ZornMatrix ℝ) * t),
      canonicalVectorEquiv (zornConj (1 : ZornMatrix ℝ) * s)) =
    (canonicalVectorEquiv t, canonicalVectorEquiv s)
  simp only [hc, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul]

private theorem sourceLeftOperator_volume :
    sourceLeftOperator 0 * sourceLeftOperator 1 * sourceLeftOperator 2 *
      sourceLeftOperator 3 * sourceLeftOperator 4 * sourceLeftOperator 5 *
      sourceLeftOperator 6 = -1 := by
  simpa [sourceLeftOperator] using
    InfoGeometry.Algebra.ZornVectorMatrix.leftMajorana_source_ordered_volume

/-- The fixed ordered product of the unit vector and the seven source vectors
in the native full Clifford algebra. -/
def sourceOrderedCliffordVolume : CliffordAlgebra (zornNorm (R := ℝ)) :=
  CliffordAlgebra.ι zornNorm (1 : ZornMatrix ℝ) *
    CliffordAlgebra.ι zornNorm (sourceImaginaryVector 0) *
    CliffordAlgebra.ι zornNorm (sourceImaginaryVector 1) *
    CliffordAlgebra.ι zornNorm (sourceImaginaryVector 2) *
    CliffordAlgebra.ι zornNorm (sourceImaginaryVector 3) *
    CliffordAlgebra.ι zornNorm (sourceImaginaryVector 4) *
    CliffordAlgebra.ι zornNorm (sourceImaginaryVector 5) *
    CliffordAlgebra.ι zornNorm (sourceImaginaryVector 6)

private theorem sourceOrderedVolume_readback
    (Ψ : DiracSpinor16 (R := ℝ)) :
    diracVectorReadbackEquiv (zornCliffordRepresentation sourceOrderedCliffordVolume Ψ) =
      ((sourceLeftOperator 0 * sourceLeftOperator 1 * sourceLeftOperator 2 *
          sourceLeftOperator 3 * sourceLeftOperator 4 * sourceLeftOperator 5 *
          sourceLeftOperator 6) (diracVectorReadbackEquiv Ψ).1,
        -((sourceLeftOperator 0 * sourceLeftOperator 1 * sourceLeftOperator 2 *
          sourceLeftOperator 3 * sourceLeftOperator 4 * sourceLeftOperator 5 *
          sourceLeftOperator 6) (diracVectorReadbackEquiv Ψ).2)) := by
  simp only [sourceOrderedCliffordVolume, map_mul, zornCliffordRepresentation_ι,
    Module.End.mul_apply, unitGamma_readback, sourceGamma_readback, map_neg, neg_neg]

private theorem readback_neg_chirality (Ψ : DiracSpinor16 (R := ℝ)) :
    diracVectorReadbackEquiv ((-diracChirality.toLinearMap) Ψ) =
      (-(diracVectorReadbackEquiv Ψ).1, (diracVectorReadbackEquiv Ψ).2) := by
  rcases Ψ with ⟨s, t⟩
  change (canonicalVectorEquiv (-s), canonicalVectorEquiv (-(-t))) =
    (-canonicalVectorEquiv s, canonicalVectorEquiv t)
  simp only [neg_neg, canonicalVectorEquiv_neg]
  rfl

/-- The source orientation gives minus chirality, rather than plus chirality. -/
theorem sourceOrderedCliffordVolume_representation :
    zornCliffordRepresentation sourceOrderedCliffordVolume =
      -diracChirality.toLinearMap := by
  apply LinearMap.ext
  intro Ψ
  apply diracVectorReadbackEquiv.injective
  rw [sourceOrderedVolume_readback, readback_neg_chirality,
    sourceLeftOperator_volume]
  simp only [LinearMap.neg_apply, Module.End.one_apply, neg_neg]

/-- The represented source volume is an involution. -/
theorem sourceOrderedCliffordVolume_operator_sq :
    zornCliffordRepresentation sourceOrderedCliffordVolume *
        zornCliffordRepresentation sourceOrderedCliffordVolume = 1 := by
  rw [sourceOrderedCliffordVolume_representation]
  apply LinearMap.ext
  intro Ψ
  simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg, Module.End.one_apply]
  exact diracChirality_sq Ψ

/-- In the source orientation, the first eight-dimensional summand has
volume eigenvalue `-1`. -/
theorem sourceOrderedCliffordVolume_plus (s : ZornMatrix ℝ) :
    zornCliffordRepresentation sourceOrderedCliffordVolume (s, 0) = (-s, 0) := by
  rw [sourceOrderedCliffordVolume_representation]
  change -(s, -(0 : ZornMatrix ℝ)) = (-s, 0)
  simp

/-- The second eight-dimensional summand has volume eigenvalue `+1`. -/
theorem sourceOrderedCliffordVolume_minus (t : ZornMatrix ℝ) :
    zornCliffordRepresentation sourceOrderedCliffordVolume (0, t) = (0, t) := by
  rw [sourceOrderedCliffordVolume_representation]
  change -((0 : ZornMatrix ℝ), -t) = (0, t)
  simp

/-- Reversing the source orientation gives the chosen `(+1,-1)` chirality. -/
theorem neg_sourceOrderedCliffordVolume_representation :
    zornCliffordRepresentation (-sourceOrderedCliffordVolume) =
      diracChirality.toLinearMap := by
  rw [map_neg, sourceOrderedCliffordVolume_representation, neg_neg]

end InfoGeometry.Canonical.ZornClifford

end
