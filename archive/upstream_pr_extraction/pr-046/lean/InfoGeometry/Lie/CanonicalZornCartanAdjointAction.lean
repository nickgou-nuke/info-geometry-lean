import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Lie.CanonicalZornDerivationDimension

/-!
# Adjoint action of the native Cartan plane on derivations

This owner exposes the first derivation-level layer needed for a genuine
Cartan/root decomposition.  It does not identify root spaces or a Weyl group;
those require an explicit coordinate computation on the fourteen-dimensional
derivation basis.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCartanAdjointAction

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Algebra
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation

abbrev Der := canonicalZornDerivations

/-- The adjoint endomorphism induced by a native traceless Cartan element. -/
noncomputable def adCartan (k : TracelessWeight) : Module.End ℝ Der where
  toFun D := ⁅axialCartanLieEquiv k, D⁆
  map_add' D E := by
    apply Subtype.ext
    simp [sub_eq_add_neg, add_mul, mul_add, add_sub, sub_add, sub_sub]
  map_smul' r D := by
    apply Subtype.ext
    simp [sub_eq_add_neg, smul_sub, smul_mul_assoc, mul_smul_comm]

@[simp] theorem adCartan_apply (k : TracelessWeight) (D : Der) :
    adCartan k D = ⁅axialCartanLieEquiv k, D⁆ := rfl

/-- Cartan parameters act linearly on the adjoint representation. -/
theorem adCartan_add (k l : TracelessWeight) :
    adCartan (k + l) = adCartan k + adCartan l := by
  apply LinearMap.ext
  intro D
  simp only [adCartan_apply, LinearMap.add_apply]
  rw [← add_lie, (axialCartanLieEquiv).map_add]

theorem adCartan_smul (r : ℝ) (k : TracelessWeight) :
    adCartan (r • k) =
      (r • (adCartan k : Module.End ℝ Der) : Module.End ℝ Der) := by
  apply LinearMap.ext
  intro D
  simp only [adCartan_apply, LinearMap.smul_apply]
  rw [← smul_lie, (axialCartanLieEquiv).map_smul]

/-- The commuting Cartan plane acts by commuting adjoint operators. -/
theorem adCartan_commute (k l : TracelessWeight) :
    adCartan k * adCartan l = adCartan l * adCartan k := by
  apply LinearMap.ext
  intro D
  simp only [adCartan_apply, Module.End.mul_apply]
  rw [leibniz_lie]
  simp [axialCartanLieSubalgebra_bracket_zero]

/-! ## The concrete fourteen-coordinate readout

The preceding endomorphism acts on the native derivation subalgebra.  The
dimension owner already supplies a genuine linear equivalence
`Params ≃ₗ[ℝ] Der`; conjugating by it gives the corresponding operator on the
explicit `Fin 14` parameter carrier.  This is a coordinate transport, not a
root-space claim: the entries/eigenvectors of these operators remain a
separate concrete computation.
-/

noncomputable def adCartanCoordinates (k : TracelessWeight) :
    Module.End ℝ Params :=
  (canonicalParameterLinearEquiv.symm :
      CanonicalZornDerivation.canonicalZornDerivations ≃ₗ[ℝ] Params).toLinearMap.comp
    ((adCartan k).comp canonicalParameterLinearEquiv.toLinearMap)

@[simp] theorem adCartanCoordinates_apply (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p =
      canonicalParameterLinearEquiv.symm (adCartan k (canonicalParameterLinearEquiv p)) :=
  rfl

theorem adCartanCoordinates_add (k l : TracelessWeight) :
    adCartanCoordinates (k + l) = adCartanCoordinates k + adCartanCoordinates l := by
  ext p
  simp [adCartanCoordinates, adCartan_add]

theorem adCartanCoordinates_smul (r : ℝ) (k : TracelessWeight) :
    adCartanCoordinates (r • k) =
      r • (adCartanCoordinates k : Module.End ℝ Params) := by
  ext p
  simp [adCartanCoordinates, adCartan_smul]

theorem adCartanCoordinates_commute (k l : TracelessWeight) :
    adCartanCoordinates k * adCartanCoordinates l =
      adCartanCoordinates l * adCartanCoordinates k := by
  let e := canonicalParameterLinearEquiv
  apply LinearMap.ext
  intro p
  apply e.injective
  have h := congrArg (fun T : Module.End ℝ Der => T (e p))
    (adCartan_commute k l)
  simpa [adCartanCoordinates, Module.End.mul_apply] using h

/-! The actual finite matrix readout.  The entries are deliberately defined
through Mathlib's basis-aware `LinearMap.toMatrix`; this keeps the coordinate
carrier tied to the proved parameter equivalence rather than introducing a
second hand-written matrix convention. -/

noncomputable def adCartanMatrix (k : TracelessWeight) :
    Matrix (Fin 14) (Fin 14) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 14)) (Pi.basisFun ℝ (Fin 14))
    (adCartanCoordinates k)

theorem adCartanMatrix_apply (k : TracelessWeight) (i j : Fin 14) :
    adCartanMatrix k i j =
      (adCartanCoordinates k (Pi.single j (1 : ℝ))) i := by
  rw [adCartanMatrix, LinearMap.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_repr]

theorem adCartanMatrix_mul (k l : TracelessWeight) :
    adCartanMatrix (k + l) = adCartanMatrix k + adCartanMatrix l := by
  rw [adCartanMatrix, adCartanMatrix, adCartanMatrix, adCartanCoordinates_add]
  exact (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 14))
    (Pi.basisFun ℝ (Fin 14))).map_add _ _

theorem adCartanMatrix_smul (r : ℝ) (k : TracelessWeight) :
    adCartanMatrix (r • k) = r • adCartanMatrix k := by
  rw [adCartanMatrix, adCartanMatrix, adCartanCoordinates_smul]
  exact (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 14))
    (Pi.basisFun ℝ (Fin 14))).map_smul r _

theorem adCartanMatrix_commute (k l : TracelessWeight) :
    adCartanMatrix k * adCartanMatrix l =
      adCartanMatrix l * adCartanMatrix k := by
  let b := Pi.basisFun ℝ (Fin 14)
  change (LinearMap.toMatrix b b (adCartanCoordinates k)) *
      (LinearMap.toMatrix b b (adCartanCoordinates l)) =
    (LinearMap.toMatrix b b (adCartanCoordinates l)) *
      (LinearMap.toMatrix b b (adCartanCoordinates k))
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul,
    adCartanCoordinates_commute]

/-! ## Explicit parameter-coordinate formula

The parameter owner uses the ordered coordinates
`0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13` supplied by
`CanonicalZornDerivationDimension`.  The following theorem is the first
source-level adjoint readout on that carrier.  It is intentionally stated as
an equality of `Fin 14 → ℝ`; no root-space or `G₂` identification is folded
into the coordinate computation.
-/

open InfoGeometry.Algebra.ZornVectorMatrix

private theorem adCartanCoordinates_component_0 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 0 = -(k.1 0) * p 0 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_1 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 1 = (k.1 1 - k.1 0) * p 1 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_2 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 2 = (k.1 2 - k.1 0) * p 2 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_3 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 3 = -(k.1 1) * p 3 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_4 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 4 = -(k.1 0 + k.1 1) * p 4 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_5 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 5 = (k.1 0 - k.1 1) * p 5 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_6 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 6 = 0 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_7 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 7 = (k.1 2 - k.1 1) * p 7 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_8 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 8 = -(k.1 2) * p 8 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_9 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 9 = -(k.1 0 + k.1 2) * p 9 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_10 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 10 = -(k.1 1 + k.1 2) * p 10 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_11 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 11 = (k.1 0 - k.1 2) * p 11 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_12 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 12 = (k.1 1 - k.1 2) * p 12 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring

private theorem adCartanCoordinates_component_13 (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p 13 = 0 := by
  simp [adCartanCoordinates_apply, derivationParameters,
      canonicalParameterLinearEquiv, parameterLinearEquiv, parameterDerivation,
      vectorCanonicalLinearEquiv, vectorToCanonicalDerivation,
      vectorToCanonicalEnd, parameterAction, E22, U, V, ZornVec3.basis,
      axialCartanEnd, axialCartanLieEquiv, axialCartanDerivationIntoLie,
      axialCartanDerivationLinear, axialCartanDerivation,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      ZornVectorMatrix.mul] <;> ring


theorem adCartanCoordinates_apply_explicit
    (k : TracelessWeight) (p : Params) :
    adCartanCoordinates k p = ![
      -(k.1 0) * p 0,
      (k.1 1 - k.1 0) * p 1,
      (k.1 2 - k.1 0) * p 2,
      -(k.1 1) * p 3,
      -(k.1 0 + k.1 1) * p 4,
      (k.1 0 - k.1 1) * p 5,
      0,
      (k.1 2 - k.1 1) * p 7,
      -(k.1 2) * p 8,
      -(k.1 0 + k.1 2) * p 9,
      -(k.1 1 + k.1 2) * p 10,
      (k.1 0 - k.1 2) * p 11,
      (k.1 1 - k.1 2) * p 12,
      0] := by
  funext i
  have hi :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
      i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by
    omega
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i
  · exact adCartanCoordinates_component_0 k p
  · exact adCartanCoordinates_component_1 k p
  · exact adCartanCoordinates_component_2 k p
  · exact adCartanCoordinates_component_3 k p
  · exact adCartanCoordinates_component_4 k p
  · exact adCartanCoordinates_component_5 k p
  · exact adCartanCoordinates_component_6 k p
  · exact adCartanCoordinates_component_7 k p
  · exact adCartanCoordinates_component_8 k p
  · exact adCartanCoordinates_component_9 k p
  · exact adCartanCoordinates_component_10 k p
  · exact adCartanCoordinates_component_11 k p
  · exact adCartanCoordinates_component_12 k p
  · exact adCartanCoordinates_component_13 k p

/-- The diagonal coefficient function exposed by the explicit adjoint
coordinate formula. -/
def adCartanDiagonalCoefficient (k : TracelessWeight) : Fin 14 → ℝ := ![
    -(k.1 0),
    k.1 1 - k.1 0,
    k.1 2 - k.1 0,
    -(k.1 1),
    -(k.1 0 + k.1 1),
    k.1 0 - k.1 1,
    0,
    k.1 2 - k.1 1,
    -(k.1 2),
    -(k.1 0 + k.1 2),
    -(k.1 1 + k.1 2),
    k.1 0 - k.1 2,
    k.1 1 - k.1 2,
    0]

theorem adCartanDiagonalCoefficient_add
    (k l : TracelessWeight) :
    adCartanDiagonalCoefficient (k + l) =
      adCartanDiagonalCoefficient k + adCartanDiagonalCoefficient l := by
  funext i
  fin_cases i <;> simp [adCartanDiagonalCoefficient] <;> ring

theorem adCartanDiagonalCoefficient_smul
    (r : ℝ) (k : TracelessWeight) :
    adCartanDiagonalCoefficient (r • k) =
      r • adCartanDiagonalCoefficient k := by
  funext i
  fin_cases i <;> simp [adCartanDiagonalCoefficient] <;> ring

/-- The `j`th diagonal eigenvalue is a genuine linear functional on the
traceless Cartan plane.  This is a weight-functional readout only; no root
system interpretation is asserted here. -/
def adCartanWeightFunctional (j : Fin 14) : TracelessWeight →ₗ[ℝ] ℝ where
  toFun k := adCartanDiagonalCoefficient k j
  map_add' k l := by
    rw [adCartanDiagonalCoefficient_add]
    rfl
  map_smul' r k := by
    rw [adCartanDiagonalCoefficient_smul]
    rfl

@[simp] theorem adCartanWeightFunctional_apply
    (j : Fin 14) (k : TracelessWeight) :
    adCartanWeightFunctional j k = adCartanDiagonalCoefficient k j := rfl

@[simp] theorem adCartanWeightFunctional_six (k : TracelessWeight) :
    adCartanWeightFunctional 6 k = 0 := by
  simp [adCartanWeightFunctional, adCartanDiagonalCoefficient]

@[simp] theorem adCartanWeightFunctional_thirteen (k : TracelessWeight) :
    adCartanWeightFunctional 13 k = 0 := by
  simp [adCartanWeightFunctional, adCartanDiagonalCoefficient]

theorem adCartanWeightFunctional_sum_zero :
    ∑ j : Fin 14, adCartanWeightFunctional j = 0 := by
  apply LinearMap.ext
  intro k
  change ∑ j : Fin 14, adCartanDiagonalCoefficient k j = 0
  simp [adCartanDiagonalCoefficient, Fin.sum_univ_succ]
  have h := k.2
  change ∑ i, k.1 i = 0 at h
  have h' : k.1 0 + k.1 1 + k.1 2 = 0 := by
    simpa [Fin.sum_univ_three] using h
  linarith

theorem adCartanCoordinates_apply_diagonal
    (k : TracelessWeight) (p : Params) (i : Fin 14) :
    adCartanCoordinates k p i = adCartanDiagonalCoefficient k i * p i := by
  rw [adCartanCoordinates_apply_explicit]
  fin_cases i <;> simp [adCartanDiagonalCoefficient]

theorem adCartanCoordinates_apply_basis
    (k : TracelessWeight) (j : Fin 14) :
    adCartanCoordinates k (Pi.single j (1 : ℝ)) =
      Pi.single j (adCartanDiagonalCoefficient k j) := by
  funext i
  rw [adCartanCoordinates_apply_diagonal]
  by_cases h : i = j
  · subst i
    simp
  · have h' : ¬ j = i := fun hij => h hij.symm
    simp [Pi.single_apply, h, h']

theorem adCartanCoordinates_basis_eigen
    (k : TracelessWeight) (j : Fin 14) :
    adCartanCoordinates k (Pi.single j (1 : ℝ)) =
      (adCartanDiagonalCoefficient k j) •
        (Pi.single j (1 : ℝ) : Params) := by
  rw [adCartanCoordinates_apply_basis]
  ext i
  by_cases h : i = j
  · subst i
    simp
  · have h' : ¬ j = i := fun hij => h hij.symm
    simp [Pi.single_apply, h, h']

theorem adCartanCoordinates_basis_six (k : TracelessWeight) :
    adCartanCoordinates k (Pi.single 6 (1 : ℝ)) = 0 := by
  rw [adCartanCoordinates_apply_explicit]
  funext i
  fin_cases i <;> simp

theorem adCartanCoordinates_basis_thirteen (k : TracelessWeight) :
    adCartanCoordinates k (Pi.single 13 (1 : ℝ)) = 0 := by
  rw [adCartanCoordinates_apply_explicit]
  funext i
  fin_cases i <;> simp

theorem adCartanMatrix_apply_diagonal
    (k : TracelessWeight) (i j : Fin 14) :
    adCartanMatrix k i j =
      if i = j then adCartanDiagonalCoefficient k j else 0 := by
  rw [adCartanMatrix_apply, adCartanCoordinates_apply_basis]
  by_cases h : i = j
  · subst i
    simp
  · simp [Matrix.diagonal, h]

theorem adCartanMatrix_eq_diagonal (k : TracelessWeight) :
    adCartanMatrix k = Matrix.diagonal (adCartanDiagonalCoefficient k) := by
  ext i j
  rw [adCartanMatrix_apply_diagonal]
  by_cases h : i = j
  · subst i
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, h]

theorem adCartanMatrix_trace (k : TracelessWeight) :
    Matrix.trace (adCartanMatrix k) = 0 := by
  rw [adCartanMatrix_eq_diagonal]
  simp [Matrix.trace, adCartanDiagonalCoefficient, Fin.sum_univ_succ]
  have h := k.2
  change ∑ i, k.1 i = 0 at h
  have h' : k.1 0 + k.1 1 + k.1 2 = 0 := by
    simpa [Fin.sum_univ_three] using h
  linarith

theorem adCartanMatrix_det (k : TracelessWeight) :
    (adCartanMatrix k).det =
      ∏ j : Fin 14, adCartanDiagonalCoefficient k j := by
  rw [adCartanMatrix_eq_diagonal, Matrix.det_diagonal]

theorem adCartanMatrix_det_eq_zero (k : TracelessWeight) :
    (adCartanMatrix k).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero 6
  intro i
  rw [adCartanMatrix_apply_diagonal]
  simp [adCartanDiagonalCoefficient]

theorem cartan_traceForm_apply_apply (k l : TracelessWeight) :
    (LieModule.traceForm ℝ
        (axialCartanLieSubalgebra : LieSubalgebra ℝ Der) Der)
        (axialCartanLieEquiv k) (axialCartanLieEquiv l) =
      ∑ j : Fin 14,
        adCartanDiagonalCoefficient k j * adCartanDiagonalCoefficient l j := by
  rw [LieModule.traceForm_apply_apply]
  change (LinearMap.trace ℝ Der) ((adCartan k) ∘ₗ (adCartan l)) = _
  let e := canonicalParameterLinearEquiv.symm
  rw [← LinearMap.trace_conj' ((adCartan k) ∘ₗ (adCartan l)) e]
  rw [LinearEquiv.conj_comp]
  change (LinearMap.trace ℝ Params)
      (adCartanCoordinates k ∘ₗ adCartanCoordinates l) = _
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 14))]
  let b := Pi.basisFun ℝ (Fin 14)
  have hcomp := LinearMap.toMatrix_comp b b b
      (adCartanCoordinates k) (adCartanCoordinates l)
  rw [show (LinearMap.toMatrix b b)
      (adCartanCoordinates k ∘ₗ adCartanCoordinates l) =
      (LinearMap.toMatrix b b) (adCartanCoordinates k) *
        (LinearMap.toMatrix b b) (adCartanCoordinates l) by exact hcomp]
  change (adCartanMatrix k * adCartanMatrix l).trace = _
  rw [adCartanMatrix_eq_diagonal, adCartanMatrix_eq_diagonal]
  simp [Matrix.trace]

theorem cartan_traceForm_left_nondegenerate
    (k : TracelessWeight)
    (h : ∀ l : TracelessWeight,
      (LieModule.traceForm ℝ
        (axialCartanLieSubalgebra : LieSubalgebra ℝ Der) Der)
        (axialCartanLieEquiv k) (axialCartanLieEquiv l) = 0) :
    k = 0 := by
  have hk := h k
  rw [cartan_traceForm_apply_apply] at hk
  simp [adCartanDiagonalCoefficient, Fin.sum_univ_succ] at hk
  have h0 : k.1 0 = 0 := by
    nlinarith [sq_nonneg (k.1 0), sq_nonneg (k.1 1),
      sq_nonneg (k.1 2), sq_nonneg (k.1 1 - k.1 0),
      sq_nonneg (k.1 2 - k.1 0), sq_nonneg (k.1 2 - k.1 1)]
  have h1 : k.1 1 = 0 := by
    nlinarith [sq_nonneg (k.1 0), sq_nonneg (k.1 1),
      sq_nonneg (k.1 2), sq_nonneg (k.1 1 - k.1 0),
      sq_nonneg (k.1 2 - k.1 0), sq_nonneg (k.1 2 - k.1 1)]
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · have hs := k.2
    change ∑ i, k.1 i = 0 at hs
    simpa [Fin.sum_univ_three, h0, h1] using hs

theorem axialCartan_traceForm_nondegenerate :
    (LieModule.traceForm ℝ
      (axialCartanLieSubalgebra : LieSubalgebra ℝ Der) Der).Nondegenerate := by
  apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (LieModule.traceForm_isSymm ℝ
      (axialCartanLieSubalgebra : LieSubalgebra ℝ Der) Der).isRefl).mpr
  intro H hH
  obtain ⟨k, rfl⟩ := axialCartanLieEquiv.surjective H
  have hk : k = 0 := by
    apply cartan_traceForm_left_nondegenerate k
    intro l
    exact hH (axialCartanLieEquiv l)
  subst k
  simp [map_zero]

end InfoGeometry.Lie.CanonicalZornCartanAdjointAction
