/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
import InfoGeometry.Canonical.ZornPolarAdjoint
import InfoGeometry.Canonical.ZornSpinor

/-!
# Krein and metric-conjugated products in the Ell circular operator basis

This bridge uses the actual eight-dimensional Ell basis and the repository's
native Zorn polarization.  The positive product is obtained by inserting the
fundamental symmetry in the second slot; it is not the raw Krein pairing.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Canonical.ZornPolarizationMetricBridge
open InfoGeometry.Canonical.ZornPolarAdjoint
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance

abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev Coordinate := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev KreinCarrier := InfoGeometry.Canonical.ZornVectorMatrixExplicit.ZornCoord

/-- The field-coordinate equivalence identifies the canonical Zorn carrier
with the tuple carrier on which the signed Krein pairing is defined. -/
noncomputable def toKreinCarrier : CanonicalZorn ≃ₗ[ℝ] KreinCarrier :=
  { toFun := fun X => (X.a, X.b, X.x, X.y)
    invFun := fun X => ⟨X.1, X.2.1, X.2.2.1, X.2.2.2⟩
    left_inv := by intro X; cases X; rfl
    right_inv := by intro X; rcases X with ⟨a, b, x, y⟩; rfl
    map_add' := by intro X Y; rfl
    map_smul' := by intro c X; rfl }

@[simp] theorem toKreinCarrier_apply (X : CanonicalZorn) :
    toKreinCarrier X = (X.a, X.b, X.x, X.y) := rfl

/-- The Ell-circular coordinate vector, read in the native Krein carrier. -/
noncomputable def ellToKrein : Coordinate ≃ₗ[ℝ] KreinCarrier :=
  coordinateEquiv.symm.trans toKreinCarrier

/-- The raw signed Krein pairing, transported to Ell-circular coordinates. -/
def ellKreinPair (x y : Coordinate) : ℝ :=
  polarPair (ellToKrein x) (ellToKrein y)

/-- The fundamental symmetry in Ell-circular coordinates. -/
noncomputable def ellFundamental : Coordinate →ₗ[ℝ] Coordinate :=
  ellToKrein.symm.toLinearMap.comp
    (fundamental.toLinearMap.comp ellToKrein.toLinearMap)

/-- The Hilbert product uses the fundamental metric symmetry in the second
argument, following the native double-real Krein convention. -/
def ellHilbertPair (x y : Coordinate) : ℝ :=
  ellKreinPair x (ellFundamental y)

@[simp] theorem ellToKrein_fundamental (x : Coordinate) :
    ellToKrein (ellFundamental x) = fundamental (ellToKrein x) := by
  simp [ellFundamental]

@[simp] theorem ellFundamental_sq (x : Coordinate) :
    ellFundamental (ellFundamental x) = x := by
  apply ellToKrein.injective
  simp [ellToKrein_fundamental]

/-- Column formula for the metric symmetry in the ordered Ell frame.  It
exchanges the two axial idempotents and exchanges each polarized root pair
with the sign dictated by the Ell root convention. -/
theorem ellFundamental_basisColumn (i : Fin 8) :
    ellFundamental (Pi.single i 1) =
      match i.val with
      | 0 => Pi.single 4 1
      | 1 => -Pi.single 5 1
      | 2 => -Pi.single 6 1
      | 3 => -Pi.single 7 1
      | 4 => Pi.single 0 1
      | 5 => -Pi.single 1 1
      | 6 => -Pi.single 2 1
      | 7 => -Pi.single 3 1
      | _ => 0 := by
  apply ellToKrein.injective
  rw [ellToKrein_fundamental]
  fin_cases i <;>
    simp [ellToKrein, coordinateEquiv_symm_single, toKreinCarrier_apply, fundamental, frame,
      uPlus, uMinus, rootPlus, rootMinus, chiralNull, ellBasis,
      quaternionBasis, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, InfoGeometry.Canonical.ZornMatrix.add_def,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.jUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.kQuaternionUnit,
      smul_eq_mul, InfoGeometry.Canonical.ZornMatrix.smul_a,
      InfoGeometry.Canonical.ZornMatrix.smul_b, InfoGeometry.Canonical.ZornMatrix.smul_x,
      InfoGeometry.Canonical.ZornMatrix.smul_y,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.one_def] <;> all_goals rfl

/-- Matrix of the fundamental symmetry in the ordered Ell coordinate basis. -/
noncomputable def ellFundamentalCoordinateMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    ellFundamental

/-- Each matrix column is the signed basis vector from
`ellFundamental_basisColumn`; thus this is the concrete operator matrix, not
just an abstract involution. -/
theorem ellFundamentalCoordinateMatrix_column (j : Fin 8) :
    (fun i : Fin 8 => ellFundamentalCoordinateMatrix i j) =
      ellFundamental (Pi.single j 1) := by
  funext i
  rw [ellFundamentalCoordinateMatrix, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]

/-- Index in the first half of the ordered Ell basis, paired with its
corresponding second-half index. -/
def ellKreinPairIndex (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩

def ellKreinOppositeIndex (i : Fin 4) : Fin 8 := ⟨i.val + 4, by omega⟩

def ellKreinPairSign (i : Fin 4) : ℝ := if i.val = 0 then 1 else -1

/-- Explicit positive and negative fundamental-symmetry eigenvectors in the
Ell circular coordinate basis. -/
def ellKreinPositiveVector (i : Fin 4) : Coordinate :=
  Pi.single (ellKreinPairIndex i) 1 +
    ellKreinPairSign i • Pi.single (ellKreinOppositeIndex i) 1

def ellKreinNegativeVector (i : Fin 4) : Coordinate :=
  Pi.single (ellKreinPairIndex i) 1 -
    ellKreinPairSign i • Pi.single (ellKreinOppositeIndex i) 1

theorem ellFundamental_positive_eigenvector (i : Fin 4) :
    ellFundamental (ellKreinPositiveVector i) = ellKreinPositiveVector i := by
  fin_cases i <;>
    simp [ellKreinPositiveVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, ellFundamental_basisColumn, ellFundamental.map_add] <;> module

theorem ellFundamental_negative_eigenvector (i : Fin 4) :
    ellFundamental (ellKreinNegativeVector i) = -ellKreinNegativeVector i := by
  fin_cases i <;>
    simp [ellKreinNegativeVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, ellFundamental_basisColumn, ellFundamental.map_sub]

theorem ellKreinPositiveVector_linearIndependent :
    LinearIndependent ℝ ellKreinPositiveVector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi := congrArg (fun z : Coordinate => z (ellKreinPairIndex i)) hg
  rw [Fin.sum_univ_four] at hi
  fin_cases i <;>
    simp [ellKreinPositiveVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, Pi.smul_apply, smul_eq_mul] at hi ⊢ <;> exact hi

theorem ellKreinNegativeVector_linearIndependent :
    LinearIndependent ℝ ellKreinNegativeVector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi := congrArg (fun z : Coordinate => z (ellKreinPairIndex i)) hg
  rw [Fin.sum_univ_four] at hi
  fin_cases i <;>
    simp [ellKreinNegativeVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, Pi.smul_apply, smul_eq_mul] at hi ⊢ <;> exact hi

/-- The regular `J` operator attached to the distinguished Ell Peirce pair.
This is the actual split-octonion regular operator transported to Ell
coordinates, rather than a newly chosen diagonal model. -/
noncomputable def ellRegularJ : Module.End ℝ Coordinate :=
  ellCoordinateConjugate (regularJ uPlus uMinus)

/-- The transported regular `J` remains an involution on the actual Ell
coordinate operator carrier. -/
theorem ellRegularJ_sq : ellRegularJ * ellRegularJ = 1 := by
  simpa [ellRegularJ, ellCoordinateConjugate] using
    congrArg (coordinateEquiv.conjAlgEquiv ℝ) regularJ_uPlus_uMinus_sq

/-- The regular `J` operator has its explicit signed column action in the
ordered Ell coordinate frame. -/
theorem ellRegularJ_basisColumn (j : Fin 8) :
    ellRegularJ (Pi.single j (1 : ℝ)) =
      (if j.val < 4 then (1 : ℝ) else -1) • Pi.single j 1 := by
  change ellCoordinateConjugate (regularJ uPlus uMinus) (Pi.single j 1) = _
  rw [ellCircular_regularJ_apply]
  ext k
  by_cases hj : j.val < 4 <;> by_cases hk : k = j <;>
    simp [hj, hk, smul_eq_mul]

/-- On the completed Krein eigenbasis, regular `J` exchanges each positive
fundamental-symmetry eigenvector with its paired negative eigenvector. -/
theorem ellRegularJ_positiveVector (i : Fin 4) :
    ellRegularJ (ellKreinPositiveVector i) = ellKreinNegativeVector i := by
  fin_cases i
  · simp [ellRegularJ_basisColumn, ellKreinPositiveVector,
      ellKreinNegativeVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, map_add]
    module
  · simp [ellRegularJ_basisColumn, ellKreinPositiveVector,
      ellKreinNegativeVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, map_add]
  · simp [ellRegularJ_basisColumn, ellKreinPositiveVector,
      ellKreinNegativeVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, map_add]
  · simp [ellRegularJ_basisColumn, ellKreinPositiveVector,
      ellKreinNegativeVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, map_add]

/-- The inverse pair exchange: regular `J` sends each negative eigenvector
back to its positive partner. -/
theorem ellRegularJ_negativeVector (i : Fin 4) :
    ellRegularJ (ellKreinNegativeVector i) = ellKreinPositiveVector i := by
  fin_cases i <;>
    simp [ellRegularJ_basisColumn, ellKreinPositiveVector,
      ellKreinNegativeVector, ellKreinPairIndex, ellKreinOppositeIndex,
      ellKreinPairSign, map_sub]

/-- The split-octonion `l`-commutator is zero on the scalar pair and
exchanges the positive/negative Krein vectors on each of the three imaginary
quaternion directions, with coefficient two. This is its action on the
actual signed operator basis, derived from the circular-coordinate diagonal
readout. -/
theorem ellCommutator_positiveVector (i : Fin 4) :
    ellCommutatorCoordinate (ellKreinPositiveVector i) =
      if i.val = 0 then 0 else 2 • ellKreinNegativeVector i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [ellKreinPositiveVector, ellKreinNegativeVector,
      ellKreinPairIndex, ellKreinOppositeIndex, ellKreinPairSign,
      ellCommutatorCoordinate_apply_diagonal,
      InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialWeight,
      Pi.smul_apply]

/-- The reverse action of the same commutator on the negative Krein sector. -/
theorem ellCommutator_negativeVector (i : Fin 4) :
    ellCommutatorCoordinate (ellKreinNegativeVector i) =
      if i.val = 0 then 0 else 2 • ellKreinPositiveVector i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [ellKreinPositiveVector, ellKreinNegativeVector,
      ellKreinPairIndex, ellKreinOppositeIndex, ellKreinPairSign,
      ellCommutatorCoordinate_apply_diagonal,
      InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialWeight,
      Pi.smul_apply]

/-- On the frozen ordered Ell basis, the Krein fundamental symmetry exchanges
the two eigenspaces of the regular `J` operator. Equivalently, the two
noncommuting operators anticommute. -/
theorem ellFundamental_regularJ_anticommute :
    ellFundamental * ellRegularJ = -(ellRegularJ * ellFundamental) := by
  apply (Pi.basisFun ℝ (Fin 8)).ext
  intro i
  simp only [Module.End.mul_apply, Pi.basisFun_apply]
  rw [ellRegularJ_basisColumn, map_smul, ellFundamental_basisColumn]
  fin_cases i <;>
    simp [ellFundamental_basisColumn, ellRegularJ_basisColumn]

/-- Reconstruction of an arbitrary Ell vector from the eight signed
fundamental-symmetry eigenvectors. The coefficients are the two projections
of each paired coordinate block, so the positive and negative families
together span the full carrier. -/
theorem ellKrein_eigenvector_expansion (x : Coordinate) :
    x = ∑ i : Fin 4,
      (((x (ellKreinPairIndex i) + ellKreinPairSign i *
          x (ellKreinOppositeIndex i)) / 2) • ellKreinPositiveVector i +
        ((x (ellKreinPairIndex i) - ellKreinPairSign i *
          x (ellKreinOppositeIndex i)) / 2) • ellKreinNegativeVector i) := by
  funext k
  rw [Fin.sum_univ_four]
  fin_cases k <;>
    simp [ellKreinPairIndex, ellKreinOppositeIndex, ellKreinPairSign,
      ellKreinPositiveVector, ellKreinNegativeVector] <;>
    ring

/-- The combined positive/negative eigenvector family, indexed without
identifying the two four-element sectors. -/
def ellKreinEigenvector : Fin 4 ⊕ Fin 4 → Coordinate
  | Sum.inl i => ellKreinPositiveVector i
  | Sum.inr i => ellKreinNegativeVector i

/-- The two four-dimensional eigenfamilies are linearly independent together:
the involution separates their coefficients, then each sector's explicit
four-vector independence applies. -/
theorem ellKreinEigenvector_linearIndependent :
    LinearIndependent ℝ ellKreinEigenvector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [ellKreinEigenvector, Fintype.sum_sum_type] at hg
  let p : Coordinate := ∑ i : Fin 4, g (Sum.inl i) • ellKreinPositiveVector i
  let n : Coordinate := ∑ i : Fin 4, g (Sum.inr i) • ellKreinNegativeVector i
  have hsum : p + n = 0 := by simpa [p, n] using hg
  have hF := congrArg ellFundamental hsum
  have hdiff : p - n = 0 := by
    simpa [p, n, sub_eq_add_neg, ellFundamental.map_add, map_sum,
      ellFundamental_positive_eigenvector,
      ellFundamental_negative_eigenvector] using hF
  have hp : p = 0 := by
    have htwo : (2 : ℝ) • p = 0 := by
      calc
        (2 : ℝ) • p = (p + n) + (p - n) := by module
        _ = 0 := by rw [hsum, hdiff]; simp
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hn : n = 0 := by simpa [hp] using hsum
  have hgp : ∀ i : Fin 4, g (Sum.inl i) = 0 := by
    have hli := Fintype.linearIndependent_iff.mp ellKreinPositiveVector_linearIndependent
    have hzero := hli (fun i => g (Sum.inl i)) (by simpa [p] using hp)
    exact hzero
  have hgn : ∀ i : Fin 4, g (Sum.inr i) = 0 := by
    have hli := Fintype.linearIndependent_iff.mp ellKreinNegativeVector_linearIndependent
    have hzero := hli (fun i => g (Sum.inr i)) (by simpa [n] using hn)
    exact hzero
  intro i
  cases i with
  | inl i => exact hgp i
  | inr i => exact hgn i

/-- Genuine eight-element basis of the Ell Krein carrier, ordered as the four
positive fundamental-symmetry eigenvectors followed by the four negative
ones. Independence and spanning are established above on this same carrier. -/
noncomputable def ellKreinEigenbasis : Module.Basis (Fin 4 ⊕ Fin 4) ℝ Coordinate :=
  Module.Basis.mk ellKreinEigenvector_linearIndependent (by
    intro x hx
    rw [ellKrein_eigenvector_expansion x]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inr i, rfl⟩))

@[simp] theorem ellKreinEigenbasis_positive_apply (i : Fin 4) :
    ellKreinEigenbasis (Sum.inl i) = ellKreinPositiveVector i :=
  Module.Basis.mk_apply _ _ _

@[simp] theorem ellKreinEigenbasis_negative_apply (i : Fin 4) :
    ellKreinEigenbasis (Sum.inr i) = ellKreinNegativeVector i :=
  Module.Basis.mk_apply _ _ _

/-- Coefficient readout for a scalar multiple of a signed Krein basis vector. -/
theorem ellKreinEigenbasis_repr_smul (c : ℝ) (i j : Fin 4 ⊕ Fin 4) :
    (ellKreinEigenbasis.repr (c • ellKreinEigenbasis j)) i =
      if i = j then c else 0 := by
  rw [map_smul, Finsupp.smul_apply,
    ellKreinEigenbasis.repr_self_apply]
  simp [eq_comm]

/-- Under the actual Ell-to-Zorn transport, the positive Krein basis vectors
are the four quaternion-basis elements. -/
theorem ellToKrein_positiveVector (i : Fin 4) :
    ellToKrein (ellKreinPositiveVector i) =
      toKreinCarrier (quaternionBasis i) := by
  fin_cases i <;>
    simp [ellToKrein, ellKreinPositiveVector, ellKreinPairIndex,
      ellKreinOppositeIndex, ellKreinPairSign, coordinateEquiv_symm_single,
      frame, rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      uPlus, uMinus,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      jUnit, kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] <;>
    norm_num

/-- The negative Krein basis vectors transport to the four vectors in the
actual Ell direction of the quaternion frame. -/
theorem ellToKrein_negativeVector (i : Fin 4) :
    ellToKrein (ellKreinNegativeVector i) =
      toKreinCarrier (ellBasis i) := by
  fin_cases i <;>
    simp [ellToKrein, ellKreinNegativeVector, ellKreinPairIndex,
      ellKreinOppositeIndex, ellKreinPairSign, coordinateEquiv_symm_single,
      frame, rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      uPlus, uMinus,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      jUnit, kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] <;>
    norm_num
  all_goals (try (funext k; fin_cases k <;> rfl))

/-- The partner involution records the positive/negative sector exchange in
the ordered Krein eigenbasis. -/
def ellKreinSectorPartner : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

/-- Matrix of the native `l`-commutator in the signed Krein eigenbasis. -/
noncomputable def ellCommutatorKreinMatrix :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellCommutatorCoordinate

/-- The `l`-commutator has a zero scalar block and exchanges each of the
three imaginary positive/negative Krein pairs with coefficient two. -/
theorem ellCommutatorKreinMatrix_apply (i j : Fin 4 ⊕ Fin 4) :
    ellCommutatorKreinMatrix i j =
      if j = Sum.inl 0 ∨ j = Sum.inr 0 then 0
      else if i = ellKreinSectorPartner j then 2 else 0 := by
  cases j with
  | inl j =>
      cases i with
      | inl i =>
          rw [ellCommutatorKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellCommutatorCoordinate (ellKreinEigenbasis (Sum.inl j)))) (Sum.inl i) = _
          rw [ellKreinEigenbasis_positive_apply, ellCommutator_positiveVector]
          by_cases hj : j = 0
          · have hv : j.val = 0 := by simpa using hj
            simp [hj]
          · have hv : j.val ≠ 0 := by simpa using hj
            rw [ite_eq_right hv, ← ellKreinEigenbasis_negative_apply]
            rw [← Nat.cast_smul_eq_nsmul ℝ 2]
            calc
              _ = if Sum.inl i = Sum.inr j then (2 : ℝ) else 0 :=
                ellKreinEigenbasis_repr_smul (2 : ℝ) (Sum.inl i) (Sum.inr j)
              _ = _ := by simp [ellKreinSectorPartner, hj]
      | inr i =>
          rw [ellCommutatorKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellCommutatorCoordinate (ellKreinEigenbasis (Sum.inl j)))) (Sum.inr i) = _
          rw [ellKreinEigenbasis_positive_apply, ellCommutator_positiveVector]
          by_cases hj : j = 0
          · have hv : j.val = 0 := by simpa using hj
            simp [hj]
          · have hv : j.val ≠ 0 := by simpa using hj
            rw [ite_eq_right hv, ← ellKreinEigenbasis_negative_apply]
            rw [← Nat.cast_smul_eq_nsmul ℝ 2]
            calc
              _ = if Sum.inr i = Sum.inr j then (2 : ℝ) else 0 :=
                ellKreinEigenbasis_repr_smul (2 : ℝ) (Sum.inr i) (Sum.inr j)
              _ = _ := by simp [ellKreinSectorPartner, hj]
  | inr j =>
      cases i with
      | inl i =>
          rw [ellCommutatorKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellCommutatorCoordinate (ellKreinEigenbasis (Sum.inr j)))) (Sum.inl i) = _
          rw [ellKreinEigenbasis_negative_apply, ellCommutator_negativeVector]
          by_cases hj : j = 0
          · have hv : j.val = 0 := by simpa using hj
            simp [hj]
          · have hv : j.val ≠ 0 := by simpa using hj
            rw [ite_eq_right hv, ← ellKreinEigenbasis_positive_apply]
            rw [← Nat.cast_smul_eq_nsmul ℝ 2]
            calc
              _ = if Sum.inl i = Sum.inl j then (2 : ℝ) else 0 :=
                ellKreinEigenbasis_repr_smul (2 : ℝ) (Sum.inl i) (Sum.inl j)
              _ = _ := by simp [ellKreinSectorPartner, hj]
      | inr i =>
          rw [ellCommutatorKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellCommutatorCoordinate (ellKreinEigenbasis (Sum.inr j)))) (Sum.inr i) = _
          rw [ellKreinEigenbasis_negative_apply, ellCommutator_negativeVector]
          by_cases hj : j = 0
          · have hv : j.val = 0 := by simpa using hj
            simp [hj]
          · have hv : j.val ≠ 0 := by simpa using hj
            rw [ite_eq_right hv, ← ellKreinEigenbasis_positive_apply]
            rw [← Nat.cast_smul_eq_nsmul ℝ 2]
            calc
              _ = if Sum.inr i = Sum.inl j then (2 : ℝ) else 0 :=
                ellKreinEigenbasis_repr_smul (2 : ℝ) (Sum.inr i) (Sum.inl j)
              _ = _ := by simp [ellKreinSectorPartner, hj]

/-- In the signed Krein basis, the induced regular-`J` double commutator is
twice the difference between an operator and its conjugate by the swap
matrix. This is the operator-algebra readout on the actual signed basis. -/
theorem ellRegularJ_doubleComm_conjugation_formula
    (T : Module.End ℝ Coordinate) :
    ellCoordinateDoubleComm ellRegularJ T =
      (2 : ℝ) • (T - ellRegularJ * T * ellRegularJ) := by
  let e := coordinateEquiv.conjAlgEquiv ℝ
  let T₀ := e.symm T
  have h := doubleComm_eq_two_smul_sub_conjugate
    (regularJ uPlus uMinus) T₀ regularJ_uPlus_uMinus_sq
  have htransport : ellCoordinateConjugate T₀ = T := by
    change e T₀ = T
    exact e.apply_symm_apply T
  have h' := congrArg ellCoordinateConjugate h
  rw [ellCoordinateConjugate_doubleComm,
    show ellCoordinateConjugate (regularJ uPlus uMinus) = ellRegularJ from rfl,
    htransport] at h'
  simpa [ellCoordinateConjugate, ellRegularJ, e, T₀, Algebra.smul_def,
    map_smul, map_sub, map_mul, map_natCast, map_ofNat] using h'

/-- Matrix of the actual regular `J` operator in the signed Krein eigenbasis.
It is the off-diagonal block exchange, not the diagonal sign matrix seen in
the original Ell coordinate frame. -/
noncomputable def ellRegularJKreinMatrix : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellRegularJ

theorem ellRegularJKreinMatrix_apply (i j : Fin 4 ⊕ Fin 4) :
    ellRegularJKreinMatrix i j = if i = ellKreinSectorPartner j then 1 else 0 := by
  cases j with
  | inl j =>
      cases i with
      | inl i =>
          rw [ellRegularJKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellRegularJ (ellKreinEigenbasis (Sum.inl j)))) (Sum.inl i) = _
          rw [ellKreinEigenbasis_positive_apply, ellRegularJ_positiveVector,
            ← ellKreinEigenbasis_negative_apply, ellKreinEigenbasis.repr_self_apply]
          simp [ellKreinSectorPartner, eq_comm]
      | inr i =>
          rw [ellRegularJKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellRegularJ (ellKreinEigenbasis (Sum.inl j)))) (Sum.inr i) = _
          rw [ellKreinEigenbasis_positive_apply, ellRegularJ_positiveVector,
            ← ellKreinEigenbasis_negative_apply, ellKreinEigenbasis.repr_self_apply]
          simp [ellKreinSectorPartner, eq_comm]
  | inr j =>
      cases i with
      | inl i =>
          rw [ellRegularJKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellRegularJ (ellKreinEigenbasis (Sum.inr j)))) (Sum.inl i) = _
          rw [ellKreinEigenbasis_negative_apply, ellRegularJ_negativeVector,
            ← ellKreinEigenbasis_positive_apply, ellKreinEigenbasis.repr_self_apply]
          simp [ellKreinSectorPartner, eq_comm]
      | inr i =>
          rw [ellRegularJKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellRegularJ (ellKreinEigenbasis (Sum.inr j)))) (Sum.inr i) = _
          rw [ellKreinEigenbasis_negative_apply, ellRegularJ_negativeVector,
            ← ellKreinEigenbasis_positive_apply, ellKreinEigenbasis.repr_self_apply]
          simp [ellKreinSectorPartner, eq_comm]

/-- Conjugation by the regular-`J` matrix permutes both indices of an
operator matrix by the positive/negative Krein-pairing involution. -/
theorem ellRegularJKreinMatrix_conj_apply
    (T : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ)
    (i j : Fin 4 ⊕ Fin 4) :
    (ellRegularJKreinMatrix * T * ellRegularJKreinMatrix) i j =
      T (ellKreinSectorPartner i) (ellKreinSectorPartner j) := by
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, ellRegularJKreinMatrix_apply,
      ellKreinSectorPartner, Fintype.sum_sum_type, Finset.sum_ite_eq']

/-- Matrix-level form of the previous identity. The middle matrix is the
explicit signed-basis swap `ellRegularJKreinMatrix`, so this computes the
induced superoperator without replacing the split-octonion carrier by a
diagonal model. -/
theorem ellRegularJ_doubleComm_kreinMatrix_formula
    (T : Module.End ℝ Coordinate) :
    LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis
        (ellCoordinateDoubleComm ellRegularJ T) =
      (2 : ℝ) •
        (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis T -
          ellRegularJKreinMatrix *
            LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis T *
            ellRegularJKreinMatrix) := by
  let e := LinearMap.toMatrixAlgEquiv ellKreinEigenbasis
  have h := congrArg e (ellRegularJ_doubleComm_conjugation_formula T)
  simp only [map_smul, map_sub, map_mul] at h
  simpa [e, ellRegularJKreinMatrix, LinearMap.toMatrixAlgEquiv] using h

/-- Entrywise form of the signed-basis superoperator: the double commutator
couples the `(i,j)` coefficient only to its simultaneously paired
`(partner i, partner j)` coefficient. -/
theorem ellRegularJ_doubleComm_kreinMatrix_entry
    (T : Module.End ℝ Coordinate) (i j : Fin 4 ⊕ Fin 4) :
    LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis
        (ellCoordinateDoubleComm ellRegularJ T) i j =
      2 * (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis T i j -
        LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis T
          (ellKreinSectorPartner i) (ellKreinSectorPartner j)) := by
  rw [ellRegularJ_doubleComm_kreinMatrix_formula]
  simp [Matrix.smul_apply, ellRegularJKreinMatrix_conj_apply]

/-- Matrix units transported by the signed Krein eigenbasis form a basis of
the full endomorphism algebra on the Ell coordinate carrier. -/
noncomputable def ellKreinOperatorBasis :
    Module.Basis ((Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) ℝ
      (Module.End ℝ Coordinate) :=
  (Matrix.stdBasis ℝ (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4)).map
    (LinearMap.toMatrixAlgEquiv ellKreinEigenbasis).symm.toLinearEquiv

theorem ellKreinOperatorBasis_apply (i j : Fin 4 ⊕ Fin 4) :
    ellKreinOperatorBasis (i, j) =
      (LinearMap.toMatrixAlgEquiv ellKreinEigenbasis).symm
        (Matrix.single i j (1 : ℝ)) := by
  simp only [ellKreinOperatorBasis, Module.Basis.map_apply,
    Matrix.stdBasis_eq_single, LinearMap.toMatrixAlgEquiv_symm]
  rfl

/-- On the signed Krein operator-unit basis, the regular-`J` double
commutator subtracts the unit with both indices paired. This is the explicit
sector mixing law in the noncommutative endomorphism algebra. -/
theorem ellRegularJ_doubleComm_operatorUnit
    (i j : Fin 4 ⊕ Fin 4) :
    LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis
        (ellCoordinateDoubleComm ellRegularJ (ellKreinOperatorBasis (i, j))) =
      (2 : ℝ) •
        (Matrix.single i j (1 : ℝ) - Matrix.single
          (ellKreinSectorPartner i) (ellKreinSectorPartner j) 1) := by
  rw [ellRegularJ_doubleComm_kreinMatrix_formula,
    ellKreinOperatorBasis_apply]
  rw [LinearMap.toMatrixAlgEquiv_symm]
  have hunit : LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis
      ((Matrix.toLinAlgEquiv ellKreinEigenbasis) (Matrix.single i j (1 : ℝ))) =
        Matrix.single i j (1 : ℝ) := by
    simpa [LinearMap.toMatrixAlgEquiv] using
      (LinearMap.toMatrixAlgEquiv_toLinAlgEquiv ellKreinEigenbasis
        (Matrix.single i j (1 : ℝ)))
  rw [hunit]
  ext a b
  simp only [Matrix.smul_apply, Matrix.sub_apply]
  rw [ellRegularJKreinMatrix_conj_apply]
  cases a <;> cases b <;> cases i <;> cases j <;>
    simp [Matrix.single, ellKreinSectorPartner]

/-- The 64 operator units split into 32 paired two-dimensional blocks under
conjugation by the actual regular `J`.  In each block, the symmetric
combination is killed by the double commutator and the antisymmetric
combination has eigenvalue four. This is the paired-block spectral law for
the induced superoperator in the signed Krein operator basis. -/
theorem ellRegularJ_doubleComm_operatorPair (i : Fin 4)
    (j : Fin 4 ⊕ Fin 4) (a b : ℝ) :
    let U := ellKreinOperatorBasis (Sum.inl i, j)
    let V := ellKreinOperatorBasis (Sum.inr i, ellKreinSectorPartner j)
    ellCoordinateDoubleComm ellRegularJ (a • U + b • V) =
      ((2 : ℝ) * (a - b)) • (U - V) := by
  dsimp
  let e := LinearMap.toMatrixAlgEquiv ellKreinEigenbasis
  let P := ellRegularJKreinMatrix
  let U := ellKreinOperatorBasis (Sum.inl i, j)
  let V := ellKreinOperatorBasis (Sum.inr i, ellKreinSectorPartner j)
  have hP : e ellRegularJ = P := rfl
  have hU : e U = Matrix.single (Sum.inl i) j (1 : ℝ) := by
    simp [e, U, ellKreinOperatorBasis_apply, LinearMap.toMatrixAlgEquiv]
  have hV : e V = Matrix.single (Sum.inr i) (ellKreinSectorPartner j) (1 : ℝ) := by
    simp [e, V, ellKreinOperatorBasis_apply, LinearMap.toMatrixAlgEquiv]
  have hconjU : ellRegularJ * U * ellRegularJ = V := by
    apply e.injective
    rw [map_mul, map_mul, hP, hU, hV]
    ext k l
    rw [ellRegularJKreinMatrix_conj_apply]
    cases k <;> cases l <;> cases j <;> simp [Matrix.single, ellKreinSectorPartner]
  have hconjV : ellRegularJ * V * ellRegularJ = U := by
    apply e.injective
    rw [map_mul, map_mul, hP, hV, hU]
    ext k l
    rw [ellRegularJKreinMatrix_conj_apply]
    cases k <;> cases l <;> cases j <;> simp [Matrix.single, ellKreinSectorPartner]
  rw [ellRegularJ_doubleComm_conjugation_formula]
  simp only [smul_add, add_mul, mul_add, smul_sub]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [hconjU, hconjV]
  module

/-- A block and one of its two sides select a unique signed Krein operator
unit. -/
def ellKreinOperatorPairMember
    (p : (Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool) :
    (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4) :=
  let (i, j) := p.1
  if p.2 then (Sum.inr i, ellKreinSectorPartner j) else (Sum.inl i, j)

theorem ellKreinSectorPartner_involutive (j : Fin 4 ⊕ Fin 4) :
    ellKreinSectorPartner (ellKreinSectorPartner j) = j := by
  cases j <;> rfl

/-- The 32 indexed pairs, with two sides each, partition all 64 units of the
signed Krein operator basis: every matrix unit has exactly one block and one
side. -/
theorem ellKreinOperatorPairMember_existsUnique
    (r c : Fin 4 ⊕ Fin 4) :
    ∃! p : (Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool,
      ellKreinOperatorPairMember p = (r, c) := by
  cases r with
  | inl i =>
      refine ⟨((i, c), false), ?_, ?_⟩
      · simp [ellKreinOperatorPairMember]
      · intro p hp
        rcases p with ⟨⟨i', j'⟩, side⟩
        cases side
        · simp [ellKreinOperatorPairMember] at hp
          rcases hp with ⟨rfl, rfl⟩
          rfl
        · simp [ellKreinOperatorPairMember] at hp
  | inr i =>
      refine ⟨((i, ellKreinSectorPartner c), true), ?_, ?_⟩
      · simp [ellKreinOperatorPairMember, ellKreinSectorPartner_involutive]
      · intro p hp
        rcases p with ⟨⟨i', j'⟩, side⟩
        cases side
        · simp [ellKreinOperatorPairMember] at hp
        · simp [ellKreinOperatorPairMember, ellKreinSectorPartner] at hp
          rcases hp with ⟨rfl, hj⟩
          have hj' : j' = ellKreinSectorPartner c := by
            calc j' = ellKreinSectorPartner (ellKreinSectorPartner j') := by
                    rw [ellKreinSectorPartner_involutive]
              _ = ellKreinSectorPartner c := congrArg ellKreinSectorPartner hj
          subst j'
          rfl

/-- There are exactly 32 block labels; adjoining the two sides gives exactly
64 labels, matching the cardinality of the signed Krein operator-unit basis. -/
theorem ellKreinOperatorPairIndex_cardinality :
    Fintype.card (Fin 4 × (Fin 4 ⊕ Fin 4)) = 32 ∧
      Fintype.card ((Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool) = 64 := by
  simp

/-- The block/side indexing is equivalent to the full pair of signed Krein
indices. This packages coverage and uniqueness as an actual carrier map. -/
noncomputable def ellKreinOperatorPairMemberEquiv :
    ((Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool) ≃
      ((Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) :=
  Equiv.ofBijective ellKreinOperatorPairMember (by
    constructor
    · intro p q hpq
      have hu := ellKreinOperatorPairMember_existsUnique
        (ellKreinOperatorPairMember p).1 (ellKreinOperatorPairMember p).2
      rcases hu with ⟨p', hp', huniq⟩
      have hq : q = p' := huniq q hpq.symm
      have hp : p = p' := huniq p rfl
      exact hp.trans hq.symm
    · intro target
      obtain ⟨p, hp, _⟩ := ellKreinOperatorPairMember_existsUnique target.1 target.2
      exact ⟨p, hp⟩)

/-- Reindexing the actual signed Krein operator-unit basis by the 32 blocks
and their two sides yields a basis of the entire endomorphism algebra. -/
noncomputable def ellKreinOperatorPairBasis :
    Module.Basis ((Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool) ℝ
      (Module.End ℝ Coordinate) :=
  ellKreinOperatorBasis.reindex ellKreinOperatorPairMemberEquiv.symm

@[simp] theorem ellKreinOperatorPairBasis_apply_false
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4) :
    ellKreinOperatorPairBasis ((i, j), false) =
      ellKreinOperatorBasis (Sum.inl i, j) := by
  rw [ellKreinOperatorPairBasis, Module.Basis.reindex_apply]
  change ellKreinOperatorBasis
    (ellKreinOperatorPairMember ((i, j), false)) = _
  simp [ellKreinOperatorPairMember]

@[simp] theorem ellKreinOperatorPairBasis_apply_true
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4) :
    ellKreinOperatorPairBasis ((i, j), true) =
      ellKreinOperatorBasis (Sum.inr i, ellKreinSectorPartner j) := by
  rw [ellKreinOperatorPairBasis, Module.Basis.reindex_apply]
  change ellKreinOperatorBasis
    (ellKreinOperatorPairMember ((i, j), true)) = _
  simp [ellKreinOperatorPairMember]

/-- The blockwise linear map sending old operator units `(U,V)` to the
zero-mode and four-mode combinations `(U+V,U-V)`. -/
noncomputable def ellKreinPairEigenTransform :
    Module.End ℝ (Module.End ℝ Coordinate) :=
  ellKreinOperatorPairBasis.constr ℝ fun p =>
    if p.2 then
      ellKreinOperatorPairBasis (p.1, false) -
        ellKreinOperatorPairBasis (p.1, true)
    else
      ellKreinOperatorPairBasis (p.1, false) +
        ellKreinOperatorPairBasis (p.1, true)

/-- The inverse blockwise transform uses the half-sum and half-difference. -/
noncomputable def ellKreinPairEigenTransformInverse :
    Module.End ℝ (Module.End ℝ Coordinate) :=
  ellKreinOperatorPairBasis.constr ℝ fun p =>
    if p.2 then
      (1 / 2 : ℝ) • (ellKreinOperatorPairBasis (p.1, false) -
        ellKreinOperatorPairBasis (p.1, true))
    else
      (1 / 2 : ℝ) • (ellKreinOperatorPairBasis (p.1, false) +
        ellKreinOperatorPairBasis (p.1, true))

theorem ellKreinPairEigenTransform_apply_false (block : Fin 4 × (Fin 4 ⊕ Fin 4)) :
    ellKreinPairEigenTransform (ellKreinOperatorPairBasis (block, false)) =
      ellKreinOperatorPairBasis (block, false) + ellKreinOperatorPairBasis (block, true) := by
  change (ellKreinOperatorPairBasis.constr ℝ (fun p => _)) _ = _
  rw [ellKreinOperatorPairBasis.constr_basis]
  simp

theorem ellKreinPairEigenTransform_apply_true (block : Fin 4 × (Fin 4 ⊕ Fin 4)) :
    ellKreinPairEigenTransform (ellKreinOperatorPairBasis (block, true)) =
      ellKreinOperatorPairBasis (block, false) - ellKreinOperatorPairBasis (block, true) := by
  change (ellKreinOperatorPairBasis.constr ℝ (fun p => _)) _ = _
  rw [ellKreinOperatorPairBasis.constr_basis]
  simp

theorem ellKreinPairEigenTransformInverse_apply_false
    (block : Fin 4 × (Fin 4 ⊕ Fin 4)) :
    ellKreinPairEigenTransformInverse (ellKreinOperatorPairBasis (block, false)) =
      (1 / 2 : ℝ) • (ellKreinOperatorPairBasis (block, false) +
        ellKreinOperatorPairBasis (block, true)) := by
  change (ellKreinOperatorPairBasis.constr ℝ (fun p => _)) _ = _
  rw [ellKreinOperatorPairBasis.constr_basis]
  simp

theorem ellKreinPairEigenTransformInverse_apply_true
    (block : Fin 4 × (Fin 4 ⊕ Fin 4)) :
    ellKreinPairEigenTransformInverse (ellKreinOperatorPairBasis (block, true)) =
      (1 / 2 : ℝ) • (ellKreinOperatorPairBasis (block, false) -
        ellKreinOperatorPairBasis (block, true)) := by
  change (ellKreinOperatorPairBasis.constr ℝ (fun p => _)) _ = _
  rw [ellKreinOperatorPairBasis.constr_basis]
  simp

/-- The block transform is invertible; its inverse is the half-sum and
half-difference transform on each pair. -/
noncomputable def ellKreinPairEigenTransformEquiv :
    (Module.End ℝ Coordinate) ≃ₗ[ℝ] (Module.End ℝ Coordinate) where
  toFun := ellKreinPairEigenTransform
  invFun := ellKreinPairEigenTransformInverse
  left_inv T := by
    have hcomp : ellKreinPairEigenTransformInverse.comp
        ellKreinPairEigenTransform = LinearMap.id := by
      apply ellKreinOperatorPairBasis.ext
      intro p
      rcases p with ⟨block, side⟩
      cases side
      · change ellKreinPairEigenTransformInverse
          (ellKreinPairEigenTransform (ellKreinOperatorPairBasis (block, false))) = _
        rw [ellKreinPairEigenTransform_apply_false, map_add,
          ellKreinPairEigenTransformInverse_apply_false,
          ellKreinPairEigenTransformInverse_apply_true]
        module
      · change ellKreinPairEigenTransformInverse
          (ellKreinPairEigenTransform (ellKreinOperatorPairBasis (block, true))) = _
        rw [ellKreinPairEigenTransform_apply_true, map_sub,
          ellKreinPairEigenTransformInverse_apply_false,
          ellKreinPairEigenTransformInverse_apply_true]
        module
    exact congrArg (fun f : Module.End ℝ (Module.End ℝ Coordinate) => f T) hcomp
  right_inv T := by
    have hcomp : ellKreinPairEigenTransform.comp
        ellKreinPairEigenTransformInverse = LinearMap.id := by
      apply ellKreinOperatorPairBasis.ext
      intro p
      rcases p with ⟨block, side⟩
      cases side
      · change ellKreinPairEigenTransform
          (ellKreinPairEigenTransformInverse (ellKreinOperatorPairBasis (block, false))) = _
        rw [ellKreinPairEigenTransformInverse_apply_false, map_smul, map_add,
          ellKreinPairEigenTransform_apply_false,
          ellKreinPairEigenTransform_apply_true]
        module
      · change ellKreinPairEigenTransform
          (ellKreinPairEigenTransformInverse (ellKreinOperatorPairBasis (block, true))) = _
        rw [ellKreinPairEigenTransformInverse_apply_true, map_smul, map_sub,
          ellKreinPairEigenTransform_apply_false,
          ellKreinPairEigenTransform_apply_true]
        module
    exact congrArg (fun f : Module.End ℝ (Module.End ℝ Coordinate) => f T) hcomp
  map_add' := ellKreinPairEigenTransform.map_add
  map_smul' := ellKreinPairEigenTransform.map_smul

/-- The full signed Krein operator algebra has an explicit eigenbasis for the
regular-`J` double commutator, obtained by applying the block transform to the
reindexed matrix-unit basis. -/
noncomputable def ellRegularJDoubleCommEigenbasis :
    Module.Basis ((Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool) ℝ
      (Module.End ℝ Coordinate) :=
  ellKreinOperatorPairBasis.map ellKreinPairEigenTransformEquiv

@[simp] theorem ellRegularJDoubleCommEigenbasis_apply_false
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4) :
    ellRegularJDoubleCommEigenbasis ((i, j), false) =
      ellKreinOperatorPairBasis ((i, j), false) +
        ellKreinOperatorPairBasis ((i, j), true) := by
  change ellKreinPairEigenTransform (ellKreinOperatorPairBasis ((i, j), false)) = _
  exact ellKreinPairEigenTransform_apply_false (i, j)

@[simp] theorem ellRegularJDoubleCommEigenbasis_apply_true
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4) :
    ellRegularJDoubleCommEigenbasis ((i, j), true) =
      ellKreinOperatorPairBasis ((i, j), false) -
        ellKreinOperatorPairBasis ((i, j), true) := by
  change ellKreinPairEigenTransform (ellKreinOperatorPairBasis ((i, j), true)) = _
  exact ellKreinPairEigenTransform_apply_true (i, j)

/-- Each uniquely indexed pair splits into an eigenvector of eigenvalue zero
and an eigenvector of eigenvalue four for the regular-`J` double commutator. -/
theorem ellRegularJ_doubleComm_pair_eigenmodes (i : Fin 4)
    (j : Fin 4 ⊕ Fin 4) :
    let U := ellKreinOperatorBasis (Sum.inl i, j)
    let V := ellKreinOperatorBasis (Sum.inr i, ellKreinSectorPartner j)
    ellCoordinateDoubleComm ellRegularJ (U + V) = 0 ∧
      ellCoordinateDoubleComm ellRegularJ (U - V) = (4 : ℝ) • (U - V) := by
  dsimp
  constructor
  · simpa using ellRegularJ_doubleComm_operatorPair i j 1 1
  · have h := ellRegularJ_doubleComm_operatorPair i j 1 (-1)
    have hl : (1 : ℝ) • ellKreinOperatorBasis (Sum.inl i, j) +
        (-1 : ℝ) • ellKreinOperatorBasis (Sum.inr i, ellKreinSectorPartner j) =
        ellKreinOperatorBasis (Sum.inl i, j) -
          ellKreinOperatorBasis (Sum.inr i, ellKreinSectorPartner j) := by module
    dsimp at h
    rw [hl] at h
    norm_num at h
    exact h

/-- Every vector in the false-side half of the full operator eigenbasis is a
zero mode of the actual regular-`J` double commutator. -/
theorem ellRegularJ_doubleComm_eigenbasis_zero
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4) :
    ellCoordinateDoubleComm ellRegularJ
      (ellRegularJDoubleCommEigenbasis ((i, j), false)) = 0 := by
  rw [ellRegularJDoubleCommEigenbasis_apply_false,
    ellKreinOperatorPairBasis_apply_false, ellKreinOperatorPairBasis_apply_true]
  exact (ellRegularJ_doubleComm_pair_eigenmodes i j).1

/-- Every vector in the true-side half of the full operator eigenbasis has
eigenvalue four for the actual regular-`J` double commutator. -/
theorem ellRegularJ_doubleComm_eigenbasis_four
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4) :
    ellCoordinateDoubleComm ellRegularJ
      (ellRegularJDoubleCommEigenbasis ((i, j), true)) =
        (4 : ℝ) • ellRegularJDoubleCommEigenbasis ((i, j), true) := by
  rw [ellRegularJDoubleCommEigenbasis_apply_true,
    ellKreinOperatorPairBasis_apply_false, ellKreinOperatorPairBasis_apply_true]
  simpa using (ellRegularJ_doubleComm_pair_eigenmodes i j).2

/-- The actual double-commutator, regarded as a linear endomorphism of the
64-dimensional operator space. -/
noncomputable def ellRegularJDoubleCommMap :
    Module.End ℝ (Module.End ℝ Coordinate) :=
  (LinearMap.mulLeft ℝ ellRegularJ -
    LinearMap.mulRight ℝ ellRegularJ).comp
      (LinearMap.mulLeft ℝ ellRegularJ -
        LinearMap.mulRight ℝ ellRegularJ)

@[simp] theorem ellRegularJDoubleCommMap_apply (T : Module.End ℝ Coordinate) :
    ellRegularJDoubleCommMap T = ellCoordinateDoubleComm ellRegularJ T := rfl

private abbrev EllRegularJPairIndex := Fin 4 × (Fin 4 ⊕ Fin 4)

private def ellRegularJZeroModeFamily (p : EllRegularJPairIndex) :
    Module.End ℝ Coordinate :=
  ellRegularJDoubleCommEigenbasis (p, false)

private def ellRegularJFourModeFamily (p : EllRegularJPairIndex) :
    Module.End ℝ Coordinate :=
  ellRegularJDoubleCommEigenbasis (p, true)

private def ellRegularJZeroModeSpan : Submodule ℝ (Module.End ℝ Coordinate) :=
  Submodule.span ℝ (Set.range ellRegularJZeroModeFamily)

private def ellRegularJFourModeSpan : Submodule ℝ (Module.End ℝ Coordinate) :=
  Submodule.span ℝ (Set.range ellRegularJFourModeFamily)

/-- The two explicit mode families each span a 32-dimensional subspace of
the full operator algebra. -/
theorem ellRegularJ_mode_span_dimensions :
    Module.finrank ℝ ellRegularJZeroModeSpan = 32 ∧
      Module.finrank ℝ ellRegularJFourModeSpan = 32 := by
  have hzero : LinearIndependent ℝ ellRegularJZeroModeFamily :=
    ellRegularJDoubleCommEigenbasis.linearIndependent.comp
      (fun p => (p, false)) (by intro p q h; exact congrArg Prod.fst h)
  have hfour : LinearIndependent ℝ ellRegularJFourModeFamily :=
    ellRegularJDoubleCommEigenbasis.linearIndependent.comp
      (fun p => (p, true)) (by intro p q h; exact congrArg Prod.fst h)
  have hcard : Fintype.card EllRegularJPairIndex = 32 := by
    simp
  constructor
  · rw [ellRegularJZeroModeSpan, finrank_span_eq_card hzero, hcard]
  · rw [ellRegularJFourModeSpan, finrank_span_eq_card hfour, hcard]

/-- The 32 zero modes and 32 four modes account for the full kernel and range
of the regular-`J` double-commutator on the 64-dimensional operator space. -/
theorem ellRegularJ_doubleComm_rank_kernel_dimensions :
    Module.finrank ℝ (LinearMap.range ellRegularJDoubleCommMap) = 32 ∧
      Module.finrank ℝ (LinearMap.ker ellRegularJDoubleCommMap) = 32 := by
  let zeroFamily := ellRegularJZeroModeFamily
  let fourFamily := ellRegularJFourModeFamily
  have hker : Submodule.span ℝ (Set.range zeroFamily) ≤
      LinearMap.ker ellRegularJDoubleCommMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨p, rfl⟩
    apply LinearMap.mem_ker.mpr
    change ellRegularJDoubleCommMap (ellRegularJZeroModeFamily p) = 0
    rw [ellRegularJDoubleCommMap_apply]
    exact ellRegularJ_doubleComm_eigenbasis_zero p.1 p.2
  have hrange : Submodule.span ℝ (Set.range fourFamily) ≤
      LinearMap.range ellRegularJDoubleCommMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨p, rfl⟩
    refine ⟨(1 / 4 : ℝ) • fourFamily p, ?_⟩
    rw [ellRegularJDoubleCommMap.map_smul, ellRegularJDoubleCommMap_apply]
    rw [show fourFamily p = ellRegularJDoubleCommEigenbasis ((p.1, p.2), true) by rfl]
    rw [ellRegularJ_doubleComm_eigenbasis_four]
    module
  have hzeroLe : 32 ≤ Module.finrank ℝ (LinearMap.ker ellRegularJDoubleCommMap) := by
    rw [← (ellRegularJ_mode_span_dimensions).1]
    exact Submodule.finrank_mono hker
  have hfourLe : 32 ≤ Module.finrank ℝ (LinearMap.range ellRegularJDoubleCommMap) := by
    rw [← (ellRegularJ_mode_span_dimensions).2]
    exact Submodule.finrank_mono hrange
  letI : FiniteDimensional ℝ (Module.End ℝ Coordinate) :=
    Module.Basis.finiteDimensional_of_finite ellRegularJDoubleCommEigenbasis
  have htotal : Module.finrank ℝ (Module.End ℝ Coordinate) = 64 := by
    rw [Module.finrank_eq_card_basis ellRegularJDoubleCommEigenbasis]
    simp
  have hrank := LinearMap.finrank_range_add_finrank_ker ellRegularJDoubleCommMap
  rw [htotal] at hrank
  constructor <;> omega

/-- The zero eigenspace of the induced double commutator is exactly the
centralizer of the actual regular-`J` operator on the Ell coordinate space.
This identifies the 32-dimensional kernel structurally, not just by its
dimension. -/
theorem ellRegularJ_doubleComm_eq_zero_iff_commutes
    (T : Module.End ℝ Coordinate) :
    ellRegularJDoubleCommMap T = 0 ↔
      ellRegularJ * T = T * ellRegularJ := by
  rw [ellRegularJDoubleCommMap_apply,
    ellRegularJ_doubleComm_conjugation_formula]
  constructor
  · intro h
    have hdiff : T - ellRegularJ * T * ellRegularJ = 0 := by
      have h' := (smul_eq_zero.mp h).resolve_left (by norm_num)
      exact h'
    have hconj : T = ellRegularJ * T * ellRegularJ := sub_eq_zero.mp hdiff
    calc ellRegularJ * T = ellRegularJ * (ellRegularJ * T * ellRegularJ) := by rw [← hconj]
      _ = T * ellRegularJ := by
        calc ellRegularJ * (ellRegularJ * T * ellRegularJ)
            = (ellRegularJ * ellRegularJ) * T * ellRegularJ := by noncomm_ring
          _ = T * ellRegularJ := by rw [ellRegularJ_sq, one_mul]
  · intro h
    have hconj : ellRegularJ * T * ellRegularJ = T := by
      calc ellRegularJ * T * ellRegularJ = T * ellRegularJ * ellRegularJ := by rw [h]
        _ = T := by
          calc T * ellRegularJ * ellRegularJ = T * (ellRegularJ * ellRegularJ) := by noncomm_ring
            _ = T := by rw [ellRegularJ_sq, mul_one]
    rw [hconj, sub_self, smul_zero]

/-- The range of the regular-`J` double commutator is exactly the
anti-invariant subspace for conjugation by `J`.  The factor-four eigenspace
description is thereby intrinsic to the split-octonion operator carrier. -/
theorem ellRegularJ_doubleComm_mem_range_iff_anti_conjugate
    (T : Module.End ℝ Coordinate) :
    T ∈ LinearMap.range ellRegularJDoubleCommMap ↔
      ellRegularJ * T * ellRegularJ = -T := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [ellRegularJDoubleCommMap_apply,
      ellRegularJ_doubleComm_conjugation_formula]
    have hdouble : ellRegularJ * (ellRegularJ * S * ellRegularJ) * ellRegularJ = S := by
      calc ellRegularJ * (ellRegularJ * S * ellRegularJ) * ellRegularJ
          = (ellRegularJ * ellRegularJ) * S * (ellRegularJ * ellRegularJ) := by
              noncomm_ring
        _ = S := by rw [ellRegularJ_sq]; noncomm_ring
    have hconj : ellRegularJ * (S - ellRegularJ * S * ellRegularJ) * ellRegularJ =
        ellRegularJ * S * ellRegularJ - S := by
      calc ellRegularJ * (S - ellRegularJ * S * ellRegularJ) * ellRegularJ
          = (ellRegularJ * S - ellRegularJ * (ellRegularJ * S * ellRegularJ)) * ellRegularJ := by
                rw [mul_sub]
        _ = ellRegularJ * S * ellRegularJ -
              ellRegularJ * (ellRegularJ * S * ellRegularJ) * ellRegularJ := by
                rw [sub_mul]
        _ = ellRegularJ * S * ellRegularJ - S := by rw [hdouble]
    calc ellRegularJ * ((2 : ℝ) • (S - ellRegularJ * S * ellRegularJ)) * ellRegularJ
        = ((2 : ℝ) • (ellRegularJ * (S - ellRegularJ * S * ellRegularJ))) * ellRegularJ := by
              rw [mul_smul_comm]
      _ = (2 : ℝ) •
            (ellRegularJ * (S - ellRegularJ * S * ellRegularJ) * ellRegularJ) := by
              rw [smul_mul_assoc]
      _ = (2 : ℝ) • (ellRegularJ * S * ellRegularJ - S) := by rw [hconj]
      _ = -((2 : ℝ) • (S - ellRegularJ * S * ellRegularJ)) := by
        rw [show ellRegularJ * S * ellRegularJ - S =
          -(S - ellRegularJ * S * ellRegularJ) by abel, smul_neg]
  · intro hanti
    refine ⟨(1 / 4 : ℝ) • T, ?_⟩
    rw [ellRegularJDoubleCommMap.map_smul,
      ellRegularJDoubleCommMap_apply,
      ellRegularJ_doubleComm_conjugation_formula]
    rw [hanti]
    module

/-- The signed Krein eigenbasis transported back through the actual Ell
coordinate algebra equivalence.  Its carrier is the native endomorphism
algebra of the split-octonion Zorn space, not the coordinate endomorphism
algebra. -/
noncomputable def nativeRegularJDoubleCommEigenbasis :
    Module.Basis ((Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool) ℝ
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
  ellRegularJDoubleCommEigenbasis.map
    ((coordinateEquiv.conjAlgEquiv ℝ).symm.toLinearEquiv)

/-- Mapping a native eigenbasis vector into Ell coordinates recovers the
corresponding explicit signed Krein operator eigenvector. -/
theorem coordinateConjugate_nativeRegularJDoubleCommEigenbasis
    (p : (Fin 4 × (Fin 4 ⊕ Fin 4)) × Bool) :
    ellCoordinateConjugate (nativeRegularJDoubleCommEigenbasis p) =
      ellRegularJDoubleCommEigenbasis p := by
  change (coordinateEquiv.conjAlgEquiv ℝ)
      ((coordinateEquiv.conjAlgEquiv ℝ).symm
        (ellRegularJDoubleCommEigenbasis p)) = _
  exact (coordinateEquiv.conjAlgEquiv ℝ).apply_symm_apply _

/-- The native regular-`J` double commutator has the same two exact
eigenvalues on the transported signed operator basis as in Ell coordinates.
This is the operator-basis soldering theorem between the two carriers. -/
theorem nativeRegularJ_doubleComm_eigenbasis_zero_four
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4) :
    doubleComm (regularJ uPlus uMinus)
        (nativeRegularJDoubleCommEigenbasis ((i, j), false)) = 0 ∧
      doubleComm (regularJ uPlus uMinus)
        (nativeRegularJDoubleCommEigenbasis ((i, j), true)) =
          (4 : ℝ) • nativeRegularJDoubleCommEigenbasis ((i, j), true) := by
  constructor
  · apply (coordinateEquiv.conjAlgEquiv ℝ).injective
    have hcoord := ellCoordinateConjugate_doubleComm
      (regularJ uPlus uMinus)
      (nativeRegularJDoubleCommEigenbasis ((i, j), false))
    rw [show ellCoordinateConjugate (regularJ uPlus uMinus) = ellRegularJ from rfl,
      coordinateConjugate_nativeRegularJDoubleCommEigenbasis] at hcoord
    simpa [ellCoordinateConjugate] using
      hcoord.trans (ellRegularJ_doubleComm_eigenbasis_zero i j)
  · apply (coordinateEquiv.conjAlgEquiv ℝ).injective
    have hcoord := ellCoordinateConjugate_doubleComm
      (regularJ uPlus uMinus)
      (nativeRegularJDoubleCommEigenbasis ((i, j), true))
    rw [show ellCoordinateConjugate (regularJ uPlus uMinus) = ellRegularJ from rfl,
      coordinateConjugate_nativeRegularJDoubleCommEigenbasis] at hcoord
    have hnative : (coordinateEquiv.conjAlgEquiv ℝ)
        (nativeRegularJDoubleCommEigenbasis ((i, j), true)) =
          ellRegularJDoubleCommEigenbasis ((i, j), true) := by
      simpa [ellCoordinateConjugate] using
        coordinateConjugate_nativeRegularJDoubleCommEigenbasis ((i, j), true)
    rw [map_smul, hnative]
    exact hcoord.trans (ellRegularJ_doubleComm_eigenbasis_four i j)

/-- The native regular-`J` double commutator as an endomorphism of the
operator space `End(CanonicalZorn)`. -/
noncomputable def nativeRegularJDoubleCommMap :
    Module.End ℝ
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
  (LinearMap.mulLeft ℝ (regularJ uPlus uMinus) -
    LinearMap.mulRight ℝ (regularJ uPlus uMinus)).comp
      (LinearMap.mulLeft ℝ (regularJ uPlus uMinus) -
        LinearMap.mulRight ℝ (regularJ uPlus uMinus))

@[simp] theorem nativeRegularJDoubleCommMap_apply
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    nativeRegularJDoubleCommMap T =
      doubleComm (regularJ uPlus uMinus) T := rfl

/-- On the native operator carrier `End(CanonicalZorn)`, the other three
regular Tetraktys generators for this distinguished Ell Peirce pair have
trivial double-commutator channels.  Their identities `Φ = 1`, `V = 0`, and
`Σ = 0` are native endomorphism identities. -/
theorem nativeRegularTetraktys_trivial_doubleComm_channels
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    doubleComm (regularPhi uPlus uMinus) T = 0 ∧
      doubleComm (regularV uPlus uMinus) T = 0 ∧
      doubleComm (regularSig uPlus uMinus) T = 0 := by
  have hΦ : regularPhi uPlus uMinus = 1 := regularPhi_uPlus_uMinus_eq_one
  have hVS := regularV_regularSig_uPlus_uMinus_eq_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [hΦ]
    simp [doubleComm, operatorComm]
  · rw [hVS.1]
    simp [doubleComm, operatorComm]
  · rw [hVS.2]
    simp [doubleComm, operatorComm]

/-- Complete four-channel Tetraktys readout on the native split-octonion
operator space.  The `Φ`, `V`, and `Σ` channels vanish, while `J` acts on the
transported signed operator basis with eigenvalues zero and four. -/
theorem nativeRegularTetraktys_operator_basis_readout
    (i : Fin 4) (j : Fin 4 ⊕ Fin 4)
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    (doubleComm (regularPhi uPlus uMinus) T = 0 ∧
      doubleComm (regularV uPlus uMinus) T = 0 ∧
      doubleComm (regularSig uPlus uMinus) T = 0) ∧
    (doubleComm (regularJ uPlus uMinus)
        (nativeRegularJDoubleCommEigenbasis ((i, j), false)) = 0 ∧
      doubleComm (regularJ uPlus uMinus)
        (nativeRegularJDoubleCommEigenbasis ((i, j), true)) =
          (4 : ℝ) • nativeRegularJDoubleCommEigenbasis ((i, j), true)) := by
  exact ⟨nativeRegularTetraktys_trivial_doubleComm_channels T,
    nativeRegularJ_doubleComm_eigenbasis_zero_four i j⟩

/-- The native and Ell-coordinate double-commutator maps are intertwined by
the algebra equivalence induced by the actual Ell circular basis. -/
theorem ellCoordinateConjugate_nativeRegularJDoubleCommMap
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    ellCoordinateConjugate (nativeRegularJDoubleCommMap T) =
      ellRegularJDoubleCommMap (ellCoordinateConjugate T) := by
  rw [nativeRegularJDoubleCommMap_apply,
    ellRegularJDoubleCommMap_apply,
    ellCoordinateConjugate_doubleComm,
    show ellCoordinateConjugate (regularJ uPlus uMinus) = ellRegularJ from rfl]

/-- On the native split-octonion endomorphism algebra, the kernel of the
regular-`J` double commutator is exactly the centralizer of native regular
`J`. -/
theorem nativeRegularJ_doubleComm_eq_zero_iff_commutes
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    nativeRegularJDoubleCommMap T = 0 ↔
      regularJ uPlus uMinus * T = T * regularJ uPlus uMinus := by
  let e := coordinateEquiv.conjAlgEquiv ℝ
  constructor
  · intro h
    have hcoord : ellRegularJDoubleCommMap (ellCoordinateConjugate T) = 0 := by
      calc ellRegularJDoubleCommMap (ellCoordinateConjugate T)
          = ellCoordinateConjugate (nativeRegularJDoubleCommMap T) :=
              (ellCoordinateConjugate_nativeRegularJDoubleCommMap T).symm
        _ = 0 := by rw [h]; exact map_zero e
    have hcomm :=
      (ellRegularJ_doubleComm_eq_zero_iff_commutes (ellCoordinateConjugate T)).mp hcoord
    apply e.injective
    simpa [e, ellRegularJ, ellCoordinateConjugate, map_mul] using hcomm
  · intro h
    have hcomm : ellRegularJ * ellCoordinateConjugate T =
        ellCoordinateConjugate T * ellRegularJ := by
      simpa [e, ellRegularJ, ellCoordinateConjugate, map_mul] using congrArg e h
    have hcoord :=
      (ellRegularJ_doubleComm_eq_zero_iff_commutes (ellCoordinateConjugate T)).mpr hcomm
    apply e.injective
    calc ellCoordinateConjugate (nativeRegularJDoubleCommMap T)
        = ellRegularJDoubleCommMap (ellCoordinateConjugate T) :=
            ellCoordinateConjugate_nativeRegularJDoubleCommMap T
      _ = 0 := hcoord
      _ = e 0 := by simp

/-- The native image of the regular-`J` double commutator is exactly the
anti-invariant subspace for conjugation by native regular `J`. -/
theorem nativeRegularJ_doubleComm_mem_range_iff_anti_conjugate
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    T ∈ LinearMap.range nativeRegularJDoubleCommMap ↔
      regularJ uPlus uMinus * T * regularJ uPlus uMinus = -T := by
  let e := coordinateEquiv.conjAlgEquiv ℝ
  constructor
  · rintro ⟨S, hS⟩
    have hcoord : ellCoordinateConjugate T ∈
        LinearMap.range ellRegularJDoubleCommMap := by
      refine ⟨ellCoordinateConjugate S, ?_⟩
      calc ellRegularJDoubleCommMap (ellCoordinateConjugate S)
          = ellCoordinateConjugate (nativeRegularJDoubleCommMap S) :=
              (ellCoordinateConjugate_nativeRegularJDoubleCommMap S).symm
        _ = ellCoordinateConjugate T := congrArg ellCoordinateConjugate hS
    have hanti :=
      (ellRegularJ_doubleComm_mem_range_iff_anti_conjugate
        (ellCoordinateConjugate T)).mp hcoord
    apply e.injective
    calc e (regularJ uPlus uMinus * T * regularJ uPlus uMinus)
        = ellRegularJ * ellCoordinateConjugate T * ellRegularJ := by
            simp [e, ellRegularJ, ellCoordinateConjugate, map_mul]
      _ = -ellCoordinateConjugate T := hanti
      _ = e (-T) := by simp [e, ellCoordinateConjugate]
  · intro hanti
    have hcoord : ellRegularJ * ellCoordinateConjugate T * ellRegularJ =
        -ellCoordinateConjugate T := by
      calc ellRegularJ * ellCoordinateConjugate T * ellRegularJ
          = e (regularJ uPlus uMinus * T * regularJ uPlus uMinus) := by
              simp [e, ellRegularJ, ellCoordinateConjugate, map_mul]
        _ = e (-T) := congrArg e hanti
        _ = -ellCoordinateConjugate T := by simp [e, ellCoordinateConjugate]
    have hrange :=
      (ellRegularJ_doubleComm_mem_range_iff_anti_conjugate
        (ellCoordinateConjugate T)).mpr hcoord
    rcases hrange with ⟨U, hU⟩
    refine ⟨e.symm U, ?_⟩
    apply e.injective
    calc e (nativeRegularJDoubleCommMap (e.symm U))
        = ellRegularJDoubleCommMap (e (e.symm U)) :=
            ellCoordinateConjugate_nativeRegularJDoubleCommMap (e.symm U)
      _ = ellRegularJDoubleCommMap U := by rw [e.apply_symm_apply]
      _ = e T := hU

private abbrev NativeRegularJPairIndex := Fin 4 × (Fin 4 ⊕ Fin 4)

private def nativeRegularJZeroModeFamily (p : NativeRegularJPairIndex) :
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
  nativeRegularJDoubleCommEigenbasis (p, false)

private def nativeRegularJFourModeFamily (p : NativeRegularJPairIndex) :
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
  nativeRegularJDoubleCommEigenbasis (p, true)

def nativeRegularJZeroModeSpan : Submodule ℝ
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
  Submodule.span ℝ (Set.range nativeRegularJZeroModeFamily)

def nativeRegularJFourModeSpan : Submodule ℝ
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
  Submodule.span ℝ (Set.range nativeRegularJFourModeFamily)

/-- The two native signed-operator mode families each span a
32-dimensional subspace of `End(CanonicalZorn)`. -/
theorem nativeRegularJ_mode_span_dimensions :
    Module.finrank ℝ nativeRegularJZeroModeSpan = 32 ∧
      Module.finrank ℝ nativeRegularJFourModeSpan = 32 := by
  have hzero : LinearIndependent ℝ nativeRegularJZeroModeFamily :=
    nativeRegularJDoubleCommEigenbasis.linearIndependent.comp
      (fun p => (p, false)) (by intro p q h; exact congrArg Prod.fst h)
  have hfour : LinearIndependent ℝ nativeRegularJFourModeFamily :=
    nativeRegularJDoubleCommEigenbasis.linearIndependent.comp
      (fun p => (p, true)) (by intro p q h; exact congrArg Prod.fst h)
  have hcard : Fintype.card NativeRegularJPairIndex = 32 := by simp
  constructor
  · rw [nativeRegularJZeroModeSpan, finrank_span_eq_card hzero, hcard]
  · rw [nativeRegularJFourModeSpan, finrank_span_eq_card hfour, hcard]

/-- On the native split-octonion operator carrier, the regular-`J`
double-commutator has rank 32 and kernel dimension 32.  The proof uses the
native zero/four eigenbasis and finite-dimensional rank-nullity. -/
theorem nativeRegularJ_doubleComm_rank_kernel_dimensions :
    Module.finrank ℝ (LinearMap.range nativeRegularJDoubleCommMap) = 32 ∧
      Module.finrank ℝ (LinearMap.ker nativeRegularJDoubleCommMap) = 32 := by
  let zeroFamily := nativeRegularJZeroModeFamily
  let fourFamily := nativeRegularJFourModeFamily
  have hker : Submodule.span ℝ (Set.range zeroFamily) ≤
      LinearMap.ker nativeRegularJDoubleCommMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨p, rfl⟩
    apply LinearMap.mem_ker.mpr
    change nativeRegularJDoubleCommMap (nativeRegularJZeroModeFamily p) = 0
    rw [nativeRegularJDoubleCommMap_apply]
    exact (nativeRegularJ_doubleComm_eigenbasis_zero_four p.1 p.2).1
  have hrange : Submodule.span ℝ (Set.range fourFamily) ≤
      LinearMap.range nativeRegularJDoubleCommMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨p, rfl⟩
    refine ⟨(1 / 4 : ℝ) • fourFamily p, ?_⟩
    rw [nativeRegularJDoubleCommMap.map_smul,
      nativeRegularJDoubleCommMap_apply]
    rw [show fourFamily p = nativeRegularJDoubleCommEigenbasis ((p.1, p.2), true) by rfl]
    rw [(nativeRegularJ_doubleComm_eigenbasis_zero_four p.1 p.2).2]
    module
  letI : FiniteDimensional ℝ
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
    Module.Basis.finiteDimensional_of_finite nativeRegularJDoubleCommEigenbasis
  have hzeroLe : 32 ≤ Module.finrank ℝ (LinearMap.ker nativeRegularJDoubleCommMap) := by
    rw [← (nativeRegularJ_mode_span_dimensions).1]
    exact Submodule.finrank_mono hker
  have hfourLe : 32 ≤ Module.finrank ℝ (LinearMap.range nativeRegularJDoubleCommMap) := by
    rw [← (nativeRegularJ_mode_span_dimensions).2]
    exact Submodule.finrank_mono hrange
  have htotal : Module.finrank ℝ
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ = 64 := by
    rw [Module.finrank_eq_card_basis nativeRegularJDoubleCommEigenbasis]
    simp
  have hrank := LinearMap.finrank_range_add_finrank_ker nativeRegularJDoubleCommMap
  rw [htotal] at hrank
  constructor <;> omega

/-- The native signed zero/four eigenfamilies span the exact kernel and range
of the regular-`J` double-commutator.  The earlier dimension calculation gives
the two ambient dimensions; the eigenvalue equations give the inclusions. -/
theorem nativeRegularJ_modes_are_exact_kernel_and_range :
    nativeRegularJZeroModeSpan = LinearMap.ker nativeRegularJDoubleCommMap ∧
      nativeRegularJFourModeSpan = LinearMap.range nativeRegularJDoubleCommMap := by
  letI : FiniteDimensional ℝ
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
    Module.Basis.finiteDimensional_of_finite nativeRegularJDoubleCommEigenbasis
  have hker : nativeRegularJZeroModeSpan ≤
      LinearMap.ker nativeRegularJDoubleCommMap := by
    apply Submodule.span_le.mpr
    rintro T ⟨p, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [nativeRegularJDoubleCommMap_apply]
    exact (nativeRegularJ_doubleComm_eigenbasis_zero_four p.1 p.2).1
  have hrange : nativeRegularJFourModeSpan ≤
      LinearMap.range nativeRegularJDoubleCommMap := by
    apply Submodule.span_le.mpr
    rintro T ⟨p, rfl⟩
    refine ⟨(1 / 4 : ℝ) • nativeRegularJFourModeFamily p, ?_⟩
    rw [nativeRegularJDoubleCommMap.map_smul,
      nativeRegularJDoubleCommMap_apply]
    rw [show nativeRegularJFourModeFamily p =
      nativeRegularJDoubleCommEigenbasis ((p.1, p.2), true) by rfl]
    rw [(nativeRegularJ_doubleComm_eigenbasis_zero_four p.1 p.2).2]
    module
  constructor
  · apply Submodule.eq_of_le_of_finrank_eq hker
    rw [nativeRegularJ_mode_span_dimensions.1,
      nativeRegularJ_doubleComm_rank_kernel_dimensions.2]
  · apply Submodule.eq_of_le_of_finrank_eq hrange
    rw [nativeRegularJ_mode_span_dimensions.2,
      nativeRegularJ_doubleComm_rank_kernel_dimensions.1]

/-- Fundamental-symmetry eigenvalue attached to a signed Krein basis index. -/
def ellFundamentalEigenvalue : Fin 4 ⊕ Fin 4 → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- Matrix of the fundamental symmetry in the completed signed Krein basis. -/
noncomputable def ellFundamentalKreinMatrix :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellFundamental

theorem ellFundamentalKreinMatrix_apply (i j : Fin 4 ⊕ Fin 4) :
    ellFundamentalKreinMatrix i j =
      if i = j then ellFundamentalEigenvalue j else 0 := by
  cases j with
  | inl j =>
      cases i with
      | inl i =>
          rw [ellFundamentalKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellFundamental (ellKreinEigenbasis (Sum.inl j)))) (Sum.inl i) = _
          rw [ellKreinEigenbasis_positive_apply, ellFundamental_positive_eigenvector,
            ← ellKreinEigenbasis_positive_apply, ellKreinEigenbasis.repr_self_apply]
          simp [ellFundamentalEigenvalue, eq_comm]
      | inr i =>
          rw [ellFundamentalKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellFundamental (ellKreinEigenbasis (Sum.inl j)))) (Sum.inr i) = _
          rw [ellKreinEigenbasis_positive_apply, ellFundamental_positive_eigenvector,
            ← ellKreinEigenbasis_positive_apply, ellKreinEigenbasis.repr_self_apply]
          simp
  | inr j =>
      cases i with
      | inl i =>
          rw [ellFundamentalKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellFundamental (ellKreinEigenbasis (Sum.inr j)))) (Sum.inl i) = _
          rw [ellKreinEigenbasis_negative_apply, ellFundamental_negative_eigenvector,
            map_neg, ← ellKreinEigenbasis_negative_apply, Finsupp.neg_apply,
            ellKreinEigenbasis.repr_self_apply]
          simp
      | inr i =>
          rw [ellFundamentalKreinMatrix, LinearMap.toMatrix_apply]
          change (ellKreinEigenbasis.repr
            (ellFundamental (ellKreinEigenbasis (Sum.inr j)))) (Sum.inr i) = _
          rw [ellKreinEigenbasis_negative_apply, ellFundamental_negative_eigenvector,
            map_neg, ← ellKreinEigenbasis_negative_apply, Finsupp.neg_apply,
            ellKreinEigenbasis.repr_self_apply]
          by_cases hji : j = i <;> simp [hji, ellFundamentalEigenvalue, eq_comm]

theorem ellRegularJKreinMatrix_sq :
    ellRegularJKreinMatrix * ellRegularJKreinMatrix = 1 := by
  change (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellRegularJ) *
      (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellRegularJ) = 1
  rw [← LinearMap.toMatrix_mul, ellRegularJ_sq]
  simp

theorem ellFundamentalKreinMatrix_sq :
    ellFundamentalKreinMatrix * ellFundamentalKreinMatrix = 1 := by
  have hF : ellFundamental * ellFundamental = 1 := by
    apply LinearMap.ext
    intro x
    change ellFundamental (ellFundamental x) = x
    exact ellFundamental_sq x
  change (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellFundamental) *
      (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellFundamental) = 1
  rw [← LinearMap.toMatrix_mul, hF]
  simp

/-- The matrix generators in the signed Krein basis represent the same
noncommuting split Clifford relation as the transported operators. -/
theorem ellFundamentalKreinMatrix_anticommutes_ellRegularJKreinMatrix :
    ellFundamentalKreinMatrix * ellRegularJKreinMatrix =
      -(ellRegularJKreinMatrix * ellFundamentalKreinMatrix) := by
  change (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellFundamental) *
      (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellRegularJ) =
    -((LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellRegularJ) *
      (LinearMap.toMatrix ellKreinEigenbasis ellKreinEigenbasis ellFundamental))
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul,
    ellFundamental_regularJ_anticommute]
  simp

/-- In Ell coordinates, the metric-conjugated product is exactly the positive
sum-of-squares product of the native Zorn Krein owner. -/
theorem ellHilbertPair_eq_native_formula (x y : Coordinate) :
    ellHilbertPair x y =
      (zornA (ellToKrein x) * zornA (ellToKrein y) +
        zornB (ellToKrein x) * zornB (ellToKrein y) +
        dot3 (zornX (ellToKrein x)) (zornX (ellToKrein y)) +
        dot3 (zornY (ellToKrein x)) (zornY (ellToKrein y))) / 2 := by
  rw [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  exact hilbertized_pair (ellToKrein x) (ellToKrein y)

theorem ellHilbertPair_nonneg (x : Coordinate) : 0 ≤ ellHilbertPair x x := by
  rw [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  exact hilbertized_nonneg (ellToKrein x)

/-- The Hilbert product transported to Ell coordinates is symmetric. -/
theorem ellHilbertPair_symm (x y : Coordinate) :
    ellHilbertPair x y = ellHilbertPair y x := by
  rw [ellHilbertPair_eq_native_formula, ellHilbertPair_eq_native_formula]
  simp only [InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3_comm]
  ring

/-- Applying the fundamental symmetry a second time recovers the raw Krein
pairing from the metric-conjugated Hilbert product. -/
theorem ellKreinPair_eq_hilbertized (x y : Coordinate) :
    ellKreinPair x y = ellHilbertPair x (ellFundamental y) := by
  simp only [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  rw [fundamental_sq]

/-- The metric-conjugated Ell product is positive definite: its null space
is trivial on the actual eight-dimensional operator carrier. -/
theorem ellHilbertPair_zero_iff (x : Coordinate) :
    ellHilbertPair x x = 0 ↔ x = 0 := by
  rw [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  constructor
  · intro h
    apply ellToKrein.injective
    simpa using ((hilbertized_zero_iff (ellToKrein x)).mp h)
  · intro hx
    subst x
    simpa using (hilbertized_zero_iff (0 : KreinCarrier)).mpr rfl

/-- Strict positivity of the Ell Hilbert product away from zero. -/
theorem ellHilbertPair_pos {x : Coordinate} (hx : x ≠ 0) :
    0 < ellHilbertPair x x := by
  rw [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  apply hilbertized_pos
  intro hzero
  exact hx (ellToKrein.injective (by simpa using hzero))

/-- The actual Ell-basis fundamental symmetry is self-adjoint for the raw
Krein pairing. -/
theorem ellFundamental_krein_self_adjoint (x y : Coordinate) :
    ellKreinPair (ellFundamental x) y = ellKreinPair x (ellFundamental y) := by
  simp only [ellKreinPair, ellToKrein_fundamental]
  calc
    polarPair (fundamental (ellToKrein x)) (ellToKrein y) =
        polarPair (fundamental (fundamental (ellToKrein x)))
          (fundamental (ellToKrein y)) := by
            rw [fundamental_preserves_polar]
    _ = polarPair (ellToKrein x) (fundamental (ellToKrein y)) := by
      rw [fundamental_sq]

/-- The metric symmetry is an isometry of the induced Hilbert product. -/
theorem ellFundamental_hilbert_isometry (x y : Coordinate) :
    ellHilbertPair (ellFundamental x) (ellFundamental y) =
      ellHilbertPair x y := by
  simp only [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  exact fundamental_preserves_polar (ellToKrein x) (fundamental (ellToKrein y))

/-- The metric symmetry is also self-adjoint for the Hilbert product induced
by that same symmetry. -/
theorem ellFundamental_hilbert_self_adjoint (x y : Coordinate) :
    ellHilbertPair (ellFundamental x) y =
      ellHilbertPair x (ellFundamental y) := by
  simp only [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  rw [fundamental_sq]
  exact fundamental_preserves_polar _ _

/-- The canonical positive and negative Krein components determined by the
metric symmetry. -/
def ellKreinPositivePart (x : Coordinate) : Coordinate :=
  (1 / 2 : ℝ) • (x + ellFundamental x)

def ellKreinNegativePart (x : Coordinate) : Coordinate :=
  (1 / 2 : ℝ) • (x - ellFundamental x)

theorem ellKreinPositivePart_eigen (x : Coordinate) :
    ellFundamental (ellKreinPositivePart x) = ellKreinPositivePart x := by
  simp only [ellKreinPositivePart, ellFundamental.map_smul, ellFundamental.map_add,
    ellFundamental_sq]
  module

theorem ellKreinNegativePart_eigen (x : Coordinate) :
    ellFundamental (ellKreinNegativePart x) = -ellKreinNegativePart x := by
  simp only [ellKreinNegativePart, ellFundamental.map_smul, ellFundamental.map_sub,
    ellFundamental_sq]
  module

theorem ellKrein_eigenspace_decomposition (x : Coordinate) :
    x = ellKreinPositivePart x + ellKreinNegativePart x := by
  simp only [ellKreinPositivePart, ellKreinNegativePart]
  module

theorem ellKreinPositivePart_idempotent (x : Coordinate) :
    ellKreinPositivePart (ellKreinPositivePart x) = ellKreinPositivePart x := by
  change (1 / 2 : ℝ) • (ellKreinPositivePart x +
    ellFundamental (ellKreinPositivePart x)) = ellKreinPositivePart x
  rw [ellKreinPositivePart_eigen]
  module

theorem ellKreinNegativePart_idempotent (x : Coordinate) :
    ellKreinNegativePart (ellKreinNegativePart x) = ellKreinNegativePart x := by
  change (1 / 2 : ℝ) • (ellKreinNegativePart x -
    ellFundamental (ellKreinNegativePart x)) = ellKreinNegativePart x
  rw [ellKreinNegativePart_eigen]
  module

theorem ellKreinPositivePart_negativePart (x : Coordinate) :
    ellKreinPositivePart (ellKreinNegativePart x) = 0 := by
  change (1 / 2 : ℝ) • (ellKreinNegativePart x +
    ellFundamental (ellKreinNegativePart x)) = 0
  rw [ellKreinNegativePart_eigen]
  module

theorem ellKreinNegativePart_positivePart (x : Coordinate) :
    ellKreinNegativePart (ellKreinPositivePart x) = 0 := by
  change (1 / 2 : ℝ) • (ellKreinPositivePart x -
    ellFundamental (ellKreinPositivePart x)) = 0
  rw [ellKreinPositivePart_eigen]
  module

theorem ellHilbertPair_smul_right (r : ℝ) (x y : Coordinate) :
    ellHilbertPair x (r • y) = r * ellHilbertPair x y := by
  rw [ellHilbertPair_eq_native_formula, ellHilbertPair_eq_native_formula]
  simp [zornA, zornB, zornX, zornY, dot3, Pi.smul_apply, smul_eq_mul]
  ring

theorem ellHilbertPair_neg_right (x y : Coordinate) :
    ellHilbertPair x (-y) = -ellHilbertPair x y := by
  change polarForm (ellToKrein x)
      (ellToKrein (ellFundamental (-y))) =
    -polarForm (ellToKrein x) (ellToKrein (ellFundamental y))
  rw [map_neg, map_neg, LinearMap.BilinForm.neg_right]

/-- Positive and negative components are orthogonal for the induced Hilbert
product. -/
theorem ellKrein_components_orthogonal (x y : Coordinate) :
    ellHilbertPair (ellKreinPositivePart x) (ellKreinNegativePart y) = 0 := by
  have h := ellFundamental_hilbert_self_adjoint
    (ellKreinPositivePart x) (ellKreinNegativePart y)
  rw [ellKreinPositivePart_eigen, ellKreinNegativePart_eigen,
    ellHilbertPair_neg_right] at h
  linarith

/-- The positive four-vector sector is orthonormal for the positive product;
the normalization is inherited from the native Zorn polarization. -/
theorem ellHilbertPair_positiveVector_gram (i j : Fin 4) :
    ellHilbertPair (ellKreinPositiveVector i) (ellKreinPositiveVector j) =
      if i = j then 1 else 0 := by
  rw [ellHilbertPair_eq_native_formula, ellToKrein_positiveVector,
    ellToKrein_positiveVector]
  fin_cases i <;> fin_cases j <;>
    norm_num [toKreinCarrier_apply, quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit, jUnit,
      kQuaternionUnit, zornA, zornB, zornX, zornY,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

/-- The negative four-vector sector is also orthonormal for the positive
product, even though its raw Krein squares have the opposite sign. -/
theorem ellHilbertPair_negativeVector_gram (i j : Fin 4) :
    ellHilbertPair (ellKreinNegativeVector i) (ellKreinNegativeVector j) =
      if i = j then 1 else 0 := by
  rw [ellHilbertPair_eq_native_formula, ellToKrein_negativeVector,
    ellToKrein_negativeVector]
  fin_cases i <;> fin_cases j <;>
    norm_num [toKreinCarrier_apply, ellBasis, quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit, jUnit,
      kQuaternionUnit, zornA, zornB, zornX, zornY,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]

/-- Positive and negative Krein eigenvectors are orthogonal for the
fundamental-symmetry Hilbert product. -/
theorem ellHilbertPair_positive_negativeVector (i j : Fin 4) :
    ellHilbertPair (ellKreinPositiveVector i) (ellKreinNegativeVector j) = 0 := by
  have hp : ellKreinPositiveVector i =
      ellKreinPositivePart (ellKreinPositiveVector i) := by
    simp only [ellKreinPositivePart, ellFundamental_positive_eigenvector]
    module
  have hn : ellKreinNegativeVector j =
      ellKreinNegativePart (ellKreinNegativeVector j) := by
    simp only [ellKreinNegativePart, ellFundamental_negative_eigenvector]
    module
  rw [hp, hn]
  exact ellKrein_components_orthogonal _ _

/-- Full positive-product Gram matrix of the signed Krein eigenbasis. -/
theorem ellHilbertPair_eigenbasis_gram (i j : Fin 4 ⊕ Fin 4) :
    ellHilbertPair (ellKreinEigenbasis i) (ellKreinEigenbasis j) =
      if i = j then 1 else 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simpa only [ellKreinEigenbasis_positive_apply, Sum.inl.injEq] using
            ellHilbertPair_positiveVector_gram i j
      | inr j =>
          rw [ellKreinEigenbasis_positive_apply,
            ellKreinEigenbasis_negative_apply,
            ellHilbertPair_positive_negativeVector]
          simp
  | inr i =>
      cases j with
      | inl j =>
          rw [ellKreinEigenbasis_negative_apply,
            ellKreinEigenbasis_positive_apply,
            ellHilbertPair_symm, ellHilbertPair_positive_negativeVector]
          simp
      | inr j =>
          simpa only [ellKreinEigenbasis_negative_apply, Sum.inr.injEq] using
            ellHilbertPair_negativeVector_gram i j

/-- Signed Gram matrix of the actual Krein eigenbasis.  The signs are exactly
the eigenvalues of the fundamental symmetry, matching the double-real Krein
pairing convention. -/
theorem ellKreinPair_eigenbasis_gram (i j : Fin 4 ⊕ Fin 4) :
    ellKreinPair (ellKreinEigenbasis i) (ellKreinEigenbasis j) =
      if i = j then ellFundamentalEigenvalue j else 0 := by
  rw [ellKreinPair_eq_hilbertized]
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          rw [ellKreinEigenbasis_positive_apply,
            ellKreinEigenbasis_positive_apply,
            ellFundamental_positive_eigenvector,
            ellHilbertPair_positiveVector_gram]
          simp [ellFundamentalEigenvalue]
      | inr j =>
          rw [ellKreinEigenbasis_positive_apply,
            ellKreinEigenbasis_negative_apply,
            ellFundamental_negative_eigenvector,
            ellHilbertPair_neg_right,
            ellHilbertPair_positive_negativeVector]
          simp
  | inr i =>
      cases j with
      | inl j =>
          rw [ellKreinEigenbasis_negative_apply,
            ellKreinEigenbasis_positive_apply,
            ellFundamental_positive_eigenvector,
            ellHilbertPair_symm,
            ellHilbertPair_positive_negativeVector]
          simp
      | inr j =>
          rw [ellKreinEigenbasis_negative_apply,
            ellKreinEigenbasis_negative_apply,
            ellFundamental_negative_eigenvector,
            ellHilbertPair_neg_right,
            ellHilbertPair_negativeVector_gram]
          by_cases hij : i = j <;> simp [hij, ellFundamentalEigenvalue]

/-- Matrix of the raw Krein form in the actual signed eigenbasis. -/
def ellKreinGramMatrix : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  fun i j => ellKreinPair (ellKreinEigenbasis i) (ellKreinEigenbasis j)

/-- Matrix of the positive Hilbertized form in the same basis. -/
def ellHilbertGramMatrix : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  fun i j => ellHilbertPair (ellKreinEigenbasis i) (ellKreinEigenbasis j)

/-- The double-real Krein metric is the signed diagonal form `(+,+,+,+,-,-,-,-)`
in this basis; inserting the fundamental symmetry gives the identity Gram
matrix. -/
theorem ellKrein_and_Hilbert_GramMatrices_eq_diagonal :
    ellKreinGramMatrix = Matrix.diagonal ellFundamentalEigenvalue ∧
    ellHilbertGramMatrix = 1 := by
  constructor
  · ext i j
    rw [ellKreinGramMatrix, ellKreinPair_eigenbasis_gram]
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  · ext i j
    rw [ellHilbertGramMatrix, ellHilbertPair_eigenbasis_gram]
    simp [Matrix.one_apply]

/-- On the positive component the raw Krein form agrees with the Hilbert
product. -/
theorem ellKrein_positive_component_positive (x : Coordinate) :
    0 ≤ ellKreinPair (ellKreinPositivePart x) (ellKreinPositivePart x) := by
  rw [ellKreinPair_eq_hilbertized, ellKreinPositivePart_eigen]
  exact ellHilbertPair_nonneg _

/-- On the negative component the raw Krein form is the negative Hilbert
product. -/
theorem ellKrein_negative_component_negative (x : Coordinate) :
    ellKreinPair (ellKreinNegativePart x) (ellKreinNegativePart x) ≤ 0 := by
  rw [ellKreinPair_eq_hilbertized, ellKreinNegativePart_eigen,
    ellHilbertPair_neg_right]
  have h := ellHilbertPair_nonneg (ellKreinNegativePart x)
  linarith

/-- The Krein form is strictly positive on every nonzero positive component. -/
theorem ellKrein_positive_component_strict {x : Coordinate}
    (hx : ellKreinPositivePart x ≠ 0) :
    0 < ellKreinPair (ellKreinPositivePart x) (ellKreinPositivePart x) := by
  rw [ellKreinPair_eq_hilbertized, ellKreinPositivePart_eigen]
  exact ellHilbertPair_pos hx

/-- The Krein form is strictly negative on every nonzero negative component. -/
theorem ellKrein_negative_component_strict {x : Coordinate}
    (hx : ellKreinNegativePart x ≠ 0) :
    ellKreinPair (ellKreinNegativePart x) (ellKreinNegativePart x) < 0 := by
  rw [ellKreinPair_eq_hilbertized, ellKreinNegativePart_eigen,
    ellHilbertPair_neg_right]
  exact neg_neg_of_pos (ellHilbertPair_pos hx)

/-- Each of the four positive basis vectors has strictly positive raw Krein
square, with positivity measured by the metric-conjugated product. -/
theorem ellKreinEigenbasis_positive_sign (i : Fin 4) :
    0 < ellKreinPair (ellKreinEigenbasis (Sum.inl i))
      (ellKreinEigenbasis (Sum.inl i)) := by
  rw [ellKreinEigenbasis_positive_apply, ellKreinPair_eq_hilbertized,
    ellFundamental_positive_eigenvector]
  apply ellHilbertPair_pos
  exact ellKreinPositiveVector_linearIndependent.ne_zero i

/-- Each of the four negative basis vectors has strictly negative raw Krein
square. -/
theorem ellKreinEigenbasis_negative_sign (i : Fin 4) :
    ellKreinPair (ellKreinEigenbasis (Sum.inr i))
      (ellKreinEigenbasis (Sum.inr i)) < 0 := by
  rw [ellKreinEigenbasis_negative_apply, ellKreinPair_eq_hilbertized,
    ellFundamental_negative_eigenvector, ellHilbertPair_neg_right]
  have hpos := ellHilbertPair_pos
    (ellKreinNegativeVector_linearIndependent.ne_zero i)
  linarith

/-- The canonical Zorn product is preserved by the actual field-coordinate
map into the Krein metric owner's tuple carrier. -/
theorem toKreinCarrier_mul (X Y : CanonicalZorn) :
    toKreinCarrier (X * Y) = zornMul (toKreinCarrier X) (toKreinCarrier Y) := by
  apply Prod.ext
  · simp [toKreinCarrier_apply, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3]
  apply Prod.ext
  · simp [toKreinCarrier_apply, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [toKreinCarrier_apply, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
        zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3,
        Pi.smul_apply, smul_eq_mul]
  · funext i
    fin_cases i <;>
      simp [toKreinCarrier_apply, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
        zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3,
        Pi.smul_apply, smul_eq_mul]

@[simp] theorem ellToKrein_leftCoordinateOperator (A : CanonicalZorn)
    (x : Coordinate) :
    ellToKrein (leftCoordinateOperator A x) =
      zornMul (toKreinCarrier A) (ellToKrein x) := by
  rw [leftCoordinateOperator_apply]
  simp only [ellToKrein, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact toKreinCarrier_mul A (coordinateEquiv.symm x)

@[simp] theorem ellToKrein_rightCoordinateOperator (A : CanonicalZorn)
    (x : Coordinate) :
    ellToKrein (rightCoordinateOperator A x) =
      zornMul (ellToKrein x) (toKreinCarrier A) := by
  rw [rightCoordinateOperator_apply]
  simp only [ellToKrein, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact toKreinCarrier_mul (coordinateEquiv.symm x) A

/-- The raw Krein adjoint of left multiplication by `A` is left multiplication
by the Zorn conjugate of `A`, transported into the Ell basis. -/
noncomputable def ellKreinAdjointElement (A : CanonicalZorn) : CanonicalZorn :=
  toKreinCarrier.symm (zornConj (toKreinCarrier A))

@[simp] theorem toKreinCarrier_kreinAdjointElement (A : CanonicalZorn) :
    toKreinCarrier (ellKreinAdjointElement A) = zornConj (toKreinCarrier A) := by
  simp [ellKreinAdjointElement]

theorem ellKreinAdjointElement_involutive (A : CanonicalZorn) :
    ellKreinAdjointElement (ellKreinAdjointElement A) = A := by
  apply toKreinCarrier.injective
  rw [toKreinCarrier_kreinAdjointElement, toKreinCarrier_kreinAdjointElement]
  simp [zornConj, zornMk, zornA, zornB, zornX, zornY]

/-- Zorn conjugation exchanges the two distinguished Ell idempotents. -/
theorem ellKreinAdjointElement_uPlus :
    ellKreinAdjointElement uPlus = uMinus := by
  apply toKreinCarrier.injective
  rw [toKreinCarrier_kreinAdjointElement]
  simp [uPlus, uMinus, zornConj, zornMk, zornA, zornB,
    zornX, zornY, InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]

theorem ellKreinAdjointElement_uMinus :
    ellKreinAdjointElement uMinus = uPlus := by
  apply toKreinCarrier.injective
  rw [toKreinCarrier_kreinAdjointElement]
  simp [uPlus, uMinus, zornConj, zornMk, zornA, zornB,
    zornX, zornY, InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]

theorem ellLeftRegular_krein_adjoint (A : CanonicalZorn) (x y : Coordinate) :
    ellKreinPair (leftCoordinateOperator A x) y =
      ellKreinPair x (leftCoordinateOperator (ellKreinAdjointElement A) y) := by
  change polarPair (ellToKrein (leftCoordinateOperator A x)) (ellToKrein y) =
    polarPair (ellToKrein x)
      (ellToKrein (leftCoordinateOperator (ellKreinAdjointElement A) y))
  rw [ellToKrein_leftCoordinateOperator, ellToKrein_leftCoordinateOperator,
    toKreinCarrier_kreinAdjointElement]
  exact polar_left_adjoint (toKreinCarrier A) (ellToKrein x) (ellToKrein y)

/-- On the actual Ell coordinates, the transported regular operator remains
the difference of the two left-regular Peirce multipliers. -/
theorem ellRegularJ_eq_leftCoordinateOperator_sub :
    ellRegularJ = leftCoordinateOperator uPlus - leftCoordinateOperator uMinus := by
  apply LinearMap.ext
  intro x
  change coordinateEquiv
    ((regularJ uPlus uMinus) (coordinateEquiv.symm x)) = _
  rw [regularJ, LinearMap.sub_apply, map_sub,
    coordinateEquiv_leftRegular_apply, coordinateEquiv_leftRegular_apply]
  simp only [coordinateEquiv.apply_symm_apply, LinearMap.sub_apply]

/-- Pulling back the native bilinear Krein form preserves subtraction in
either slot. -/
theorem ellKreinPair_sub_left (x y z : Coordinate) :
    ellKreinPair (x - y) z = ellKreinPair x z - ellKreinPair y z := by
  change polarForm (ellToKrein (x - y)) (ellToKrein z) =
    polarForm (ellToKrein x) (ellToKrein z) -
      polarForm (ellToKrein y) (ellToKrein z)
  rw [map_sub, LinearMap.BilinForm.sub_left]

theorem ellKreinPair_sub_right (x y z : Coordinate) :
    ellKreinPair x (y - z) = ellKreinPair x y - ellKreinPair x z := by
  change polarForm (ellToKrein x) (ellToKrein (y - z)) =
    polarForm (ellToKrein x) (ellToKrein y) -
      polarForm (ellToKrein x) (ellToKrein z)
  rw [map_sub, LinearMap.BilinForm.sub_right]

/-- The distinguished regular `J` is skew-adjoint for the raw signed Krein
pairing. The sign comes from Zorn conjugation exchanging `uPlus` and
`uMinus`; this is a statement on the transported regular operator itself. -/
theorem ellRegularJ_krein_skew_adjoint (x y : Coordinate) :
    ellKreinPair (ellRegularJ x) y = -ellKreinPair x (ellRegularJ y) := by
  rw [ellRegularJ_eq_leftCoordinateOperator_sub, LinearMap.sub_apply,
    ellKreinPair_sub_left,
    ellLeftRegular_krein_adjoint uPlus, ellLeftRegular_krein_adjoint uMinus,
    ellKreinAdjointElement_uPlus, ellKreinAdjointElement_uMinus]
  rw [LinearMap.sub_apply, ellKreinPair_sub_right]
  ring

/-- The raw Krein adjoint of right multiplication is right multiplication by
the Zorn conjugate. -/
theorem ellRightRegular_krein_adjoint (A : CanonicalZorn) (x y : Coordinate) :
    ellKreinPair (rightCoordinateOperator A x) y =
      ellKreinPair x (rightCoordinateOperator (ellKreinAdjointElement A) y) := by
  change polarPair (ellToKrein (rightCoordinateOperator A x)) (ellToKrein y) =
    polarPair (ellToKrein x)
      (ellToKrein (rightCoordinateOperator (ellKreinAdjointElement A) y))
  rw [ellToKrein_rightCoordinateOperator, ellToKrein_rightCoordinateOperator,
    toKreinCarrier_kreinAdjointElement]
  exact polar_right_adjoint (toKreinCarrier A) (ellToKrein x) (ellToKrein y)

/-- The positive-product adjoint is metric-conjugated: its multiplying element
is `fundamental (zornConj A)`, not merely `zornConj A`. -/
noncomputable def ellHilbertAdjointElement (A : CanonicalZorn) : CanonicalZorn :=
  toKreinCarrier.symm (fundamental (zornConj (toKreinCarrier A)))

@[simp] theorem toKreinCarrier_hilbertAdjointElement (A : CanonicalZorn) :
    toKreinCarrier (ellHilbertAdjointElement A) =
      fundamental (zornConj (toKreinCarrier A)) := by
  simp [ellHilbertAdjointElement]

theorem ellHilbertAdjointElement_involutive (A : CanonicalZorn) :
    ellHilbertAdjointElement (ellHilbertAdjointElement A) = A := by
  apply toKreinCarrier.injective
  simp only [toKreinCarrier_hilbertAdjointElement]
  change fundamental (zornConj (fundamental (zornConj (toKreinCarrier A)))) =
    toKreinCarrier A
  simp [fundamental, zornConj, zornMk, zornA, zornB, zornX, zornY]

theorem ellLeftRegular_hilbert_adjoint (A : CanonicalZorn) (x y : Coordinate) :
    ellHilbertPair (leftCoordinateOperator A x) y =
      ellHilbertPair x (leftCoordinateOperator (ellHilbertAdjointElement A) y) := by
  simp only [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  rw [ellToKrein_leftCoordinateOperator, ellToKrein_leftCoordinateOperator,
    toKreinCarrier_hilbertAdjointElement]
  exact hilbertized_left_adjoint (toKreinCarrier A) (ellToKrein x) (ellToKrein y)

/-- For the metric-conjugated product, the adjoint of right multiplication by
`A` is right multiplication by `fundamental (zornConj A)`. -/
theorem ellRightRegular_hilbert_adjoint (A : CanonicalZorn) (x y : Coordinate) :
    ellHilbertPair (rightCoordinateOperator A x) y =
      ellHilbertPair x (rightCoordinateOperator (ellHilbertAdjointElement A) y) := by
  simp only [ellHilbertPair, ellKreinPair, ellToKrein_fundamental]
  rw [ellToKrein_rightCoordinateOperator, ellToKrein_rightCoordinateOperator,
    toKreinCarrier_hilbertAdjointElement]
  exact hilbertized_right_adjoint (toKreinCarrier A) (ellToKrein x) (ellToKrein y)

/-- The adjoint of either distinguished Peirce multiplier for the
metric-conjugated product is itself. -/
theorem ellHilbertAdjointElement_uPlus :
    ellHilbertAdjointElement uPlus = uPlus := by
  apply toKreinCarrier.injective
  rw [toKreinCarrier_hilbertAdjointElement]
  simp [uPlus, zornConj, fundamental, zornMk, zornA, zornB, zornX, zornY,
    InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]

theorem ellHilbertAdjointElement_uMinus :
    ellHilbertAdjointElement uMinus = uMinus := by
  apply toKreinCarrier.injective
  rw [toKreinCarrier_hilbertAdjointElement]
  simp [uMinus, zornConj, fundamental, zornMk, zornA, zornB, zornX, zornY,
    InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]

theorem ellHilbertPair_sub_left (x y z : Coordinate) :
    ellHilbertPair (x - y) z = ellHilbertPair x z - ellHilbertPair y z := by
  change ellKreinPair (x - y) (ellFundamental z) =
    ellKreinPair x (ellFundamental z) - ellKreinPair y (ellFundamental z)
  rw [ellKreinPair_sub_left]

theorem ellHilbertPair_sub_right (x y z : Coordinate) :
    ellHilbertPair x (y - z) = ellHilbertPair x y - ellHilbertPair x z := by
  change ellKreinPair x (ellFundamental (y - z)) =
    ellKreinPair x (ellFundamental y) - ellKreinPair x (ellFundamental z)
  rw [map_sub, ellKreinPair_sub_right]

/-- The same regular `J` is self-adjoint for the positive product obtained
by inserting the fundamental symmetry in the second argument. -/
theorem ellRegularJ_hilbert_self_adjoint (x y : Coordinate) :
    ellHilbertPair (ellRegularJ x) y = ellHilbertPair x (ellRegularJ y) := by
  rw [ellRegularJ_eq_leftCoordinateOperator_sub, LinearMap.sub_apply,
    ellHilbertPair_sub_left, ellLeftRegular_hilbert_adjoint uPlus,
    ellLeftRegular_hilbert_adjoint uMinus,
    ellHilbertAdjointElement_uPlus, ellHilbertAdjointElement_uMinus,
    LinearMap.sub_apply, ellHilbertPair_sub_right]

end InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge
