import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import proofs.ZornLightconeCAR

/-!
# Exact classification of the Zorn lightcone channel operator

The operator historically named `lightconeChannelProjector` is the
anticommutator of the two directed nilpotent blocks.  Its exact coordinate
action shows that it is the negative of a rank-eight projection, rather than
itself an idempotent.
-/

noncomputable section

namespace ZornLightconeChannelOperator

open SplitOctonionBraidSU3
open CanonicalZornFiveGradedClosure
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ZornChiralLightcone
open ZornLightconeCAR
open Module

/-- Four selected coordinates in the positive semispinor block. -/
def channelPlusZorn (r : Fin 3) (X : Zorn) : Zorn where
  a := -X.a
  u := fun i => if i = r then -X.u i else 0
  v := fun i => if i = r then 0 else -X.v i
  b := 0

/-- Four selected coordinates in the negative semispinor block. -/
def channelMinusZorn (r : Fin 3) (X : Zorn) : Zorn where
  a := 0
  u := fun i => if i = r then 0 else -X.u i
  v := fun i => if i = r then -X.v i else 0
  b := -X.b

/-- Exact coordinate action of the channel anticommutator. -/
@[simp] theorem lightconeChannelProjector_apply_exact (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeChannelProjector r (S, C) =
      (⟨channelPlusZorn r S.val⟩, ⟨channelMinusZorn r C.val⟩) := by
  rw [lightconeChannelProjector_apply]
  apply Prod.ext
  · apply ZornCopy.ext
    apply zorn_ext
    · fin_cases r <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelPlusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]
    · funext i
      fin_cases r <;> fin_cases i <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelPlusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]
    · funext i
      fin_cases r <;> fin_cases i <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelPlusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]
    · fin_cases r <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelPlusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]
  · apply ZornCopy.ext
    apply zorn_ext
    · fin_cases r <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelMinusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]
    · funext i
      fin_cases r <;> fin_cases i <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelMinusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]
    · funext i
      fin_cases r <;> fin_cases i <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelMinusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]
    · fin_cases r <;> simp [cliffordMinus, cliffordPlus,
        upperLightconeVector, lowerLightconeVector, channelMinusZorn,
        zornConj, zornMul, E_k, F_k, e_k, dot3, cross3]

@[simp] theorem channelPlusZorn_iterate (r : Fin 3) (X : Zorn) :
    channelPlusZorn r (channelPlusZorn r X) =
      zornSmul (-1) (channelPlusZorn r X) := by
  apply zorn_ext
  · simp [channelPlusZorn, zornSmul]
  · funext i
    by_cases h : i = r <;> simp [channelPlusZorn, zornSmul, h]
  · funext i
    by_cases h : i = r <;> simp [channelPlusZorn, zornSmul, h]
  · simp [channelPlusZorn, zornSmul]

@[simp] theorem channelMinusZorn_iterate (r : Fin 3) (X : Zorn) :
    channelMinusZorn r (channelMinusZorn r X) =
      zornSmul (-1) (channelMinusZorn r X) := by
  apply zorn_ext
  · simp [channelMinusZorn, zornSmul]
  · funext i
    by_cases h : i = r <;> simp [channelMinusZorn, zornSmul, h]
  · funext i
    by_cases h : i = r <;> simp [channelMinusZorn, zornSmul, h]
  · simp [channelMinusZorn, zornSmul]

/-- The channel operator satisfies `C² = -C`; it is not itself a projector. -/
theorem lightconeChannelProjector_sq (r : Fin 3) :
    lightconeChannelProjector r * lightconeChannelProjector r =
      -lightconeChannelProjector r := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp only [Module.End.mul_apply, LinearMap.neg_apply,
    lightconeChannelProjector_apply_exact]
  apply Prod.ext <;> apply ZornCopy.ext
  · rw [channelPlusZorn_iterate]
    change zornSmul (-1) (channelPlusZorn r S.val) =
      (- (⟨channelPlusZorn r S.val⟩ : SpinorPlus8)).val
    rw [← neg_one_smul ℂ (⟨channelPlusZorn r S.val⟩ : SpinorPlus8),
      copy_smul_val]
  · rw [channelMinusZorn_iterate]
    change zornSmul (-1) (channelMinusZorn r C.val) =
      (- (⟨channelMinusZorn r C.val⟩ : SpinorMinus8)).val
    rw [← neg_one_smul ℂ (⟨channelMinusZorn r C.val⟩ : SpinorMinus8),
      copy_smul_val]

/-- The correctly normalized channel projection. -/
def normalizedChannelProjection (r : Fin 3) :
    Module.End ℂ DiracSpinor16 :=
  -lightconeChannelProjector r

/-- The normalized channel operator is genuinely idempotent. -/
theorem normalizedChannelProjection_sq (r : Fin 3) :
    normalizedChannelProjection r * normalizedChannelProjection r =
      normalizedChannelProjection r := by
  change (-lightconeChannelProjector r) * (-lightconeChannelProjector r) =
    -lightconeChannelProjector r
  calc
    _ = lightconeChannelProjector r * lightconeChannelProjector r := by
      exact neg_mul_neg (lightconeChannelProjector r)
        (lightconeChannelProjector r)
    _ = -lightconeChannelProjector r := lightconeChannelProjector_sq r

/-! ## Diagonal coordinate form -/

def spinorPlusCoordinateBasis : Basis (Fin 8) ℂ SpinorPlus8 :=
  Basis.ofEquivFun
    (copyLinearEquivCoordinates TrialitySector.spinorPlus)

def spinorMinusCoordinateBasis : Basis (Fin 8) ℂ SpinorMinus8 :=
  Basis.ofEquivFun
    (copyLinearEquivCoordinates TrialitySector.spinorMinus)

/-- Coordinate basis on `S₊ × S₋`, indexed by two copies of `Fin 8`. -/
def diracCoordinateBasis : Basis (Fin 8 ⊕ Fin 8) ℂ DiracSpinor16 :=
  spinorPlusCoordinateBasis.prod spinorMinusCoordinateBasis

@[simp] theorem spinorPlusCoordinateBasis_repr
    (S : SpinorPlus8) (i : Fin 8) :
    spinorPlusCoordinateBasis.repr S i = zornCoordinates S.val i := by
  rfl

@[simp] theorem spinorMinusCoordinateBasis_repr
    (C : SpinorMinus8) (i : Fin 8) :
    spinorMinusCoordinateBasis.repr C i = zornCoordinates C.val i := by
  rfl

@[simp] theorem spinorPlusCoordinateBasis_val (i : Fin 8) :
    (spinorPlusCoordinateBasis i).val =
      coordinatesToZorn (Pi.single i 1) := by
  apply zornCoordinates_injective
  change copyLinearEquivCoordinates TrialitySector.spinorPlus
      (spinorPlusCoordinateBasis i) =
    zornCoordinates (coordinatesToZorn (Pi.single i 1))
  rw [zornCoordinates_coordinatesToZorn]
  simp [spinorPlusCoordinateBasis, Basis.coe_ofEquivFun]

@[simp] theorem spinorMinusCoordinateBasis_val (i : Fin 8) :
    (spinorMinusCoordinateBasis i).val =
      coordinatesToZorn (Pi.single i 1) := by
  apply zornCoordinates_injective
  change copyLinearEquivCoordinates TrialitySector.spinorMinus
      (spinorMinusCoordinateBasis i) =
    zornCoordinates (coordinatesToZorn (Pi.single i 1))
  rw [zornCoordinates_coordinatesToZorn]
  simp [spinorMinusCoordinateBasis, Basis.coe_ofEquivFun]

/-- Coordinates selected in the positive semispinor block. -/
def channelPlusSelected (r : Fin 3) (i : Fin 8) : Prop :=
  i.1 = 0 ∨
      (1 ≤ i.1 ∧ i.1 ≤ 3 ∧ i.1 = r.1 + 1) ∨
      (4 ≤ i.1 ∧ i.1 ≤ 6 ∧ i.1 ≠ r.1 + 4)

/-- Coordinates selected in the negative semispinor block. -/
def channelMinusSelected (r : Fin 3) (i : Fin 8) : Prop :=
  i.1 = 7 ∨
      (1 ≤ i.1 ∧ i.1 ≤ 3 ∧ i.1 ≠ r.1 + 1) ∨
      (4 ≤ i.1 ∧ i.1 ≤ 6 ∧ i.1 = r.1 + 4)

instance channelPlusSelectedDecidable (r : Fin 3) (i : Fin 8) :
    Decidable (channelPlusSelected r i) := by
  unfold channelPlusSelected
  infer_instance

instance channelMinusSelectedDecidable (r : Fin 3) (i : Fin 8) :
    Decidable (channelMinusSelected r i) := by
  unfold channelMinusSelected
  infer_instance

/-- Diagonal weights on the positive semispinor coordinates. -/
def channelPlusWeight (r : Fin 3) (i : Fin 8) : ℂ :=
  if channelPlusSelected r i then -1 else 0

/-- Diagonal weights on the negative semispinor coordinates. -/
def channelMinusWeight (r : Fin 3) (i : Fin 8) : ℂ :=
  if channelMinusSelected r i then -1 else 0

def channelSelected (r : Fin 3) : (Fin 8 ⊕ Fin 8) → Prop
  | Sum.inl i => channelPlusSelected r i
  | Sum.inr i => channelMinusSelected r i

instance channelSelectedDecidable (r : Fin 3) (i : Fin 8 ⊕ Fin 8) :
    Decidable (channelSelected r i) := by
  cases i with
  | inl i => exact channelPlusSelectedDecidable r i
  | inr i => exact channelMinusSelectedDecidable r i

/-- Diagonal weight of the channel operator in canonical Zorn coordinates. -/
def channelWeight (r : Fin 3) : (Fin 8 ⊕ Fin 8) → ℂ
  | Sum.inl i => channelPlusWeight r i
  | Sum.inr i => channelMinusWeight r i

private theorem channelPlusZorn_coordinateBasis_zero (i : Fin 8) :
    channelPlusZorn 0 (spinorPlusCoordinateBasis i).val =
      zornSmul (channelPlusWeight 0 i)
        (spinorPlusCoordinateBasis i).val := by
  apply zorn_ext
  · fin_cases i <;> simp [channelPlusZorn, channelPlusWeight, channelPlusSelected,
      coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelPlusZorn,
      channelPlusWeight, channelPlusSelected, coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelPlusZorn,
      channelPlusWeight, channelPlusSelected, coordinatesToZorn, zornSmul]
  · fin_cases i <;> simp [channelPlusZorn, channelPlusWeight, channelPlusSelected,
      coordinatesToZorn, zornSmul]

private theorem channelPlusZorn_coordinateBasis_one (i : Fin 8) :
    channelPlusZorn 1 (spinorPlusCoordinateBasis i).val =
      zornSmul (channelPlusWeight 1 i)
        (spinorPlusCoordinateBasis i).val := by
  apply zorn_ext
  · fin_cases i <;> simp [channelPlusZorn, channelPlusWeight, channelPlusSelected,
      coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelPlusZorn,
      channelPlusWeight, channelPlusSelected, coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelPlusZorn,
      channelPlusWeight, channelPlusSelected, coordinatesToZorn, zornSmul]
  · fin_cases i <;> simp [channelPlusZorn, channelPlusWeight, channelPlusSelected,
      coordinatesToZorn, zornSmul]

private theorem channelPlusZorn_coordinateBasis_two (i : Fin 8) :
    channelPlusZorn 2 (spinorPlusCoordinateBasis i).val =
      zornSmul (channelPlusWeight 2 i)
        (spinorPlusCoordinateBasis i).val := by
  apply zorn_ext
  · fin_cases i <;> simp [channelPlusZorn, channelPlusWeight, channelPlusSelected,
      coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelPlusZorn,
      channelPlusWeight, channelPlusSelected, coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelPlusZorn,
      channelPlusWeight, channelPlusSelected, coordinatesToZorn, zornSmul]
  · fin_cases i <;> simp [channelPlusZorn, channelPlusWeight, channelPlusSelected,
      coordinatesToZorn, zornSmul]

theorem channelPlusZorn_coordinateBasis (r : Fin 3) (i : Fin 8) :
    channelPlusZorn r (spinorPlusCoordinateBasis i).val =
      zornSmul (channelPlusWeight r i)
        (spinorPlusCoordinateBasis i).val := by
  fin_cases r
  · exact channelPlusZorn_coordinateBasis_zero i
  · exact channelPlusZorn_coordinateBasis_one i
  · exact channelPlusZorn_coordinateBasis_two i

private theorem channelMinusZorn_coordinateBasis_zero (i : Fin 8) :
    channelMinusZorn 0 (spinorMinusCoordinateBasis i).val =
      zornSmul (channelMinusWeight 0 i)
        (spinorMinusCoordinateBasis i).val := by
  apply zorn_ext
  · fin_cases i <;> simp [channelMinusZorn, channelMinusWeight, channelMinusSelected,
      coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelMinusZorn,
      channelMinusWeight, channelMinusSelected, coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelMinusZorn,
      channelMinusWeight, channelMinusSelected, coordinatesToZorn, zornSmul]
  · fin_cases i <;> simp [channelMinusZorn, channelMinusWeight, channelMinusSelected,
      coordinatesToZorn, zornSmul]

private theorem channelMinusZorn_coordinateBasis_one (i : Fin 8) :
    channelMinusZorn 1 (spinorMinusCoordinateBasis i).val =
      zornSmul (channelMinusWeight 1 i)
        (spinorMinusCoordinateBasis i).val := by
  apply zorn_ext
  · fin_cases i <;> simp [channelMinusZorn, channelMinusWeight, channelMinusSelected,
      coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelMinusZorn,
      channelMinusWeight, channelMinusSelected, coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelMinusZorn,
      channelMinusWeight, channelMinusSelected, coordinatesToZorn, zornSmul]
  · fin_cases i <;> simp [channelMinusZorn, channelMinusWeight, channelMinusSelected,
      coordinatesToZorn, zornSmul]

private theorem channelMinusZorn_coordinateBasis_two (i : Fin 8) :
    channelMinusZorn 2 (spinorMinusCoordinateBasis i).val =
      zornSmul (channelMinusWeight 2 i)
        (spinorMinusCoordinateBasis i).val := by
  apply zorn_ext
  · fin_cases i <;> simp [channelMinusZorn, channelMinusWeight, channelMinusSelected,
      coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelMinusZorn,
      channelMinusWeight, channelMinusSelected, coordinatesToZorn, zornSmul]
  · funext j
    fin_cases i <;> fin_cases j <;> simp [channelMinusZorn,
      channelMinusWeight, channelMinusSelected, coordinatesToZorn, zornSmul]
  · fin_cases i <;> simp [channelMinusZorn, channelMinusWeight, channelMinusSelected,
      coordinatesToZorn, zornSmul]

theorem channelMinusZorn_coordinateBasis (r : Fin 3) (i : Fin 8) :
    channelMinusZorn r (spinorMinusCoordinateBasis i).val =
      zornSmul (channelMinusWeight r i)
        (spinorMinusCoordinateBasis i).val := by
  fin_cases r
  · exact channelMinusZorn_coordinateBasis_zero i
  · exact channelMinusZorn_coordinateBasis_one i
  · exact channelMinusZorn_coordinateBasis_two i

@[simp] theorem diracCoordinateBasis_inl (i : Fin 8) :
    diracCoordinateBasis (Sum.inl i) =
      (spinorPlusCoordinateBasis i, 0) := by
  apply Prod.ext
  · exact Basis.prod_apply_inl_fst _ _ i
  · exact Basis.prod_apply_inl_snd _ _ i

@[simp] theorem diracCoordinateBasis_inr (i : Fin 8) :
    diracCoordinateBasis (Sum.inr i) =
      (0, spinorMinusCoordinateBasis i) := by
  apply Prod.ext
  · exact Basis.prod_apply_inr_fst _ _ i
  · exact Basis.prod_apply_inr_snd _ _ i

theorem lightconeChannelProjector_basis (r : Fin 3)
    (i : Fin 8 ⊕ Fin 8) :
    lightconeChannelProjector r (diracCoordinateBasis i) =
      channelWeight r i • diracCoordinateBasis i := by
  cases i with
  | inl i =>
      rw [diracCoordinateBasis_inl, lightconeChannelProjector_apply_exact]
      rw [show channelWeight r (Sum.inl i) = channelPlusWeight r i by rfl,
        Prod.smul_mk, smul_zero]
      change ((⟨channelPlusZorn r
          (spinorPlusCoordinateBasis i).val⟩ : SpinorPlus8),
          (⟨channelMinusZorn r
            (0 : SpinorMinus8).val⟩ : SpinorMinus8)) =
        (channelPlusWeight r i • spinorPlusCoordinateBasis i, 0)
      apply Prod.ext <;> apply ZornCopy.ext
      · rw [channelPlusZorn_coordinateBasis, copy_smul_val]
      · apply zorn_ext
        · simp [channelMinusZorn]
        · funext j; simp [channelMinusZorn]
        · funext j; simp [channelMinusZorn]
        · simp [channelMinusZorn]
  | inr i =>
      rw [diracCoordinateBasis_inr, lightconeChannelProjector_apply_exact]
      rw [show channelWeight r (Sum.inr i) = channelMinusWeight r i by rfl,
        Prod.smul_mk, smul_zero]
      change ((⟨channelPlusZorn r
          (0 : SpinorPlus8).val⟩ : SpinorPlus8),
          (⟨channelMinusZorn r
            (spinorMinusCoordinateBasis i).val⟩ : SpinorMinus8)) =
        (0, channelMinusWeight r i • spinorMinusCoordinateBasis i)
      apply Prod.ext <;> apply ZornCopy.ext
      · apply zorn_ext
        · simp [channelPlusZorn]
        · funext j; simp [channelPlusZorn]
        · funext j; simp [channelPlusZorn]
        · simp [channelPlusZorn]
      · rw [channelMinusZorn_coordinateBasis, copy_smul_val]

/-- Matrix of the channel operator: eight entries `-1` and eight entries `0`. -/
theorem lightconeChannelProjector_toMatrix (r : Fin 3) :
    (LinearMap.toMatrix diracCoordinateBasis diracCoordinateBasis)
        (lightconeChannelProjector r) =
      Matrix.diagonal (channelWeight r) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [lightconeChannelProjector_basis, map_smul]
  simp [Matrix.diagonal, Finsupp.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem channelWeight_nonzero_card (r : Fin 3) :
    Fintype.card {i // channelWeight r i ≠ 0} = 8 := by
  let e : {i // channelWeight r i ≠ 0} ≃ {i // channelSelected r i} :=
    Equiv.subtypeEquivProp (by
      funext i
      apply propext
      cases i with
      | inl i =>
          by_cases h : channelPlusSelected r i <;>
            simp [channelWeight, channelPlusWeight, channelSelected, h]
      | inr i =>
          by_cases h : channelMinusSelected r i <;>
            simp [channelWeight, channelMinusWeight, channelSelected, h])
  rw [Fintype.card_congr e]
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  simp only [channelSelected]
  fin_cases r <;>
    simp only [channelPlusSelected, channelMinusSelected] <;> decide

theorem channelWeight_sum (r : Fin 3) :
    ∑ i, channelWeight r i = -8 := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_eight, Fin.sum_univ_eight]
  fin_cases r <;>
    norm_num [channelWeight, channelPlusWeight, channelPlusSelected, channelMinusWeight, channelMinusSelected]

/-- The channel operator has rank eight. -/
theorem lightconeChannelProjector_finrank_range (r : Fin 3) :
    Module.finrank ℂ (LinearMap.range (lightconeChannelProjector r)) = 8 := by
  have h := Matrix.rank_eq_finrank_range_toLin
    ((LinearMap.toMatrix diracCoordinateBasis diracCoordinateBasis)
      (lightconeChannelProjector r))
    diracCoordinateBasis diracCoordinateBasis
  rw [Matrix.toLin_toMatrix] at h
  rw [lightconeChannelProjector_toMatrix, Matrix.rank_diagonal,
    channelWeight_nonzero_card] at h
  exact h.symm

/-- The channel operator also has an eight-dimensional kernel. -/
theorem lightconeChannelProjector_finrank_ker (r : Fin 3) :
    Module.finrank ℂ (LinearMap.ker (lightconeChannelProjector r)) = 8 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (lightconeChannelProjector r)
  rw [lightconeChannelProjector_finrank_range, diracSpinor_finrank] at h
  omega

/-- Its operator trace is the sum of eight `-1` eigenvalues. -/
theorem lightconeChannelProjector_trace (r : Fin 3) :
    LinearMap.trace ℂ DiracSpinor16 (lightconeChannelProjector r) = -8 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ diracCoordinateBasis,
    lightconeChannelProjector_toMatrix, Matrix.trace_diagonal,
    channelWeight_sum]

/-- Exact characteristic polynomial: eight zero and eight minus-one roots. -/
theorem lightconeChannelProjector_charpoly (r : Fin 3) :
    LinearMap.charpoly (lightconeChannelProjector r) =
      Polynomial.X ^ 8 * (Polynomial.X + 1) ^ 8 := by
  rw [← LinearMap.charpoly_toMatrix (lightconeChannelProjector r)
    diracCoordinateBasis, lightconeChannelProjector_toMatrix,
    Matrix.charpoly_diagonal, Fintype.prod_sum_type,
    Fin.prod_univ_eight, Fin.prod_univ_eight]
  fin_cases r <;>
    simp [channelWeight, channelPlusWeight, channelPlusSelected, channelMinusWeight, channelMinusSelected] <;> ring

/-- A canonical zero-eigenvalue witness. -/
def channelZeroEigenvector : DiracSpinor16 :=
  diracCoordinateBasis (Sum.inl 7)

/-- A canonical minus-one-eigenvalue witness. -/
def channelNegOneEigenvector : DiracSpinor16 :=
  diracCoordinateBasis (Sum.inl 0)

theorem channelZeroEigenvector_ne_zero : channelZeroEigenvector ≠ 0 :=
  diracCoordinateBasis.ne_zero (Sum.inl 7)

theorem channelNegOneEigenvector_ne_zero : channelNegOneEigenvector ≠ 0 :=
  diracCoordinateBasis.ne_zero (Sum.inl 0)

theorem lightconeChannelProjector_hasEigenvalue_zero (r : Fin 3) :
    (lightconeChannelProjector r).HasEigenvalue 0 := by
  rw [Module.End.hasEigenvalue_iff]
  refine (Submodule.ne_bot_iff _).mpr ⟨channelZeroEigenvector, ?_,
    channelZeroEigenvector_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff]
  rw [channelZeroEigenvector, lightconeChannelProjector_basis]
  simp [channelWeight, channelPlusWeight, channelPlusSelected]

theorem lightconeChannelProjector_hasEigenvalue_neg_one (r : Fin 3) :
    (lightconeChannelProjector r).HasEigenvalue (-1) := by
  rw [Module.End.hasEigenvalue_iff]
  refine (Submodule.ne_bot_iff _).mpr ⟨channelNegOneEigenvector, ?_,
    channelNegOneEigenvector_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff]
  rw [channelNegOneEigenvector, lightconeChannelProjector_basis]
  simp [channelWeight, channelPlusWeight, channelPlusSelected]

/-- The quadratic polynomial `X(X+1)` annihilates the channel operator. -/
theorem lightconeChannelProjector_quadratic_aeval (r : Fin 3) :
    Polynomial.aeval (lightconeChannelProjector r)
        ((Polynomial.X : Polynomial ℂ) * (Polynomial.X + 1)) = 0 := by
  rw [Polynomial.aeval_mul, Polynomial.aeval_X, Polynomial.aeval_add,
    Polynomial.aeval_X, Polynomial.aeval_one]
  rw [mul_add, mul_one, lightconeChannelProjector_sq]
  module

/-- Exact minimal polynomial. -/
theorem lightconeChannelProjector_minpoly (r : Fin 3) :
    minpoly ℂ (lightconeChannelProjector r) =
      Polynomial.X * (Polynomial.X + 1) := by
  let C := lightconeChannelProjector r
  have h0 : (minpoly ℂ C).IsRoot 0 :=
    Module.End.isRoot_of_hasEigenvalue
      (lightconeChannelProjector_hasEigenvalue_zero r)
  have hneg : (minpoly ℂ C).IsRoot (-1) :=
    Module.End.isRoot_of_hasEigenvalue
      (lightconeChannelProjector_hasEigenvalue_neg_one r)
  have hd0 : Polynomial.X - Polynomial.C (0 : ℂ) ∣ minpoly ℂ C :=
    Polynomial.dvd_iff_isRoot.mpr h0
  have hdneg : Polynomial.X - Polynomial.C (-1 : ℂ) ∣ minpoly ℂ C :=
    Polynomial.dvd_iff_isRoot.mpr hneg
  have hcop : IsCoprime
      (Polynomial.X - Polynomial.C (0 : ℂ))
      (Polynomial.X - Polynomial.C (-1 : ℂ)) := by
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    norm_num
  have hforward : Polynomial.X * (Polynomial.X + 1) ∣ minpoly ℂ C := by
    convert hcop.mul_dvd hd0 hdneg using 1
    all_goals norm_num
  have hback : minpoly ℂ C ∣ Polynomial.X * (Polynomial.X + 1) := by
    exact minpoly.dvd ℂ C (lightconeChannelProjector_quadratic_aeval r)
  apply Polynomial.eq_of_monic_of_associated
    (minpoly.monic (Algebra.IsIntegral.isIntegral C))
    ((Polynomial.monic_X).mul (Polynomial.monic_X_add_C 1))
  exact associated_of_dvd_dvd hback hforward

/-- The kernel is exactly the zero eigenspace. -/
theorem lightconeChannelProjector_ker_eq_eigenspace_zero (r : Fin 3) :
    LinearMap.ker (lightconeChannelProjector r) =
      Module.End.eigenspace (lightconeChannelProjector r) 0 := by
  ext x
  simp

/-- The range is exactly the minus-one eigenspace. -/
theorem lightconeChannelProjector_range_eq_eigenspace_neg_one (r : Fin 3) :
    LinearMap.range (lightconeChannelProjector r) =
      Module.End.eigenspace (lightconeChannelProjector r) (-1) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := LinearMap.congr_fun (lightconeChannelProjector_sq r) y
    simpa [Module.End.mul_apply] using h
  · intro hx
    rw [Module.End.mem_eigenspace_iff] at hx
    refine ⟨-x, ?_⟩
    rw [map_neg, hx]
    simp

/-- The normalized projection splits the carrier into its range and kernel. -/
theorem normalizedChannelProjection_isIdempotent (r : Fin 3) :
    IsIdempotentElem (normalizedChannelProjection r) := by
  exact normalizedChannelProjection_sq r

theorem normalizedChannelProjection_range_eq_ker_one_sub (r : Fin 3) :
    LinearMap.range (normalizedChannelProjection r) =
      LinearMap.ker (1 - normalizedChannelProjection r) :=
  LinearMap.IsIdempotentElem.range_eq_ker_one_sub
    (normalizedChannelProjection_isIdempotent r)

theorem normalizedChannelProjection_ker_eq_range_one_sub (r : Fin 3) :
    LinearMap.ker (normalizedChannelProjection r) =
      LinearMap.range (1 - normalizedChannelProjection r) :=
  LinearMap.IsIdempotentElem.ker_eq_range_one_sub
    (normalizedChannelProjection_isIdempotent r)

/-- The normalized channel projection gives a genuine direct-sum decomposition. -/
theorem normalizedChannelProjection_isCompl (r : Fin 3) :
    IsCompl (LinearMap.range (normalizedChannelProjection r))
      (LinearMap.ker (normalizedChannelProjection r)) :=
  LinearMap.IsIdempotentElem.isCompl
    (normalizedChannelProjection_isIdempotent r)

/--
The complete finite-dimensional classification of the channel operator: its
quadratic relation, rank, nullity, trace, characteristic polynomial, and
minimal polynomial.
-/
theorem lightconeChannelProjector_classification (r : Fin 3) :
    lightconeChannelProjector r * lightconeChannelProjector r =
        -lightconeChannelProjector r ∧
      Module.finrank ℂ (LinearMap.range (lightconeChannelProjector r)) = 8 ∧
      Module.finrank ℂ (LinearMap.ker (lightconeChannelProjector r)) = 8 ∧
      LinearMap.trace ℂ DiracSpinor16 (lightconeChannelProjector r) = -8 ∧
      LinearMap.charpoly (lightconeChannelProjector r) =
        Polynomial.X ^ 8 * (Polynomial.X + 1) ^ 8 ∧
      minpoly ℂ (lightconeChannelProjector r) =
        Polynomial.X * (Polynomial.X + 1) := by
  exact ⟨lightconeChannelProjector_sq r,
    lightconeChannelProjector_finrank_range r,
    lightconeChannelProjector_finrank_ker r,
    lightconeChannelProjector_trace r,
    lightconeChannelProjector_charpoly r,
    lightconeChannelProjector_minpoly r⟩

end ZornLightconeChannelOperator

end noncomputable section
