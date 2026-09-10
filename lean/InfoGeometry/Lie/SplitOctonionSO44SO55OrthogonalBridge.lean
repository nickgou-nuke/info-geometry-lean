import Mathlib.Data.Matrix.Block
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge

open Matrix
open InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Mat8 := Matrix (Fin 8) (Fin 8) ℝ
abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R
abbrev Mat10Sum := Matrix (Fin 8 ⊕ Fin 2) (Fin 8 ⊕ Fin 2) ℝ

def fin8Equiv : Fin 8 ≃ Fin 4 ⊕ Fin 4 where
  toFun i := if h : i.val < 4 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 4, by omega⟩
  invFun s := match s with
    | Sum.inl i => ⟨i.val, by omega⟩
    | Sum.inr i => ⟨i.val + 4, by omega⟩
  left_inv i := by
    dsimp
    split_ifs with h
    · rfl
    · apply Fin.ext
      dsimp
      omega
  right_inv s := by
    rcases s with i | i <;> dsimp <;> simp [i.isLt]

def eta44 : Mat8 :=
  (Matrix.reindex fin8Equiv.symm fin8Equiv.symm etaW)

def eta2 : Mat2 := fun i j =>
  if i.val = 0 ∧ j.val = 1 then 1
  else if i.val = 1 ∧ j.val = 0 then 1 else 0

def eta55Levi : Mat10Sum :=
  fromBlocks eta44 0 0 eta2

def so44ToSO55Sum (M : Mat8) : Mat10Sum :=
  fromBlocks M 0 0 0

def IsEtaSkew {ι : Type*} [Fintype ι]
    (eta M : Matrix ι ι ℝ) : Prop :=
  Mᵀ * eta + eta * M = 0

theorem eta2_symm : eta2ᵀ = eta2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta2]

theorem so44ToSO55Sum_preserves_etaSkew (M : Mat8)
    (hM : IsEtaSkew eta44 M) :
    IsEtaSkew eta55Levi (so44ToSO55Sum M) := by
  dsimp [IsEtaSkew, eta55Levi, so44ToSO55Sum]
  rw [fromBlocks_transpose]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add]
  rw [fromBlocks_add]
  rw [← (fromBlocks_zero : fromBlocks (0 : Mat8) 0 0 0 = (0 : Mat10Sum))]
  rw [fromBlocks_inj]
  rcases hM with hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hM
  · ext i j
    simp
  · ext i j
    simp
  · ext i j
    simp [eta2]

theorem so44ToSO55Sum_add (M N : Mat8) :
    so44ToSO55Sum (M + N) = so44ToSO55Sum M + so44ToSO55Sum N := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [so44ToSO55Sum]

theorem so44ToSO55Sum_smul (r : ℝ) (M : Mat8) :
    so44ToSO55Sum (r • M) = r • so44ToSO55Sum M := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [so44ToSO55Sum]

theorem so44ToSO55Sum_mul (M N : Mat8) :
    so44ToSO55Sum (M * N) = so44ToSO55Sum M * so44ToSO55Sum N := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [so44ToSO55Sum, Matrix.mul_apply]
  · simp [so44ToSO55Sum, Matrix.mul_apply]
  · simp [so44ToSO55Sum, Matrix.mul_apply]
  · simp [so44ToSO55Sum, Matrix.mul_apply]

theorem so44ToSO55Sum_bracket (M N : Mat8) :
    so44ToSO55Sum (M * N - N * M) =
      so44ToSO55Sum M * so44ToSO55Sum N -
        so44ToSO55Sum N * so44ToSO55Sum M := by
  rw [show so44ToSO55Sum (M * N - N * M) =
      so44ToSO55Sum (M * N) - so44ToSO55Sum (N * M) by
        ext i j
        rcases i with i | i <;> rcases j with j | j <;>
          simp [so44ToSO55Sum]]
  rw [so44ToSO55Sum_mul, so44ToSO55Sum_mul]

noncomputable def so44ToSO55SumLieHom :
    Mat8 →ₗ⁅ℝ⁆ Mat10Sum where
  toFun := so44ToSO55Sum
  map_add' := by
    intro M N
    exact so44ToSO55Sum_add M N
  map_smul' := by
    intro r M
    exact so44ToSO55Sum_smul r M
  map_lie' := by
    intro M N
    exact so44ToSO55Sum_bracket M N

theorem so44ToSO55SumLieHom_apply (M : Mat8) :
    so44ToSO55SumLieHom M = so44ToSO55Sum M := rfl

theorem so44ToSO55Sum_injective :
    Function.Injective so44ToSO55Sum := by
  intro M N h
  ext i j
  have h' := congrArg
    (fun K : Mat10Sum => K (Sum.inl i) (Sum.inl j)) h
  exact h'

theorem so44ToSO55SumLieHom_injective :
    Function.Injective so44ToSO55SumLieHom := by
  intro M N h
  exact so44ToSO55Sum_injective h

theorem so44ToSO55_eq_reindex (M : Mat8) :
    so44ToSO55 M = Matrix.reindex fin10Equiv.symm fin10Equiv.symm (so44ToSO55Sum M) := by
  ext i j
  dsimp [so44ToSO55, Matrix.reindex, so44ToSO55Sum, fromBlocks]
  rcases fin10Equiv i with a | a <;> rcases fin10Equiv j with b | b <;> rfl

def eta55LeviMat10 : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.reindex fin10Equiv.symm fin10Equiv.symm eta55Levi

theorem so44ToSO55_preserves_etaSkew (M : Mat8) (hM : IsEtaSkew eta44 M) :
    IsEtaSkew eta55LeviMat10 (so44ToSO55 M) := by
  dsimp [IsEtaSkew, eta55LeviMat10]
  have h := so44ToSO55Sum_preserves_etaSkew M hM
  dsimp [IsEtaSkew] at h
  ext i j
  rw [so44ToSO55_eq_reindex]
  dsimp [Matrix.reindex]
  have h_entry := congrFun (congrFun h (fin10Equiv i)) (fin10Equiv j)
  have hmul1 : ((submatrix (so44ToSO55Sum M) ⇑fin10Equiv ⇑fin10Equiv)ᵀ *
      submatrix eta55Levi ⇑fin10Equiv ⇑fin10Equiv) i j =
      ((so44ToSO55Sum M)ᵀ * eta55Levi) (fin10Equiv i) (fin10Equiv j) := by
    dsimp [Matrix.mul_apply]
    have hequiv : ∑ k : Fin 10, (so44ToSO55Sum M) (fin10Equiv k) (fin10Equiv i) * eta55Levi (fin10Equiv k) (fin10Equiv j) =
                  ∑ s : Fin 8 ⊕ Fin 2, (so44ToSO55Sum M) s (fin10Equiv i) * eta55Levi s (fin10Equiv j) := by
      exact (fin10Equiv.sum_comp (fun s => (so44ToSO55Sum M) s (fin10Equiv i) * eta55Levi s (fin10Equiv j)))
    exact hequiv
  have hmul2 : (submatrix eta55Levi ⇑fin10Equiv ⇑fin10Equiv *
      submatrix (so44ToSO55Sum M) ⇑fin10Equiv ⇑fin10Equiv) i j =
      (eta55Levi * (so44ToSO55Sum M)) (fin10Equiv i) (fin10Equiv j) := by
    dsimp [Matrix.mul_apply]
    have hequiv : ∑ k : Fin 10, eta55Levi (fin10Equiv i) (fin10Equiv k) * (so44ToSO55Sum M) (fin10Equiv k) (fin10Equiv j) =
                  ∑ s : Fin 8 ⊕ Fin 2, eta55Levi (fin10Equiv i) s * (so44ToSO55Sum M) s (fin10Equiv j) := by
      exact (fin10Equiv.sum_comp (fun s => eta55Levi (fin10Equiv i) s * (so44ToSO55Sum M) s (fin10Equiv j)))
    exact hequiv
  change ((submatrix (so44ToSO55Sum M) ⇑fin10Equiv ⇑fin10Equiv)ᵀ * submatrix eta55Levi ⇑fin10Equiv ⇑fin10Equiv) i j +
         (submatrix eta55Levi ⇑fin10Equiv ⇑fin10Equiv * submatrix (so44ToSO55Sum M) ⇑fin10Equiv ⇑fin10Equiv) i j = 0
  rw [hmul1, hmul2]
  exact h_entry

theorem wittIndex_fin8Equiv (i : Fin 8) :
    SplitOctonionDerivationWittBlockRealization.wittIndex (fin8Equiv i) = i := by
  ext
  dsimp [fin8Equiv, SplitOctonionDerivationWittBlockRealization.wittIndex]
  split_ifs with h
  · rfl
  · dsimp; omega

theorem canonicalDerivationFinMatrix_isEtaSkew (D : SplitOctonionDerivationWittOrthogonalBridge.Derivation) :
    IsEtaSkew eta44 (SplitOctonionDerivationWittBlockRealization.canonicalDerivationFinMatrix D) := by
  dsimp [IsEtaSkew, eta44, SplitOctonionDerivationWittBlockRealization.canonicalDerivationFinMatrix]
  have h := SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix_eta_skew D
  ext i j
  have h_entry := congrFun (congrFun h (fin8Equiv i)) (fin8Equiv j)
  have hmul1 : ((LinearMap.toMatrix' (SplitOctonionDerivationWittBlockRealization.transportedDerivation D))ᵀ *
      submatrix etaW ⇑fin8Equiv ⇑fin8Equiv) i j =
      ((SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix D)ᵀ * etaW) (fin8Equiv i) (fin8Equiv j) := by
    dsimp [Matrix.mul_apply]
    have hequiv : ∑ k : Fin 8, (LinearMap.toMatrix' (SplitOctonionDerivationWittBlockRealization.transportedDerivation D)) k i * etaW (fin8Equiv k) (fin8Equiv j) =
                  ∑ s : Fin 4 ⊕ Fin 4, (SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix D) s (fin8Equiv i) * etaW s (fin8Equiv j) := by
      rw [← fin8Equiv.sum_comp (fun s => (SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix D) s (fin8Equiv i) * etaW s (fin8Equiv j))]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix, LinearMap.toMatrix', LinearMap.toMatrix]
      rw [wittIndex_fin8Equiv, wittIndex_fin8Equiv]
    exact hequiv
  have hmul2 : (submatrix etaW ⇑fin8Equiv ⇑fin8Equiv *
      LinearMap.toMatrix' (SplitOctonionDerivationWittBlockRealization.transportedDerivation D)) i j =
      (etaW * (SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix D)) (fin8Equiv i) (fin8Equiv j) := by
    dsimp [Matrix.mul_apply]
    have hequiv : ∑ k : Fin 8, etaW (fin8Equiv i) (fin8Equiv k) * (LinearMap.toMatrix' (SplitOctonionDerivationWittBlockRealization.transportedDerivation D)) k j =
                  ∑ s : Fin 4 ⊕ Fin 4, etaW (fin8Equiv i) s * (SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix D) s (fin8Equiv j) := by
      rw [← fin8Equiv.sum_comp (fun s => etaW (fin8Equiv i) s * (SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix D) s (fin8Equiv j))]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [SplitOctonionDerivationWittBlockRealization.canonicalDerivationMatrix, LinearMap.toMatrix', LinearMap.toMatrix]
      rw [wittIndex_fin8Equiv, wittIndex_fin8Equiv]
    exact hequiv
  change ((LinearMap.toMatrix' (SplitOctonionDerivationWittBlockRealization.transportedDerivation D))ᵀ * submatrix etaW ⇑fin8Equiv ⇑fin8Equiv) i j +
         (submatrix etaW ⇑fin8Equiv ⇑fin8Equiv * LinearMap.toMatrix' (SplitOctonionDerivationWittBlockRealization.transportedDerivation D)) i j = 0
  rw [hmul1, hmul2]
  exact h_entry

end InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge
