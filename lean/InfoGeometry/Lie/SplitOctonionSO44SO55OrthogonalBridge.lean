import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge

open Matrix
open InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Mat8 := Matrix (Fin 8) (Fin 8) ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
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

end InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge
