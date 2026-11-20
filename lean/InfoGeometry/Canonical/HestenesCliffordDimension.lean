/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.HestenesClPlus14
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Real dimensions of the native spacetime Clifford algebra

The existing exterior-basis and parity arguments are owned here so that real
Clifford consumers do not need the Pauli representation. Declaration names
are preserved for existing users.
-/

noncomputable section
namespace HestenesEvenPauliEquiv
open scoped DirectSum
open HestenesCl14

def sigmaPowersetCardFin4Equiv :
    (Σ n : ℕ, Set.powersetCard (Fin 4) n) ≃ Finset (Fin 4) where
  toFun x := x.2.1
  invFun s := ⟨s.card, ⟨s, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨n, s, hs⟩
    subst n
    rfl
  right_inv _ := rfl

def exteriorAlgebraV14Basis :
    Module.Basis (Finset (Fin 4)) ℝ (ExteriorAlgebra ℝ V14) := by
  let homogeneousBasis :
      Module.Basis (Σ n : ℕ, Set.powersetCard (Fin 4) n) ℝ
        (⨁ n : ℕ, ExteriorAlgebra.exteriorPower ℝ n V14) :=
    DFinsupp.basis (fun n => (Pi.basisFun ℝ (Fin 4)).exteriorPower n)
  let transported := homogeneousBasis.map
    (DirectSum.decomposeLinearEquiv
      (fun n : ℕ => ExteriorAlgebra.exteriorPower ℝ n V14)).symm
  exact transported.reindex sigmaPowersetCardFin4Equiv

def cliffordAlgebra14Basis : Module.Basis (Finset (Fin 4)) ℝ Cl14 :=
  exteriorAlgebraV14Basis.map (CliffordAlgebra.equivExterior Q14).symm

theorem cliffordAlgebra14_finrank : Module.finrank ℝ Cl14 = 16 := by
  rw [Module.finrank_eq_card_basis cliffordAlgebra14Basis]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

noncomputable instance : FiniteDimensional ℝ Cl14 :=
  cliffordAlgebra14Basis.finiteDimensional_of_finite

/-- Right multiplication by the time-like generator exchanges the even and
odd Clifford summands. -/
def evenOddLinearEquiv :
    CliffordAlgebra.evenOdd Q14 0 ≃ₗ[ℝ] CliffordAlgebra.evenOdd Q14 1 where
  toFun x := ⟨x.1 * gamma 0, by
    simpa using SetLike.mul_mem_graded x.2 gamma_zero_mem_odd⟩
  invFun x := ⟨x.1 * gamma 0, by
    have h := SetLike.mul_mem_graded x.2 gamma_zero_mem_odd
    have h1 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h1] at h
    exact h⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_add' x y := by
    apply Subtype.ext
    simp [add_mul]
  map_smul' c x := by
    apply Subtype.ext
    simp

theorem clPlus14_finrank : Module.finrank ℝ ClPlus14 = 8 := by
  change Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 0) = 8
  have hsum : Module.finrank ℝ Cl14 =
      Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 0) +
        Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 1) := by
    rw [← Module.finrank_prod]
    exact LinearEquiv.finrank_eq
      (Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl Q14)).symm
  have heq : Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 0) =
      Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 1) :=
    LinearEquiv.finrank_eq evenOddLinearEquiv
  rw [cliffordAlgebra14_finrank, ← heq] at hsum
  omega

end HestenesEvenPauliEquiv
