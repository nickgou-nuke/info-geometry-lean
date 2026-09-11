import InfoGeometry.Algebra.Zorn.G2HexagonIncidence
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Incidence-preserving permutations on the finite G₂ flag certificate

This is the exact transport interface between a verified permutation of the
63 point/line indices and the 189 incident flags.  It does not assert that a
given automorphism preserves the exported certificate; that is a separate
carrier-alignment obligation.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction

open InfoGeometry.Algebra.Zorn.G2HexagonIncidence

abbrev Flag := G2HexagonIncidence.Flag G2HexagonIncidence.parabolicIncidenceData

def PreservesIncidence (π : Equiv.Perm HexPoint) : Prop :=
  ∀ p l, p ∈ G2HexagonIncidence.parabolicIncidenceData.linePoints l ↔
    π p ∈ G2HexagonIncidence.parabolicIncidenceData.linePoints (π l)

def flagMap (π : Equiv.Perm HexPoint) (hπ : PreservesIncidence π) : Flag → Flag
  | ⟨p, ⟨l, h⟩⟩ => ⟨π p, ⟨π l, (hπ p l).mp h⟩⟩

theorem PreservesIncidence.one : PreservesIncidence (1 : Equiv.Perm HexPoint) := by
  intro p l
  rfl

theorem PreservesIncidence.mul {π₁ π₂ : Equiv.Perm HexPoint}
    (hπ₁ : PreservesIncidence π₁) (hπ₂ : PreservesIncidence π₂) :
    PreservesIncidence (π₁ * π₂) := by
  intro p l
  exact (hπ₂ p l).trans (hπ₁ (π₂ p) (π₂ l))



theorem PreservesIncidence.symm {π : Equiv.Perm HexPoint} (hπ : PreservesIncidence π) :
    PreservesIncidence π.symm := by
  intro p l
  have h := (hπ (π.symm p) (π.symm l)).symm
  simpa using h

def flagMapInv (π : Equiv.Perm HexPoint) (hπ : PreservesIncidence π) : Flag → Flag :=
  flagMap π.symm hπ.symm

theorem flagMap_congr {π₁ π₂ : Equiv.Perm HexPoint} (h : π₁ = π₂)
    (hπ₁ : PreservesIncidence π₁) (hπ₂ : PreservesIncidence π₂) :
    flagMap π₁ hπ₁ = flagMap π₂ hπ₂ := by
  subst h
  rfl

theorem flagMap_one (f : Flag) :
    flagMap 1 PreservesIncidence.one f = f := by
  cases f
  rfl

theorem flagMap_mul (π₁ π₂ : Equiv.Perm HexPoint)
    (hπ₁ : PreservesIncidence π₁) (hπ₂ : PreservesIncidence π₂) (f : Flag) :
    flagMap (π₁ * π₂) (PreservesIncidence.mul hπ₁ hπ₂) f =
      flagMap π₁ hπ₁ (flagMap π₂ hπ₂ f) := by
  cases f
  rfl

theorem flagMap_left_inv (π : Equiv.Perm HexPoint) (hπ : PreservesIncidence π) :
    Function.LeftInverse (flagMapInv π hπ) (flagMap π hπ) := by
  intro f
  dsimp [flagMapInv]
  have h_mul := (flagMap_mul π.symm π hπ.symm hπ f).symm
  have h_inv : π.symm * π = 1 := inv_mul_cancel π
  rw [h_mul]
  have h_eq := flagMap_congr h_inv (PreservesIncidence.mul hπ.symm hπ) PreservesIncidence.one
  rw [congrFun h_eq f]
  exact flagMap_one f

theorem flagMap_right_inv (π : Equiv.Perm HexPoint) (hπ : PreservesIncidence π) :
    Function.RightInverse (flagMapInv π hπ) (flagMap π hπ) := by
  intro f
  dsimp [flagMapInv]
  have h_mul := (flagMap_mul π π.symm hπ hπ.symm f).symm
  have h_inv : π * π.symm = 1 := mul_inv_cancel π
  rw [h_mul]
  have h_eq := flagMap_congr h_inv (PreservesIncidence.mul hπ hπ.symm) PreservesIncidence.one
  rw [congrFun h_eq f]
  exact flagMap_one f

noncomputable def flagPerm (π : Equiv.Perm HexPoint) (hπ : PreservesIncidence π) :
    Equiv.Perm Flag where
  toFun := flagMap π hπ
  invFun := flagMapInv π hπ
  left_inv := flagMap_left_inv π hπ
  right_inv := flagMap_right_inv π hπ

theorem flagPerm_apply (π : Equiv.Perm HexPoint) (hπ : PreservesIncidence π)
    (f : Flag) : flagPerm π hπ f = flagMap π hπ f := by
  rfl

end InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
