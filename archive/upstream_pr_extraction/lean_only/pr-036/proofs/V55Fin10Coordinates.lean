import proofs.RealPin55QuadraticRepresentation
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Coordinates for the split real carrier `V55` -/

noncomputable section
namespace V55Fin10Coordinates

open Clifford55
open SplitOctonionTKK55

def sumBasis55 : Module.Basis (Fin 5 ⊕ Fin 5) ℝ V55 :=
  (Pi.basisFun ℝ (Fin 5)).prod (Pi.basisFun ℝ (Fin 5))

def fin10Basis55 : Module.Basis (Fin 10) ℝ V55 :=
  sumBasis55.reindex finSumFinEquiv

def v55Fin10Equiv : V55 ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  fin10Basis55.equivFun

@[simp] theorem v55Fin10Equiv_apply_lt (v : V55) (i : Fin 5) :
    v55Fin10Equiv v (Fin.castAdd 5 i) = v.1 i := by
  change sumBasis55.repr v
    (finSumFinEquiv.symm (Fin.castAdd 5 i)) = v.1 i
  rw [finSumFinEquiv_symm_apply_castAdd]
  simp [sumBasis55]

@[simp] theorem v55Fin10Equiv_apply_ge (v : V55) (i : Fin 5) :
    v55Fin10Equiv v (Fin.natAdd 5 i) = v.2 i := by
  change sumBasis55.repr v
    (finSumFinEquiv.symm (Fin.natAdd 5 i)) = v.2 i
  rw [finSumFinEquiv_symm_apply_natAdd]
  simp [sumBasis55]

theorem Q55_eq_eta55 (v : V55) :
    Q55 v = dotProduct (v55Fin10Equiv v) (eta55.mulVec (v55Fin10Equiv v)) := by
  simp [Q55_apply, eta55, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add (a := 5) (b := 5)]
  simp_rw [v55Fin10Equiv_apply_lt, v55Fin10Equiv_apply_ge]
  simp [pow_two]
  ring_nf

def Qcoord55 : QuadraticForm ℝ (Fin 10 → ℝ) :=
  Q55.comp v55Fin10Equiv.symm

@[simp] theorem Qcoord55_apply (x : Fin 10 → ℝ) :
    Qcoord55 x = dotProduct x (eta55.mulVec x) := by
  simpa [Qcoord55] using Q55_eq_eta55 (v55Fin10Equiv.symm x)

theorem eta55_bilinear_add (x y : Fin 10 → ℝ) :
    dotProduct (x + y) (eta55.mulVec (x + y)) =
      dotProduct x (eta55.mulVec x) + dotProduct y (eta55.mulVec y) +
        2 * dotProduct x (eta55.mulVec y) := by
  classical
  simp [dotProduct, Matrix.mulVec, eta55]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

theorem associated_Qcoord55 (x y : Fin 10 → ℝ) :
    QuadraticMap.associated Qcoord55 x y = dotProduct x (eta55.mulVec y) := by
  rw [QuadraticMap.associated_apply]
  simp only [Qcoord55_apply]
  rw [eta55_bilinear_add]
  norm_num
  ring

theorem Qcoord55_toMatrix : Qcoord55.toMatrix' = eta55 := by
  classical
  ext i j
  rw [QuadraticMap.toMatrix', LinearMap.toMatrix₂'_apply,
    associated_Qcoord55]
  simp [dotProduct, Matrix.mulVec, eta55, Pi.single_apply]
  split_ifs <;> subst_vars <;> simp_all

end V55Fin10Coordinates
end noncomputable section
