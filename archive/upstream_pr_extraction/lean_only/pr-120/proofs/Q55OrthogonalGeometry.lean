import proofs.RealO55CartanDieudonneStep
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # Nondegenerate orthogonal geometry of the real split `(5,5)` form -/

noncomputable section
namespace Q55OrthogonalGeometry

open BigOperators
open Clifford55
open V55Fin10Coordinates
open SplitOctonionTKK55

abbrev B55 : LinearMap.BilinForm ℝ V55 := QuadraticMap.associated Q55

theorem associated_Q55 (x y : V55) :
    B55 x y =
      (∑ i : Fin 5, x.1 i * y.1 i) -
        (∑ i : Fin 5, x.2 i * y.2 i) := by
  rw [QuadraticMap.associated_apply]
  simp only [Q55_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  simp_rw [add_sq]
  simp only [Finset.sum_add_distrib]
  have hp : (∑ i : Fin 5, 2 * x.1 i * y.1 i) =
      2 * ∑ i : Fin 5, x.1 i * y.1 i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hn : (∑ i : Fin 5, 2 * x.2 i * y.2 i) =
      2 * ∑ i : Fin 5, x.2 i * y.2 i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hp, hn]
  norm_num [invOf_eq_inv]
  ring

@[simp] theorem B55_self (x : V55) : B55 x x = Q55 x := by
  rw [associated_Q55, Q55_apply]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem B55_isSymm : B55.IsSymm := by
  exact ⟨QuadraticMap.associated_isSymm ℝ Q55⟩

theorem B55_separatingLeft : B55.SeparatingLeft := by
  intro x hx
  apply Prod.ext
  · funext i
    have hi := hx (e_pos i)
    rw [associated_Q55] at hi
    simpa [e_pos] using hi
  · funext i
    have hi := hx (f_neg i)
    rw [associated_Q55] at hi
    have : -x.2 i = 0 := by simpa [f_neg] using hi
    exact neg_eq_zero.mp this

theorem B55_nondegenerate : B55.Nondegenerate := by
  exact LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft B55_separatingLeft

theorem B55_coordinates (x y : V55) :
    B55 x y = dotProduct (v55Fin10Equiv x) (eta55.mulVec (v55Fin10Equiv y)) := by
  rw [← associated_Qcoord55]
  simp [Qcoord55, QuadraticMap.associated_comp, B55]

theorem fin10Basis55_orthogonal {i j : Fin 10} (hij : i ≠ j) :
    B55 (fin10Basis55 i) (fin10Basis55 j) = 0 := by
  rw [B55_coordinates]
  simp [v55Fin10Equiv, fin10Basis55.equivFun_self, eta55, dotProduct,
    Matrix.mulVec, hij]

theorem fin10Basis55_anisotropic (i : Fin 10) :
    Q55 (fin10Basis55 i) ≠ 0 := by
  rw [Q55_eq_eta55]
  simp [v55Fin10Equiv, eta55, dotProduct, Matrix.mulVec]
  split_ifs <;> norm_num

/-- A proper subspace misses an anisotropic vector from the fixed coordinate
basis.  This is the split-signature replacement for choosing an arbitrary
nonzero vector in the positive-definite Cartan--Dieudonne proof. -/
theorem exists_anisotropic_basis_not_mem (W : Submodule ℝ V55) (hW : W ≠ ⊤) :
    ∃ i : Fin 10, fin10Basis55 i ∉ W ∧ Q55 (fin10Basis55 i) ≠ 0 := by
  by_contra hn
  apply hW
  rw [Submodule.eq_top_iff_forall_basis_mem fin10Basis55]
  intro i
  by_contra hi
  exact hn ⟨i, hi, fin10Basis55_anisotropic i⟩

end Q55OrthogonalGeometry
end noncomputable section
