import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

open CategoryTheory

noncomputable section

namespace InfoGeometry.Topology

variable (R : Type*) [CommRing R] [Algebra ℝ R]
abbrev V (n : ℕ) : Type := Fin (2 * n) → ℝ
variable (Q : ∀ n, QuadraticForm ℝ (V n))
variable (h_Q_compat : ∀ (m n : ℕ) (h : m ≤ n) (x : V m), 
  Q n (fun i => if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) = Q m x)

def V_inclusion_mn (m n : ℕ) (h : m ≤ n) : Q m →qᵢ Q n :=
  { toFun := fun x i => 
      if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0
    map_add' := by 
      intro x y
      ext i
      change (if h_lim : i.val < 2 * m then (x + y) ⟨i.val, h_lim⟩ else 0) = 
             (if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) + 
             (if h_lim : i.val < 2 * m then y ⟨i.val, h_lim⟩ else 0)
      split_ifs with h_lim
      · rfl
      · exact (add_zero (0 : ℝ)).symm
    map_smul' := by 
      intro c x
      ext i
      change (if h_lim : i.val < 2 * m then (c • x) ⟨i.val, h_lim⟩ else 0) = 
             c • (if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0)
      split_ifs with h_lim
      · rfl
      · exact (smul_zero c).symm
    map_app' := by intro x; exact h_Q_compat m n h x }

def Cl (n : ℕ) : Type := CliffordAlgebra (Q n)
instance (n : ℕ) : Ring (Cl Q n) := by dsimp [Cl]; infer_instance
instance (n : ℕ) : Algebra ℝ (Cl Q n) := by dsimp [Cl]; infer_instance

def Cl_bonding_map_mn (m n : ℕ) (h : m ≤ n) : Cl Q m →ₐ[ℝ] Cl Q n :=
  CliffordAlgebra.map (V_inclusion_mn Q h_Q_compat m n h)

abbrev J : Type := ℕ

def CliffordTowerFunctor : J ⥤ AlgCat ℝ where
  obj n := AlgCat.of ℝ (Cl Q n)
  map {m n} h := AlgCat.ofHom (Cl_bonding_map_mn Q h_Q_compat m n h.le)
  map_id n := sorry
  map_comp {l m n} h_lm h_mn := sorry

end InfoGeometry.Topology
