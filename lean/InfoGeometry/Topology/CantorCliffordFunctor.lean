import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
variable (h_Q_compat : ∀ (m n : ℕ) (_h : m ≤ n) (x : V m), 
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
  map_id n := by
    ext x
    change Cl_bonding_map_mn Q h_Q_compat n n (le_rfl : n ≤ n) x = x
    have h_id : V_inclusion_mn Q h_Q_compat n n (le_rfl : n ≤ n) = QuadraticMap.Isometry.id (Q n) := by
      ext v i
      change (if h_lim : i.1 < 2 * n then v ⟨i.1, h_lim⟩ else 0) = v i
      simp [i.2]
    rw [Cl_bonding_map_mn, h_id, CliffordAlgebra.map_id]
    rfl
  map_comp {l m n} h_lm h_mn := by
    ext x
    change
      Cl_bonding_map_mn Q h_Q_compat l n (le_trans h_lm.le h_mn.le) x =
        ((Cl_bonding_map_mn Q h_Q_compat m n h_mn.le).comp
          (Cl_bonding_map_mn Q h_Q_compat l m h_lm.le)) x
    have h_comp :
        (V_inclusion_mn Q h_Q_compat m n h_mn.le).comp (V_inclusion_mn Q h_Q_compat l m h_lm.le) =
          V_inclusion_mn Q h_Q_compat l n (le_trans h_lm.le h_mn.le) := by
      ext v i
      by_cases hi : i.1 < 2 * l
      · have him : i.1 < 2 * m := by
          exact lt_of_lt_of_le hi (Nat.mul_le_mul_left 2 h_lm.le)
        change
          (if hmn : i.1 < 2 * m then (if hlm : i.1 < 2 * l then v ⟨i.1, hlm⟩ else 0) else 0) =
            if hln : i.1 < 2 * l then v ⟨i.1, hln⟩ else 0
        simp [hi, him]
      · by_cases him : i.1 < 2 * m
        · change
            (if hmn : i.1 < 2 * m then (if hlm : i.1 < 2 * l then v ⟨i.1, hlm⟩ else 0) else 0) =
              if hln : i.1 < 2 * l then v ⟨i.1, hln⟩ else 0
          simp [hi, him]
        · change
            (if hmn : i.1 < 2 * m then (if hlm : i.1 < 2 * l then v ⟨i.1, hlm⟩ else 0) else 0) =
              if hln : i.1 < 2 * l then v ⟨i.1, hln⟩ else 0
          simp [hi, him]
    rw [Cl_bonding_map_mn, Cl_bonding_map_mn, Cl_bonding_map_mn, ← h_comp,
      CliffordAlgebra.map_comp_map]

end InfoGeometry.Topology
