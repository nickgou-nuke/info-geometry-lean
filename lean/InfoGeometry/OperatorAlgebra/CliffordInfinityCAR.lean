import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Real.Basic
import InfoGeometry.Algebraic.SplitQuadraticForm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.CategoryTheory.Filtered.Basic

open CategoryTheory
open InfoGeometry.Algebraic.SplitSignature
open AlgCat
open IsFiltered

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-- The canonical inclusion map i_n: V_n ⟶ V_{n+1} 
  padding the two new coordinates with 0. -/
def V_inclusion (n : ℕ) : SplitModule n →ₗ[ℝ] SplitModule (n + 1) :=
  { toFun := fun v => fun i : SplitIndex (n + 1) =>
      match i with
      | Sum.inl j => 
          if h : j.val < n then v (Sum.inl ⟨j.val, by exact_mod_cast h⟩) else 0
      | Sum.inr j => 
          if h : j.val < n then v (Sum.inr ⟨j.val, by exact_mod_cast h⟩) else 0
    map_add' := by
      intro v w
      ext i
      rcases i with j | j <;> simp only [Pi.add_apply] <;> split_ifs <;> simp_all
    map_smul' := by
      intro c v
      ext i
      rcases i with j | j <;> simp only [Pi.smul_apply, RingHom.id_apply] <;> split_ifs <;> simp_all
  }

/-- The inclusion is an isometry: Q_{n+1}(i_n(x)) = Q_n(x). -/
theorem V_inclusion_is_isometry (n : ℕ) (x : SplitModule n) :
    splitQuadraticForm (n + 1) (V_inclusion n x) = splitQuadraticForm n x := by
  have h₁ : splitQuadraticForm (n + 1) (V_inclusion n x) = ∑ i : SplitIndex (n + 1), splitWeight (n + 1) i * ((V_inclusion n x) i * (V_inclusion n x) i) := by
    simp [splitQuadraticForm]
  rw [h₁]
  have h₂ : (∑ i : SplitIndex (n + 1), splitWeight (n + 1) i * ((V_inclusion n x) i * (V_inclusion n x) i)) = ∑ i : SplitIndex n, splitWeight n i * (x i * x i) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    congr 1
    · rw [Fin.sum_univ_castSucc]
      simp [V_inclusion, splitWeight, SplitIndex]
    · rw [Fin.sum_univ_castSucc]
      simp [V_inclusion, splitWeight, SplitIndex]
  rw [h₂]
  simp [splitQuadraticForm]

def Cl_bonding_map (n : ℕ) : Cl_nn n →ₐ[ℝ] Cl_nn (n + 1) :=
  CliffordAlgebra.lift (splitQuadraticForm n)
    ⟨CliffordAlgebra.ι (splitQuadraticForm (n + 1)) ∘ₗ V_inclusion n,
     by intro x
        dsimp
        rw [CliffordAlgebra.ι_sq_scalar, V_inclusion_is_isometry]⟩

def Cl_bonding_map_of_le {m n : ℕ} (h : m ≤ n) : Cl_nn m →ₐ[ℝ] Cl_nn n :=
  Nat.leRecOn h (fun {k} g => (Cl_bonding_map k).comp g) (AlgHom.id ℝ (Cl_nn m))

theorem Cl_bonding_map_of_le_self {n : ℕ} (h : n ≤ n) :
    Cl_bonding_map_of_le h = AlgHom.id ℝ (Cl_nn n) := by
  dsimp [Cl_bonding_map_of_le]
  rw [Nat.leRecOn_self]

theorem Cl_bonding_map_of_le_comp {m n k : ℕ} (h1 : m ≤ n) (h2 : n ≤ k) :
    Cl_bonding_map_of_le (le_trans h1 h2) = (Cl_bonding_map_of_le h2).comp (Cl_bonding_map_of_le h1) := by
  dsimp [Cl_bonding_map_of_le]
  induction' h2 with k' h2 ih
  · rw [Nat.leRecOn_self]
    ext x
    rfl
  · rw [Nat.leRecOn_succ (le_trans h1 h2)]
    rw [Nat.leRecOn_succ h2]
    rw [ih]
    ext x
    rfl

def Cl_functor : ℕ ⥤ RingCat where
  obj n := RingCat.of (Cl_nn n)
  map {m n} h := RingCat.ofHom (Cl_bonding_map_of_le (leOfHom h)).toRingHom
  map_id := by
    intro n
    ext x
    change Cl_bonding_map_of_le (le_refl n) x = x
    rw [Cl_bonding_map_of_le_self]
    rfl
  map_comp := by
    intro m n k f g
    ext x
    change Cl_bonding_map_of_le (le_trans (leOfHom f) (leOfHom g)) x = Cl_bonding_map_of_le (leOfHom g) (Cl_bonding_map_of_le (leOfHom f) x)
    rw [Cl_bonding_map_of_le_comp]
    rfl

def CliffordInfinity : RingCat := 
  Limits.colimit Cl_functor

end InfoGeometry.OperatorAlgebra
