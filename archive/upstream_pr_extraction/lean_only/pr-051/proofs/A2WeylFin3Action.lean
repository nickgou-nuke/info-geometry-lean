import Mathlib

/-!
# Direct finite permutation realization of the `A₂` Weyl group

The generators act first on `Fin 3`.  This owner proves the finite
permutation relations and the fact that the generated subgroup is all of
`Equiv.Perm (Fin 3)`.  No geometric or topological quotient is asserted.
-/

namespace A2WeylFin3Action

abbrev WeylA2 := Equiv.Perm (Fin 3)

def rho3 : WeylA2 := Equiv.swap 0 1
def shiftC3 : WeylA2 := Equiv.swap 0 1 * Equiv.swap 1 2

theorem rho3_sq : rho3 * rho3 = 1 := by
  ext x
  fin_cases x <;> native_decide

theorem shiftC3_cube : shiftC3 * shiftC3 * shiftC3 = 1 := by
  ext x
  fin_cases x <;> native_decide

theorem rho3_shiftC3_rho3 :
    rho3 * shiftC3 * rho3 = shiftC3⁻¹ := by
  ext x
  fin_cases x <;> native_decide

def a2WeylSubgroup : Subgroup WeylA2 :=
  Subgroup.closure {rho3, shiftC3}

theorem rho3_mem_a2WeylSubgroup : rho3 ∈ a2WeylSubgroup := by
  exact Subgroup.subset_closure
    (Set.mem_insert_iff.mpr (Or.inl rfl))

theorem shiftC3_mem_a2WeylSubgroup : shiftC3 ∈ a2WeylSubgroup := by
  exact Subgroup.subset_closure
    (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton shiftC3)))

/-- The two displayed generators generate the full permutation group on the
three `A₂` coordinates. -/
theorem a2WeylSubgroup_eq_top : a2WeylSubgroup = ⊤ := by
  have hcycle : Equiv.Perm.IsCycle shiftC3 := by
    have heq : shiftC3 = Equiv.swap 0 2 * Equiv.swap 0 1 := by
      ext x
      fin_cases x <;> decide
    rw [heq]
    exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (by decide) (by decide) (by decide)).isCycle
  have hsupp : shiftC3.support = Finset.univ := by
    native_decide
  have h := Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupp (0 : Fin 3)
  have hzero : shiftC3 0 = (1 : Fin 3) := by native_decide
  rw [hzero] at h
  simpa [a2WeylSubgroup, rho3, Set.pair_comm] using h

end A2WeylFin3Action
