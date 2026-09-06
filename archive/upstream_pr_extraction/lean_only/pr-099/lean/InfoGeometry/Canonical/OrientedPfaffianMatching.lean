import Mathlib

/-!
# Finite perfect matchings for an oriented Pfaffian

This file supplies the combinatorial foundation for a signed Pfaffian.  A
matching is represented by its partner involution.  No Pfaffian polynomial or
determinant identity is postulated here.
-/

namespace InfoGeometry.Canonical.OrientedPfaffianMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite perfect matching, represented by a fixed-point-free involution. -/
structure PerfectMatching where
  partner : ι → ι
  involutive : Function.Involutive partner
  fixed_free : ∀ i, partner i ≠ i

namespace PerfectMatching

variable (M : PerfectMatching (ι := ι))

theorem partner_injective : Function.Injective M.partner :=
  fun a b h => by
    calc
      a = M.partner (M.partner a) := (M.involutive a).symm
      _ = M.partner (M.partner b) := congrArg M.partner h
      _ = b := M.involutive b

theorem partner_bijective : Function.Bijective M.partner :=
  ⟨M.partner_injective, fun j => ⟨M.partner j, M.involutive j⟩⟩

/-- The partner involution as a permutation of the finite index type. -/
noncomputable def permutation : Equiv.Perm ι :=
  Equiv.ofBijective M.partner M.partner_bijective

@[simp] theorem permutation_apply (i : ι) :
    M.permutation i = M.partner i :=
  rfl

@[simp] theorem permutation_sq (i : ι) :
    M.permutation (M.permutation i) = i :=
  M.involutive i

theorem permutation_ne_self (i : ι) :
    M.permutation i ≠ i :=
  M.fixed_free i

/-! The permutation sign is the orientation sign contributed by a matching. -/

noncomputable def sign : ℝ :=
  (Equiv.Perm.sign M.permutation : ℤ)

theorem sign_sq : M.sign ^ 2 = 1 := by
  unfold sign
  have hsign : Equiv.Perm.sign M.permutation = 1 ∨
      Equiv.Perm.sign M.permutation = -1 :=
    Int.units_eq_one_or (Equiv.Perm.sign M.permutation)
  rcases hsign with h | h <;> simp [h]

end PerfectMatching

end InfoGeometry.Canonical.OrientedPfaffianMatching
