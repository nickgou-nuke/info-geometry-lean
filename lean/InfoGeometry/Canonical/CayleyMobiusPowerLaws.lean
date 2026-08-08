import Mathlib.Tactic
import InfoGeometry.Canonical.PrimeHurwitzLimit

noncomputable section

namespace InfoGeometry.Canonical.CayleyMobiusPowerLaws

/--
An explicit involutive-power lemma with no property/socket fields:
an involutive map `f` is periodic of period `2` pointwise.
-/
theorem iterate_two_of_involution
    {α : Type*} (f : α → α) (hff : ∀ x : α, f (f x) = x)
    (x : α) : f^[2] x = x := by
  simp [Nat.iterate, hff]

/-- Möbius-reflection on `ℂ`: `s ↦ 1 - s` is an involution. -/
@[simp]
theorem reflection_iterate_two (s : ℂ) : (fun z : ℂ => 1 - z)^[2] s = s := by
  simp

/-- Complex inversion is an involution. -/
@[simp]
theorem inversion_iterate_two (z : ℂ) : (fun z : ℂ => z⁻¹)^[2] z = z := by
  simp

/-- Even iterates for a map with `f ∘ f = id` pointwise. -/
theorem iterate_even_of_involution
    {α : Type*} (f : α → α)
    (hff : ∀ x : α, f (f x) = x)
    (n : ℕ) (x : α) : f^[2 * n] x = x := by
  induction n with
  | zero => simp [Nat.iterate]
  | succ n ih =>
      have hdecomp := congrArg (fun F => F x) (Function.iterate_add f 2 (2 * n))
      have hdecomp' : f^[2 * n + 2] x = f^[2] (f^[2 * n] x) := by
        simpa [Function.comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdecomp
      calc
        f^[2 * (n + 1)] x = f^[2 * n + 2] x := by
          simp [Nat.mul_succ, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = f^[2] (f^[2 * n] x) := hdecomp'
        _ = f^[2 * n] x := by simp [Nat.iterate, hff]
        _ = x := ih

/-- Odd iterates for an involution map. -/
theorem iterate_odd_of_involution
    {α : Type*} (f : α → α)
    (hff : ∀ x : α, f (f x) = x)
    (n : ℕ) (x : α) : f^[2 * n + 1] x = f x := by
  have hdecomp := congrArg (fun F => F x) (Function.iterate_add f 1 (2 * n))
  have hdecomp' : f^[1 + 2 * n] x = f^[1] (f^[2 * n] x) := by
    simpa [Function.comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdecomp
  calc
    f^[2 * n + 1] x = f^[1 + 2 * n] x := by
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    _ = f^[1] (f^[2 * n] x) := hdecomp'
    _ = f (f^[2 * n] x) := rfl
    _ = f x := by simpa using congrArg f (iterate_even_of_involution f hff n x)

/-- Reflection map with explicit even iterate parity. -/
theorem reflection_iterate_even (n : ℕ) (s : ℂ) : (fun z : ℂ => 1 - z)^[2 * n] s = s := by
  simpa using (iterate_even_of_involution (f := fun z : ℂ => 1 - z) (by intro x; ring_nf) n s)

/-- Reflection map with explicit odd iterate parity. -/
theorem reflection_iterate_odd (n : ℕ) (s : ℂ) : (fun z : ℂ => 1 - z)^[2 * n + 1] s = 1 - s := by
  simpa using (iterate_odd_of_involution (f := fun z : ℂ => 1 - z) (by intro x; ring_nf) n s)

/-- Affine-reflection map parity around `a`: `f z = a - z`. -/
theorem affine_reflection_iterate_even (a s : ℂ) (n : ℕ) :
    (fun z : ℂ => a - z)^[2 * n] s = s := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (iterate_even_of_involution (f := fun z : ℂ => a - z) (by intro x; ring_nf) n s)

/-- Affine-reflection map parity around `a`: odd iterate gives one reflection. -/
theorem affine_reflection_iterate_odd (a s : ℂ) (n : ℕ) :
    (fun z : ℂ => a - z)^[2 * n + 1] s = a - s := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (iterate_odd_of_involution (f := fun z : ℂ => a - z) (by intro x; ring_nf) n s)

/-- Inversion map even iterate parity. -/
theorem inversion_iterate_even (n : ℕ) (z : ℂ) : (fun w : ℂ => w⁻¹)^[2 * n] z = z := by
  simpa using
    (iterate_even_of_involution (f := fun w : ℂ => w⁻¹) (by intro w; simp) n z)

/-- Inversion map odd iterate parity. -/
theorem inversion_iterate_odd (n : ℕ) (z : ℂ) : (fun w : ℂ => w⁻¹)^[2 * n + 1] z = z⁻¹ := by
  simpa using
    (iterate_odd_of_involution (f := fun w : ℂ => w⁻¹) (by intro w; simp) n z)

/-- Partition readout inherited by inversion invariance in the Cayley variable. -/
theorem cayley_partition_invariant_under_reflection
    (Z : ℂ → ℂ)
    (hZ : ∀ z : ℂ, Z (z⁻¹) = Z z)
    (s : ℂ)
    (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    Z (PrimeHurwitzLimit.cayley (1 - s)) = Z (PrimeHurwitzLimit.cayley s) := by
  rw [PrimeHurwitzLimit.CayleyCriticalWitness.cayley_reflection_to_inversion s hs0 hs1]
  exact hZ (PrimeHurwitzLimit.cayley s)

end InfoGeometry.Canonical.CayleyMobiusPowerLaws
