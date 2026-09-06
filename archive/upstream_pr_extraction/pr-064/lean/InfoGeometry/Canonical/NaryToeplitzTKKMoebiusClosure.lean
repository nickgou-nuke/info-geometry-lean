import Mathlib

namespace InfoGeometry.Canonical

/-!
This file records consequences of an explicitly supplied `sl₂` action.  The
operators and their relations are hypotheses of the theorems, not fields of a
purported TKK or Toeplitz construction.  A genuine TKK realization belongs to
the native Jordan-pair owner.
-/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def sl2DiracPlus (e_plus e_minus : V →ₗ[ℚ] V) : V →ₗ[ℚ] V :=
  e_plus + e_minus

def sl2DiracMinus (e_plus e_minus : V →ₗ[ℚ] V) : V →ₗ[ℚ] V :=
  e_plus - e_minus

theorem sl2_sum_difference_commutator
    (e_plus e_minus h : V →ₗ[ℚ] V)
    (hbracket : ∀ x, e_plus (e_minus x) - e_minus (e_plus x) = h x)
    (x : V) :
    sl2DiracPlus e_plus e_minus (sl2DiracMinus e_plus e_minus x) -
        sl2DiracMinus e_plus e_minus (sl2DiracPlus e_plus e_minus x) =
      -2 • h x := by
  calc
    sl2DiracPlus e_plus e_minus (sl2DiracMinus e_plus e_minus x) -
        sl2DiracMinus e_plus e_minus (sl2DiracPlus e_plus e_minus x) =
      (e_plus (e_plus x) - e_plus (e_minus x)) +
        (e_minus (e_plus x) - e_minus (e_minus x)) -
        ((e_plus (e_plus x) + e_plus (e_minus x)) -
          (e_minus (e_plus x) + e_minus (e_minus x))) := by
            simp only [sl2DiracPlus, sl2DiracMinus,
              LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub]
            abel
    _ = -2 • (e_plus (e_minus x) - e_minus (e_plus x)) := by module
    _ = -2 • h x := by rw [hbracket]

theorem sl2_bracket_apply_e_plus
    (e_plus e_minus h : V →ₗ[ℚ] V)
    (hbracket : ∀ x, e_plus (e_minus x) - e_minus (e_plus x) = h x)
    (x : V) :
    e_plus (e_minus (e_plus x)) - e_minus (e_plus (e_plus x)) =
      h (e_plus x) :=
  hbracket (e_plus x)

theorem sl2_relations
    (e_plus e_minus h : V →ₗ[ℚ] V)
    (h_plus : ∀ x, h (e_plus x) - e_plus (h x) = 2 • e_plus x)
    (h_minus : ∀ x, h (e_minus x) - e_minus (h x) = -2 • e_minus x)
    (hbracket : ∀ x, e_plus (e_minus x) - e_minus (e_plus x) = h x)
    (x : V) :
    h (e_plus x) - e_plus (h x) = 2 • e_plus x ∧
    h (e_minus x) - e_minus (h x) = -2 • e_minus x ∧
    e_plus (e_minus x) - e_minus (e_plus x) = h x :=
  ⟨h_plus x, h_minus x, hbracket x⟩

end InfoGeometry.Canonical
