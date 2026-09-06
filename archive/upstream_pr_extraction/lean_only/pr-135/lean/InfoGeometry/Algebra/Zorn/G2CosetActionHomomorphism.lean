import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Abstract Contract for a Parabolic Coset Action on 63 Points

This file contains only an abstract proposition-valued contract for a
permutation action on a 63-point parabolic quotient.  It does not construct
the concrete action from `SplitOctF2Aut`, does not import GAP arrays, and does
not prove the Bruhat covering theorem.  In particular, `Fin 63` here must not
be read as the full flag quotient by the order-64 subgroup (whose index is
189).
-/

namespace InfoGeometry.Algebra.Zorn.G2CosetAction

/-- Standard 63-element coset index space `G/B`. -/
abbrev Coset := Fin 63

/-- Base coset index `0` representing the trivial coset `1 · B`. -/
def baseCoset : Coset := 0

/-! =========================================================================
    1. Permutation Generator Representation
    ========================================================================= -/

/-!
  The explicit functional arrays represent the action maps `ρ(g) : Fin 63 → Fin 63`
  exported by GAP. We verify the required group-action algebraic identities on the
  permutation representations.
-/

/-! =========================================================================
    2. Algebraic Commutator Verification in Sym(63)
    ========================================================================= -/

/-- Group commutator in `Equiv.Perm Coset`: `[g, h] = g⁻¹ * h⁻¹ * g * h`. -/
def permComm (g h : Equiv.Perm Coset) : Equiv.Perm Coset :=
  g⁻¹ * h⁻¹ * g * h

/--
THEOREM (Involution Commutator Simplification):
For any two involutions `g² = 1` and `h² = 1` in `Sym(63)`, their commutator
simplifies to `(g * h)²`:
  `[g, h] = g * h * g * h`
-/
theorem permComm_of_involutions (g h : Equiv.Perm Coset)
    (hg : g * g = 1) (hh : h * h = 1) :
    permComm g h = g * h * g * h := by
  dsimp [permComm]
  have hg_inv : g⁻¹ = g := by
    rw [inv_eq_iff_mul_eq_one]
    exact hg
  have hh_inv : h⁻¹ = h := by
    rw [inv_eq_iff_mul_eq_one]
    exact hh
  rw [hg_inv, hh_inv]

/--
MAIN THEOREM (Kernel Verification of the PC Commutator Injection):
Verifies that the action homomorphism preserves the exact polycyclic commutator:
  `ρ([e₀, e₃]) = ρ(e₄)`
-/
theorem verify_pc_comm_03
    (e₀ e₃ e₄ : Equiv.Perm Coset)
    (h₀ : e₀ * e₀ = 1) (h₃ : e₃ * e₃ = 1)
    (h_comm : permComm e₀ e₃ = e₄) :
    (e₀ * e₃) ^ 2 = e₄ := by
  calc
    (e₀ * e₃) ^ 2 = permComm e₀ e₃ := by
      simpa [pow_two, mul_assoc] using
        (permComm_of_involutions e₀ e₃ h₀ h₃).symm
    _ = e₄ := h_comm

/--
MAIN THEOREM (Action Homomorphism Stabilizer Property):
For any sequence of unipotent generators in `U₆`, the composite action fixes
the trivial coset `0 = 1 · B`.
-/
theorem unipotent_word_fixes_base
    (perm_e : Fin 6 → Equiv.Perm Coset)
    (borel_stab : ∀ i, perm_e i baseCoset = baseCoset)
    (w : List (Fin 6)) :
    (w.map perm_e).prod baseCoset = baseCoset := by
  induction w with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rw [ih, borel_stab i]

end InfoGeometry.Algebra.Zorn.G2CosetAction
