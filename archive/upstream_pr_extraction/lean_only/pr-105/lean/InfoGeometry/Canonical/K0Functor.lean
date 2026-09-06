import Mathlib.Tactic
import InfoGeometry.Algebra.Grothendieck

/-
--- AUDIT PROTOCOL MAP ---

BUCKET 1: CLOSED FINITE THEOREMS:
  Delegated to `InfoGeometry.Algebra.Grothendieck`.

BUCKET 2: None.  BUCKET 3: None.
--------------------------
-/

noncomputable def K0 (M : Type u) [AddCommMonoid M] : Type u := Grothendieck M

instance (M : Type u) [AddCommMonoid M] : AddCommGroup (K0 M) :=
  inferInstanceAs (AddCommGroup (Grothendieck M))

def K0_map (M : Type u) [AddCommMonoid M] : M →+ K0 M := grothendieckMap M

noncomputable def K0_equiv_int : K0 ℕ ≃+ ℤ := grothendieckEquivInt
