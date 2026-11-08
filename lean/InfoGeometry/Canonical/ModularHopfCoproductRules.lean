import InfoGeometry.Canonical.ModularCoproductFlux
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# InfoGeometry.Canonical.ModularHopfCoproductRules

Lean-facing Hopf-coproduct rules for the modular nilpotent generator lane.

This file is a theorem-only wrapper over `ModularCoproductFlux` using the
notations from the Jaynes/modular discussion:

* `Φ := N`
* `Δ := 1 + Φ`
* `hatDelta(Δ) = Δ ⊗ Δ`
* centered coproduct flux
  `hatDelta(Φ) = Φ ⊗ 1 + 1 ⊗ Φ + Φ ⊗ Φ`

No global Hopf completion claim.
No Virasoro central-charge theorem.
-/

namespace InfoGeometry.Canonical.ModularHopfCoproductRules

open scoped TensorProduct
open ModularCoproductFlux

section

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

/-- `Φ` is the nilpotent/modular flux generator (`Φ := N`). -/
abbrev Phi (N : A) : A := N

/-- `Δ := 1 + Φ` on the finite algebraic lane. -/
def modularDelta (N : A) : A := 1 + Phi N

/-- Group-like coproduct on the restricted modular generator lane: `hatDelta(Δ) = Δ ⊗ Δ`. -/
def hatDeltaDelta (N : A) : A ⊗[R] A :=
  modularDelta N ⊗ₜ[R] modularDelta N

/-- Centered coproduct flux: `hatDelta(Φ) := hatDelta(Δ) - 1 ⊗ 1`. -/
def hatDeltaPhi (N : A) : A ⊗[R] A :=
  hatDeltaDelta (R := R) N - ((1 : A) ⊗ₜ[R] (1 : A))

/-- Exact centered group-like expansion. -/
theorem hatDeltaPhi_eq_primitive_plus_cross
    (N : A) :
    hatDeltaPhi (R := R) N =
      primitiveFlux (R := R) N + crossFlux (R := R) N := by
  simpa [hatDeltaPhi, hatDeltaDelta, modularDelta, Phi, liftFlux] using
    one_add_tmul_one_add_sub_one_eq_liftFlux (R := R) N

/-- Equivalent expansion in explicit tensor terms. -/
theorem hatDeltaPhi_eq_tensor_expansion
    (N : A) :
    hatDeltaPhi (R := R) N =
      (N ⊗ₜ[R] (1 : A)) + ((1 : A) ⊗ₜ[R] N) + (N ⊗ₜ[R] N) := by
  simpa [primitiveFlux, crossFlux, add_assoc] using
    hatDeltaPhi_eq_primitive_plus_cross (R := R) N

/-- If `N² = 0`, then the cross-flux square vanishes: `(N ⊗ N)^2 = 0`. -/
theorem crossFlux_square_zero_of_nilpotent
    (N : A) (hN : N * N = 0) :
    crossFlux (R := R) N * crossFlux (R := R) N = 0 :=
  tensor_nilpotent_sq_zero (R := R) N hN

/-- Primitive reduction is valid exactly under explicit cross-flux annihilation. -/
theorem hatDeltaPhi_eq_primitive_of_cross_zero
    (N : A)
    (hcross : crossFlux (R := R) N = 0) :
    hatDeltaPhi (R := R) N = primitiveFlux (R := R) N := by
  simpa [hatDeltaPhi, hatDeltaDelta, modularDelta, Phi] using
    one_add_tmul_one_add_sub_one_eq_primitive_of_cross_zero (R := R) N hcross

end

/-! ## Operator-surprisal coproduct defect -/

section Coalgebra

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A] [Coalgebra R A]

/--
Failure of an operator-valued surprisal/log generator `K` to be primitive
under the actual coalgebra comultiplication.

This definition uses `Coalgebra.comul`; it is distinct from the concrete
tensor expression `hatDeltaDelta` above.
-/
def surprisalCoproductDefect (K : A) : A ⊗[R] A :=
  (Coalgebra.comul : A →ₗ[R] A ⊗[R] A) K - primitiveFlux (R := R) K

/--
Every coalgebra coproduct decomposes exactly into the primitive tensor sum and
the operatorial surprisal coproduct defect.
-/
theorem comul_eq_primitiveFlux_add_surprisalCoproductDefect
    (K : A) :
    (Coalgebra.comul : A →ₗ[R] A ⊗[R] A) K =
      primitiveFlux (R := R) K + surprisalCoproductDefect (R := R) K := by
  simp [surprisalCoproductDefect]

/--
The operatorial surprisal coproduct defect vanishes exactly when the
surprisal/log generator is primitive.
-/
theorem surprisalCoproductDefect_eq_zero_iff
    (K : A) :
    surprisalCoproductDefect (R := R) K = 0 ↔
      (Coalgebra.comul : A →ₗ[R] A ⊗[R] A) K =
        primitiveFlux (R := R) K := by
  simp [surprisalCoproductDefect, sub_eq_zero]

end Coalgebra

end InfoGeometry.Canonical.ModularHopfCoproductRules
