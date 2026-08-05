import Mathlib.Algebra.Algebra.Equiv
import InfoGeometry.Physics.BdGChiralBlockMatrix

namespace InfoGeometry.Physics

/-!
# Algebraic transport of chiral relations

This owner supplies the missing, theorem-honest transport layer.  A parameter
indexed `AlgEquiv` is the actual hypothesis needed for an operator vielbein:
it preserves addition, zero, multiplication, and the scalar algebra
structure.  An arbitrary multiplicative function is not enough to transport
an anticommutator.

No claim is made here that an existing Bogoliubov/Pauli frame is already such
an equivalence on the native split-octonion colour core.  That requires a
separate explicit witness.
-/

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- A parameter-indexed algebraic vielbein. -/
abbrev AlgebraVielbein (M : Type*) (A : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] := M → A ≃ₐ[R] A

/-- Transport of an anticommutator through an algebra equivalence. -/
theorem algEquiv_map_add_mul_swap
    {M : Type*} (V : AlgebraVielbein (R := R) M A) (t : M)
    (x y : A) :
    V t x * V t y + V t y * V t x =
      V t (x * y + y * x) := by
  calc
    V t x * V t y + V t y * V t x =
        V t (x * y) + V t (y * x) := by
          congr 1
          · exact ((V t).map_mul x y).symm
          · exact ((V t).map_mul y x).symm
    _ = V t (x * y + y * x) := ((V t).map_add _ _).symm

/-- A transported grading-fixed odd element remains odd. -/
theorem transported_anticommutator_zero
    {M : Type*} (V : AlgebraVielbein (R := R) M A) (t : M)
    {D gamma : A}
    (hD : D * gamma + gamma * D = 0)
    (hgamma : V t gamma = gamma) :
    V t D * gamma + gamma * V t D = 0 := by
  calc
    V t D * gamma + gamma * V t D =
    V t D * V t gamma + V t gamma * V t D := by rw [hgamma]
    _ = V t (D * gamma + gamma * D) := by
      exact algEquiv_map_add_mul_swap V t D gamma
    _ = 0 := by rw [hD]; exact (V t).map_zero

/-- Algebraic transport preserves the square of an operator. -/
theorem transported_square
    {M : Type*} (V : AlgebraVielbein (R := R) M A) (t : M)
    (D : A) :
    V t D * V t D = V t (D * D) := by
  exact ((V t).map_mul D D).symm

section BdG

variable {M : Type*} {A : Type*} [Ring A] [StarRing A]
  [CommSemiring R] [Algebra R (BdGBlock A)]

/-- The native BdG Dirac anticommutator survives any grading-fixed algebraic
vielbein.  The parameter `t` is intentionally abstract: it may later be
instantiated by a chemical potential or rapidity once an actual equivalence
has been constructed. -/
theorem transported_bdg_dirac_anticommutator
    (V : AlgebraVielbein (R := R) M (BdGBlock A)) (t : M)
    (Delta : A)
    (hgamma : V t chiralGrading = chiralGrading) :
    V t (diracOperator Delta) * chiralGrading +
        chiralGrading * V t (diracOperator Delta) = 0 := by
  exact transported_anticommutator_zero V t
    (dirac_anticommutes_with_chirality Delta) hgamma

end BdG

end InfoGeometry.Physics
