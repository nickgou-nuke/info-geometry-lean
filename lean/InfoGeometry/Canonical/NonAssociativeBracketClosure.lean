import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic

/-!
# Closure under the binary Jordan/Lie splitting

This owner isolates the algebraic fact used by split-octonion element closure.
It does not assume associativity.  The only extra property is that the
scalar `2` is invertible, so multiplication can be recovered from its
commutator and anticommutator parts.
-/

namespace InfoGeometry.Canonical

variable {R A : Type*} [Field R] [NeZero (2 : R)]
  [NonUnitalNonAssocRing A] [Module R A]

def commutator (x y : A) : A := x * y - y * x

def anticommutator (x y : A) : A := x * y + y * x

theorem mul_eq_half_add_commutator (x y : A) :
    (2 : R)⁻¹ • (anticommutator x y + commutator x y) = x * y := by
  change (2 : R)⁻¹ • ((x * y + y * x) + (x * y - y * x)) = x * y
  rw [smul_add, smul_add, smul_sub]
  calc
    ((2 : R)⁻¹ • (x * y) + (2 : R)⁻¹ • (y * x)) +
          ((2 : R)⁻¹ • (x * y) - (2 : R)⁻¹ • (y * x)) =
        (2 : R)⁻¹ • (x * y) + (2 : R)⁻¹ • (x * y) := by abel
    _ = ((2 : R)⁻¹ + (2 : R)⁻¹) • (x * y) := by
      rw [add_smul]
    _ = x * y := by
      rw [← mul_two, inv_mul_cancel₀ (NeZero.ne (2 : R)), one_smul]

theorem submodule_mul_mem_of_bracket_mem
    (U : Submodule R A)
    (hcomm : ∀ {x y : A}, x ∈ U → y ∈ U → commutator x y ∈ U)
    (hanti : ∀ {x y : A}, x ∈ U → y ∈ U → anticommutator x y ∈ U)
    {x y : A} (hx : x ∈ U) (hy : y ∈ U) :
    x * y ∈ U := by
  rw [← mul_eq_half_add_commutator (R := R) x y]
  show (2 : R)⁻¹ • (anticommutator x y + commutator x y) ∈ U
  have hsum : anticommutator x y + commutator x y ∈ U :=
    U.add_mem (hanti (x := x) (y := y) hx hy) (hcomm (x := x) (y := y) hx hy)
  exact Submodule.smul_mem U (2 : R)⁻¹ hsum

theorem bracket_closure_eq_mul_closure
    (U : Submodule R A)
    (hcomm : ∀ {x y : A}, x ∈ U → y ∈ U → commutator x y ∈ U)
    (hanti : ∀ {x y : A}, x ∈ U → y ∈ U → anticommutator x y ∈ U) :
    (∀ {x y : A}, x ∈ U → y ∈ U → x * y ∈ U) := by
  intro x y hx hy
  rw [← mul_eq_half_add_commutator (R := R) x y]
  show (2 : R)⁻¹ • (anticommutator x y + commutator x y) ∈ U
  have hsum : anticommutator x y + commutator x y ∈ U :=
    U.add_mem (hanti (x := x) (y := y) hx hy) (hcomm (x := x) (y := y) hx hy)
  exact Submodule.smul_mem U (2 : R)⁻¹ hsum

theorem mul_closure_implies_bracket_closure
    (U : Submodule R A)
    (hmul : ∀ {x y : A}, x ∈ U → y ∈ U → x * y ∈ U)
    {x y : A} (hx : x ∈ U) (hy : y ∈ U) :
    commutator x y ∈ U ∧ anticommutator x y ∈ U := by
  constructor
  · exact U.sub_mem (hmul hx hy) (hmul hy hx)
  · exact U.add_mem (hmul hx hy) (hmul hy hx)

theorem submodule_bracket_closure_iff_mul_closure
    (U : Submodule R A) :
    (∀ {x y : A}, x ∈ U → y ∈ U → x * y ∈ U) ↔
      ((∀ {x y : A}, x ∈ U → y ∈ U → commutator x y ∈ U) ∧
       (∀ {x y : A}, x ∈ U → y ∈ U → anticommutator x y ∈ U)) := by
  constructor
  · intro hmul
    refine ⟨?_, ?_⟩
    · intro x y hx hy
      exact (mul_closure_implies_bracket_closure U hmul hx hy).1
    · intro x y hx hy
      exact (mul_closure_implies_bracket_closure U hmul hx hy).2
  · rintro ⟨hcomm, hanti⟩
    exact bracket_closure_eq_mul_closure U hcomm hanti

end InfoGeometry.Canonical
