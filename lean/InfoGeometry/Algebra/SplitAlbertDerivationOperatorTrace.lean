import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Trace

/-!
# Operator trace of split-Albert derivations

The trace statement in this owner is deliberately kept at the native finite
dimensional operator level. The scalar `linearTrace` readout is a separate
coordinate theorem and is not identified here without a completed proof.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- Every bundled derivation of the split-Albert Jordan algebra sends every
vector to an element whose left-multiplication operator has vanishing native
finite-dimensional operator trace. -/
theorem h3Zorn_derivation_jordanLmul_operatorTrace_zero
    (D : NonAssocDerivation.derivations ℝ (H3Zorn ℝ))
    (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
      (jordanLmul (R := ℝ)
        ((D : Module.End ℝ (H3Zorn ℝ)) x)) = 0 := by
  rw [← lie_derivation_jordanLmul (D := (D : Module.End ℝ (H3Zorn ℝ)))
    (hD := D.property) x]
  simp only [Ring.lie_def]
  rw [map_sub, LinearMap.trace_mul_comm]
  exact sub_self _

/-!
The named `H3ZornF4Derivations` owner uses the same Leibniz predicate as the
generic non-associative derivation carrier.  This adapter exposes the operator
trace theorem on that existing Lie-subalgebra carrier; it does not identify
the scalar Jordan trace with the operator trace.
-/

theorem h3ZornF4_derivation_jordanLmul_operatorTrace_zero
    (D : H3ZornF4Derivations) (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
      (jordanLmul (R := ℝ) (D.1 x)) = 0 := by
  let D' : NonAssocDerivation.derivations ℝ (H3Zorn ℝ) :=
    ⟨D.1, D.2⟩
  exact h3Zorn_derivation_jordanLmul_operatorTrace_zero D' x

/-- The existing `H3ZornF4Derivations` carrier inherits the unit-annihilation
law of the generic non-associative derivation carrier. -/
theorem h3ZornF4_derivation_apply_one_eq_zero
    (D : H3ZornF4Derivations) :
    D.1 (1 : H3Zorn ℝ) = 0 := by
  let D' : NonAssocDerivation.derivations ℝ (H3Zorn ℝ) :=
    ⟨D.1, D.2⟩
  exact h3Zorn_derivation_apply_one_eq_zero D'

/-!
The scalar trace readout is controlled by the installed bilinear form.  This
is the exact interface needed before a universal scalar-trace theorem can be
proved: it separates the algebraic consequence from the independent task of
showing that every derivation is skew for `traceBilin`.
-/

theorem h3Zorn_derivation_linearTrace_zero_of_traceBilin_skew
    (D : NonAssocDerivation.derivations ℝ (H3Zorn ℝ))
    (hskew : ∀ x y : H3Zorn ℝ,
      traceBilin ((D : Module.End ℝ (H3Zorn ℝ)) x) y +
        traceBilin x ((D : Module.End ℝ (H3Zorn ℝ)) y) = 0)
    (x : H3Zorn ℝ) :
    linearTrace ((D : Module.End ℝ (H3Zorn ℝ)) x) = 0 := by
  rw [← traceBilin_one]
  have h := hskew x (1 : H3Zorn ℝ)
  rw [h3Zorn_derivation_apply_one_eq_zero D, traceBilin_zero_right,
    add_zero] at h
  exact h

theorem h3ZornF4_derivation_linearTrace_zero_of_traceBilin_skew
    (D : H3ZornF4Derivations)
    (hskew : ∀ x y : H3Zorn ℝ,
      traceBilin (D.1 x) y + traceBilin x (D.1 y) = 0)
    (x : H3Zorn ℝ) :
    linearTrace (D.1 x) = 0 := by
  let D' : NonAssocDerivation.derivations ℝ (H3Zorn ℝ) :=
    ⟨D.1, D.2⟩
  apply h3Zorn_derivation_linearTrace_zero_of_traceBilin_skew D'
  intro u v
  exact hskew u v

/-!
The next identities expose the linear dependence of the left-multiplication
operator on its algebra element.  They are the algebraic prerequisites for a
basis computation of its native operator trace; no scalar trace identity is
assumed here.
-/

theorem h3Zorn_jordanLmul_add (X Y : H3Zorn ℝ) :
    jordanLmul (R := ℝ) (X + Y) =
      jordanLmul (R := ℝ) X + jordanLmul (R := ℝ) Y := by
  apply LinearMap.ext
  intro Z
  change (X + Y) * Z = X * Z + Y * Z
  exact add_mul X Y Z

theorem h3Zorn_jordanLmul_smul (r : ℝ) (X : H3Zorn ℝ) :
    jordanLmul (R := ℝ) (r • X) =
      r • jordanLmul (R := ℝ) X := by
  apply LinearMap.ext
  intro Z
  change (r • X) * Z = r • (X * Z)
  change candidateJordanMul (r • X) Z = r • candidateJordanMul X Z
  exact candidateJordanMul_smul_left r X Z

theorem h3Zorn_jordanLmul_operatorTrace_add (X Y : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
        (jordanLmul (R := ℝ) (X + Y)) =
      LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) X) +
        LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) Y) := by
  rw [h3Zorn_jordanLmul_add, map_add]

theorem h3Zorn_jordanLmul_operatorTrace_smul (r : ℝ) (X : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
        (jordanLmul (R := ℝ) (r • X)) =
      r * LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) X) := by
  rw [h3Zorn_jordanLmul_smul, map_smul]
  rfl

end InfoGeometry.Algebra
