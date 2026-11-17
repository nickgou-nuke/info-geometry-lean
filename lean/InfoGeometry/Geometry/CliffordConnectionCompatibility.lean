/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AssociativeGaugeConnection
import InfoGeometry.OperatorAlgebra.CliffordDirac.Defect

/-!
# Connection compatibility in the Clifford square

The native fundamental connection `D + L_a` acts on the regular module of an
associative coefficient ring. Its commutator with `L_g` is left multiplication
by the existing adjoint covariant derivative `D g + [a, g]`. Faithfulness of
left multiplication makes vanishing of that derivative exactly the condition
for these two operators to commute.

The existing Clifford square expansion then retains both the commutator of
the base derivatives and all four coefficient-compatibility defects. No
commutativity of coefficients, flat connection, metric, or scalar curvature
is assumed. The final specialization assumes commuting base derivatives and
covariantly constant Clifford coefficients, and still retains gauge curvature.

All operators are native total linear endomorphisms. A realization by
unbounded differential operators requires a separately constructed common
invariant domain. These identities do not assert a geometric Lichnerowicz
formula or construct a Laplace--Beltrami operator.
-/

namespace InfoGeometry.Geometry.AssociativeGaugeConnection

open InfoGeometry.OperatorAlgebra.CliffordDirac

variable {R A : Type*} [Ring R] [Ring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- The mixed operator commutator is the adjoint covariant derivative of
the left-multiplication coefficient. -/
theorem covariantDerivative_mulLeft_commutator
    (D : Module.End R A) (hD : IsLeibniz D) (a g : A) :
    ⁅covariantDerivative D a, LinearMap.mulLeft R g⁆ =
      LinearMap.mulLeft R (adjointCovariantDerivative D a g) := by
  ext x
  change (D (g * x) + a * (g * x)) - g * (D x + a * x) =
    (D g + (a * g - g * a)) * x
  rw [hD g x]
  noncomm_ring

/-- Compatibility with the faithful left action is equivalent to covariant
constancy of its coefficient, rather than ordinary constancy `D g = 0`. -/
theorem covariantDerivative_mulLeft_commute_iff
    (D : Module.End R A) (hD : IsLeibniz D) (a g : A) :
    Commute (covariantDerivative D a) (LinearMap.mulLeft R g) ↔
      adjointCovariantDerivative D a g = 0 := by
  rw [commute_iff_lie_eq, covariantDerivative_mulLeft_commutator D hD a g,
    LinearMap.mulLeft_eq_zero_iff]

/-- The fundamental curvature action with the base commutator retained.
The two base derivatives need not commute. -/
theorem covariantDerivative_commutator_with_base_defect
    (D E : Module.End R A) (hD : IsLeibniz D) (hE : IsLeibniz E)
    (a b : A) :
    ⁅covariantDerivative D a, covariantDerivative E b⁆ =
      ⁅D, E⁆ + LinearMap.mulLeft R (curvature D E a b) := by
  ext x
  change
    (D (E x + b * x) + a * (E x + b * x)) -
        (E (D x + a * x) + b * (D x + a * x)) =
      (D (E x) - E (D x)) + (D b - E a + a * b - b * a) * x
  rw [map_add, map_add, hD b x, hE a x]
  noncomm_ring

/-- The two-direction gauged Clifford square, with both base curvature and
all four mixed coefficient derivatives explicit. The order `g * h * F` is
preserved in the zero-order curvature action. -/
theorem clifford_covariant_square_with_defects
    (D E : Module.End R A) (hD : IsLeibniz D) (hE : IsLeibniz E)
    (a b g h : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0) :
    let X := covariantDerivative D a
    let Y := covariantDerivative E b
    let Q := LinearMap.mulLeft R g * X + LinearMap.mulLeft R h * Y
    Q * Q =
      X * X + Y * Y +
        LinearMap.mulLeft R (g * h) * ⁅D, E⁆ +
        LinearMap.mulLeft R ((g * h) * curvature D E a b) +
        LinearMap.mulLeft R (g * adjointCovariantDerivative D a g) * X +
        LinearMap.mulLeft R (g * adjointCovariantDerivative D a h) * Y +
        LinearMap.mulLeft R (h * adjointCovariantDerivative E b g) * X +
        LinearMap.mulLeft R (h * adjointCovariantDerivative E b h) * Y := by
  dsimp only
  have hmul (u v : A) :
      LinearMap.mulLeft R u * LinearMap.mulLeft R v =
        LinearMap.mulLeft R (u * v) :=
    (LinearMap.mulLeft_mul R A u v).symm
  have hlg : LinearMap.mulLeft R g * LinearMap.mulLeft R g = 1 := by
    rw [hmul, hg]
    exact LinearMap.mulLeft_one R A
  have hlh : LinearMap.mulLeft R h * LinearMap.mulLeft R h = 1 := by
    rw [hmul, hh]
    exact LinearMap.mulLeft_one R A
  have hlanti :
      LinearMap.mulLeft R g * LinearMap.mulLeft R h +
        LinearMap.mulLeft R h * LinearMap.mulLeft R g = 0 := by
    ext x
    change g * (h * x) + h * (g * x) = 0
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hanti, zero_mul]
  have hs := clifford_sum_sq_with_defect
    (LinearMap.mulLeft R g) (LinearMap.mulLeft R h)
    (covariantDerivative D a) (covariantDerivative E b) hlg hlh hlanti
  rw [covariantDerivative_commutator_with_base_defect D E hD hE a b,
    covariantDerivative_mulLeft_commutator D hD a g,
    covariantDerivative_mulLeft_commutator D hD a h,
    covariantDerivative_mulLeft_commutator E hE b g,
    covariantDerivative_mulLeft_commutator E hE b h] at hs
  simpa only [hmul, mul_add, add_assoc] using hs

/-- Covariant constancy removes the mixed defects without discarding the
commutator of the base derivatives or the gauge curvature. -/
theorem clifford_covariant_square_of_compatible
    (D E : Module.End R A) (hD : IsLeibniz D) (hE : IsLeibniz E)
    (a b g h : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (hDg : adjointCovariantDerivative D a g = 0)
    (hDh : adjointCovariantDerivative D a h = 0)
    (hEg : adjointCovariantDerivative E b g = 0)
    (hEh : adjointCovariantDerivative E b h = 0) :
    let X := covariantDerivative D a
    let Y := covariantDerivative E b
    let Q := LinearMap.mulLeft R g * X + LinearMap.mulLeft R h * Y
    Q * Q =
      X * X + Y * Y +
        LinearMap.mulLeft R (g * h) * ⁅D, E⁆ +
        LinearMap.mulLeft R ((g * h) * curvature D E a b) := by
  have hs := clifford_covariant_square_with_defects D E hD hE a b g h hg hh hanti
  dsimp only at hs ⊢
  simpa only [hDg, hDh, hEg, hEh, mul_zero,
    LinearMap.mulLeft_zero_eq_zero, zero_mul, add_zero] using hs

/-- For commuting base derivatives and compatible Clifford coefficients,
the square retains the full ordered gauge-curvature term. -/
theorem clifford_covariant_square_of_compatible_of_commute
    (D E : Module.End R A) (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hDE : Commute D E) (a b g h : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (hDg : adjointCovariantDerivative D a g = 0)
    (hDh : adjointCovariantDerivative D a h = 0)
    (hEg : adjointCovariantDerivative E b g = 0)
    (hEh : adjointCovariantDerivative E b h = 0) :
    let X := covariantDerivative D a
    let Y := covariantDerivative E b
    let Q := LinearMap.mulLeft R g * X + LinearMap.mulLeft R h * Y
    Q * Q = X * X + Y * Y +
      LinearMap.mulLeft R ((g * h) * curvature D E a b) := by
  have hs := clifford_covariant_square_of_compatible D E hD hE a b g h
    hg hh hanti hDg hDh hEg hEh
  dsimp only at hs ⊢
  simpa only [hDE.lie_eq, mul_zero, add_zero] using hs

end InfoGeometry.Geometry.AssociativeGaugeConnection
