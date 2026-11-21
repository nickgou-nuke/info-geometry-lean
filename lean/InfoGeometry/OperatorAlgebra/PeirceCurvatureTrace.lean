/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature

/-!
# Cyclic traces of projector tangents and curvature

These are the finite algebraic ingredients in Lemma 5.1 and equation (8.6)
of Craig, *A gauge-invariant measure for lattice chiral fermions*,
arXiv:2610.09093v1, printed pages 23 and 40.

The tangent equation, its canonical double-commutator generator, and the
even product of two tangents are reused from their existing owners. The
trace is a native additive homomorphism with explicit cyclicity. No division,
adjoint, characteristic restriction, topology, spectral gap, differential
form, transport ODE, or integration measure is assumed or constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace

open InfoGeometry.Core.PeirceTangent
open InfoGeometry.Clifford.ChiralProjectorBerryCurvature
open InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature

variable {A M : Type*} [Ring A] [AddCommGroup M]

private theorem trace_mul_commutator_left (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (a b c : A) :
    τ (a * InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator b c) =
      τ (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator a b * c) := by
  unfold InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
  simp only [mul_sub, sub_mul, map_sub]
  have hcycle : τ (a * (c * b)) = τ ((b * a) * c) := by
    calc
      τ (a * (c * b)) = τ ((a * c) * b) := by rw [mul_assoc]
      _ = τ (b * (a * c)) := hτ _ _
      _ = τ ((b * a) * c) := by rw [mul_assoc]
  rw [hcycle, mul_assoc a b c]

private theorem trace_mul_commutator_rotate (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (a b c : A) :
    τ (a * InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator b c) =
      τ (b * InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator c a) := by
  unfold InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
  simp only [mul_sub, map_sub]
  have hleft : τ (a * (b * c)) = τ (b * (c * a)) := by
    calc
      τ (a * (b * c)) = τ ((b * c) * a) := hτ _ _
      _ = τ (b * (c * a)) := by rw [mul_assoc]
  have hright : τ (a * (c * b)) = τ (b * (a * c)) := by
    calc
      τ (a * (c * b)) = τ ((a * c) * b) := by rw [mul_assoc]
      _ = τ (b * (a * c)) := hτ _ _
  rw [hleft, hright]

private theorem trace_idempotent_sandwich (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) {p : A}
    (hp : p * p = p) (a : A) : τ (p * a * p) = τ (p * a) := by
  calc
    τ (p * a * p) = τ (p * (p * a)) := hτ _ _
    _ = τ ((p * p) * a) := by rw [mul_assoc]
    _ = τ (p * a) := by rw [hp]

/-- A projector tangent is a commutator, so every cyclic trace kills it.
The existing reconstruction avoids a characteristic-two cancellation. -/
theorem trace_tangent_zero (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) {p x : A}
    (hp : p * p = p) (hx : p * x + x * p = x) : τ x = 0 := by
  rw [← tangent_eq_double_commutator hp hx, map_sub,
    hτ (x * p - p * x) p, sub_self]

/-- An even product followed by a third tangent is tangent again.
The order of the three insertions is retained. -/
theorem tangent_triple {p x y z : A}
    (hx : p * x + x * p = x) (hy : p * y + y * p = y)
    (hz : p * z + z * p = z) :
    p * (x * y * z) + (x * y * z) * p = x * y * z := by
  have hxy := tangent_product_commutes hx hy
  calc
    p * (x * y * z) + (x * y * z) * p =
        (p * (x * y)) * z + (x * y) * (z * p) := by
          simp only [mul_assoc]
    _ = ((x * y) * p) * z + (x * y) * (z * p) := by rw [hxy]
    _ = (x * y) * (p * z + z * p) := by noncomm_ring
    _ = x * y * z := by rw [hz]

/-- The exact triple-tangent trace cancellation used in the algebraic part
of projector-curvature closure. No analytic exterior derivative is asserted. -/
theorem trace_tangent_triple_zero (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) {p x y z : A}
    (hp : p * p = p) (hx : p * x + x * p = x)
    (hy : p * y + y * p = y) (hz : p * z + z * p = z) :
    τ (x * y * z) = 0 :=
  trace_tangent_zero τ hτ hp (tangent_triple hx hy hz)

/-- The existing sandwiched curvature has the paper's single-projector
trace, using cyclicity and idempotence rather than a changed definition. -/
theorem trace_projectorCurvature (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) {p : A}
    (hp : p * p = p) (x y : A) :
    τ (projectorCurvature p x y) =
      τ (p * InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator x y) :=
  trace_idempotent_sandwich τ hτ hp
    (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator x y)

/-- The finite gauge-variation identity from equation (8.6). The gauge
generator is arbitrary; tangency of `[g,p]` follows from idempotence. -/
theorem trace_projectorCurvature_gauge (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) {p x : A}
    (hp : p * p = p) (hx : p * x + x * p = x) (g : A) :
    τ (projectorCurvature p x
      (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator g p)) = τ (g * x) := by
  have hdouble : InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator p
      (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator p x) = x := by
    change idempotentAdjoint p (idempotentAdjoint p x) = x
    exact (tangent_iff_adjoint_square_eq_self hp).mp hx
  calc
    τ (projectorCurvature p x
      (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator g p)) =
        τ (p * InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator x
          (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator g p)) :=
          trace_projectorCurvature τ hτ hp x
            (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator g p)
    _ = τ (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator p x *
        InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator g p) :=
      trace_mul_commutator_left τ hτ p x
        (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator g p)
    _ = τ (g * InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator p
        (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator p x)) :=
      trace_mul_commutator_rotate τ hτ
        (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator p x) g p
    _ = τ (g * x) := by rw [hdouble]

/-- Complementing a projector negates its curvature trace. Both tangent
insertions also change sign; their ordered commutator retains its sign. -/
theorem trace_projectorCurvature_complement (τ : A →+ M)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) {p : A}
    (hp : p * p = p) (x y : A) :
    τ (projectorCurvature (1 - p) (-x) (-y)) =
      -τ (projectorCurvature p x y) := by
  have hq : (1 - p) * (1 - p) = 1 - p := by noncomm_ring [hp]
  have hsign : InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator (-x) (-y) =
      InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator x y := by
    unfold InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
    noncomm_ring
  have hzero : τ (InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator x y) = 0 := by
    rw [InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator,
      map_sub, hτ x y, sub_self]
  rw [trace_projectorCurvature τ hτ hq,
    trace_projectorCurvature τ hτ hp, hsign, sub_mul, one_mul, map_sub,
    hzero, zero_sub]

end InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace
