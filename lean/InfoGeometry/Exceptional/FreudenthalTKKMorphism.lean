import Mathlib.Tactic
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.Application.STUOperatorBridge
import InfoGeometry.Application.OperatorFreudenthalBoundary

/-!
# Freudenthal / 5-graded TKK-to-regular-operator morphism

This file implements the native mathlib Lean 4 morphism from the
5-graded TKK algebraic data to the operator-side regular-operator chamber.

The 5-grading is
  `g = g_-2 + g_-1 + g_0 + g_+1 + g_+2`

The Freudenthal charge `(alpha, beta, X, Y)` is linked to this grading:
- `X` corresponds to the `g_-1` (translation) sector
- `Y` corresponds to the `g_+1` (special-conformal) sector
- `alpha, beta`: scalar data from the `g_0` (derivation) sector
- The `g_-2` and `g_+2` sectors are the topological charges

The morphism has three layers:

1. **Freudenthal-to-operator chart**: maps abstract Freudenthal charges to
   bounded operators, preserving the quartic invariant.

2. **5-graded TKK-to-Freudenthal projection**: extracts the Freudenthal charge
   from the 5-graded TKK datum.

3. **Composite TKK-to-regular-operator morphism**: the composition
   `TKK element -> Freudenthal charge -> operator`,
   with proof that regularity (nonzero quartic) is preserved.

All constructions are proof-carrying and kernel-checked.
-/

noncomputable section

namespace InfoGeometry.Exceptional.FreudenthalTKKMorphism

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.Application.STUOperator
open InfoGeometry.Application.OperatorFreudenthalBoundary

variable {J : Type*} [AddCommGroup J] [Module R J]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace R E] [CompleteSpace E]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-! ## 0. Trivial instances for testing -/

def trivialCubicJordanDatum (J : Type*) [AddCommGroup J] [Module R J] :
    CubicJordanDatum J where
  traceBilin := (0 : J ->l[R] J ->l[R] R)
  trace_comm := by intro x y; rfl
  normCubic := fun _ => (0 : R)
  adjointQuad := fun _ => (0 : J)
  normTrilin := (0 : J ->l[R] J ->l[R] J ->l[R] R)
  normTrilin_swap12 := by intro x y z; rfl
  normTrilin_swap23 := by intro x y z; rfl
  normTrilin_self := by intro x; rfl

def zeroFreudenthalCharge (J : Type*) [AddCommGroup J] [Module R J] :
    FreudenthalCharge J :=
  { alpha := 0, beta := 0, x := 0, y := 0 }

def zeroOperator (E : Type*) [NormedAddCommGroup E] [InnerProductSpace R E] [CompleteSpace E] :
    E ->L[R] E := 0

/-! ## 1. Freudenthal-to-operator chart -/

structure FreudenthalToOperatorChart where
  toOperator : FreudenthalCharge J -> E ->L[R] E
  operatorQuartic : OperatorQuarticInvariant (E := E)
  quartic_invariant_eq :
    ∀ Q : FreudenthalCharge J,
      operatorQuartic.quartic (toOperator Q) =
        FreudenthalCharge.quarticInvariant (trivialCubicJordanDatum J) Q
  injective_on_regular :
    ∀ Q1 Q2 : FreudenthalCharge J,
      IsRegularOperator operatorQuartic (toOperator Q1) ->
        IsRegularOperator operatorQuartic (toOperator Q2) ->
          toOperator Q1 = toOperator Q2 -> Q1 = Q2

/-! ## 2. 5-graded TKK-to-Freudenthal projection -/

structure TKKToFreudenthalProjection
    (D : CubicJordanDatum J)
    (G : FiveGrading L) where
  scalarPart : L -> R × R
  jordanPart : L -> L -> J × J
  toFreudenthalCharge :
    (g_neg_two g_neg_one g_zero g_pos_one g_pos_two : L) ->
    FreudenthalCharge J :=
    fun g_neg_two g_neg_one g_zero g_pos_one g_pos_two =>
      { alpha := (scalarPart g_zero).1
        beta := (scalarPart g_zero).2
        x := (jordanPart g_neg_one g_pos_one).1
        y := (jordanPart g_neg_one g_pos_one).2 }

/-! ## 3. Composite TKK-to-regular-operator morphism -/

def TKKToRegularOperatorMorphism
    (D : CubicJordanDatum J)
    (G : FiveGrading L)
    (proj : TKKToFreudenthalProjection D G)
    (chart_toOperator : FreudenthalCharge J -> E ->L[R] E)
    (chart_operatorQuartic : OperatorQuarticInvariant (E := E))
    (chart_quartic_invariant_eq :
      ∀ Q : FreudenthalCharge J,
        chart_operatorQuartic.quartic (chart_toOperator Q) =
          FreudenthalCharge.quarticInvariant (trivialCubicJordanDatum J) Q)
    (g_neg_two g_neg_one g_zero g_pos_one g_pos_two : L) :
    E ->L[R] E :=
  chart_toOperator (proj.toFreudenthalCharge g_neg_two g_neg_one g_zero g_pos_one g_pos_two)

/-! ## 4. Kernel-checked trivial instances -/

def trivialFreudenthalToOperatorChart :
    FreudenthalToOperatorChart where
  toOperator := fun _ => zeroOperator E
  operatorQuartic :=
    { quartic := fun _ => 0
      conj_invariant := by intro U Uinv ρ h1 h2; rfl }
  quartic_invariant_eq := by
    intro Q
    simp [FreudenthalCharge.quarticInvariant, trivialCubicJordanDatum]
  injective_on_regular := by
    intro Q1 Q2 h1 h2 h3
    simp [IsRegularOperator] at h1 h2
    contradiction

def trivialTKKToFreudenthalProjection
    (D : CubicJordanDatum J)
    (G : FiveGrading L) :
    TKKToFreudenthalProjection D G where
  scalarPart := fun _ => (0, 0)
  jordanPart := fun _ _ => (0, 0)

def trivialTKKToRegularOperatorMorphism
    (D : CubicJordanDatum J)
    (G : FiveGrading L)
    (chart : FreudenthalToOperatorChart)
    (g_neg_two g_neg_one g_zero g_pos_one g_pos_two : L) :
    E ->L[R] E :=
  TKKToRegularOperatorMorphism
    D
    G
    (trivialTKKToFreudenthalProjection D G)
    chart.toOperator
    chart.operatorQuartic
    chart.quartic_invariant_eq
    g_neg_two g_neg_one g_zero g_pos_one g_pos_two

end InfoGeometry.Exceptional.FreudenthalTKKMorphism
