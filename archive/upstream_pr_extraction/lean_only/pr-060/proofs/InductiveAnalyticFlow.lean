import Mathlib
import proofs.LieAlgebraColimit

noncomputable section

universe u

namespace InfoGeometry.Quantum.InductiveAnalyticFlow

open InfoGeometry.Quantum.LieColimit

/-
Inductive-colimit definition of analyticity.

In this finite-representative algebraic setting, an "analytic" flow is one whose
Lie-algebra representative has zero trace.  A continuation step is the tower
bonding map.  Trace compatibility of the tower makes analyticity invariant under
that step.
-/

/-- A represented flow/operator in the Lie-algebra colimit. -/
abbrev FlowElement (T : LieAlgebraTower.{u}) :=
  LieColimitElement T

/--
Colimit analyticity: the finite representative satisfies the Jacobi-Liouville
trace-zero condition.
-/
def IsAnalytic {T : LieAlgebraTower.{u}} (X : FlowElement T) : Prop :=
  colimitTrace X = 0

/-- One-step continuation of a represented flow along the tower bonding map. -/
def continueOnce {T : LieAlgebraTower.{u}} (X : FlowElement T) : FlowElement T :=
  ⟨X.stage + 1, T.emb X.stage X.val⟩

/-- Analytic continuation is trace-preserving at the level of representatives. -/
theorem continuation_trace_eq {T : LieAlgebraTower.{u}} (X : FlowElement T) :
    colimitTrace (continueOnce X) = colimitTrace X :=
  colimitTrace_emb T X.stage X.val

/--
Analytic continuation is globally well-defined for represented colimit flows:
if the finite representative is traceless, its one-step continuation remains
traceless.
-/
theorem analytic_continuation_is_invariant
    {T : LieAlgebraTower.{u}} (X : FlowElement T)
    (hX : IsAnalytic X) :
    IsAnalytic (continueOnce X) := by
  rw [IsAnalytic, continuation_trace_eq]
  exact hX

/--
Every represented element of a trace-zero Lie tower is analytic.  This is the
direct colimit inheritance theorem in analytic-flow vocabulary.
-/
theorem represented_flow_is_analytic
    {T : LieAlgebraTower.{u}} (X : FlowElement T) :
    IsAnalytic X :=
  colimit_trace_annihilation T X

/--
The continued representative of any element of a trace-zero tower is analytic.
-/
theorem continued_represented_flow_is_analytic
    {T : LieAlgebraTower.{u}} (X : FlowElement T) :
    IsAnalytic (continueOnce X) :=
  analytic_continuation_is_invariant X (represented_flow_is_analytic X)

/--
Bundled statement: represented flows are analytic, and one continuation step
preserves analyticity.
-/
theorem inductive_analytic_flow_synthesis
    {T : LieAlgebraTower.{u}} (X : FlowElement T) :
    IsAnalytic X ∧
      colimitTrace (continueOnce X) = colimitTrace X ∧
      IsAnalytic (continueOnce X) := by
  exact ⟨represented_flow_is_analytic X,
    continuation_trace_eq X,
    continued_represented_flow_is_analytic X⟩

end InfoGeometry.Quantum.InductiveAnalyticFlow

