import InfoGeometry.Canonical.RealIncidenceHomology
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

namespace RealIncidenceChains

/-!
# Real incidence chains

This file turns a typed `DAG.TripleSystem` into degree-0/degree-1 real
incidence chains.

It defines:

* `C₀(A)`: finitely supported real object chains;
* `C₁(A)`: finitely supported real valid-triple chains;
* `∂₁(s,p,o) = o - s`.

No higher faces, `∂² = 0` theorem, quotient homology, singular homology, or
de Rham/cohomology theorem is asserted here.
-/

open InfoGeometry.Canonical.RealIncidenceHomology

namespace Incidence

/-- Degree-0 real incidence chains: finitely supported formal sums of objects. -/
@[rep_depth transport]
abbrev ZeroChains (A : DAG.TripleSystem) :=
  A.Obj →₀ ℝ

/-- Degree-1 real incidence chains: finitely supported formal sums of valid triples. -/
@[rep_depth transport]
abbrev OneChains (A : DAG.TripleSystem) :=
  RealIncidenceHomology.Incidence.Edge A →₀ ℝ

/-- Boundary of one valid incidence edge: `∂(s,p,o) = o - s`. -/
@[rep_depth transport]
def edgeBoundary {A : DAG.TripleSystem}
    (e : RealIncidenceHomology.Incidence.Edge A) : ZeroChains A :=
  Finsupp.single e.tgt (1 : ℝ) - Finsupp.single e.src (1 : ℝ)

/--
The degree-1 incidence boundary map induced by
`∂(s,p,o) = o - s`.
-/
@[rep_depth transport]
def boundaryOne (A : DAG.TripleSystem) : OneChains A →ₗ[ℝ] ZeroChains A :=
  Finsupp.linearCombination ℝ (edgeBoundary (A := A))

/--
Readback: the boundary of a finite real sum of valid triples is the sum of
their target-minus-source boundaries.
-/
@[rep_depth transport]
theorem boundaryOne_apply
    {A : DAG.TripleSystem}
    (c : OneChains A) :
    boundaryOne A c =
      c.sum fun e a => a • edgeBoundary (A := A) e := by
  simpa [boundaryOne] using
    (Finsupp.linearCombination_apply (R := ℝ)
      (v := edgeBoundary (A := A)) c)

/-- Boundary of a single weighted incidence edge. -/
@[rep_depth transport]
theorem boundaryOne_single
    {A : DAG.TripleSystem}
    [DecidableEq (RealIncidenceHomology.Incidence.Edge A)]
    (e : RealIncidenceHomology.Incidence.Edge A)
    (a : ℝ) :
    boundaryOne A (Finsupp.single e a) =
      a • edgeBoundary (A := A) e := by
  simpa [boundaryOne] using
    (Finsupp.linearCombination_single (R := ℝ)
      (v := edgeBoundary (A := A)) a e)

/-- Boundary of an unweighted incidence edge. -/
@[rep_depth transport]
theorem boundaryOne_single_one
    {A : DAG.TripleSystem}
    [DecidableEq (RealIncidenceHomology.Incidence.Edge A)]
    (e : RealIncidenceHomology.Incidence.Edge A) :
    boundaryOne A (Finsupp.single e (1 : ℝ)) =
      edgeBoundary (A := A) e := by
  simpa using boundaryOne_single (A := A) e (1 : ℝ)

end Incidence

end RealIncidenceChains
