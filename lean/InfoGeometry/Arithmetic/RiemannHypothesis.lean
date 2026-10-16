/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.BregmanAnalyticBound
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.BregmanMonodromyBridge
import InfoGeometry.Arithmetic.RHEquivalence
import InfoGeometry.Canonical.VarlamovDiscreteSymmetry
import DAG.AffineProjectiveClosure
import DAG.GraphHodge
import DAG.ChiralDiracAnticommutation

/-!
# Riemann-hypothesis predicates and finite projections

This file exports only kernel-checked finite/local facts. The actual
nontrivial-zero formulation is owned by
`RiemannHypothesisProjectiveFormulation`; this file does not claim an analytic
Fredholm determinant or a proof of RH.
-/

namespace InfoGeometry.Arithmetic.RiemannHypothesis

open InfoGeometry.Analysis.BregmanAnalyticBound

/--
**Formulation 1 (Dikin Sandwich — PROVED).**

ω(t) = t - log(1+t) > 0 for all t > 0.

This theorem asserts only Dikin positivity. It does not assert a zeta zero
exclusion theorem.
-/
theorem dikin_sandwich_strictly_positive (t : ℝ) (ht : 0 < t) : 0 < dikinOmega t := by
  exact InfoGeometry.Arithmetic.RHEquivalence.dikinOmega_pos t ht

/--
**Formulation 2 (CPT Invariance — PROVED).**

The closed Varlamov split-atom law: `W² = +1`, `E² = +1`, and `C² = -1`.

Owner theorem: `InfoGeometry.Canonical.KreinDoubledAtom.varlamov_signature_plus_plus_minus`.
-/
theorem cpt_preserves_idempotent_splitting
    (X : InfoGeometry.Canonical.KreinDoubledAtom) :
    ((InfoGeometry.Canonical.KreinDoubledAtom.varlamovW X).comp
        (InfoGeometry.Canonical.KreinDoubledAtom.varlamovW X)
          =
        (LinearMap.id : X →ₗ[ℝ] X))
      ∧
      ((InfoGeometry.Canonical.KreinDoubledAtom.varlamovE X).comp
        (InfoGeometry.Canonical.KreinDoubledAtom.varlamovE X)
          =
        (LinearMap.id : X →ₗ[ℝ] X))
      ∧
      ((InfoGeometry.Canonical.KreinDoubledAtom.varlamovC X).comp
        (InfoGeometry.Canonical.KreinDoubledAtom.varlamovC X)
          =
        -((LinearMap.id : X →ₗ[ℝ] X))) := by
  exact InfoGeometry.Canonical.KreinDoubledAtom.varlamov_signature_plus_plus_minus X

/--
**Formulation 3 (Finite Graph Hodge/Dirac Anticommutation — PROVED).**

The finite graph Dirac operator anticommutes with chirality. This is the
kernel-checked Hodge/Dirac fact currently available in the DAG owner layer.
-/
theorem hodge_chiral_dirac_anticommutation {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
    DAG.ChiralDiracAnticommutation.chiralGamma (n0 := n0) (n1 := n1) (n2 := n2)
        * DAG.ChiralDiracAnticommutation.diracOp B1 B2
      + DAG.ChiralDiracAnticommutation.diracOp B1 B2
        * DAG.ChiralDiracAnticommutation.chiralGamma (n0 := n0) (n1 := n1)
          (n2 := n2)
        =
      0 := by
  exact DAG.ChiralDiracAnticommutation.dirac_anticommutes_gamma B1 B2

end InfoGeometry.Arithmetic.RiemannHypothesis
