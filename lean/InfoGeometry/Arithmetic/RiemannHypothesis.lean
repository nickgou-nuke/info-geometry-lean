import InfoGeometry.Analysis.BregmanAnalyticBound
import InfoGeometry.Analysis.BregmanMonodromyBridge
import InfoGeometry.Arithmetic.RHEquivalence
import InfoGeometry.Canonical.VarlamovDiscreteSymmetry
import DAG.AffineProjectiveClosure
import DAG.GraphHodge
import DAG.ChiralDiracAnticommutation

/-!
# Riemann-hypothesis bridge interfaces and finite projections

This file keeps the RH bridge honest by exporting only kernel-checked facts
from owner files and by making the analytic Fredholm half-plane claim an
explicit certificate interface.

The closed local projections are:

1. `dikin_sandwich_strictly_positive`, delegated to
   `InfoGeometry.Arithmetic.RHEquivalence.dikinOmega_pos`.

2. `cpt_preserves_idempotent_splitting`, delegated to the Varlamov split atom
   theorem `varlamov_signature_plus_plus_minus`.

3. `hodge_chiral_dirac_anticommutation`, delegated to the finite graph Dirac
   theorem `DAG.ChiralDiracAnticommutation.dirac_anticommutes_gamma`.

The Fredholm determinant nonvanishing claim is not proved here. It is exposed
as `FredholmHalfPlaneCertificate`, so downstream code must supply the analytic
determinant and its half-plane nonvanishing proof instead of relying on a
vacuous theorem.
-/

open Complex

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

/-- Property that a candidate Fredholm determinant has no zeros in the open half-plane Re(s) > 1/2. -/
def FredholmHalfPlaneProperty (determinant : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, (1 / 2 : ℝ) < s.re → determinant s ≠ 0

/--
Analytic certificate required for the Fredholm half-plane claim.

This is intentionally a data interface: the repo does not currently contain a
trace-class Fredholm determinant theorem proving this certificate from first
principles.
-/
def FredholmHalfPlaneCertificate : Type _ :=
  {determinant : ℂ → ℂ // FredholmHalfPlaneProperty determinant}

namespace FredholmHalfPlaneCertificate

/-- The Fredholm determinant carried by the certificate. -/
abbrev determinant (C : FredholmHalfPlaneCertificate) : ℂ → ℂ :=
  C.1

/-- The half-plane nonvanishing law carried by the certificate. -/
theorem determinant_ne_zero
    (C : FredholmHalfPlaneCertificate)
    (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    determinant C s ≠ 0 :=
  C.2 s hs

/-- Construct a Fredholm half-plane certificate from its determinant law. -/
def mk
    (determinant : ℂ → ℂ)
    (h : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → determinant s ≠ 0) :
    FredholmHalfPlaneCertificate :=
  ⟨determinant, h⟩

end FredholmHalfPlaneCertificate

/--
**Formulation 4 (Fredholm Invertibility).**

Projection from an explicit analytic certificate: if a Fredholm determinant
certificate supplies nonvanishing on the open half-plane, the local readout is
nonzero there.
-/
theorem fredholm_determinant_nonzero_on_critical_halfplane
    (C : FredholmHalfPlaneCertificate) {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    C.determinant s ≠ 0 :=
  C.determinant_ne_zero s hs

end InfoGeometry.Arithmetic.RiemannHypothesis
