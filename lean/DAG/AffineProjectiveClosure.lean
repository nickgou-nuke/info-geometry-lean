import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.KreinSpace
import DAG.GradedBottInclusion
import DAG.AnalyticBridge

/-!
# DAG.AffineProjectiveClosure — Doubled Krein Particle-Hole Interface

This file exposes the doubled-Krein particle-hole and chiral-parity operators
used by the anomaly-cancellation narrative.  It does not prove a Dixmier-trace
anomaly cancellation theorem.

## The Operators (all exist in InfoGeometry.Krein)

- `modular_j` (x,ξ) ↦ (ξ,x) — swap isometry, particle ↔ hole
- `spectral_epsilon` (x,ξ) ↦ (x,-ξ) — fundamental symmetry, Z₂ grading
- `complex_i` = modular_j ∘ spectral_epsilon — complex structure J² = -1

## Intended Theorem Target

    Anomaly(D) + Anomaly(C D C⁻¹) = 0

where C = modular_j is particle-hole conjugation and the anomaly is expressed
through a chosen trace/residue functional.  That target needs explicit
premises for the Dirac operator, conjugation law, trace cyclicity, and residue
definition.

## Physical Meaning

The finite operator names below are kernel objects.  The physical claims about
central charge, PSL(2,Z) invariance, KMS equilibrium, and Dixmier residues
remain closure debt until they are stated with theorem-level hypotheses.
-/

open InfoGeometry.Krein

namespace DAG.AffineProjectiveClosure

/--
Particle-hole conjugation: C = modular_j.
Satisfies C² = 1, C D C⁻¹ = -D for skew-adjoint D.
-/
noncomputable def particleHoleC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  modular_j

/--
The chiral parity operator on the doubled space:
Γ = spectral_epsilon = diag(1, -1).

In the discrete DAG: chiralGamma = diag(+1 on C⁰, -1 on C¹, +1 on C²).
In the continuous Krein space: Γ picks up +1 on particles, -1 on holes.

The Möbius function μ(n) = (-1)^F is the eigenvalue of Γ on the n-th
energy level: μ(n) = +1 for even fermion number, -1 for odd.
-/
noncomputable def chiralParity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectral_epsilon

/--
Closure debt: affine projective anomaly cancellation.

For any skew-adjoint Dirac operator D and gauge transformation A on the
doubled Krein space, the intended theorem target is:

    Anomaly(D) + Anomaly(C D C⁻¹) = 0

Required premises include:
1. C² = 1 and C D C⁻¹ = -D (particle-hole conjugates D to -D)
2. the chirality conjugation/anticommutation law;
3. cyclicity or covariance of the chosen trace/residue;
4. compatibility of the absolute-value/power term under `D ↦ -D`.
-/
def affine_projective_closure_debt : String :=
  "Open: prove doubled-Krein anomaly cancellation after supplying Dirac, chirality, trace/residue, and conjugation premises."

end DAG.AffineProjectiveClosure
