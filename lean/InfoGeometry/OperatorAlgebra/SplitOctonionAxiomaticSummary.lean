import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.OperatorAlgebra.SplitOctonionNormComposition
import InfoGeometry.OperatorAlgebra.SplitOctonionModularJ
import InfoGeometry.Physics.D4Triality
import InfoGeometry.Topology.ArtinBraidS3Quotient
import InfoGeometry.Topology.ParafermionBraiding
import InfoGeometry.Topology.BraidParafermionClosure
import InfoGeometry.Quantum.Monodromy
import InfoGeometry.Canonical.TimeAsWindingMonodromy3D
import InfoGeometry.Canonical.NullConeConfinement
import InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace
import InfoGeometry.Arithmetic.PrimonGasSupertrace
import InfoGeometry.Arithmetic.PrimeLatticeGasVariational
import InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex

/-!
# Split-Octonionic Primon Gas: axiomatic summary

This file is documentation-only.  It records the theorem-owned dictionary
connecting the split-octonion core, triality/braid transport, monodromy,
null-cone confinement, and the primon free-energy / crystallization corridor.

## 1. Split-octonion composition and modular reflection

\[
\detZ(XY)=\detZ(X)\detZ(Y)
\]
via `InfoGeometry.OperatorAlgebra.SplitOctonionNormComposition.detZ_mulZ`.

\[
\mathrm{conjZ}(XY)=\mathrm{conjZ}(Y)\,\mathrm{conjZ}(X),\qquad
\detZ(\mathrm{conjZ}(X))=\detZ(X),\qquad
X\,\mathrm{conjZ}(X)=\detZ(X)\cdot 1
\]
via `InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication.conjZ_mulZ`,
`InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication.detZ_conjZ`, and
`InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication.mul_conjZ_eq_scalar_detZ`.

The modular-J packet reexports these as
`InfoGeometry.OperatorAlgebra.SplitOctonionModularJ.modularJ_anti_automorphism`,
`InfoGeometry.OperatorAlgebra.SplitOctonionModularJ.detZ_modularJ_invariant`,
and `InfoGeometry.OperatorAlgebra.SplitOctonionModularJ.mul_modularJ_eq_scalar_detZ`.

## 2. Triality and braid shadow

\[
|S_3|=6
\]
via `InfoGeometry.Physics.D4Triality.S3Triality_card`.

The finite braid shadow is given by
`InfoGeometry.Topology.ArtinBraidS3Quotient.s3_adjacent_artin_relation` and
`InfoGeometry.Topology.ParafermionBraiding.su3_parafermion_braiding`.

The packaged braid/phase closure is
`InfoGeometry.Topology.BraidParafermionClosure.finite_braid_parafermion_closure`.

## 3. Monodromy and time freezing

The unipotent winding law is
`InfoGeometry.Quantum.Monodromy.monodromy_winding_formula`.

The 3D chiral boundary identity is
`InfoGeometry.Canonical.TimeAsWindingMonodromy3D.chiralMatrix_det`
and
`InfoGeometry.Canonical.TimeAsWindingMonodromy3D.boundary_eq_det_zero_iff`.

The logarithmic winding readout is
`InfoGeometry.Canonical.TimeAsWindingMonodromy3D.poleWinding_eq_logarithmicPhase`
with integer clock readout `time_tick_is_integer`.

## 4. Null-cone confinement

The null cone and Klein boundary are owned by
`InfoGeometry.Canonical.NullConeConfinement.NullCone` and
`InfoGeometry.Canonical.NullConeConfinement.KleinQuadricBoundary`.

The confinement operator satisfies
`InfoGeometry.Canonical.NullConeConfinement.confinement_preserves_valid_states`.

## 5. Primon thermodynamics and crystallization

The free-energy inversion law is
`InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace.freeEnergy_determinantLineInversion_eq_log`.

The Gibbs/KMS minimizer theorem is
`InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace.GibbsKMS_freeEnergy_ge_gibbs`.

The finite supertrace support theorem is
`InfoGeometry.Arithmetic.PrimonGasSupertrace.finiteSupertrace_eq_squarefree_filter`.

The finite hard-core prime lattice partition identity is
`InfoGeometry.Arithmetic.PrimeLatticeGasVariational.grandPartition_eq_closed`,
and the zero-feature entropy maximizer is
`InfoGeometry.Arithmetic.PrimeLatticeGasVariational.primeLatticeGas_zeroFeature_entropy_maximizer`.

The finite Dyson/Vandermonde and collision locus are owned by
`InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.finite_dyson_vandermonde_potential`,
`InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.finite_vandermonde_zero_iff_collision`,
and `InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.finite_prime_lattice_entropy_maximizer`.

## 6. Summary dictionary

\[
\text{split-octonion composition}
\to
\text{triality / braid shadow}
\to
\text{monodromy / boundary}
\to
\text{null-cone confinement}
\to
\text{primon free energy / crystallization}.
\]

No theorem in this file asserts a Riemann-zero spacing theorem or a physical
baryon-confinement theorem.
-/

namespace SplitOctonionAxiomaticSummary

end SplitOctonionAxiomaticSummary
