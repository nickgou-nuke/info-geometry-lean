# Onsite native CStarMatrix norm layer

Candidate: GrowingOnsiteMatrixNorm20261024.lean, source-only/uncompiled.
Pending native dependency: InfoGeometry.Canonical.GrowingOnsiteMatrixHamiltonian.
Other owners are existing CantorBernoulliCStarMatrixTraceState and Mathlib.

The two value definitions cstarTailZ and cstarOnsiteHamiltonian apply the existing
CStarMatrix.ofMatrixStarAlgEquiv to the raw tail and Hamiltonian. No new carrier
or independent recursion is introduced. The raw matrix norm is not used.

Proof chain:
1. map_star and raw tail Hermiticity give self-adjointness.
2. map_mul and native tilt2_sq give tail square = 1; hence native unitary
   membership and norm = 1 in the nontrivial finite CStarMatrix stage.
3. cstarConcreteStep is contractive by native C-star hom contractivity.
4. The transported successor recursion is the original equation under the
   native matrix equivalence. Triangle inequality and real scalar norm give
   norm H_n <= sum_{j<n} |w_j| by induction from H_0=0.
5. Actual Summable (fun j => |w j|) gives the uniform bound by its tsum.

No numerical bound field, normalization condition, coupled interaction claim,
completion, or GNS operator theorem is assumed or asserted. This layer is an
input to the later genuinely growing trace-GNS commutator construction.

No builds/tests/live-owner edits. Staged for independent AA and serialized QA.
