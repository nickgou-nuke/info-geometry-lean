# Projection, graded coupling, and attention: formal scope

## Projection decomposition

`Epistemology/WheelersSelfObservingUniverse.lean` uses native `Module.End`,
`IsIdempotentElem`, `LinearMap.range`, `LinearMap.ker`, and Mathlib's complementary
submodule theorem. It proves fixed-point/range equivalence, the kernel remainder,
and an actual unique decomposition into a fixed component and a killed component.
The direction of the no-remainder equality is corrected.

Idempotence gives an algebraic direct sum, not orthogonality. The separate inner
product theorem explicitly assumes symmetry of the linear operator. No statement
about consciousness, observation creating reality, or psychological theories is
encoded or proved.

## Chiral algebra

`QuantumContext/MassAsCommutantCoupling.lean` reuses
`Core/PeirceDecomposition.lean` for the complementary idempotent and its algebraic
annihilation laws. There is no new `ChiralCommutant` structure duplicating the
existing owners. The input is an idempotent `projection` and an element `coupling`
satisfying the explicit sector-swap equation.

The implementation derives both vanishing diagonal corners, anticommutation
with the signed grading, its scalar multiple's square, and the Hamiltonian square
conditional on the specified scalar coupling-square law. Ordinary block-diagonal
operators need not anticommute with off-diagonal operators: the signed form of
momentum is essential. A matrix regression example uses the identity and the swap
matrix to demonstrate this failure.

The complementary sector is not identified with an operator commutant. The
existing `Algebra/IdempotentCornerCommutant.lean` owns the distinct regular-ideal
commutant construction. No Tomita–Takesaki operator, time evolution, mass-generation
mechanism, or memory interpretation is supplied here.

## Attention audit

`QuantumContext/TransformerLatentSpace.lean` reuses the finite softmax weight
owner in `Routing/FiniteSoftmax.lean`. For unmasked finite real scores it defines
the two-token row-softmax weight matrix, proves positivity and row normalization,
and proves that its projected diagonal corner is nonzero. Consequently this
matrix does not satisfy the required swap hypothesis. Zero scores also give a
concrete softmax matrix whose square is not any scalar multiple of the identity.

This is a statement about attention weights, not a claim about all masked
attention variants or the complete `softmax(QKᵀ)V` map. The proposed identification
of general transformer attention with the algebraic coupling cannot be obtained
from these assumptions. The implementation makes no claim equating attention,
backpropagation, physical mass, or semantic meaning.

## Ordering and checks

`QuantumContext/ProjectionCouplingDependencies.lean` models prerequisites through
finite-set inclusion and a native lifted partial order. Range and kernel are
parallel branches; inner-product symmetry and scalar coupling-square data are
separate assumptions, not consequences of idempotence or softmax normalization.

`QuantumContext/ProjectionCouplingTests.lean` includes an oblique projection,
a nontrivial swap-matrix model, a counterexample to diagonal/off-diagonal
anticommutation without signs, softmax obstructions, and axiom printouts.
No new axiom, `sorry`, `admit`, or `True` placeholder is used.

After inspecting compiler processes, use the shared lock:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.QuantumContext.ProjectionCouplingTests
```

Verification remains pending until that target finishes successfully. These
files do not alter categorical colimit owners or dependency pins.
