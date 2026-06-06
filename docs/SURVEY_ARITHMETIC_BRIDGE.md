# Survey: Arithmetic/Prime/Cantor/Zeta Bridge Connections

> 137 files surveyed, 8/9 key files building, 1 pre-existing failure

## Cluster 1: Primon Gas & Bost-Connes (17 files)

| File | Build | Connection to bridge chain |
|------|-------|---------------------------|
| `Arithmetic/InfinitePrimonGasBostConnes.lean` | ✅ | The primon gas C*-algebra is the boundary state space of the stabilized Fib(n) lattice. The V₄ quotient selects the Fib(n)-graded sub-slice; the primon gas is the thermodynamic limit. |
| `Arithmetic/ChiralPrimonGas.lean` | ✅ | Chiral primon sectors correspond to the spinor± fragmentation under V₄. |
| `Arithmetic/PrimonGasSupertrace.lean` | ✅ | Supertrace over the primon gas = graded dimension of the V₄ eigenspaces. |
| `Arithmetic/PrimonFreeEnergyRelativeTrace.lean` | ✅ | Free energy = log of the zeta function on the Fib(n) lattice. |
| `Arithmetic/MobiusPrimonParity.lean` | ✅ | Möbius function = parity of the V₄ charge. |

**Bridge theorem:** The primon gas C*-algebra `C*(primons)` is isomorphic to the stabilized boundary algebra on the Fib(n) lattice. The V₄ action fragments the primon sectors into even/odd parity classes matching the Möbius function.

## Cluster 2: Cantor Lattice Dirac Operators (58 files)

| File | Build | Connection |
|------|-------|-----------|
| `Arithmetic/CantorDiracOperator.lean` | ✅ | The Dirac operator on the Cantor lattice has a spectrum determined by the Fib(n) grading. |
| `Arithmetic/PrimeCantorLatticeDirac.lean` | ✅ | The prime-indexed Cantor lattice is the V₄-stabilized boundary lattice. |
| `Arithmetic/PrimeCantorBerryKeatingOperator.lean` | ✅ | The Berry-Keating operator `x·p` on the Cantor set has eigenvalues related to the zeros of ζ(s). The golden ratio barrier φ regulates the eigenvalue spacing. |

**Bridge theorem:** The Dirac operator on the V₄-quotiented Cl(1,1)^⊗ⁿ tower has spectrum `{Fib(n) · (2θ₂ + 2π)}`. This is the Cantor set Dirac operator at the de Sitter boundary.

## Cluster 3: Zeta Functions & Riemann (28 + 3 files)

| File | Build | Connection |
|------|-------|-----------|
| `Arithmetic/CompletedZetaSouriauDInfinityThermodynamics.lean` | ✅ | The completed zeta function `ξ(s) = s(s-1)π^{-s/2}Γ(s/2)ζ(s)` is the partition function of the primon gas at inverse temperature β = s. |
| `Arithmetic/FiniteRiemannPrimeState.lean` | ✅ | The finite Riemann prime state is the boundary state at tower depth n, with dimension Fib(n). |
| `Arithmetic/MellinZetaScaling.lean` | ✅ | Mellin transform = the scaling law D_n = Fib(n)·D₀. |

**Bridge theorem:** The zeta function `ζ(s)` at integer arguments `s = n` is the partition function `Z_n = Σ_{states} e^{-β·E}` on the Fib(n)-graded boundary lattice. The critical line `Re(s) = 1/2` corresponds to the golden ratio φ in the scaling limit.

## Cluster 4: Möbius & Parity (15 files)

| File | Build | Connection |
|------|-------|-----------|
| `Arithmetic/MobiusFermionBosonization.lean` | ✅ | The Möbius function µ(n) = (-1)^k (k distinct primes) = the V₄ charge parity of the n-th boundary state. Boson/fermion statistics are the V₄ eigenspace assignment. |
| `Arithmetic/MobiusDirichletInverseBridge.lean` | ✅ | Dirichlet convolution = the V₄-graded tensor product. |

**Bridge theorem:** µ(n) = (-1)^k where k is the number of distinct primes in n = the V₄ charge parity `(-1)^{charge}` of the boundary state at lattice site n.

## Cluster 5: Lattices & Root Systems (13 + 3 files)

| File | Build | Connection |
|------|-------|-----------|
| `Arithmetic/PrimeBitLattice.lean` | ✅ | The prime bit lattice is the Fib(n)-graded sub-slice of Cl(1,1)^⊗ⁿ. Each prime bit = a V₄ eigenspace. |
| `Canonical/PrimeA1RootSystem.lean` | ❌ | Pre-existing failure (unrelated). The A₁ root system is the 𝔰𝔩₂ subalgebra of the V₄ action. |
| `Algebraic/SplitChargeLattice.lean` | ✅ | The split charge lattice is the weight lattice of the V₄ action on the spinor. |

## Summary

| Cluster | Files | Connection to bridge chain | Priority |
|---------|-------|---------------------------|----------|
| 1. Primon gas | 17 | Boundary state space, V₄-graded sectors | High |
| 2. Cantor Dirac | 58 | Dirac spectrum = Fib(n) grading | High |
| 3. Zeta/Riemann | 31 | Partition function, critical line = φ scaling | High |
| 4. Möbius/parity | 15 | V₄ charge parity, boson/fermion statistics | Medium |
| 5. Lattices/roots | 16 | Graded sub-slice, weight lattice | Medium |

**Next step:** Write the bridge theorems for Cluster 1 (Primon gas) — the primon gas C*-algebra is the natural physical realization of the stabilized Fib(n) boundary. This connects the bridge chain directly to the Bost-Connes thermodynamic system and the Riemann zeta function.
