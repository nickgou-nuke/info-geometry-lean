# Transform Atlas Architecture

> **Status:** Draft / Initiated
> **Owner:** InfoGeometry Architecture
> **Focus:** Unifying algebraic transform calculi over Split Clifford algebras and Nonabelian Lie groups.

## Overview

The native spectral geometry of the split-octonion and split-quaternion bases contains a fundamental "Mellin/Laplace split" bounded by the signature of the generator. 

The transform itself is not just a change of basis but a **change of category**. The Transform Atlas establishes a strictly typed hierarchy where the target coefficient algebra is dictated by the algebraic symmetry of the domain.

```text
ordinary Fourier (scalar-valued)
      ⊂ Lie-group Fourier (representation-valued)
      and Clifford Fourier/Mellin (Clifford-valued)
```

For a locally compact nonabelian group $G$, the natural Fourier transform is representation/operator-valued:
$$ \widehat{f}(\pi) = \int_G f(g) \pi(g^{-1}) dg $$
where $\pi$ runs over the irreducible representations.

## Atlas Hierarchy

### 1. Elliptic Generators ($J^2 = -1$)
- **Domain:** Compact, periodic orbits, standard circle $S^1$.
- **Transform:** Standard Fourier transform (compact/discrete spectrum).
- **Kernels:** Unitary representations ($U(1)$ and compact Lie group characters).
- **Implementation Status:** Standard Mathlib trigonometric polynomials and compact group characters.

### 2. Hyperbolic Generators ($H^2 = 1$)
- **Domain:** Noncompact, split causal cones, hyperbolic orbits.
- **Transform:** Mellin/Laplace transforms.
- **Kernels:** 
  - Peirce split channels: $u_\pm = \frac{1}{2}(1 \pm H)$
  - Implemented in `InfoGeometry.Algebra.SplitCliffordTransformKernel`.
  - Orthogonality and idempotency: $u_\pm^2 = u_\pm$, $u_+ u_- = 0$.
  - These projectors isolate the scale-invariant Mellin data.

### 3. Mixed / Nonabelian Kernels
- **Domain:** Semisimple Lie groups (e.g., $G_2$, $SL(2,\mathbb{R})$) and Noncommutative Monoid Algebras.
- **Transform:** Operator/Representation-valued Noncommutative Fourier Transform.
- **Kernels:** 
  - Explicit finite noncommutative plane waves: $E_g \star E_h = E_{g h}$, implemented via `MonoidAlgebra` in `InfoGeometry.Algebra.NoncommutativePlaneWaveKernel`.
  - Weyl-invariant representations: $G_2$ Mellin/Fourier invariants are derived by summing over the Weyl orbit (implemented in `CanonicalZornG2CartanMellinWeylInvariant`).
- **Implementation Status:** Algebraic core finite kernels implemented without analytic topology assumptions (relying on `MonoidAlgebra` and explicit finite sums). 

## Formalization Strategy

When formalizing these transforms, the repository relies on:
1. **Target Category Shift:** Instead of redefining integration theories, we lift the target space to the appropriate `MonoidAlgebra` or `CliffordAlgebra`.
2. **Finite Base Rings:** Transforms must first be validated on finite lattices/groups before performing inductive colimits to the continuum.
3. **Peirce Ladder:** Any object carrying an $H^2=1$ generator must be canonically split via its Peirce ladder before defining integration against hyperbolic characters.

## Next Steps
- Port the $H^2=1$ Mellin continuous integrals into categorical limits over the existing discrete Peirce projectors.
- Expand `NoncommutativePlaneWaveKernel` to include Plancherel-type identities for finite group representation traces.
