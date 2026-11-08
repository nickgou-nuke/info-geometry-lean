/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.Convolution
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.Resolvent
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.KroneckerPartition
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixLegendre
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.SpineResolvent
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixPeirceResolvent
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixChiralConvolution

/-!
# Operator Dirichlet / resolvent / Legendre layer

Causal poset:

```
Convolution   μ ⋆ ζ = 1 (delta), centrality, two-sided Möbius inversion,
              non-commutativity of the matrix Dirichlet ring,
              log-derivation, Λ = (log·ζ) ⋆ μ
Resolvent     nilpotent resolvent, periodic average (n·idempotent),
              ∏_{d|n} Φ_d(T) = Tⁿ - 1, (z - Φ)⁻¹ = (z + Φ)(z² - V)⁻¹
 └─ SpineResolvent   instantiation at N_±, Φ, J of PeirceSpine
KroneckerPartition   tr((A ⊗ B)^k) = tr(A^k) tr(B^k)
MatrixLegendre       ½⟨y, A⁻¹ y⟩ is the Legendre conjugate of ½⟨x, A x⟩
```

The stream also mentioned "Mandelbrot–Fourier relations" and the "Riemann zeta product".
They were not formalized: nothing in the stream pins down a precise operator statement
for either.
-/
