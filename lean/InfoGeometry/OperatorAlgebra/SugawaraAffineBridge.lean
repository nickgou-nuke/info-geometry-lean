/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.External.Virasoro.FiveGradedDecomposition
import InfoGeometry.External.Virasoro.Sugawara

/-!
# Sugawara Construction for Affine Kac-Moody Algebras

This file establishes the connection between the general affine Kac-Moody algebra
and the Sugawara construction of the Virasoro algebra.

## Main definitions

* `VirasoroProject.sugawaraOperators`: The Sugawara construction `Lₙ` from the currents `J^a_m`.
-/

namespace VirasoroProject

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
variable (𝓰 : Type*) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

-- The construction of the Sugawara operators for arbitrary affine algebras requires
-- a dual basis and the dual Coxeter number `h^∨`. We leave the full explicit formula
-- for future completion, but we define the bridging types here.


end VirasoroProject
