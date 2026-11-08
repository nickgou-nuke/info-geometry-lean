/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.InnerDerivationSpectra
import InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity

/-!
# Bridge to `PeirceDissipatorTrinity`

The inner-derivation Laplacians of a square-zero pair are exactly the sum and
difference dissipators of the existing trinity owner, so every spectral
identity in `SquareZeroPairSpectral` transfers to those channels.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {u v : A}

theorem phiLaplacian_eq_sumDissipator (hu : u * u = 0) (hv : v * v = 0) :
    phiLaplacian R u v = PeirceDissipatorTrinity.sumDissipator (R := R) u v :=
  (PeirceDissipatorTrinity.sumDissipator_eq_neg_doubleLie hu hv).symm

theorem jLaplacian_eq_differenceDissipator (hu : u * u = 0) (hv : v * v = 0) :
    jLaplacian R u v = PeirceDissipatorTrinity.differenceDissipator (R := R) u v :=
  (PeirceDissipatorTrinity.differenceDissipator_eq_doubleLie hu hv).symm

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral
