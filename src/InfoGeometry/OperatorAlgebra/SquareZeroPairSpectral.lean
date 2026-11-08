/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.MassCommutant
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.InnerDerivationSpectra
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.KleinHadamard
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.FourierCharacterDefect
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.Equivariance
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.UnipotentSteinberg
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.Corner
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.TrinityBridge
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.Orientation

/-!
# Spectral superoperator theory of a square-zero operator pair

Causal order of the submodules:

1. `MassCommutant`: `V = u v + v u` commutes with `u, v`; `L_V` commutes with
   the inner derivations `ad_Φ, ad_J, ad_Σ` in `Module.End R A`.
2. `InnerDerivationSpectra`: first-order actions, the three Laplacians,
   the mixed ladders, and the Casimir on `(Φ, J, V, Σ)`.
3. `KleinHadamard`: raw and `V`-homogenized character superoperators, their
   partitions, diagonalization, and second-order orthogonality.
   `FourierCharacterDefect`: comparison with the proposed multiplicative
   sandwich character averages, retaining the exact off-centralizer defect.
   `Equivariance`: all Laplacians and homogenized projectors commute with the
   two-sided multiplications `x ↦ g x g`, `g ∈ {J, Φ, Σ}`.
4. `UnipotentSteinberg`: unipotent conjugations, the Weyl element, and the
   Steinberg braids `B₊, B₋` as units.
5. `Corner`: instantiation at the Peirce corners `component10 p a`,
   `component01 p b`, plus identities involving the idempotent itself.
6. `TrinityBridge`: identification with `PeirceDissipatorTrinity`.
7. `Orientation`: half-twist sandwiches by `Φ, J, Σ`; the Cartan grading
   `S = 2 p - 1` as `⋆ = L_S`; graded derivations with `d̄ = -(⋆ d ⋆)`,
   `d² = ad_{x²}` and `{d, d̄} = 2 • jordanOp (x²)`.
-/
