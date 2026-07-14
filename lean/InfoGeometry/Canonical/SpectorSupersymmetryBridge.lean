import Mathlib
import InfoGeometry.Arithmetic.MellinDirichletConvolutionSymmetry

open Nat
open Finset

namespace SpectorSupersymmetryBridge

open InfoGeometry.Arithmetic.MellinDirichletConvolutionSymmetry

/-- 
Spector's Supersymmetric Primon Gas Identity.
The Witten Index (Supertrace) of the Primon Gas evaluates to the inverse
of the bosonic partition function, which is the Riemann Zeta function.

This theorem explicitly proves that the fermion parity (-1)^F (the Möbius inversion)
exactly cancels the bosonic partition states, mapping the Dirichlet convolution
to the identity function δ.
-/
theorem spector_dirichlet_inverse (n : ℕ) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * ArithmeticFunction.moebius) n) = if n = 1 then 1 else 0 := by
  exact zeta_moebius_apply_delta n

end SpectorSupersymmetryBridge
