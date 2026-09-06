import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
import InfoGeometry.Canonical.RelativeDeterminantScatteringSocket

/-!
# InfoGeometry.Canonical.PrimeLeeYangHopfieldLimitBridge

Hopfield/rank-one and Hurwitz-limit bridge for the centered prime Lee--Yang
chain.

This file proves finite algebraic facts about the centered chain:

* the full centered coupling is the rank-one outer-product readout
  `(κ / 2) log(pᵢ) log(pⱼ)`;
* the diagonal spin-square contribution is configuration-independent;
* the two-prime logarithmic-convolution coefficient is
  `2 log(pᵢ) log(pⱼ)`;
* the centered occupation coupling equals `κ` times that two-prime coefficient.

The infinite Lee--Yang/Hurwitz transfer to completed `xi` remains a
proof-carrying socket.  No RH theorem is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangHopfieldLimitBridge

open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
open InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
open InfoGeometry.Canonical.RelativeDeterminantScatteringSocket

variable {n : ℕ}
variable (C : PrimeFerromagneticChain n)

/--
Full rank-one centered coupling, before deleting the diagonal.

This is the Hopfield/Curie--Weiss one-pattern matrix
`J_full = (κ/2) ℓ ℓᵀ`.
-/
def hopfieldFullCoupling
    (i j : Fin n) : ℝ :=
  C.centeredSpinCoupling i j

/-- The full Hopfield coupling is the centered spin coupling. -/
@[simp]
theorem hopfieldFullCoupling_eq_centeredSpinCoupling
    (i j : Fin n) :
    hopfieldFullCoupling C i j = C.centeredSpinCoupling i j := rfl

/-- Explicit outer-product formula for the full Hopfield coupling. -/
theorem hopfieldFullCoupling_eq_outerProduct
    (i j : Fin n) :
    hopfieldFullCoupling C i j =
      (C.kappa / 2) * C.siteEnergy i * C.siteEnergy j := rfl

/--
Rank-one cross-minor identity for the full Hopfield coupling.

This is a theorem-safe algebraic way to say the full matrix is an outer
product, without depending on a matrix-rank API.
-/
theorem hopfieldFullCoupling_cross_minor
    (i j r t : Fin n) :
    hopfieldFullCoupling C i j * hopfieldFullCoupling C r t =
      hopfieldFullCoupling C i t * hopfieldFullCoupling C r j := by
  unfold hopfieldFullCoupling PrimeFerromagneticChain.centeredSpinCoupling
  ring

/--
The diagonal spin-square contribution is independent of the spin
configuration.
-/
theorem centeredDiagonalSpinContribution_eq_constant
    (σ : Fin n → IsingSpin) :
    (∑ i : Fin n,
      C.centeredSpinCoupling i i *
        IsingSpin.sign (σ i) * IsingSpin.sign (σ i)) =
      ∑ i : Fin n, C.centeredSpinCoupling i i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  cases σ i <;> norm_num [IsingSpin.sign]

/--
Two-prime logarithmic-convolution coefficient:
`(log * log)(pᵢpⱼ) = 2 log(pᵢ) log(pⱼ)` on a square-free two-prime state.

This is the finite two-body coefficient, not a global analytic Dirichlet-series
theorem.
-/
def twoPrimeLogConvolutionCoeff
    (i j : Fin n) : ℝ :=
  2 * C.siteEnergy i * C.siteEnergy j

/-- The two-prime logarithmic-convolution coefficient is symmetric. -/
theorem twoPrimeLogConvolutionCoeff_symm
    (i j : Fin n) :
    twoPrimeLogConvolutionCoeff C i j =
      twoPrimeLogConvolutionCoeff C j i := by
  unfold twoPrimeLogConvolutionCoeff
  ring

/-- The two-prime logarithmic-convolution coefficient is nonnegative. -/
theorem twoPrimeLogConvolutionCoeff_nonneg
    (i j : Fin n) :
    0 ≤ twoPrimeLogConvolutionCoeff C i j := by
  unfold twoPrimeLogConvolutionCoeff
  exact mul_nonneg (mul_nonneg (by norm_num)
    (C.siteEnergy_nonneg i)) (C.siteEnergy_nonneg j)

/-- The two-prime logarithmic-convolution coefficient is strictly positive. -/
theorem twoPrimeLogConvolutionCoeff_pos
    (i j : Fin n) :
    0 < twoPrimeLogConvolutionCoeff C i j := by
  unfold twoPrimeLogConvolutionCoeff
  exact mul_pos (mul_pos (by norm_num) (C.siteEnergy_pos i)) (C.siteEnergy_pos j)

/--
The centered occupation coupling is `κ` times the two-prime logarithmic
coefficient.
-/
theorem centeredOccupationCoupling_eq_kappa_mul_logConvolutionCoeff
    (i j : Fin n) :
    C.centeredOccupationCoupling i j =
      C.kappa * twoPrimeLogConvolutionCoeff C i j := by
  unfold PrimeFerromagneticChain.centeredOccupationCoupling twoPrimeLogConvolutionCoeff
  ring

/-! ## Wick/Krein and Hurwitz limit sockets -/

/--
witness-gated (Native Closure Mandated: Closure Debt) sign bridge between Euclidean damping and Lee--Yang
ferromagnetic sign.

This records the Wick/Krein step as data.  The file does not turn a positive
Euclidean heat kernel into a Lee--Yang theorem.
-/
structure WickKreinSignBridge
    (EuclideanWeight FerromagneticWeight KreinReadout : Type) where
  euclideanWeight : EuclideanWeight
  ferromagneticWeight : FerromagneticWeight
  kreinReadout : KreinReadout
  dampingSign : Prop
  ferromagneticSign : Prop
  wickKreinContinuation : Prop

namespace WickKreinSignBridge

variable {EuclideanWeight FerromagneticWeight KreinReadout : Type}
variable (W : WickKreinSignBridge EuclideanWeight FerromagneticWeight KreinReadout)

end WickKreinSignBridge

/--
witness-gated (Native Closure Mandated: Closure Debt) Hurwitz/Lee--Yang limit packet.

This is the final analytic bridge:
finite Lee--Yang stability plus nonvanishing renormalization plus locally
uniform convergence to the completed-`xi` Cayley readout, with no surviving
spurious zeros.
-/
@[socket_debt_tag, rep_depth operator]
structure HurwitzLeeYangXiLimitPacket
    (CompletedXiReadout RenormalizationReadout LimitReadout : Type) where
  completedXiReadout : CompletedXiReadout
  renormalizationReadout : RenormalizationReadout
  limitReadout : LimitReadout
  finiteLeeYangStability : Prop
  nonvanishingRenormalization : Prop
  locallyUniformXiLimit : Prop
  noSpuriousZeros : Prop
  hurwitzTransfer : Prop

namespace HurwitzLeeYangXiLimitPacket

variable {CompletedXiReadout RenormalizationReadout LimitReadout : Type}
variable (H : HurwitzLeeYangXiLimitPacket
  CompletedXiReadout RenormalizationReadout LimitReadout)

end HurwitzLeeYangXiLimitPacket

/--
Capstone packet joining finite Hopfield algebra, Wick/Krein sign bridge,
Hurwitz transfer, zero-mode protection, and relative determinant/scattering.
-/
structure HopfieldLimitBridgePacket
    (CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
      EuclideanWeight FerromagneticWeight KreinReadout RenormalizationReadout
      LimitReadout : Type) where
  zeroModeProtection :
    ZeroModeProtectionPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
  wickKrein :
    WickKreinSignBridge EuclideanWeight FerromagneticWeight KreinReadout
  hurwitzLimit :
    HurwitzLeeYangXiLimitPacket
      CompletedXiReadout RenormalizationReadout LimitReadout
  relativeDeterminant :
    RelativeDeterminantScatteringPacket
  /-- Final supplied law linking the analytic limit to the protected zero-mode lane. -/
  limit_eq_protectedZeroModeReadout : Prop

namespace HopfieldLimitBridgePacket

variable {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
    EuclideanWeight FerromagneticWeight KreinReadout RenormalizationReadout
    LimitReadout : Type}
variable
  (B : HopfieldLimitBridgePacket
    CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
    EuclideanWeight FerromagneticWeight KreinReadout RenormalizationReadout
    LimitReadout)

end HopfieldLimitBridgePacket

end InfoGeometry.Canonical.PrimeLeeYangHopfieldLimitBridge
