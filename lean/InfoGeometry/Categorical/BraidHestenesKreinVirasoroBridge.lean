/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Braid--Hestenes--Krein--Virasoro bridge

This module connects the existing categorical braid/Hestenes--Krein closure to
the existing Prime Sugawara/Virasoro owner.  It deliberately does not assert
an operator intertwiner that is not present in the repository: the categorical
braid endomorphisms and the affine Virasoro modes currently have different
carriers.  The common theorem is consequently a proof-carrying synthesis
packet, with any future representation/intertwining map left explicit.
-/

import InfoGeometry.Canonical.DikinLambdaBraidHestenesKreinClosure
import InfoGeometry.Canonical.PrimeVirasoroSugawara
import InfoGeometry.Canonical.CliffordToVirasoro
import InfoGeometry.Canonical.VirasoroSugawaraCentralChargeBridge

noncomputable section

namespace InfoGeometry.Categorical.BraidHestenesKreinVirasoroBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DikinLambdaBraidHestenesKreinClosure
open InfoGeometry.Canonical.PrimeVirasoroSugawara
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open InfoGeometry.Canonical.CliffordToVirasoro
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

universe u

/-- The existing closure data and the existing Sugawara/Virasoro owner,
without identifying their carriers. -/
structure BridgeData
    (PrimeLabel Field Coeff Finite Alg Weight Tangent State : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite]
    [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg]
    [LieAlgebra ℝ Alg]
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  closure : ClosureData Weight Tangent State
  sugawara :
    PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg

namespace BridgeData

variable
    {PrimeLabel Field Coeff Finite Alg Weight Tangent State : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite]
    [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg]
    [LieAlgebra ℝ Alg]
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (P : BridgeData PrimeLabel Field Coeff Finite Alg Weight Tangent State)

/-- The Hestenes--Krein/categorical closure is inherited unchanged. -/
theorem closure_readout :
    CertifiedReadout P.closure :=
  certifiedReadout P.closure

/-- The normalized Virasoro bracket is inherited from the Sugawara owner. -/
theorem virasoro_bracket
    (m n : ℤ)
    (hvir :
      ∀ m n : ℤ,
        ⁅P.sugawara.affineVirasoro.virasoro.Lmode m,
          P.sugawara.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) •
              P.sugawara.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) •
              P.sugawara.affineVirasoro.virasoro.central) :
    ⁅P.sugawara.affineVirasoro.virasoro.Lmode m,
      P.sugawara.affineVirasoro.virasoro.Lmode n⁆ =
      (m - n : ℝ) •
          P.sugawara.affineVirasoro.virasoro.Lmode (m + n) +
        (virasoroCentralCoefficient m n : ℝ) •
          P.sugawara.affineVirasoro.virasoro.central :=
  P.sugawara.virasoro_bracket_modes_normalized m n hvir

/-- The global-conformal low-mode subalgebra is inherited from Sugawara. -/
theorem sl2_low_modes
    (hvir :
      ∀ m n : ℤ,
        ⁅P.sugawara.affineVirasoro.virasoro.Lmode m,
          P.sugawara.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) •
              P.sugawara.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) •
              P.sugawara.affineVirasoro.virasoro.central) :
    ⁅P.sugawara.affineVirasoro.virasoro.Lmode 1,
        P.sugawara.affineVirasoro.virasoro.Lmode (-1)⁆ =
        (2 : ℝ) • P.sugawara.affineVirasoro.virasoro.Lmode 0 ∧
    ⁅P.sugawara.affineVirasoro.virasoro.Lmode (-1),
        P.sugawara.affineVirasoro.virasoro.Lmode 1⁆ =
        (-2 : ℝ) • P.sugawara.affineVirasoro.virasoro.Lmode 0 ∧
    ⁅P.sugawara.affineVirasoro.virasoro.Lmode 0,
        P.sugawara.affineVirasoro.virasoro.Lmode 0⁆ = 0 :=
  P.sugawara.virasoro_bracket_sl2_low_modes hvir

/-- The existing abelian Sugawara owner supplies the cardinality-style
central-charge specialization used by the Virasoro lane. -/
theorem abelian_central_charge_eq_dimension
    (k d : ℝ) (hk : k ≠ 0) :
    VirasoroSugawaraCentralChargeBridge.sugawaraCentralCharge k d 0 = d :=
  VirasoroSugawaraCentralChargeBridge.sugawara_central_charge_abelian k d hk

theorem central_charge_eq_card
    (S : Finset PrimeLabel)
    (hlevel : P.sugawara.affineVirasoro.level = 1)
    (hdim :
      P.sugawara.affineVirasoro.finiteDimension = (S.card : ℝ))
    (hdual : P.sugawara.affineVirasoro.dualCoxeterNumber = 0)
    (hcc :
      P.sugawara.affineVirasoro.centralCharge =
        P.sugawara.affineVirasoro.level *
            P.sugawara.affineVirasoro.finiteDimension /
          (P.sugawara.affineVirasoro.level +
            P.sugawara.affineVirasoro.dualCoxeterNumber)) :
    P.sugawara.affineVirasoro.centralCharge = (S.card : ℝ) := by
  rw [hcc, hlevel, hdual, hdim]
  norm_num

/-- Combined bridge theorem for the audited braid/Hestenes--Krein and
Virasoro/Sugawara lanes. -/
theorem certified_bridge
    (S : Finset PrimeLabel)
    (hlevel : P.sugawara.affineVirasoro.level = 1)
    (hdim :
      P.sugawara.affineVirasoro.finiteDimension = (S.card : ℝ))
    (hdual : P.sugawara.affineVirasoro.dualCoxeterNumber = 0)
    (hcc :
      P.sugawara.affineVirasoro.centralCharge =
        P.sugawara.affineVirasoro.level *
            P.sugawara.affineVirasoro.finiteDimension /
          (P.sugawara.affineVirasoro.level +
            P.sugawara.affineVirasoro.dualCoxeterNumber))
    (hvir :
      ∀ m n : ℤ,
        ⁅P.sugawara.affineVirasoro.virasoro.Lmode m,
          P.sugawara.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) •
              P.sugawara.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) •
              P.sugawara.affineVirasoro.virasoro.central) :
    CertifiedReadout P.closure ∧
    (⁅P.sugawara.affineVirasoro.virasoro.Lmode 1,
        P.sugawara.affineVirasoro.virasoro.Lmode (-1)⁆ =
        (2 : ℝ) • P.sugawara.affineVirasoro.virasoro.Lmode 0 ∧
      ⁅P.sugawara.affineVirasoro.virasoro.Lmode (-1),
        P.sugawara.affineVirasoro.virasoro.Lmode 1⁆ =
        (-2 : ℝ) • P.sugawara.affineVirasoro.virasoro.Lmode 0 ∧
      ⁅P.sugawara.affineVirasoro.virasoro.Lmode 0,
        P.sugawara.affineVirasoro.virasoro.Lmode 0⁆ = 0) ∧
    P.sugawara.affineVirasoro.centralCharge = (S.card : ℝ) :=
  ⟨certifiedReadout P.closure, P.sl2_low_modes hvir, P.central_charge_eq_card S
    hlevel hdim hdual hcc⟩

end BridgeData

end InfoGeometry.Categorical.BraidHestenesKreinVirasoroBridge
