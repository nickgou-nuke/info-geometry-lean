import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet

/-!
# InfoGeometry.Canonical.PrimeLeeYangRHBridge

Conditional Lee--Yang reduction of RH.

This file records the theorem-safe target:

finite Lee--Yang prime approximants
+ nonvanishing renormalization
+ categorical/Hestenes--Krein colimit convergence to the Cayley pullback readout
+ no surviving spurious zeros
⇒ RH-style critical-line zero location.

No global number-theoretic conclusion is asserted without the colimit witness.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangRHBridge

open CayleyCriticalLineCircleBridge
open PrimeLeeYangFerromagnet

/-- Cayley map sending the Riemann critical line to the Lee--Yang unit circle. -/
@[rep_depth operator]
def cayley
    (s : ℂ) : ℂ :=
  cayleyToFugacity s

/-- Inverse Cayley map. -/
@[rep_depth operator]
def cayleyInv
    (z : ℂ) : ℂ :=
  cayleyToTemperature z

/--
Abstract predicate for the completed `xi` zero set.

The `zero_ne_one` field explicitly excludes the Cayley pole/boundary point.
This is supplied by the owner of the concrete completed-`xi` zero predicate.
-/
@[rep_depth operator]
structure CompletedXiZeroPredicate where
  xiZero : ℂ → Prop
  zero_ne_one :
    ∀ s : ℂ, xiZero s → s ≠ 1

/-- RH formulated relative to a supplied completed-`xi` zero predicate. -/
@[rep_depth operator]
def RiemannHypothesis
    (Ξ : CompletedXiZeroPredicate) : Prop :=
  ∀ s : ℂ, Ξ.xiZero s → s.re = (1 / 2 : ℝ)

/--
Cayley geometry witness.

The elementary geometry is already proved in `CayleyCriticalLineCircleBridge`;
this witness is kept as a compact interface for later analytic models that use
`Complex.normSq`, matching the existing Cayley geometry owner.
-/
@[rep_depth operator]
structure CayleyCriticalLineWitness where
  critical_iff_unit :
    ∀ s : ℂ, s ≠ 1 →
      (s.re = (1 / 2 : ℝ) ↔ Complex.normSq (cayley s) = 1)
  reflection_inversion :
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      cayley (1 - s) = (cayley s)⁻¹

/--
Finite Lee--Yang approximation packet for the Cayley pullback of completed
`xi`.

The colimit work remains explicit:

* finite Lee--Yang stability for the actual partition polynomials;
* nonvanishing renormalization;
* filtered-colimit convergence to the completed-`xi` Cayley readout;
* no surviving spurious zeros;
* zero transfer from completed-`xi` zeros to the Cayley unit circle.
-/
@[socket_debt_tag, rep_depth operator]
structure LeeYangPrimeApproximation
    (Ξ : CompletedXiZeroPredicate) where
  approximant :
    ℕ → Polynomial ℂ
  renormalization :
    ℕ → ℂ → ℂ
  leeYangZerosOnCircle :
    ∀ N : ℕ, ∀ z : ℂ,
      (approximant N).IsRoot z → Complex.normSq z = 1
  renormalization_nonzero :
    ∀ N : ℕ, ∀ z : ℂ,
      renormalization N z ≠ 0
  locallyUniformLimitToXi : Prop
  noSpuriousZeros : Prop
  zeros_transfer_to_xi :
    ∀ s : ℂ, Ξ.xiZero s → Complex.normSq (cayley s) = 1

namespace LeeYangPrimeApproximation

variable {Ξ : CompletedXiZeroPredicate}
variable (A : LeeYangPrimeApproximation Ξ)

/-- Re-export of the supplied finite Lee--Yang circle law. -/
@[bridge_target_tag, rep_depth operator]
theorem leeYang
    (N : ℕ)
    (z : ℂ)
    (hz : (A.approximant N).IsRoot z) :
    Complex.normSq z = 1 :=
  A.leeYangZerosOnCircle N z hz

/-- Re-export of the supplied nonvanishing-renormalization law. -/
@[rep_depth operator]
theorem renormalization_nonzero_holds
    (N : ℕ)
    (z : ℂ) :
    A.renormalization N z ≠ 0 :=
  A.renormalization_nonzero N z

end LeeYangPrimeApproximation

/--
Conditional RH theorem from a Lee--Yang prime approximation.

This theorem is deliberately small: the colimit zero-transfer work is exactly
the supplied `zeros_transfer_to_xi` witness, and the final geometric step is
the supplied Cayley critical-line witness.
-/
@[bridge_target_tag, rep_depth operator]
theorem RH_of_LeeYangPrimeApproximation
    (Ξ : CompletedXiZeroPredicate)
    (C : CayleyCriticalLineWitness)
    (A : LeeYangPrimeApproximation Ξ) :
    RiemannHypothesis Ξ := by
  intro s hs
  have hcircle : Complex.normSq (cayley s) = 1 :=
    A.zeros_transfer_to_xi s hs
  by_cases hs1 : s = 1
  · exact False.elim (Ξ.zero_ne_one s hs hs1)
  · exact (C.critical_iff_unit s hs1).mpr hcircle

end InfoGeometry.Canonical.PrimeLeeYangRHBridge
