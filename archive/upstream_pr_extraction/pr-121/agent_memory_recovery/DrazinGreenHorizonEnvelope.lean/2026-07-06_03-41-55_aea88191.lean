import Mathlib
import InfoGeometry.Canonical.HorizonZitterModes
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinGreenHorizonEnvelope

Drazin-Green-Hodge envelope socket.

This module separates the two Drazin roles:

* `p_A = A * Aᴰ` is the signal/horizon support;
* `H_L = 1 - L * Lᴰ` is the harmonic/generalized-zero projector of a
  frequency/Laplacian-like operator.

The matter envelope is the two-stage compression

`H_L * (p_A * x * p_A) * H_L`.

If `p_A` and `H_L` commute, the envelope is a single corner

`e_{A,L} * x * e_{A,L}`, where `e_{A,L} = p_A * H_L`.

The word "harmonic" is theorem-safe here: without additional semisimplicity or
self-adjoint Laplacian hypotheses, `H_L` is the Drazin generalized zero-sector
projector.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinGreenHorizonEnvelope

open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.Canonical.HorizonZitterModes
open InfoGeometry.Canonical.Drazin

/--
Drazin/Green data for a frequency or Laplacian-like operator `L`.

`LD` is the Drazin inverse.  `P_reg = L * LD` is the regular/nonzero-sector
projector.  `P_harm = 1 - P_reg` is the harmonic/generalized-null projector.
-/
@[rep_depth operator]
structure DrazinGreenData
    (Obs : Type*) [Ring Obs] [Star Obs] where
  L : Obs
  LD : Obs
  P_reg : Obs
  P_harm : Obs
  index : ℕ
  drazin_True : IsDrazinInverse L LD index
  P_reg_def : P_reg = L * LD
  P_harm_def : P_harm = 1 - P_reg
  P_reg_self_adjoint : star P_reg = P_reg
  P_harm_self_adjoint : star P_harm = P_harm

namespace DrazinGreenData

variable {Obs : Type*} [Ring Obs] [Star Obs]
variable (G : DrazinGreenData Obs)

/-- The regular/nonzero-sector projector is idempotent. -/
@[rep_depth operator]
theorem P_reg_idempotent :
    G.P_reg * G.P_reg = G.P_reg := by
  rw [G.P_reg_def]
  exact IsDrazinInverse.projection_is_idempotent G.drazin_True

/-- The harmonic/generalized-zero projector is idempotent. -/
@[rep_depth operator]
theorem P_harm_idempotent :
    G.P_harm * G.P_harm = G.P_harm := by
  rw [G.P_harm_def, G.P_reg_def]
  simpa [IsDrazinInverse.complementaryProjection, IsDrazinInverse.projection] using
    IsDrazinInverse.complementaryProjection_is_idempotent G.drazin_True

/-- The Drazin Green operator commutes with the frequency operator on the core. -/
@[rep_depth operator]
theorem L_mul_LD_eq_LD_mul_L :
    G.L * G.LD = G.LD * G.L :=
  G.drazin_True.comm

end DrazinGreenData

/-- Drazin horizon data reuses the persistence support owner. -/
abbrev DrazinHorizon
    (Obs : Type*) [Ring Obs] [Star Obs] :=
  DrazinSupportData Obs

/--
Matter envelope:
first compress to the Drazin horizon `p_A`, then project to the
harmonic/generalized-zero sector of `L`.
-/
@[rep_depth operator]
def horizonHarmonicEnvelope
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (x : Obs) : Obs :=