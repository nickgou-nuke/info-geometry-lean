import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.PhotonicSOI

open Complex

/-- 
The Variant B photonic SOI analog to the Microsoft Tetron.
It replaces the superconducting gap `Δ` with a dissipative coupling `κ_im`.
-/
structure PhotonicTetron where
  /-- The intrinsic loss rate of the silicon waveguides. -/
  gamma : ℝ
  /-- The dissipative coupling strength mimicking the superconducting gap. -/
  kappa_im : ℝ
  /-- Physical constraint: coupling cannot exceed intrinsic loss in passive systems. -/
  passive_constraint : kappa_im ≤ gamma

/-- The effective decay rate of the topologically protected parity mode. -/
@[rep_depth thermo]
def parity_decay_rate (pt : PhotonicTetron) : ℝ :=
  pt.gamma - pt.kappa_im

/-- The decay rate of the unprotected bulk mode. -/
@[rep_depth thermo]
def bulk_decay_rate (pt : PhotonicTetron) : ℝ :=
  pt.gamma + pt.kappa_im

/-- 
Theorem: The parity mode has a strictly longer lifetime (smaller decay rate)
than the bulk mode, assuming strictly positive dissipative coupling.
-/
@[rep_depth thermo]
theorem parity_lifetime_boost (pt : PhotonicTetron) (h : 0 < pt.kappa_im) :
    parity_decay_rate pt < bulk_decay_rate pt := by
  dsimp [parity_decay_rate, bulk_decay_rate]
  linarith

/-- 
Theorem: As the dissipative coupling approaches the intrinsic loss,
the parity decay rate vanishes, yielding the macroscopic parity lifetime.
(Analogous to the 20-second lifetime in the InAs-Pb Tetron).
-/
@[rep_depth thermo]
theorem macroscopic_parity_lifetime (pt : PhotonicTetron) (h : pt.kappa_im = pt.gamma) :
    parity_decay_rate pt = 0 := by
  dsimp [parity_decay_rate]
  rw [h, sub_self]

end InfoGeometry.Canonical.PhotonicSOI
