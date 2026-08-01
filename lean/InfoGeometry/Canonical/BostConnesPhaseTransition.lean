import Mathlib

namespace InfoGeometry.Canonical

/--
Scalar partition-term readout for a Bost-Connes-style packet.
This file does not claim a zeta pole theorem or a phase-transition theorem.
-/
noncomputable def bostConnesPartitionTerm (n : ℕ) (β : ℝ) : ℝ :=
  (n : ℝ) ^ (-β)

/-- Carrier-only readout for a would-be KMS state. -/
structure KMSStateReadout (A : Type*) [Ring A] (β : ℝ) where
  /-- The evaluation functional (expectation value / thermodynamic state). -/
  eval : A → ℝ

end InfoGeometry.Canonical
