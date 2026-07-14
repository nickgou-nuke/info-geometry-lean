import InfoGeometry.Canonical.HypercomplexTriadVirasoroBridge

/-!
# InfoGeometry.Canonical.VirasoroCasimirCentralChargeReadback

Finite readback layer for extracting the Virasoro central charge from cocycle and
Casimir-defect data.

This is theorem-only and algebraic:

* no analytic completion claim,
* no global CFT construction,
* no Type III factor theorem.
-/

namespace VirasoroCasimirCentralChargeReadback

open InfoGeometry.Canonical.HypercomplexTriadVirasoroBridge

/--
A compact readback packet over a Virasoro cocycle/Casimir datum.
-/
structure CentralChargeReadbackPacket
    (A : Type*) [Ring A] [Module ℝ A] where
  datum : VirasoroCocycleCasimirDatum A

namespace CentralChargeReadbackPacket

variable {A : Type*} [Ring A] [Module ℝ A]

/-- Central charge equals the Casimir defect readout. -/
theorem centralCharge_eq_casimirDefect
    (P : CentralChargeReadbackPacket A) :
    P.datum.centralCharge = P.datum.casimirDefect :=
  P.datum.centralCharge_eq_casimirDefect

/-- Cocycle value on opposite modes is the standard central term. -/
theorem cocycle_on_opposite_modes
    (P : CentralChargeReadbackPacket A) (m : ℤ) :
    P.datum.cocycle m (-m) =
      (P.datum.centralCharge / 12) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) := by
  simpa using P.datum.cocycle_on_opposite_modes m

/-- Central cocycle vanishes on `m = 0`. -/
theorem cocycle_zero_zero
    (P : CentralChargeReadbackPacket A) :
    P.datum.cocycle 0 0 = 0 := by
  have h := P.cocycle_on_opposite_modes 0
  simpa using h

/-- Central cocycle vanishes on `m = 1`. -/
theorem cocycle_one_neg_one
    (P : CentralChargeReadbackPacket A) :
    P.datum.cocycle 1 (-1) = 0 := by
  have h := P.cocycle_on_opposite_modes 1
  norm_num at h
  simpa using h

/-- Central cocycle vanishes on `m = -1`. -/
theorem cocycle_neg_one_one
    (P : CentralChargeReadbackPacket A) :
    P.datum.cocycle (-1) 1 = 0 := by
  have h := P.cocycle_on_opposite_modes (-1)
  norm_num at h
  simpa using h

/-- The mode-2 opposite-mode cocycle is exactly `c/2`. -/
theorem cocycle_two_neg_two
    (P : CentralChargeReadbackPacket A) :
    P.datum.cocycle 2 (-2) = P.datum.centralCharge / 2 := by
  have h := P.cocycle_on_opposite_modes 2
  norm_num at h
  linarith

/-- The mode-(-2) opposite-mode cocycle is exactly `-c/2`. -/
theorem cocycle_neg_two_two
    (P : CentralChargeReadbackPacket A) :
    P.datum.cocycle (-2) 2 = -(P.datum.centralCharge / 2) := by
  have h := P.cocycle_on_opposite_modes (-2)
  norm_num at h
  linarith

/-- Virasoro bracket readback at arbitrary pair `(m,n)`. -/
theorem virasoro_bracket_readback
    (P : CentralChargeReadbackPacket A) (m n : ℤ) :
    commutator (P.datum.L m) (P.datum.L n) =
      ((m - n : ℤ) : ℝ) • P.datum.L (m + n) + (P.datum.cocycle m n) • (1 : A) :=
  P.datum.virasoro_bracket m n

/-- Specialization of the bracket at opposite modes `(m,-m)`. -/
theorem virasoro_bracket_opposite_modes
    (P : CentralChargeReadbackPacket A) (m : ℤ) :
    commutator (P.datum.L m) (P.datum.L (-m)) =
      ((2 * m : ℤ) : ℝ) • P.datum.L 0 + (P.datum.cocycle m (-m)) • (1 : A) := by
  simpa [sub_eq_add_neg, two_mul, add_assoc] using P.virasoro_bracket_readback m (-m)

end CentralChargeReadbackPacket

/--
Bridge-level readback packet:
triad identification plus Virasoro central/cocycle readback.
-/
structure TriadVirasoroCentralReadback
    (A : Type*) [Ring A] [Module ℝ A] where
  bridge : TriadToVirasoroBridge A

namespace TriadVirasoroCentralReadback

variable {A : Type*} [Ring A] [Module ℝ A]

/-- Central charge as Casimir defect through the triad-to-Virasoro bridge. -/
theorem centralCharge_eq_casimirDefect
    (B : TriadVirasoroCentralReadback A) :
    B.bridge.vir.centralCharge = B.bridge.vir.casimirDefect :=
  B.bridge.vir.centralCharge_eq_casimirDefect

/-- Opposite-mode cocycle readback through the triad-to-Virasoro bridge. -/
theorem cocycle_on_opposite_modes
    (B : TriadVirasoroCentralReadback A) (m : ℤ) :
    B.bridge.vir.cocycle m (-m) =
      (B.bridge.vir.centralCharge / 12) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) := by
  simpa using B.bridge.vir.cocycle_on_opposite_modes m

/-- Vacuum annihilation transfer from triad nilpotent `N` to Virasoro `L_{-1}`. -/
theorem LminusOne_vacuum_of_N_vacuum
    (B : TriadVirasoroCentralReadback A)
    (Ω : A)
    (hNvac : B.bridge.triad.N * Ω = 0) :
    B.bridge.vir.L (-1) * Ω = 0 :=
  TriadToVirasoroBridge.LminusOne_vacuum_of_N_vacuum B.bridge Ω hNvac

end TriadVirasoroCentralReadback

end VirasoroCasimirCentralChargeReadback
