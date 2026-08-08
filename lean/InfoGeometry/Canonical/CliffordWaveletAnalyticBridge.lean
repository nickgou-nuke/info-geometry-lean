import Mathlib.Tactic
import InfoGeometry.Canonical.CliffordFractalWaveletBridge
import InfoGeometry.Canonical.PrimeCl11ModularAtomCore

/-!
# InfoGeometry.Canonical.CliffordWaveletAnalyticBridge

Closed algebraic bridge for the Clifford fractal wavelet socket.

This file proves only the local algebraic consequences already present in the
socket:

* tilt/switch admissibility;
* extraction of a local `Cl(1,1)` atom;
* involutivity of the local pseudoscalar.

No `sorry`.
No Hilbert-space representation theorem.
No wavelet convergence theorem.
No RH-level property.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordWaveletAnalyticBridge

open InfoGeometry.Canonical

namespace CliffordFractalWaveletSocket

variable {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]

/-- The socket already contains exactly the admissibility fields. -/
@[rep_depth operator]
theorem tiltSwitchCliffordAdmissible
    (S : CliffordFractalWaveletSocket Op) :
    TiltSwitchCliffordAdmissible S := by
  exact ⟨S.T_sq, S.S_sq, S.T_S_anticomm, S.gamma_anticomm⟩

/-- The local `Cl(1,1)` atom at coordinate `j`. -/
@[rep_depth operator]
def cl11AtomOfTiltSwitch
    (S : CliffordFractalWaveletSocket Op) (j : ℕ) :
    PrimeCl11ModularAtomCore.Cl11Atom Op where
  c := S.T j
  d := S.T j * S.S j
  c_sq := S.T_sq j
  d_sq := by
    have hT : S.T j * S.T j = 1 := S.T_sq j
    have hS : S.S j * S.S j = 1 := S.S_sq j
    have hTS : S.T j * S.S j = -(S.S j * S.T j) :=
      S.T_S_anticomm j
    have hST : S.S j * S.T j = -(S.T j * S.S j) := by
      simp [hTS]
    calc
      (S.T j * S.S j) * (S.T j * S.S j)
          = S.T j * (S.S j * S.T j) * S.S j := by
              noncomm_ring
      _ = S.T j * (-(S.T j * S.S j)) * S.S j := by
            rw [hST]
      _ = - ((S.T j * S.T j) * (S.S j * S.S j)) := by
            noncomm_ring
      _ = - (1 * 1) := by
            rw [hT, hS]
      _ = -1 := by simp
  anticomm := by
    have hT : S.T j * S.T j = 1 := S.T_sq j
    have hTS : S.T j * S.S j = -(S.S j * S.T j) :=
      S.T_S_anticomm j
    have hST : S.S j * S.T j = -(S.T j * S.S j) := by
      simp [hTS]
    calc
      S.T j * (S.T j * S.S j) + (S.T j * S.S j) * S.T j
          = (S.T j * S.T j) * S.S j + S.T j * (S.S j * S.T j) := by
              noncomm_ring
      _ = 1 * S.S j + S.T j * (-(S.T j * S.S j)) := by
            rw [hT, hST]
      _ = S.S j + -((S.T j * S.T j) * S.S j) := by
            noncomm_ring
      _ = S.S j + -(1 * S.S j) := by
            rw [hT]
      _ = 0 := by simp

/-- The local pseudoscalar squares to one. -/
@[rep_depth operator]
theorem cl11AtomOfTiltSwitch_mobiusParity_sq_eq_one
    (S : CliffordFractalWaveletSocket Op) (j : ℕ) :
    (CliffordFractalWaveletSocket.cl11AtomOfTiltSwitch S j).mobiusParity *
      (CliffordFractalWaveletSocket.cl11AtomOfTiltSwitch S j).mobiusParity = 1 :=
  (CliffordFractalWaveletSocket.cl11AtomOfTiltSwitch S j).mobiusParity_sq_eq_one

end CliffordFractalWaveletSocket

/-- Top-level alias for the socket admissibility packet. -/
@[rep_depth operator]
theorem tiltSwitchCliffordAdmissible
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (S : CliffordFractalWaveletSocket Op) :
    TiltSwitchCliffordAdmissible S :=
  CliffordFractalWaveletSocket.tiltSwitchCliffordAdmissible S

/-- Top-level alias for the local `Cl(1,1)` atom construction. -/
@[rep_depth operator]
def cl11AtomOfTiltSwitch
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (S : CliffordFractalWaveletSocket Op) (j : ℕ) :
    PrimeCl11ModularAtomCore.Cl11Atom Op :=
  CliffordFractalWaveletSocket.cl11AtomOfTiltSwitch S j

/-- Top-level alias for the local pseudoscalar involution. -/
@[rep_depth operator]
theorem cl11AtomOfTiltSwitch_mobiusParity_sq_eq_one
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (S : CliffordFractalWaveletSocket Op) (j : ℕ) :
    (cl11AtomOfTiltSwitch S j).mobiusParity *
      (cl11AtomOfTiltSwitch S j).mobiusParity = 1 :=
  CliffordFractalWaveletSocket.cl11AtomOfTiltSwitch_mobiusParity_sq_eq_one S j

end InfoGeometry.Canonical.CliffordWaveletAnalyticBridge
