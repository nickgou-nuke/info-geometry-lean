import Mathlib
import InfoGeometry.Spectral.Homotopy.Suspension
import InfoGeometry.Spectral.Spectrum.Basic

/-!
# Finite Eilenberg--MacLane-style readouts

Mathlib does not provide the unstable `K(G,n)` API expected by the old port.
This file records the finite algebraic readout that the surrounding spectral
bookkeeping actually uses.
-/

noncomputable section

universe u

namespace InfoGeometry.Spectral.Homotopy.EM

open InfoGeometry.Spectral.Homotopy.Suspension
open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Canonical.SplitCliffordTensorBridge

set_option linter.dupNamespace false

/-- Finite `K(G,n)` readout: the carrier is `G` with basepoint `0`. -/
def EM (G : Type*) [Zero G] (_n : ℕ) : PointedReadout where
  carrier := G
  base := 0

@[simp]
theorem EM_base (G : Type*) [Zero G] (n : ℕ) :
    (EM G n).base = (0 : G) :=
  rfl

/-- Constant Eilenberg--MacLane-style prespectrum for a ring. -/
def EMRing (R : Type*) [Ring R] : Prespectrum :=
  Prespectrum.ofFun (fun _ => R) (fun _ x => x)

@[simp]
theorem EMRing_space (R : Type*) [Ring R] (n : ℕ) :
    (EMRing R).space n = R :=
  rfl

@[simp]
theorem EMRing_step (R : Type*) [Ring R] (n : ℕ) (x : R) :
    (EMRing R).step n x = x :=
  rfl

/-- Alias retained for the old port name. -/
def EMPrespectrum (R : Type*) [Ring R] : Prespectrum :=
  EMRing R

/-- Finite split-Clifford homotopy readout: iterated loops are carrier identity. -/
def SplitCliffordHomotopyGroup (n k : ℕ) : Type :=
  (IteratedLoopSpace k (SplitCliffordSuspension n)).carrier

@[simp]
theorem SplitCliffordHomotopyGroup_zero (n : ℕ) :
    SplitCliffordHomotopyGroup n 0 = (SplitCliffordSuspension n).carrier :=
  rfl

/-- Finite homology readout for an EM carrier. -/
def EMHomology (G : Type u) [Zero G] (_n _i : ℕ) : Type u :=
  G

/-- Split-Clifford Postnikov bookkeeping as the finite prespectrum already owned. -/
def SplitCliffordPostnikov (_n : ℕ) : Prespectrum :=
  SplitCliffordPrespectrum

@[simp]
theorem SplitCliffordPostnikov_space (n k : ℕ) :
    (SplitCliffordPostnikov n).space k = SplitClNNAlg k :=
  rfl

end InfoGeometry.Spectral.Homotopy.EM
