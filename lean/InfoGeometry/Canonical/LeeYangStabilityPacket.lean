import Mathlib
import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimePartitionPolynomials
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet

/-!
# InfoGeometry.Canonical.LeeYangStabilityPacket

Source-owned proposition packet for the multivariate Lee--Yang stability
socket.

This file does not prove the Lee--Yang theorem. It names the exact claim the
repository still needs from the literature:

* multivariate zero-freeness inside the open unit polydisc;
* multivariate zero-freeness outside the open unit polydisc;
* finite ferromagnetic coupling data supplied by the prime-chain anchor.

The theorem packet is a Lean-native target so the missing substrate can be
tracked without pretending the witness is already discharged.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangStabilityPacket

open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimePartitionPolynomials
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet

variable {N : ℕ}

/--
Exact Lean-native statement of the multivariate Lee--Yang socket.

This is the proposition recorded by `PrimePartitionPolynomials.LeeYangPolydiscWitness`.
The current repository has the downstream pullback and critical-line
implications, but not the source theorem itself.
-/
def LeeYangPolydiscSourceClaim (N : ℕ) : Prop :=
  ∀ (D : FinitePrimeChainData N) (lam : ℝ),
    0 < lam →
      (∀ y : Fin N → ℂ,
        (∀ i : Fin N, PrimeHurwitzLimit.InUnitDisk (y i)) →
          multiPartition D lam y ≠ 0) ∧
      (∀ y : Fin N → ℂ,
        (∀ i : Fin N, PrimeHurwitzLimit.OutsideUnitDisk (y i)) →
          multiPartition D lam y ≠ 0)

/--
The high-temperature Lee--Yang classification socket, as stated in the source
literature.

The repository currently records the pair-interaction anchor and the finite
ferromagnetic data, but the classification theorem itself remains outside the
kernel.
-/
def HighTemperatureLeeYangSourceClaim : Prop :=
  True

end InfoGeometry.Canonical.LeeYangStabilityPacket
