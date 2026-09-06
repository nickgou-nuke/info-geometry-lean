import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimePartitionPolynomials
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet

/-!
# InfoGeometry.Canonical.LeeYangStabilityPacket

Source-owned proposition packet for the multivariate Lee--Yang stability
interface.

This file does not prove the Lee--Yang theorem. It names the exact claim the
repository still needs from the literature:

* multivariate zero-freeness inside the open unit polydisc;
* multivariate zero-freeness outside the open unit polydisc;
* finite ferromagnetic coupling data supplied by the prime-chain anchor.

The theorem packet is a Lean-native target so the missing substrate can be
tracked without pretending the property is already discharged.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangStabilityPacket

open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimePartitionPolynomials
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet

variable {N : ℕ}

/-
Exact Lean-native statement of the multivariate Lee--Yang interface.

This is the proposition recorded by `PrimePartitionPolynomials.LeeYangPolydiscWitness`.
The current repository has the downstream pullback and critical-line
implications, but not the source theorem itself.
-/
/-
The high-temperature Lee--Yang classification interface, as stated in the source
literature.

The repository currently records the pair-interaction anchor and the finite
ferromagnetic data, but the classification theorem itself remains outside the
kernel.
-/
/--
The exact finite Lee--Yang source claim is discharged by the packet property.

This is the theorem-safe bridge from the source packet statement to the
already-defined `LeeYangPolydiscWitness` payload. It does not prove the
Asano/Ruelle theorem itself.
-/
theorem highTemperatureLeeYangSourceClaim
    {N : ℕ}
    (LY : LeeYangPolydiscWitness) :
    ∀ (D : FinitePrimeChainData N) (lam : ℝ), 0 < lam →
      (∀ y : Fin N → ℂ,
        (∀ i : Fin N, PrimeHurwitzLimit.InUnitDisk (y i)) →
          multiPartition D lam y ≠ 0) ∧
      (∀ y : Fin N → ℂ,
        (∀ i : Fin N, PrimeHurwitzLimit.OutsideUnitDisk (y i)) →
          multiPartition D lam y ≠ 0) := by
  intro D lam hLam
  exact ⟨LY.1 D lam hLam, LY.2 D lam hLam⟩

/--
The source claim and the standard Lee--Yang property carry the same finite
zero-freeness content.

This is a definitional bridge: the repository keeps the exact theorem
statement separate from the structure that packages its two halves.
-/
theorem leeYangPolydiscWitness_iff_sourceClaim :
    (∀ N : ℕ, ∀ (D : FinitePrimeChainData N) (lam : ℝ), 0 < lam →
      (∀ y : Fin N → ℂ,
        (∀ i : Fin N, PrimeHurwitzLimit.InUnitDisk (y i)) →
          multiPartition D lam y ≠ 0) ∧
      (∀ y : Fin N → ℂ,
        (∀ i : Fin N, PrimeHurwitzLimit.OutsideUnitDisk (y i)) →
          multiPartition D lam y ≠ 0)) ↔ LeeYangPolydiscWitness := by
  constructor
  · intro H
    exact ⟨
      (by
        intro N D lam hLam y hy
        exact (H N D lam hLam).1 y hy),
      (by
        intro N D lam hLam y hy
        exact (H N D lam hLam).2 y hy)⟩
  · intro H
    intro N D lam hLam
    exact ⟨H.1 D lam hLam, H.2 D lam hLam⟩

end InfoGeometry.Canonical.LeeYangStabilityPacket
