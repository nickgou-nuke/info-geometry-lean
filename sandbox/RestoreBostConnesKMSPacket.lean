import InfoGeometry.Canonical.BostConnesKMS

/-!
# RestoreBostConnesKMSPacket

Small sandbox packet for the projection-level KMS formulas.
-/

namespace InfoGeometry.Restore.BostConnesKMSPacket

open scoped BigOperators
open InfoGeometry.Arithmetic.BostConnesSystem

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- Prime-power readout for the multiplicative Cuntz indexing. -/
theorem S_prime_power_restore (C : InfoGeometry.Canonical.BostConnesKMS.BostConnesCuntzSystem Op)
    (p k : ℕ) (hp : Nat.Prime p) :
    InfoGeometry.Canonical.BostConnesKMS.S C
        ((InfoGeometry.Arithmetic.BostConnesSystem.MultiplicativeIndexing.primePNat p hp) ^ k) =
      InfoGeometry.Canonical.BostConnesKMS.S C
        (InfoGeometry.Arithmetic.BostConnesSystem.MultiplicativeIndexing.primePNat p hp) ^ k := by
  exact InfoGeometry.Canonical.BostConnesKMS.S_prime_power C p k hp

/-- Ordered prime-power word readout. -/
theorem S_prime_power_list_prod_restore
    (C : InfoGeometry.Canonical.BostConnesKMS.BostConnesCuntzSystem Op)
    (factors : List InfoGeometry.Canonical.BostConnesKMS.PrimePowerIndex) :
    InfoGeometry.Canonical.BostConnesKMS.S C (factors.map InfoGeometry.Canonical.BostConnesKMS.PrimePowerIndex.toPNat).prod =
      (factors.map fun a => (InfoGeometry.Canonical.BostConnesKMS.PrimePowerIndex.primeGenerator C a) ^ a.k).prod := by
  exact InfoGeometry.Canonical.BostConnesKMS.S_prime_power_list_prod C factors

/-- Normalized KMS Boltzmann weight. -/
theorem kmsProjectionWeight_eq_restore (β ζβ : ℝ) (n : ℕ+) :
    InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight β ζβ n =
      ((n : ℕ) : ℝ) ^ (-β) / ζβ := by
  exact InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight_eq β ζβ n

/-- Diagonal KMS projection readout. -/
theorem kmsProjectionReadout_self_restore (β ζβ : ℝ) (n : ℕ+) :
    InfoGeometry.Canonical.BostConnesKMS.kmsProjectionReadout β ζβ n n =
      ((n : ℕ) : ℝ) ^ (-β) / ζβ := by
  exact InfoGeometry.Canonical.BostConnesKMS.kmsProjectionReadout_self β ζβ n

/-- Off-diagonal KMS projection readout vanishes. -/
theorem kmsProjectionReadout_ne_restore {β ζβ : ℝ} {n m : ℕ+} (h : n ≠ m) :
    InfoGeometry.Canonical.BostConnesKMS.kmsProjectionReadout β ζβ n m = 0 := by
  exact InfoGeometry.Canonical.BostConnesKMS.kmsProjectionReadout_ne (β := β) (ζβ := ζβ) h

end InfoGeometry.Restore.BostConnesKMSPacket
