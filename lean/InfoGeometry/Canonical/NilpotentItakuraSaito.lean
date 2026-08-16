import InfoGeometry.Canonical.BiquaternionKANnilpotent

/-!
# Nilpotent Itakura--Saito finite algebra

This owner contains only finite matrix identities proved in the repository.
Analytic coefficient limits and boundary interpretations are deliberately not
represented as structure fields: without a concrete construction they would be
assumptions rather than theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.NilpotentItakuraSaito

open Matrix
open BiquaternionKANnilpotent

/-- The concrete nilpotent Jordan/KAN boundary mode reused from the restored
KAN nilpotent owner. -/
abbrev KNil : BiquaternionKANnilpotent.M2C := K_N

/-- The concrete boundary mode is nilpotent. -/
theorem KNil_sq_zero : KNil * KNil = 0 :=
  K_N_is_nilpotent

/-- Formal exponential truncation for a square-zero element. -/
def nilExp (K : BiquaternionKANnilpotent.M2C) : BiquaternionKANnilpotent.M2C := 1 + K

/-- Itakura--Saito remainder using the nilpotent-truncated exponential. -/
def nilItakuraSaito (K : BiquaternionKANnilpotent.M2C) : BiquaternionKANnilpotent.M2C := nilExp K - 1 - K

/-- The nilpotent Itakura--Saito remainder vanishes algebraically. -/
theorem nilItakuraSaito_zero (K : BiquaternionKANnilpotent.M2C) : nilItakuraSaito K = 0 := by
  ext i j
  simp [nilItakuraSaito, nilExp, Matrix.sub_apply]

/-- In particular, the concrete nilpotent has zero divergence. -/
theorem KNil_itakura_zero : nilItakuraSaito KNil = 0 :=
  nilItakuraSaito_zero KNil

/-- Scaled nilpotents also have zero truncated Itakura--Saito remainder. -/
theorem scaled_nilItakuraSaito_zero (eps : ℂ) (K : BiquaternionKANnilpotent.M2C) :
    nilItakuraSaito (eps • K) = 0 :=
  nilItakuraSaito_zero (eps • K)

theorem nonzero_nilpotent_not_isUnit
    (K : BiquaternionKANnilpotent.M2C) (hKsq : K * K = 0) :
    ¬ IsUnit K := by
  intro hKunit
  have hzeroUnit : IsUnit (K * K) := hKunit.mul hKunit
  rw [hKsq] at hzeroUnit
  exact not_isUnit_zero hzeroUnit

/-! The complete finite conclusion for an explicitly supplied nilpotent mode. -/
theorem nilpotent_itakura_saito_synthesis
    (K : BiquaternionKANnilpotent.M2C) (hK : K * K = 0)
    (hMassless : Matrix.trace K = 0)
    (hPara : K ≠ 0) :
    KNil * KNil = 0 ∧
    nilItakuraSaito KNil = 0 ∧
    (∀ eps : ℂ, nilItakuraSaito (eps • K) = 0) ∧
    K * K = 0 ∧
    (¬ IsUnit K) ∧ Matrix.trace K = 0 ∧ K ≠ 0 := by
  exact ⟨KNil_sq_zero, KNil_itakura_zero,
    fun eps => scaled_nilItakuraSaito_zero eps K,
    hK, nonzero_nilpotent_not_isUnit K hK, hMassless, hPara⟩

end InfoGeometry.Canonical.NilpotentItakuraSaito

end noncomputable section
