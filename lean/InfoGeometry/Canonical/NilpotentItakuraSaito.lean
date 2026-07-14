import InfoGeometry.Canonical.BiquaternionKANnilpotent

/-!
# Nilpotent Itakura--Saito bridge

Recovered and normalized owner for the finite nilpotent Itakura--Saito slice.
The removable-disk archive carried a smaller theorem packet, while the external
auto lane preserved additional socket structure. This maintained owner keeps the
closed finite algebra together with the explicit socketed interpretation fields,
without asserting analytic or continuum claims.
-/

noncomputable section

namespace NilpotentItakuraSaito

open Matrix
open InfoGeometry.Canonical.BiquaternionKANnilpotent

abbrev M2C := InfoGeometry.Canonical.BiquaternionKANnilpotent.M2C

/-- The concrete nilpotent Jordan/KAN boundary mode reused from the restored
KAN nilpotent owner. -/
abbrev KNil : M2C := K_N

/-- The concrete boundary mode is nilpotent. -/
theorem KNil_sq_zero : KNil * KNil = 0 :=
  K_N_is_nilpotent

/-- Formal exponential truncation for a square-zero element. -/
def nilExp (K : M2C) : M2C := 1 + K

/-- Itakura--Saito remainder using the nilpotent-truncated exponential. -/
def nilItakuraSaito (K : M2C) : M2C := nilExp K - 1 - K

/-- The nilpotent Itakura--Saito remainder vanishes algebraically. -/
theorem nilItakuraSaito_zero (K : M2C) : nilItakuraSaito K = 0 := by
  ext i j
  simp [nilItakuraSaito, nilExp, Matrix.sub_apply]

/-- In particular, the concrete nilpotent has zero divergence. -/
theorem KNil_itakura_zero : nilItakuraSaito KNil = 0 :=
  nilItakuraSaito_zero KNil

/-- Scaled nilpotents also have zero truncated Itakura--Saito remainder. -/
theorem scaled_nilItakuraSaito_zero (eps : ℂ) (K : M2C) :
    nilItakuraSaito (eps • K) = 0 :=
  nilItakuraSaito_zero (eps • K)

/-- Socket for the analytic coefficient limit in the closed biquaternion formula. -/
structure NilpotentCoefficientLimitSocket where
  identityCoeffLimitZero : Prop
  generatorCoeffLimitZero : Prop

/-- Socket for the boundary parafermion information-geometry interpretation. -/
structure NilpotentBoundaryInfoSocket where
  K : M2C
  nilpotent : K * K = 0
  nonInvertibleBoundaryMode : Prop
  masslessLightconeMode : Prop
  parafermionDefect : Prop

/-- Nilpotency kills the Fisher/Bures quadratic term `K²`. -/
theorem fisher_quadratic_zero (S : NilpotentBoundaryInfoSocket) : S.K * S.K = 0 :=
  S.nilpotent

/-- Main synthesis theorem. -/
theorem nilpotent_itakura_saito_synthesis
    (C : NilpotentCoefficientLimitSocket) (S : NilpotentBoundaryInfoSocket)
    (hI : C.identityCoeffLimitZero) (hK : C.generatorCoeffLimitZero)
    (hNonInv : S.nonInvertibleBoundaryMode) (hMassless : S.masslessLightconeMode)
    (hPara : S.parafermionDefect) :
    KNil * KNil = 0 ∧
    nilItakuraSaito KNil = 0 ∧
    (∀ eps : ℂ, nilItakuraSaito (eps • S.K) = 0) ∧
    S.K * S.K = 0 ∧
    C.identityCoeffLimitZero ∧ C.generatorCoeffLimitZero ∧
    S.nonInvertibleBoundaryMode ∧ S.masslessLightconeMode ∧ S.parafermionDefect := by
  exact ⟨KNil_sq_zero, KNil_itakura_zero,
    fun eps => scaled_nilItakuraSaito_zero eps S.K,
    S.nilpotent, hI, hK, hNonInv, hMassless, hPara⟩

end NilpotentItakuraSaito

end noncomputable section