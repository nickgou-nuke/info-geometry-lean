import InfoGeometry.Categorical.LogNilpotentCrossCheckedR
import InfoGeometry.Canonical.LogJordanTensorFusionDepth
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

Concrete non-involutive checked braid on the repository's standard rank-two
logarithmic Jordan cell.

This file closes the final explicit witness required by
`LogNilpotentCrossCheckedR.logCheckedRDatum`: for every nonzero scalar `p`, the
checked braid

`τ ∘ (I + p (N ⊗ N))`

has nontrivial double braiding.  The proof reuses the existing rank-two Jordan
basis and the tensor-coordinate detector from `LogJordanTensorFusionDepth`.
The Hadjiivanov coefficient `logShearBase = -2πi` is then shown nonzero and used
to produce a concrete repository-owned checked-`R` datum and a logarithmic
categorical automorphism.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

open scoped TensorProduct

open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Canonical.LogJordanTensorFusion
open InfoGeometry.Canonical.LogJordanTensorFusionDepth
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
open InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum
open InfoGeometry.Clifford.LogCftMonodromy

/-- The standard square-zero rank-two logarithmic object. -/
def standardJordanObject : LogNilpotentModule ℂ where
  toLogEndModule :=
    { V := JordanCarrier ℂ
      N := jordanNilpotentLinear }
  nilpotencyOrder := 2
  nilpotent := by
    simpa [pow_two, Module.End.mul_eq_comp] using
      (jordanNilpotentLinear_sq_zero (𝕜 := ℂ))

/-- Square-zero certificate in the exact form consumed by the checked-`R`
construction. -/
theorem standardJordanObject_sq_zero :
    standardJordanObject.N ^ 2 = 0 := by
  exact standardJordanObject.nilpotent

@[simp]
theorem standardJordanObject_N_e0 :
    standardJordanObject.N (e0 : JordanCarrier ℂ) = 0 := by
  exact jordanNilpotentLinear_e0 (𝕜 := ℂ)

@[simp]
theorem standardJordanObject_N_e1 :
    standardJordanObject.N (e1 : JordanCarrier ℂ) =
      (e0 : JordanCarrier ℂ) := by
  exact jordanNilpotentLinear_e1 (𝕜 := ℂ)

/-- Two applications of the checked logarithmic braid differ from the identity
by the explicit mixed primary tensor state. -/
theorem standard_logCheckedR_sq_e1_tmul_e1 (p : ℂ) :
    let R := logCheckedR standardJordanObject standardJordanObject_sq_zero p
    R (R ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ))) =
      (e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ) +
        (2 * p) •
          ((e0 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e0 : JordanCarrier ℂ)) := by
  dsimp
  rw [logCheckedR_tmul, logCheckedR_tmul]
  simp [standardJordanObject_N_e0, standardJordanObject_N_e1]
  module

/-- Every nonzero logarithmic cross coefficient produces nontrivial double
braiding on the standard rank-two Jordan cell. -/
theorem standard_logCheckedR_monodromy_nontrivial
    (p : ℂ) (hp : p ≠ 0) :
    ((logCheckedR standardJordanObject standardJordanObject_sq_zero p).trans
      (logCheckedR standardJordanObject standardJordanObject_sq_zero p)).toLinearMap ≠
      LinearMap.id := by
  intro hmono
  have hv := LinearMap.congr_fun hmono
    ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ))
  have hsq := standard_logCheckedR_sq_e1_tmul_e1 p
  change
    logCheckedR standardJordanObject standardJordanObject_sq_zero p
        (logCheckedR standardJordanObject standardJordanObject_sq_zero p
          ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ))) =
      ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ)) at hv
  rw [hsq] at hv
  have hcoord := congrArg (coord00 (𝕜 := ℂ)) hv
  have h2p : (2 : ℂ) * p = 0 := by
    simpa [coord00_tmul, e0, e1, Pi.single] using hcoord
  rcases mul_eq_zero.mp h2p with h2 | hp0
  · norm_num at h2
  · exact hp hp0

/-- The universal Hadjiivanov logarithmic shear coefficient is nonzero. -/
theorem logShearBase_ne_zero : logShearBase ≠ 0 := by
  unfold logShearBase
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by norm_num))
    Complex.I_ne_zero) hpi

/-- Concrete checked-`R` datum for the standard rank-two logarithmic cell at the
repository-owned Hadjiivanov shear parameter. -/
def standardHadjiivanovCheckedRDatum :
    QuantumG2RMatrixDatum ℂ standardJordanObject :=
  logCheckedRDatum standardJordanObject standardJordanObject_sq_zero
    logShearBase
    (standard_logCheckedR_monodromy_nontrivial
      logShearBase logShearBase_ne_zero)

/-- The corresponding checked braid is a genuine automorphism of the
logarithmic tensor object. -/
def standardHadjiivanovCheckedRLogIso :
    PairObj standardJordanObject ≅ PairObj standardJordanObject :=
  logCheckedRLogIso standardJordanObject standardJordanObject_sq_zero
    logShearBase
    (standard_logCheckedR_monodromy_nontrivial
      logShearBase logShearBase_ne_zero)

/-- The concrete standard Hadjiivanov checked `R` inherits the repository-owned
Yang--Baxter theorem through the existing datum interface. -/
theorem standardHadjiivanov_yangBaxter :
    standardHadjiivanovCheckedRDatum.checkR12.toLinearMap ∘ₗ
          standardHadjiivanovCheckedRDatum.checkR23.toLinearMap ∘ₗ
          standardHadjiivanovCheckedRDatum.checkR12.toLinearMap =
      standardHadjiivanovCheckedRDatum.checkR23.toLinearMap ∘ₗ
          standardHadjiivanovCheckedRDatum.checkR12.toLinearMap ∘ₗ
          standardHadjiivanovCheckedRDatum.checkR23.toLinearMap :=
  standardHadjiivanovCheckedRDatum.yangBaxter

/-- Its double braiding is strictly nontrivial. -/
theorem standardHadjiivanov_monodromy_ne_id :
    standardHadjiivanovCheckedRDatum.monodromy.toLinearMap ≠ LinearMap.id :=
  standardHadjiivanovCheckedRDatum.monodromy_nontrivial

end InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
