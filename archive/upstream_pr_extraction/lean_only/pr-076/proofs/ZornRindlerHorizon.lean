import proofs.ZornLightconeCAR
import InfoGeometry.Physics.SplitOctonionBraidSU3

noncomputable section

open CliffordAlgebra LinearMap
open InfoGeometry.Physics.SplitOctonionBraidSU3 CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation ZornCliffordParityAPI
open ZornChiralLightcone ZornLightconeCAR

namespace ZornRindlerHorizon

/-- Algebraic grading generator used by the Rindler analogy.

This is `χ`, not the complex structure `J = iχ`. The module proves grading
and CAR identities; it does not construct a boost flow or a KMS state.
-/
def rindlerModularHamiltonian : Module.End ℂ DiracSpinor16 :=
  ZornCliffordParityAPI.chiralityOperator

/-- 2. Хоризонтното усукано CAR условие за невакуозност. -/
theorem rindler_horizon_anticommutator (r : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaMinus r + lightconeSigmaMinus r * lightconeSigmaPlus r = 
    lightconeChannelProjector r := by
  exact lightconeSigma_anticommutator r

/-- The upper directed block has grading weight `+2`. -/
theorem causal_order_proof (r : Fin 3) :
    rindlerModularHamiltonian * lightconeSigmaPlus r - lightconeSigmaPlus r * rindlerModularHamiltonian = 
    (2 : ℂ) • lightconeSigmaPlus r := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.smul_apply]
  rw [rindlerModularHamiltonian,
    ZornCliffordParityAPI.chiralityOperator_apply,
    lightconeSigmaPlus_apply,
    ZornCliffordParityAPI.chiralityOperator_apply,
    lightconeSigmaPlus_apply,
    CanonicalZornSpinChirality.cliffordMinus_neg]
  apply Prod.ext <;> simp [two_smul, sub_eq_add_neg]

/-- The lower directed block has grading weight `-2`. -/
theorem causal_order_minus_proof (r : Fin 3) :
    rindlerModularHamiltonian * lightconeSigmaMinus r -
        lightconeSigmaMinus r * rindlerModularHamiltonian =
      (-2 : ℂ) • lightconeSigmaMinus r := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.smul_apply]
  rw [rindlerModularHamiltonian,
    ZornCliffordParityAPI.chiralityOperator_apply,
    lightconeSigmaMinus_apply,
    ZornCliffordParityAPI.chiralityOperator_apply,
    lightconeSigmaMinus_apply]
  apply Prod.ext <;> simp [two_smul, sub_eq_add_neg]

/-- 3. ОФИЦИАЛНА СТРУКТУРА НА РИНДЛЕРОВИЯ ХОРИЗОНТ (Causal Orientation) -/
structure RindlerHorizonStructure (r : Fin 3) where
  horizonPlus  : Module.End ℂ DiracSpinor16 := lightconeSigmaPlus r
  horizonMinus : Module.End ℂ DiracSpinor16 := lightconeSigmaMinus r
  modularH     : Module.End ℂ DiracSpinor16 := rindlerModularHamiltonian
  is_horizon   : horizonPlus * horizonPlus = 0 ∧ horizonMinus * horizonMinus = 0
  non_vacuous  : horizonPlus * horizonMinus + horizonMinus * horizonPlus ≠ 0
  causal_order_plus : modularH * horizonPlus - horizonPlus * modularH =
    (2 : ℂ) • horizonPlus
  causal_order_minus : modularH * horizonMinus - horizonMinus * modularH =
    (-2 : ℂ) • horizonMinus

/-- Конструкция на реалния Риндлеров хоризонт за даден канал -/
def buildRindlerHorizon (r : Fin 3) : RindlerHorizonStructure r where
  is_horizon := ⟨lightconeSigmaPlus_nilpotent r, lightconeSigmaMinus_nilpotent r⟩
  non_vacuous := by
    rw [rindler_horizon_anticommutator]
    exact lightconeChannelProjector_ne_zero r
  causal_order_plus := causal_order_proof r
  causal_order_minus := causal_order_minus_proof r

end ZornRindlerHorizon
