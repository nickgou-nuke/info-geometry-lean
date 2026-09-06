import proofs.ZornChiralLightcone
import InfoGeometry.Canonical.CanonicalZornCliffordRepresentation
import InfoGeometry.Physics.SplitOctonionBraidSU3
import proofs.ZornCliffordParityAPI

noncomputable section

open CliffordAlgebra LinearMap
open InfoGeometry.Physics.SplitOctonionBraidSU3 CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation ZornCliffordParityAPI
open ZornChiralLightcone

namespace ZornLightconeCAR

/-- Odd gamma operators exchange the two Peirce projectors. -/
theorem peirceProjectorMinus_mul_diracGamma (V : Vector8) :
    peirceProjectorMinus * diracGamma V =
      diracGamma V * peirceProjectorPlus := by
  rw [peirceProjectorMinus, peirceProjectorPlus]
  have hodd := diracGamma_odd V
  rw [IsOddOperator] at hodd
  have hodd' : ZornChiralLightcone.chiralityOperator * diracGamma V =
      -(diracGamma V * ZornChiralLightcone.chiralityOperator) := by
    simpa [ZornChiralLightcone.chiralityOperator,
      ZornCliffordParityAPI.chiralityOperator] using hodd
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, one_mul, mul_add,
    mul_one]
  rw [hodd']
  module

/-- The companion projector-exchange identity for an odd gamma operator. -/
theorem peirceProjectorPlus_mul_diracGamma (V : Vector8) :
    peirceProjectorPlus * diracGamma V =
      diracGamma V * peirceProjectorMinus := by
  rw [peirceProjectorMinus, peirceProjectorPlus]
  have hodd := diracGamma_odd V
  rw [IsOddOperator] at hodd
  have hodd' : ZornChiralLightcone.chiralityOperator * diracGamma V =
      -(diracGamma V * ZornChiralLightcone.chiralityOperator) := by
    simpa [ZornChiralLightcone.chiralityOperator,
      ZornCliffordParityAPI.chiralityOperator] using hodd
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, one_mul, mul_sub,
    mul_one]
  rw [hodd']
  module

/-- 1. Смесено произведение на операторите на светлинния конус (плюс-минус) -/
theorem lightconeSigmaPlus_mul_minus (r : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaMinus r =
      peirceProjectorPlus * (diracGamma (upperLightconeVector r) * diracGamma (lowerLightconeVector r)) * peirceProjectorPlus := by
  rw [lightconeSigmaPlus, lightconeSigmaMinus]
  calc
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) *
        (peirceProjectorMinus * peirceProjectorMinus) *
        diracGamma (lowerLightconeVector r) * peirceProjectorPlus := by
      noncomm_ring
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) *
        peirceProjectorMinus * diracGamma (lowerLightconeVector r) *
        peirceProjectorPlus := by rw [peirceProjectorMinus_sq]
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) *
        (peirceProjectorMinus * diracGamma (lowerLightconeVector r)) *
        peirceProjectorPlus := by
      noncomm_ring
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) *
        (diracGamma (lowerLightconeVector r) * peirceProjectorPlus) *
        peirceProjectorPlus := by rw [peirceProjectorMinus_mul_diracGamma]
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) *
        diracGamma (lowerLightconeVector r) *
        (peirceProjectorPlus * peirceProjectorPlus) := by noncomm_ring
    _ = _ := by rw [peirceProjectorPlus_sq]; noncomm_ring

/-- 2. Смесено произведение на операторите на светлинния конус (минус-плюс) -/
theorem lightconeSigmaMinus_mul_plus (r : Fin 3) :
    lightconeSigmaMinus r * lightconeSigmaPlus r =
      peirceProjectorMinus * (diracGamma (lowerLightconeVector r) * diracGamma (upperLightconeVector r)) * peirceProjectorMinus := by
  rw [lightconeSigmaMinus, lightconeSigmaPlus]
  calc
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) *
        (peirceProjectorPlus * peirceProjectorPlus) *
        diracGamma (upperLightconeVector r) * peirceProjectorMinus := by
      noncomm_ring
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) *
        peirceProjectorPlus * diracGamma (upperLightconeVector r) *
        peirceProjectorMinus := by rw [peirceProjectorPlus_sq]
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) *
        (peirceProjectorPlus * diracGamma (upperLightconeVector r)) *
        peirceProjectorMinus := by
      noncomm_ring
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) *
        (diracGamma (upperLightconeVector r) * peirceProjectorMinus) *
        peirceProjectorMinus := by rw [peirceProjectorPlus_mul_diracGamma]
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) *
        diracGamma (upperLightconeVector r) *
        (peirceProjectorMinus * peirceProjectorMinus) := by noncomm_ring
    _ = _ := by rw [peirceProjectorMinus_sq]; noncomm_ring

/--
The lightcone channel anticommutator for channel `r`.

The historical API name is retained, but this operator itself is not idempotent:
`C_r ^ 2 = -C_r`.  Its negative is the normalized channel projection; the full
classification is proved in `ZornLightconeChannelOperator`.
-/
def lightconeChannelProjector (r : Fin 3) : Module.End ℂ DiracSpinor16 :=
  lightconeSigmaPlus r * lightconeSigmaMinus r +
    lightconeSigmaMinus r * lightconeSigmaPlus r

/-- The exact channel anticommutator, by definition. -/
theorem lightconeSigma_anticommutator (r : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaMinus r + lightconeSigmaMinus r * lightconeSigmaPlus r = lightconeChannelProjector r := by
  rfl

/-- The channel operator also has the explicit gamma/Peirce realization. -/
theorem lightconeChannelProjector_eq_gamma (r : Fin 3) :
    lightconeChannelProjector r =
      peirceProjectorPlus *
          (diracGamma (upperLightconeVector r) *
            diracGamma (lowerLightconeVector r)) * peirceProjectorPlus +
        peirceProjectorMinus *
          (diracGamma (lowerLightconeVector r) *
            diracGamma (upperLightconeVector r)) * peirceProjectorMinus := by
  rw [← lightconeSigmaPlus_mul_minus, ← lightconeSigmaMinus_mul_plus]
  rfl

@[simp] theorem lightconeChannelProjector_apply (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeChannelProjector r (S, C) =
      (cliffordMinus (upperLightconeVector r)
          (cliffordPlus (lowerLightconeVector r) S),
        cliffordPlus (lowerLightconeVector r)
          (cliffordMinus (upperLightconeVector r) C)) := by
  rw [lightconeChannelProjector, LinearMap.add_apply,
    Module.End.mul_apply, Module.End.mul_apply]
  exact lightconeSigma_anticommutator_apply r S C

/-- The mixed color-channel operator is nonzero. -/
theorem lightconeChannelProjector_ne_zero (r : Fin 3) :
    lightconeChannelProjector r ≠ 0 := by
  intro hzero
  let S : SpinorPlus8 := ⟨E_k r⟩
  have h := LinearMap.congr_fun hzero (S, 0)
  have hfirst := congrArg Prod.fst h
  have hfirst' :
      (lightconeChannelProjector r (S, 0)).1 =
        (0 : SpinorPlus8) := by
    simpa using hfirst
  have ha := congrArg (fun X : SpinorPlus8 => X.val.u r) hfirst'
  simp only [map_zero, Pi.zero_apply] at ha
  fin_cases r <;>
    simp [S, cliffordMinus, cliffordPlus,
      upperLightconeVector, lowerLightconeVector, zornConj, zornMul,
      E_k, F_k, I_zorn, e_k, dot3, cross3,
      copyLinearEquivCoordinates, copyEquivCoordinates,
      CanonicalZornFiveGradedClosure.zornCoordinates] at ha

/-- 3. ТЕОРЕМА ЗА НЕВАКУОЗНОСТ: sigma+ не е нулев оператор -/
theorem lightconeSigmaPlus_ne_zero (r : Fin 3) :
    lightconeSigmaPlus r ≠ 0 := by
  exact ZornChiralLightcone.lightconeSigmaPlus_ne_zero r

/-- ТЕОРЕМА ЗА НЕВАКУОЗНОСТ: sigma- не е нулев оператор -/
theorem lightconeSigmaMinus_ne_zero (r : Fin 3) :
    lightconeSigmaMinus r ≠ 0 := by
  exact ZornChiralLightcone.lightconeSigmaMinus_ne_zero r

/-- 4. ОКОНЧАТЕЛЕН ПАКЕТ: Канонични Антикомутационни Релации (CAR) за хиралния светлинен конус -/
structure ChiralLightconeCAR (r : Fin 3) where
  sigmaPlus   : Module.End ℂ DiracSpinor16 := lightconeSigmaPlus r
  sigmaMinus  : Module.End ℂ DiracSpinor16 := lightconeSigmaMinus r
  plus_sq     : sigmaPlus * sigmaPlus = 0
  minus_sq    : sigmaMinus * sigmaMinus = 0
  antiComm    : sigmaPlus * sigmaMinus + sigmaMinus * sigmaPlus = lightconeChannelProjector r
  plus_ne     : sigmaPlus ≠ 0
  minus_ne    : sigmaMinus ≠ 0
  causal_plus : peirceProjectorPlus * sigmaPlus * peirceProjectorMinus = sigmaPlus
  causal_minus: peirceProjectorMinus * sigmaMinus * peirceProjectorPlus = sigmaMinus

/-- Конструкция на реалния физически CAR пакет за даден канал -/
def buildChiralLightconeCAR (r : Fin 3) : ChiralLightconeCAR r where
  plus_sq := lightconeSigmaPlus_nilpotent r
  minus_sq := lightconeSigmaMinus_nilpotent r
  antiComm := lightconeSigma_anticommutator r
  plus_ne  := lightconeSigmaPlus_ne_zero r
  minus_ne := lightconeSigmaMinus_ne_zero r
  causal_plus := peirce_causal_closure_plus r
  causal_minus := peirce_causal_closure_minus r

end ZornLightconeCAR
