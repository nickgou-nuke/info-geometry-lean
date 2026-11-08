/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.QuantumContext.FresnelGramMoorePenroseProjector

/-!
# Одит на Раздел 124: Спектрална Дуалност на Грам и Проектор на Мур–Пенроуз в Cℓ(1,1)

Конкретни целочислени (`ℤ`) проверки с `decide` за операторите на Грам,
теоремата на Кейли–Хамилтон и проектора в симетричния център.
-/

namespace InfoGeometry.QuantumContext.FresnelGramProjectorAudit

open InfoGeometry.QuantumContext.FresnelGramProjector

def slitPosInt : FresnelSlitAmp ℤ := ⟨3, 4⟩
def slitNegInt : FresnelSlitAmp ℤ := ⟨1, -2⟩

theorem audit_gram_isospectral_int :
    Cl11Op.trace (Cl11Op.leftGram slitPosInt slitNegInt) = 30 ∧
    Cl11Op.trace (Cl11Op.rightGram slitPosInt slitNegInt) = 30 ∧
    Cl11Op.det (Cl11Op.leftGram slitPosInt slitNegInt) = 100 ∧
    Cl11Op.det (Cl11Op.rightGram slitPosInt slitNegInt) = 100 := by
  decide

theorem audit_origin_zero_divisor_int :
    let M₀ := Cl11Op.embedFresnelPair slitPosInt slitPosInt
    Cl11Op.mul M₀ (Cl11Op.adjugate M₀) = Cl11Op.zero ∧
    Cl11Op.mul (Cl11Op.adjugate M₀) M₀ = Cl11Op.zero := by
  decide

theorem audit_cayley_hamilton_gram_int :
    let G_L := Cl11Op.leftGram slitPosInt slitNegInt
    let I_sum := FresnelSlitAmp.intensity slitPosInt + FresnelSlitAmp.intensity slitNegInt
    let H_sq := FresnelSlitAmp.yinSymplecticH slitPosInt slitNegInt *
                  FresnelSlitAmp.yinSymplecticH slitPosInt slitNegInt
    Cl11Op.mul G_L G_L = Cl11Op.sub (Cl11Op.scale I_sum G_L) (Cl11Op.scale H_sq Cl11Op.one) := by
  decide

theorem audit_origin_idempotent_projector_int :
    let G₀ := Cl11Op.leftGram slitPosInt slitPosInt
    Cl11Op.mul G₀ G₀ = Cl11Op.scale (2 * FresnelSlitAmp.intensity slitPosInt) G₀ := by
  decide

theorem audit_ab_prob_trace_formula_int :
    let M := Cl11Op.embedFresnelPair slitPosInt slitNegInt
    let G_L := Cl11Op.leftGram slitPosInt slitNegInt
    Cl11Op.trace (Cl11Op.mul (Cl11Op.add Cl11Op.one (Cl11Op.scale 2 Cl11Op.sigma1)) G_L) +
      2 * 3 * Cl11Op.det M = -50 := by
  decide

end InfoGeometry.QuantumContext.FresnelGramProjectorAudit
