import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.GrandCanonical.Core

/-!
# Dirac--Krein conjugation of a positive bilinear form

The positive doubled form is conjugated by the existing `spectral_epsilon`.
The resulting form is neutral and is compatible with the existing modular
swap, without identifying an indefinite form with a positive Fisher form.
-/

noncomputable section

namespace InfoGeometry.Krein.DiracKreinFisherBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def doubledPositiveBilin (G : LinearMap.BilinForm ℝ E) :
    LinearMap.BilinForm ℝ (DoubledSpace E) :=
  LinearMap.mk₂ ℝ
    (fun u v => G (WithLp.fst u) (WithLp.fst v) +
      G (WithLp.snd u) (WithLp.snd v))
    (by intro u v w; simp [map_add]; ring)
    (by intro c u v; simp [map_smul]; ring)
    (by intro u v w; simp [map_add]; ring)
    (by intro c u v; simp [map_smul]; ring)

def diracKreinBilin (G : LinearMap.BilinForm ℝ E) :
    LinearMap.BilinForm ℝ (DoubledSpace E) :=
  LinearMap.mk₂ ℝ
    (fun u v => doubledPositiveBilin G u (spectral_epsilon v))
    (by intro u v w; simp [doubledPositiveBilin, map_add])
    (by intro c u v; simp [doubledPositiveBilin, map_smul])
    (by intro u v w; simp [doubledPositiveBilin, map_add, spectral_epsilon])
    (by intro c u v; simp [doubledPositiveBilin, map_smul, spectral_epsilon])

@[simp] theorem diracKreinBilin_apply (G : LinearMap.BilinForm ℝ E)
    (u v : DoubledSpace E) :
    diracKreinBilin G u v =
      G (WithLp.fst u) (WithLp.fst v) -
        G (WithLp.snd u) (WithLp.snd v) := by
  simp [diracKreinBilin, doubledPositiveBilin, spectral_epsilon]
  ring

theorem diracKreinBilin_eq_difference (G : LinearMap.BilinForm ℝ E)
    (u v : DoubledSpace E) :
    diracKreinBilin G u v =
      G (WithLp.fst u) (WithLp.fst v) -
        G (WithLp.snd u) (WithLp.snd v) :=
  diracKreinBilin_apply G u v

theorem diracKreinBilin_symm (G : LinearMap.BilinForm ℝ E)
    (hG : ∀ x y, G x y = G y x) (u v : DoubledSpace E) :
    diracKreinBilin G u v = diracKreinBilin G v u := by
  simp only [diracKreinBilin_apply]
  rw [hG (WithLp.fst u) (WithLp.fst v)]
  rw [hG (WithLp.snd u) (WithLp.snd v)]

noncomputable def diracParaComplexStructure :
    ParaComplexStructure ℝ (DoubledSpace E) where
  K := (modular_j (E := E)).toLinearMap
  K_sq := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [modular_j]

theorem diracKreinBilin_modular_j_anti (G : LinearMap.BilinForm ℝ E)
    (u v : DoubledSpace E) :
    diracKreinBilin G (modular_j u) (modular_j v) =
      -diracKreinBilin G u v := by
  simp only [diracKreinBilin_apply]
  simp [modular_j]

noncomputable def diracKreinParaKahlerDatum
    (G : LinearMap.BilinForm ℝ E) (hG : ∀ x y, G x y = G y x) :
    ParaKahlerDatum ℝ (DoubledSpace E) where
  metric := diracKreinBilin G
  para := diracParaComplexStructure
  metric_symm := diracKreinBilin_symm G hG
  metric_anti_compat := by
    intro u v
    exact diracKreinBilin_modular_j_anti G u v

theorem diracKrein_paraBerry_eq (G : LinearMap.BilinForm ℝ E)
    (hG : ∀ x y, G x y = G y x) (u v : DoubledSpace E) :
    (diracKreinParaKahlerDatum G hG).paraBerryTwoForm u v =
      diracKreinBilin G (modular_j u) v := rfl

end InfoGeometry.Krein.DiracKreinFisherBridge
