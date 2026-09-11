/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.GoodBadGibbs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.GoodFitVolume
import InfoGeometry.Inference.RegularizedPoissonDeviance

/-!
# Poisson good/bad Gibbs adapter

The contamination layer is now tied to two explicit Poisson mean models. The
good and bad responsibilities therefore have a statistical energy contract.
-/

namespace InfoGeometry.Inference

variable {Data Theta : Type*} [Fintype Data]

structure PoissonGoodBadModel where
  observed : Data → ℝ
  goodMean : Data → Theta → ℝ
  badMean : Data → Theta → ℝ
  goodPrior : Data → ℝ
  badPrior : Data → ℝ
  observed_nonneg : ∀ i, 0 ≤ observed i
  goodMean_pos : ∀ i θ, 0 < goodMean i θ
  badMean_pos : ∀ i θ, 0 < badMean i θ
  goodPrior_pos : ∀ i, 0 < goodPrior i
  badPrior_pos : ∀ i, 0 < badPrior i

noncomputable def PoissonGoodBadModel.energyModel
    (M : PoissonGoodBadModel (Data := Data) (Theta := Theta))
    (θ : Theta) : GoodBadEnergy (Data := Data) where
  goodEnergy := fun i => poissonDeviance (M.observed i) (M.goodMean i θ)
  badEnergy := fun i => poissonDeviance (M.observed i) (M.badMean i θ)
  goodPrior := M.goodPrior
  badPrior := M.badPrior

theorem poissonGoodBad_goodEnergy_nonneg
    (M : PoissonGoodBadModel (Data := Data) (Theta := Theta))
    (θ : Theta) (i : Data) :
    0 ≤ (M.energyModel θ).goodEnergy i := by
  exact poissonDeviance_nonneg (M.observed_nonneg i) (M.goodMean_pos i θ)

theorem poissonGoodBad_badEnergy_nonneg
    (M : PoissonGoodBadModel (Data := Data) (Theta := Theta))
    (θ : Theta) (i : Data) :
    0 ≤ (M.energyModel θ).badEnergy i := by
  exact poissonDeviance_nonneg (M.observed_nonneg i) (M.badMean_pos i θ)

theorem poissonGoodBad_goodResponsibility_nonneg
    (M : PoissonGoodBadModel (Data := Data) (Theta := Theta))
    (θ : Theta) {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb) (i : Data) :
    0 ≤ goodResponsibility (M.energyModel θ) εg εb i := by
  exact goodResponsibility_nonneg (M.energyModel θ) hεg hεb
    M.goodPrior_pos M.badPrior_pos i

theorem poissonGoodBad_goodResponsibility_le_one
    (M : PoissonGoodBadModel (Data := Data) (Theta := Theta))
    (θ : Theta) {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb) (i : Data) :
    goodResponsibility (M.energyModel θ) εg εb i ≤ 1 := by
  exact goodResponsibility_le_one (M.energyModel θ) hεg hεb
    M.goodPrior_pos M.badPrior_pos i

theorem poissonGoodBad_effectiveGoodFraction_pos
    [Nonempty Data]
    (M : PoissonGoodBadModel (Data := Data) (Theta := Theta))
    (θ : Theta) {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb) :
    0 < effectiveGoodFraction (M.energyModel θ) εg εb := by
  exact effectiveGoodFraction_pos (M.energyModel θ) hεg hεb
    M.goodPrior_pos M.badPrior_pos

theorem poissonGoodBad_effectiveGoodFraction_le_one
    [Nonempty Data]
    (M : PoissonGoodBadModel (Data := Data) (Theta := Theta))
    (θ : Theta) {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb) :
    effectiveGoodFraction (M.energyModel θ) εg εb ≤ 1 := by
  exact effectiveGoodFraction_le_one (M.energyModel θ) hεg hεb
    M.goodPrior_pos M.badPrior_pos

end InfoGeometry.Inference
