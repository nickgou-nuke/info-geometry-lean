import InfoGeometry.Physics.FreeEntropySouriauBridge
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Souriau entropy foliation

This file keeps three layers separate:

* Souriau `β`-sheets, using the finite Gibbs/Massieu model;
* entropy-preserving leafwise motion, modeled constructively by finite
  permutation/unitary transport of weights;
* Weyl/dilaton scale shifts, modeled as an additive logarithmic cocycle.

It does not assert that the free-entropy functional alone induces the
Einstein-Hilbert action or the Bekenstein-Hawking area law.
-/

namespace SouriauEntropyFoliation

open Finset
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

abbrev gibbsWeight (beta : ℝ) (energy : ι → ℝ) (i : ι) : ℝ :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.gibbsWeight beta energy i

abbrev boltzmannEntropy (weight : ι → ℝ) : ℝ :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.boltzmannEntropy weight

abbrev massieuPlanckPotential (beta : ℝ) (energy : ι → ℝ) : ℝ :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.massieuPlanckPotential beta energy

abbrev meanEnergy (beta : ℝ) (energy : ι → ℝ) : ℝ :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.meanEnergy beta energy

/-- A scalar `β`-sheet in the finite Souriau model. -/
def souriauSheetEntropy (beta : ℝ) (energy : ι → ℝ) : ℝ :=
  boltzmannEntropy (gibbsWeight beta energy)

/-- The finite Massieu--Legendre entropy formula on each `β`-sheet. -/
theorem souriauSheetEntropy_eq_massieu_add_beta_meanEnergy
    [Nonempty ι] (beta : ℝ) (energy : ι → ℝ) :
    souriauSheetEntropy beta energy =
      massieuPlanckPotential beta energy + beta * meanEnergy beta energy :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.boltzmannEntropy_gibbsWeight_eq_massieu_add_beta_meanEnergy
    beta energy

/-- Finite constructive stand-in for unitary conjugation: transport weights by a permutation. -/
def permuteWeight (σ : Equiv.Perm ι) (weight : ι → ℝ) : ι → ℝ :=
  fun i => weight (σ.symm i)

/--
Boltzmann entropy is preserved by finite permutation transport.

This is the finite constructive form of "unitary conjugation preserves the
spectrum of the density operator, hence preserves entropy".
-/
theorem boltzmannEntropy_permuteWeight
    (σ : Equiv.Perm ι) (weight : ι → ℝ) :
    boltzmannEntropy (permuteWeight σ weight) = boltzmannEntropy weight := by
  unfold boltzmannEntropy InfoGeometry.Physics.SouriauMassieuPlanckFunctional.boltzmannEntropy permuteWeight
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun i => weight (σ.symm i) *
        InfoGeometry.Physics.SouriauMassieuPlanckFunctional.surprisal (weight (σ.symm i)))
      (fun i => weight i *
        InfoGeometry.Physics.SouriauMassieuPlanckFunctional.surprisal (weight i))
      (by intro i; rfl))

/-- Entropy-sheet equivalence: two explicit weights sit on the same entropy leaf. -/
def sameEntropySheet (weight₁ weight₂ : ι → ℝ) : Prop :=
  boltzmannEntropy weight₁ = boltzmannEntropy weight₂

/-- Permutation/unitary leaf motion stays inside the same entropy sheet. -/
theorem sameEntropySheet_permuteWeight
    (σ : Equiv.Perm ι) (weight : ι → ℝ) :
    sameEntropySheet (permuteWeight σ weight) weight :=
  boltzmannEntropy_permuteWeight σ weight

/-- The scalar free-entropy functional readout used by the Souriau/free layer. -/
def S_free
    (massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree : ℝ) : ℝ :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.S_free
    massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree

/-- Expansion of the scalar free-entropy functional. -/
theorem S_free_eq
    (massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree : ℝ) :
    S_free massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree =
      massieu - kl - lambdaInc * incidenceFriction - lambdaFree * freeEnergy :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.S_free_eq
    massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree

/-- Sixteen chiral Majorana channels carry central charge `c = 8`. -/
theorem sixteenMajorana_centralCharge_eq_eight :
    InfoGeometry.Physics.FreeEntropyDiffusionFunctional.majoranaCentralCharge 16 = 8 :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.majoranaCentralCharge_sixteen_eq_eight

/-- A logarithmic Weyl/dilaton shift of the local volume cocycle. -/
def dilatonShift (dimension phi logScale : ℝ) : ℝ :=
  logScale + dimension * phi

/-- Dilaton shifts compose additively along the logarithmic Weyl scale. -/
theorem dilatonShift_comp
    (dimension phi psi logScale : ℝ) :
    dilatonShift dimension psi (dilatonShift dimension phi logScale) =
      dilatonShift dimension (phi + psi) logScale := by
  unfold dilatonShift
  ring

/--
The Weyl/dilaton layer is a scale-sheet motion, not an entropy-preserving
unitary leaf motion.
-/
def weylScaleSheetMove (dimension phi logScale : ℝ) : ℝ :=
  dilatonShift dimension phi logScale

theorem weylScaleSheetMove_eq_dilatonShift
    (dimension phi logScale : ℝ) :
    weylScaleSheetMove dimension phi logScale =
      dilatonShift dimension phi logScale := by
  rfl

end

end SouriauEntropyFoliation
