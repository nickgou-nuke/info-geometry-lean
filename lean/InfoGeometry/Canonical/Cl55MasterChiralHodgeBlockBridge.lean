import InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral block calculus for the finite `Cl(5,5)` Hodge packet

This owner packages the already proved master chirality and the already proved
odd Hodge--Dirac operator into its native matrix projectors.  It does not
introduce a second Hodge operator or identify the master carrier with the
separate concrete Hestenes embedding.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge

open Matrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

def masterChiralProjectorPlus : Mat32 :=
  (1 / 2 : ℝ) • (1 + MasterChirality)

def masterChiralProjectorMinus : Mat32 :=
  (1 / 2 : ℝ) • (1 - MasterChirality)

theorem masterChiralProjectorPlus_sq :
    masterChiralProjectorPlus * masterChiralProjectorPlus =
      masterChiralProjectorPlus := by
  unfold masterChiralProjectorPlus
  rw [smul_mul_assoc, mul_smul_comm]
  rw [smul_smul]
  norm_num
  simp only [one_mul, mul_one, add_mul, mul_add]
  rw [masterChirality_sq]
  module

theorem masterChiralProjectorMinus_sq :
    masterChiralProjectorMinus * masterChiralProjectorMinus =
      masterChiralProjectorMinus := by
  unfold masterChiralProjectorMinus
  rw [smul_mul_assoc, mul_smul_comm]
  rw [smul_smul]
  norm_num
  simp only [one_mul, mul_one, sub_mul, mul_sub]
  rw [masterChirality_sq]
  module

theorem masterChiralProjectors_orthogonal :
    masterChiralProjectorPlus * masterChiralProjectorMinus = 0 ∧
      masterChiralProjectorMinus * masterChiralProjectorPlus = 0 := by
  constructor
  · rw [masterChiralProjectorPlus, masterChiralProjectorMinus,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
    simp only [one_mul, mul_one, add_mul, mul_sub]
    rw [masterChirality_sq]
    module
  · rw [masterChiralProjectorMinus, masterChiralProjectorPlus,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
    simp only [one_mul, mul_one, sub_mul, mul_add]
    rw [masterChirality_sq]
    module

theorem masterChiralProjectors_sum :
    masterChiralProjectorPlus + masterChiralProjectorMinus = 1 := by
  rw [masterChiralProjectorPlus, masterChiralProjectorMinus]
  module

theorem masterHodgeDirac_comp_projectorPlus :
    embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus =
      masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac := by
  rw [masterChiralProjectorPlus, masterChiralProjectorMinus,
    mul_smul_comm, smul_mul_assoc]
  simp only [mul_add, add_mul, mul_one, one_mul, sub_mul]
  have hodd := masterChirality_anticomm_hodge
  have hodd' : embeddedSplitOctonionHodgeDirac * MasterChirality +
      MasterChirality * embeddedSplitOctonionHodgeDirac = 0 := by
    simpa [add_comm] using hodd
  rw [show embeddedSplitOctonionHodgeDirac * MasterChirality =
      -(MasterChirality * embeddedSplitOctonionHodgeDirac) by
        exact eq_neg_of_add_eq_zero_left hodd']
  module

theorem masterHodgeDirac_comp_projectorMinus :
    embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus =
      masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac := by
  rw [masterChiralProjectorMinus, masterChiralProjectorPlus,
    mul_smul_comm, smul_mul_assoc]
  simp only [mul_sub, add_mul, mul_one, one_mul]
  have hodd := masterChirality_anticomm_hodge
  have hodd' : embeddedSplitOctonionHodgeDirac * MasterChirality +
      MasterChirality * embeddedSplitOctonionHodgeDirac = 0 := by
    simpa [add_comm] using hodd
  rw [show embeddedSplitOctonionHodgeDirac * MasterChirality =
      -(MasterChirality * embeddedSplitOctonionHodgeDirac) by
        exact eq_neg_of_add_eq_zero_left hodd']
  module

theorem masterHodgeDirac_is_odd_on_plus :
  masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac *
        masterChiralProjectorPlus = 0 := by
  rw [Matrix.mul_assoc, masterHodgeDirac_comp_projectorPlus,
    ← Matrix.mul_assoc, masterChiralProjectors_orthogonal.1]
  simp

theorem masterHodgeDirac_is_odd_on_minus :
  masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac *
        masterChiralProjectorMinus = 0 := by
  rw [Matrix.mul_assoc, masterHodgeDirac_comp_projectorMinus,
    ← Matrix.mul_assoc, masterChiralProjectors_orthogonal.2]
  simp

def masterChiralDiracPlus : Mat32 :=
  masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac *
    masterChiralProjectorPlus

def masterChiralDiracMinus : Mat32 :=
  masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac *
    masterChiralProjectorMinus

theorem masterChiralDiracPlus_eq_projectorMinus_mul_hodge :
    masterChiralDiracPlus =
      masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac := by
  unfold masterChiralDiracPlus
  rw [Matrix.mul_assoc, masterHodgeDirac_comp_projectorPlus,
    ← Matrix.mul_assoc, masterChiralProjectorMinus_sq]

theorem masterChiralDiracMinus_eq_projectorPlus_mul_hodge :
    masterChiralDiracMinus =
      masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac := by
  unfold masterChiralDiracMinus
  rw [Matrix.mul_assoc, masterHodgeDirac_comp_projectorMinus,
    ← Matrix.mul_assoc, masterChiralProjectorPlus_sq]

theorem masterChiralDirac_decomposition :
    masterChiralDiracPlus + masterChiralDiracMinus =
      embeddedSplitOctonionHodgeDirac := by
  rw [masterChiralDiracPlus_eq_projectorMinus_mul_hodge,
    masterChiralDiracMinus_eq_projectorPlus_mul_hodge,
    ← add_mul]
  have hsum : masterChiralProjectorMinus + masterChiralProjectorPlus = 1 := by
    rw [add_comm, masterChiralProjectors_sum]
  rw [hsum]
  simp

theorem masterChiralDiracPlus_sq_zero :
    masterChiralDiracPlus * masterChiralDiracPlus = 0 := by
  rw [masterChiralDiracPlus_eq_projectorMinus_mul_hodge]
  calc
    (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) *
        (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) =
      masterChiralProjectorMinus *
        (embeddedSplitOctonionHodgeDirac *
          (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac)) := by
            noncomm_ring
    _ = masterChiralProjectorMinus *
        ((embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus) *
          embeddedSplitOctonionHodgeDirac) := by
            rw [Matrix.mul_assoc]
    _ = masterChiralProjectorMinus *
        ((masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) *
          embeddedSplitOctonionHodgeDirac) := by
            rw [masterHodgeDirac_comp_projectorMinus]
    _ = (masterChiralProjectorMinus * masterChiralProjectorPlus) *
        (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) := by
            noncomm_ring
    _ = 0 := by
      rw [masterChiralProjectors_orthogonal.2]
      simp

theorem masterChiralDiracMinus_sq_zero :
    masterChiralDiracMinus * masterChiralDiracMinus = 0 := by
  rw [masterChiralDiracMinus_eq_projectorPlus_mul_hodge]
  calc
    (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) *
        (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) =
      masterChiralProjectorPlus *
        (embeddedSplitOctonionHodgeDirac *
          (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac)) := by
            noncomm_ring
    _ = masterChiralProjectorPlus *
        ((embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus) *
          embeddedSplitOctonionHodgeDirac) := by
            rw [Matrix.mul_assoc]
    _ = masterChiralProjectorPlus *
        ((masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) *
          embeddedSplitOctonionHodgeDirac) := by
            rw [masterHodgeDirac_comp_projectorPlus]
    _ = (masterChiralProjectorPlus * masterChiralProjectorMinus) *
        (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) := by
            noncomm_ring
    _ = 0 := by
      rw [masterChiralProjectors_orthogonal.1]
      simp

def masterHodgeLaplacian : Mat32 :=
  embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac

def masterChiralLaplacianPlus : Mat32 :=
  masterChiralDiracMinus * masterChiralDiracPlus

def masterChiralLaplacianMinus : Mat32 :=
  masterChiralDiracPlus * masterChiralDiracMinus

theorem masterHodgeLaplacian_eq_three :
    masterHodgeLaplacian = (3 : ℝ) • (1 : Mat32) := by
  exact embeddedSplitOctonionHodgeDirac_sq

theorem masterChiralLaplacianPlus_eq_three_projector :
    masterChiralLaplacianPlus =
      (3 : ℝ) • masterChiralProjectorPlus := by
  unfold masterChiralLaplacianPlus
  rw [masterChiralDiracMinus_eq_projectorPlus_mul_hodge,
    masterChiralDiracPlus_eq_projectorMinus_mul_hodge]
  calc
    (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) *
        (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) =
      masterChiralProjectorPlus *
        ((embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus) *
          embeddedSplitOctonionHodgeDirac) := by
            noncomm_ring
    _ = masterChiralProjectorPlus *
        ((masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) *
          embeddedSplitOctonionHodgeDirac) := by
            rw [masterHodgeDirac_comp_projectorMinus]
    _ = (masterChiralProjectorPlus * masterChiralProjectorPlus) *
        (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) := by
            noncomm_ring
    _ = masterChiralProjectorPlus *
        ((3 : ℝ) • (1 : Mat32)) := by
            rw [masterChiralProjectorPlus_sq,
              embeddedSplitOctonionHodgeDirac_sq]
    _ = (3 : ℝ) • masterChiralProjectorPlus := by
            rw [mul_smul_comm]
            simp

theorem masterChiralLaplacianMinus_eq_three_projector :
    masterChiralLaplacianMinus =
      (3 : ℝ) • masterChiralProjectorMinus := by
  unfold masterChiralLaplacianMinus
  rw [masterChiralDiracPlus_eq_projectorMinus_mul_hodge,
    masterChiralDiracMinus_eq_projectorPlus_mul_hodge]
  calc
    (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) *
        (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) =
      masterChiralProjectorMinus *
        ((embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus) *
          embeddedSplitOctonionHodgeDirac) := by
            noncomm_ring
    _ = masterChiralProjectorMinus *
        ((masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) *
          embeddedSplitOctonionHodgeDirac) := by
            rw [masterHodgeDirac_comp_projectorPlus]
    _ = (masterChiralProjectorMinus * masterChiralProjectorMinus) *
        (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) := by
            noncomm_ring
    _ = masterChiralProjectorMinus *
        ((3 : ℝ) • (1 : Mat32)) := by
            rw [masterChiralProjectorMinus_sq,
              embeddedSplitOctonionHodgeDirac_sq]
    _ = (3 : ℝ) • masterChiralProjectorMinus := by
            rw [mul_smul_comm]
            simp

end InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
