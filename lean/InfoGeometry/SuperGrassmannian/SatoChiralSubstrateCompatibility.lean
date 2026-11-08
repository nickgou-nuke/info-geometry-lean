/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.SuperGrassmannian.SplitCliffordCellMatrixWitness
import InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdeal

noncomputable section

namespace InfoGeometry.SuperGrassmannian.ProjectorCompatibility

open InfoGeometry.SuperGrassmannian.MajoranaCAR
open InfoGeometry.SuperGrassmannian.SatoColimitTriality
open InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdeal


/-- The Sato split-cell grading and its transverse generator form the
concrete two-sheeted Majorana substrate. -/
noncomputable def satoChiralSubstrate :
    ChiralSheetSubstrate MajoranaCAR.WitnessMat2R where
  Γ := SatoColimitTriality.SplitCliffordCell.gamma
    SatoColimitTriality.matrixSplitCliffordCell
  J := SatoColimitTriality.matrixSplitCliffordCell.e
  Γ_sq := by
    exact SatoColimitTriality.SplitCliffordCell.gamma_sq_one
      SatoColimitTriality.matrixSplitCliffordCell
  J_sq := SatoColimitTriality.matrixSplitCliffordCell.e_sq
  J_Γ_anticomm := by
    have he : SatoColimitTriality.matrixSplitCliffordCell.e *
        SatoColimitTriality.matrixSplitCliffordCell.e = 1 :=
      SatoColimitTriality.SplitCliffordCell.e_mul_e
        SatoColimitTriality.matrixSplitCliffordCell
    have hfe : SatoColimitTriality.matrixSplitCliffordCell.f *
        SatoColimitTriality.matrixSplitCliffordCell.e =
        -(SatoColimitTriality.matrixSplitCliffordCell.e *
          SatoColimitTriality.matrixSplitCliffordCell.f) :=
      SatoColimitTriality.SplitCliffordCell.fe_eq_neg_ef
        SatoColimitTriality.matrixSplitCliffordCell
    dsimp [SatoColimitTriality.SplitCliffordCell.gamma]
    calc
      SatoColimitTriality.matrixSplitCliffordCell.e *
            (SatoColimitTriality.matrixSplitCliffordCell.e *
              SatoColimitTriality.matrixSplitCliffordCell.f) +
          (SatoColimitTriality.matrixSplitCliffordCell.e *
            SatoColimitTriality.matrixSplitCliffordCell.f) *
            SatoColimitTriality.matrixSplitCliffordCell.e =
          (SatoColimitTriality.matrixSplitCliffordCell.e *
            SatoColimitTriality.matrixSplitCliffordCell.e) *
              SatoColimitTriality.matrixSplitCliffordCell.f +
            SatoColimitTriality.matrixSplitCliffordCell.e *
              (SatoColimitTriality.matrixSplitCliffordCell.f *
                SatoColimitTriality.matrixSplitCliffordCell.e) := by
              noncomm_ring
      _ = 1 * SatoColimitTriality.matrixSplitCliffordCell.f +
            SatoColimitTriality.matrixSplitCliffordCell.e *
              (-(SatoColimitTriality.matrixSplitCliffordCell.e *
                SatoColimitTriality.matrixSplitCliffordCell.f)) := by
              rw [he, hfe]
      _ = SatoColimitTriality.matrixSplitCliffordCell.f -
            (SatoColimitTriality.matrixSplitCliffordCell.e *
              SatoColimitTriality.matrixSplitCliffordCell.e) *
              SatoColimitTriality.matrixSplitCliffordCell.f := by noncomm_ring
      _ = 0 := by rw [he]; noncomm_ring
  half := SatoColimitTriality.matrixSplitCliffordCell.half
  two_half := SatoColimitTriality.matrixSplitCliffordCell.two_half
  half_comm := SatoColimitTriality.matrixSplitCliffordCell.half_comm

/-- The positive Sato projector is exactly the positive projector of the
abstract Majorana substrate on the same matrix carrier. -/
theorem sato_projPlus_eq_substrate_PL :
    SatoColimitTriality.SplitCliffordCell.projPlus
        SatoColimitTriality.matrixSplitCliffordCell =
      satoChiralSubstrate.PL := by
  dsimp [satoChiralSubstrate, ChiralSheetSubstrate.PL]
  have hsum := SatoColimitTriality.SplitCliffordCell.proj_sum_one
    SatoColimitTriality.matrixSplitCliffordCell
  have hdiff := SatoColimitTriality.SplitCliffordCell.proj_sub_gamma
    SatoColimitTriality.matrixSplitCliffordCell
  have htwo := SatoColimitTriality.SplitCliffordCell.half_mul_two
    SatoColimitTriality.matrixSplitCliffordCell
  calc
    SatoColimitTriality.SplitCliffordCell.projPlus
        SatoColimitTriality.matrixSplitCliffordCell =
        SatoColimitTriality.matrixSplitCliffordCell.half *
          (SatoColimitTriality.SplitCliffordCell.projPlus
              SatoColimitTriality.matrixSplitCliffordCell +
            SatoColimitTriality.SplitCliffordCell.projPlus
              SatoColimitTriality.matrixSplitCliffordCell) := by
              calc
                SatoColimitTriality.SplitCliffordCell.projPlus
                    SatoColimitTriality.matrixSplitCliffordCell =
                    (SatoColimitTriality.matrixSplitCliffordCell.half +
                      SatoColimitTriality.matrixSplitCliffordCell.half) *
                      SatoColimitTriality.SplitCliffordCell.projPlus
                        SatoColimitTriality.matrixSplitCliffordCell := by
                          rw [SatoColimitTriality.matrixSplitCliffordCell.two_half, one_mul]
                _ = SatoColimitTriality.matrixSplitCliffordCell.half *
                      (SatoColimitTriality.SplitCliffordCell.projPlus
                        SatoColimitTriality.matrixSplitCliffordCell +
                        SatoColimitTriality.SplitCliffordCell.projPlus
                        SatoColimitTriality.matrixSplitCliffordCell) := by
                          noncomm_ring
    _ = SatoColimitTriality.matrixSplitCliffordCell.half *
          (SatoColimitTriality.SplitCliffordCell.projPlus
              SatoColimitTriality.matrixSplitCliffordCell +
            SatoColimitTriality.SplitCliffordCell.projMinus
              SatoColimitTriality.matrixSplitCliffordCell +
            (SatoColimitTriality.SplitCliffordCell.projPlus
              SatoColimitTriality.matrixSplitCliffordCell -
              SatoColimitTriality.SplitCliffordCell.projMinus
                SatoColimitTriality.matrixSplitCliffordCell)) := by
              congr 1
              abel
    _ = SatoColimitTriality.matrixSplitCliffordCell.half *
          (1 + SatoColimitTriality.SplitCliffordCell.gamma
            SatoColimitTriality.matrixSplitCliffordCell) := by
              rw [hsum, hdiff]

/-- The negative Sato projector is exactly the negative projector of the
abstract Majorana substrate on the same matrix carrier. -/
theorem sato_projMinus_eq_substrate_PR :
    SatoColimitTriality.SplitCliffordCell.projMinus
        SatoColimitTriality.matrixSplitCliffordCell =
      satoChiralSubstrate.PR := by
  dsimp [satoChiralSubstrate, ChiralSheetSubstrate.PR]
  have hsum := SatoColimitTriality.SplitCliffordCell.proj_sum_one
    SatoColimitTriality.matrixSplitCliffordCell
  have hdiff := SatoColimitTriality.SplitCliffordCell.proj_sub_gamma
    SatoColimitTriality.matrixSplitCliffordCell
  have htwo := SatoColimitTriality.SplitCliffordCell.half_mul_two
    SatoColimitTriality.matrixSplitCliffordCell
  calc
    SatoColimitTriality.SplitCliffordCell.projMinus
        SatoColimitTriality.matrixSplitCliffordCell =
        SatoColimitTriality.matrixSplitCliffordCell.half *
          (SatoColimitTriality.SplitCliffordCell.projMinus
              SatoColimitTriality.matrixSplitCliffordCell +
            SatoColimitTriality.SplitCliffordCell.projMinus
              SatoColimitTriality.matrixSplitCliffordCell) := by
              calc
                SatoColimitTriality.SplitCliffordCell.projMinus
                    SatoColimitTriality.matrixSplitCliffordCell =
                    (SatoColimitTriality.matrixSplitCliffordCell.half +
                      SatoColimitTriality.matrixSplitCliffordCell.half) *
                      SatoColimitTriality.SplitCliffordCell.projMinus
                        SatoColimitTriality.matrixSplitCliffordCell := by
                          rw [SatoColimitTriality.matrixSplitCliffordCell.two_half, one_mul]
                _ = SatoColimitTriality.matrixSplitCliffordCell.half *
                      (SatoColimitTriality.SplitCliffordCell.projMinus
                        SatoColimitTriality.matrixSplitCliffordCell +
                        SatoColimitTriality.SplitCliffordCell.projMinus
                        SatoColimitTriality.matrixSplitCliffordCell) := by
                          noncomm_ring
    _ = SatoColimitTriality.matrixSplitCliffordCell.half *
          ((SatoColimitTriality.SplitCliffordCell.projPlus
              SatoColimitTriality.matrixSplitCliffordCell +
            SatoColimitTriality.SplitCliffordCell.projMinus
              SatoColimitTriality.matrixSplitCliffordCell) -
            (SatoColimitTriality.SplitCliffordCell.projPlus
              SatoColimitTriality.matrixSplitCliffordCell -
              SatoColimitTriality.SplitCliffordCell.projMinus
                SatoColimitTriality.matrixSplitCliffordCell)) := by
              congr 1
              abel
    _ = SatoColimitTriality.matrixSplitCliffordCell.half *
          (1 - SatoColimitTriality.SplitCliffordCell.gamma
            SatoColimitTriality.matrixSplitCliffordCell) := by
              rw [hsum, hdiff]

/-- The Sato CAR projector pair and the abstract Majorana substrate projector
pair are the same pair on the concrete matrix carrier. -/
theorem sato_projector_pair_transport :
    (SatoColimitTriality.SplitCliffordCell.projPlus
        SatoColimitTriality.matrixSplitCliffordCell =
      satoChiralSubstrate.PL) ∧
    (SatoColimitTriality.SplitCliffordCell.projMinus
        SatoColimitTriality.matrixSplitCliffordCell =
      satoChiralSubstrate.PR) := by
  exact ⟨sato_projPlus_eq_substrate_PL, sato_projMinus_eq_substrate_PR⟩

end InfoGeometry.SuperGrassmannian.ProjectorCompatibility
