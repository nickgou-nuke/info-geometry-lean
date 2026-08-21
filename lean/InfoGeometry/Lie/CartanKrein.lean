import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Lie.CartanKrein

structure FundamentalSymmetry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : H →L[ℂ] H
  is_self_adjoint : adjoint op = op
  is_involution : op.comp op = ContinuousLinearMap.id ℂ H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

def kreinAdjoint (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  J.op.comp ((adjoint T).comp J.op)

def IsKreinSkew (J : FundamentalSymmetry H) (T : EndH) : Prop :=
  kreinAdjoint J T = -T

def cartanInvolution (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  J.op.comp (T.comp J.op)

@[simp]
theorem cartanInvolution_apply (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J T = J.op.comp (T.comp J.op) := rfl

theorem cartanInvolution_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    cartanInvolution J T = - adjoint T := by
  dsimp [IsKreinSkew, kreinAdjoint] at hT
  have h_wrap := congrArg (fun S : EndH => J.op.comp (S.comp J.op)) hT
  dsimp at h_wrap
  have hJJ : J.op.comp ((J.op.comp ((adjoint T).comp J.op)).comp J.op) = adjoint T := by
    calc
      J.op.comp ((J.op.comp ((adjoint T).comp J.op)).comp J.op)
        = (J.op.comp J.op).comp ((adjoint T).comp (J.op.comp J.op)) := by
          simp only [comp_assoc]
      _ = (ContinuousLinearMap.id ℂ H).comp ((adjoint T).comp (ContinuousLinearMap.id ℂ H)) := by rw [J.is_involution]
      _ = adjoint T := by simp only [id_comp, comp_id]
  rw [hJJ] at h_wrap
  have h_neg : J.op.comp ((-T).comp J.op) = - (J.op.comp (T.comp J.op)) := by
    simp only [comp_neg, neg_comp]
  rw [h_neg] at h_wrap
  rw [cartanInvolution_apply]
  exact neg_eq_iff_eq_neg.mp h_wrap.symm

theorem adjoint_cartanInvolution_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    adjoint (cartanInvolution J T) = - T := by
  dsimp [cartanInvolution]
  calc
    adjoint (J.op.comp (T.comp J.op))
      = (adjoint (T.comp J.op)).comp (adjoint J.op) := by rw [adjoint_comp]
    _ = ((adjoint J.op).comp (adjoint T)).comp (adjoint J.op) := by rw [adjoint_comp]
    _ = (J.op.comp (adjoint T)).comp J.op := by rw [J.is_self_adjoint]
    _ = J.op.comp ((adjoint T).comp J.op) := by simp only [comp_assoc]
    _ = kreinAdjoint J T := rfl
    _ = -T := hT

theorem cartanInvolution_involutive (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J (cartanInvolution J T) = T := by
  dsimp [cartanInvolution]
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  calc
    J.op.comp ((J.op.comp (T.comp J.op)).comp J.op)
      = (J.op.comp J.op).comp (T.comp (J.op.comp J.op)) := by
        simp only [comp_assoc]
    _ = (ContinuousLinearMap.id ℂ H).comp (T.comp (ContinuousLinearMap.id ℂ H)) := by rw [hJ]
    _ = T := by simp only [id_comp, comp_id]

def compactPart (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T + cartanInvolution J T)

def noncompactPart (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T - cartanInvolution J T)

theorem cartan_reconstruction (J : FundamentalSymmetry H) (T : EndH) :
    compactPart J T + noncompactPart J T = T := by
  unfold compactPart noncompactPart
  rw [← smul_add]
  have h_add : (T + cartanInvolution J T) + (T - cartanInvolution J T) = (2 : ℂ) • T := by
    calc
      (T + cartanInvolution J T) + (T - cartanInvolution J T)
        = (T + T) + (cartanInvolution J T - cartanInvolution J T) := by abel
      _ = (2 : ℂ) • T + 0 := by rw [two_smul, sub_self]
      _ = (2 : ℂ) • T := by rw [add_zero]
  rw [h_add, smul_smul]
  have h_half : (1 / 2 : ℂ) * 2 = 1 := by ring
  rw [h_half, one_smul]

theorem compactPart_cartan_eigenvalue (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J (compactPart J T) = compactPart J T := by
  unfold compactPart cartanInvolution
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  simp only [comp_smul, smul_comp, comp_add, add_comp]
  congr 1
  calc
    J.op.comp (T.comp J.op) + J.op.comp ((J.op.comp (T.comp J.op)).comp J.op)
      = J.op.comp (T.comp J.op) + (J.op.comp J.op).comp (T.comp (J.op.comp J.op)) := by
        simp only [comp_assoc]
    _ = J.op.comp (T.comp J.op) + (ContinuousLinearMap.id ℂ H).comp (T.comp (ContinuousLinearMap.id ℂ H)) := by rw [hJ]
    _ = J.op.comp (T.comp J.op) + T := by simp only [id_comp, comp_id]
    _ = T + J.op.comp (T.comp J.op) := add_comm _ _

theorem noncompactPart_cartan_eigenvalue (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J (noncompactPart J T) = - (noncompactPart J T) := by
  unfold noncompactPart cartanInvolution
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  simp only [comp_smul, smul_comp, comp_sub, sub_comp]
  have h_inner : J.op.comp (T.comp J.op) - J.op.comp ((J.op.comp (T.comp J.op)).comp J.op) =
      - (T - J.op.comp (T.comp J.op)) := by
    calc
      J.op.comp (T.comp J.op) - J.op.comp ((J.op.comp (T.comp J.op)).comp J.op)
        = J.op.comp (T.comp J.op) - (J.op.comp J.op).comp (T.comp (J.op.comp J.op)) := by
          simp only [comp_assoc]
      _ = J.op.comp (T.comp J.op) - (ContinuousLinearMap.id ℂ H).comp (T.comp (ContinuousLinearMap.id ℂ H)) := by rw [hJ]
      _ = J.op.comp (T.comp J.op) - T := by simp only [id_comp, comp_id]
      _ = - (T - J.op.comp (T.comp J.op)) := by abel
  rw [h_inner, smul_neg]

theorem starRingEnd_half : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  apply Complex.ext
  · simp
  · simp

theorem compactPart_is_hilbert_skew
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    adjoint (compactPart J T) = - (compactPart J T) := by
  unfold compactPart
  rw [map_smulₛₗ adjoint, map_add adjoint]
  rw [starRingEnd_half]
  have h_adjT : adjoint T = - cartanInvolution J T := by
    have h_inv := cartanInvolution_of_isKreinSkew J T hT
    exact neg_eq_iff_eq_neg.mp h_inv.symm
  have h_adj_theta : adjoint (cartanInvolution J T) = - T :=
    adjoint_cartanInvolution_of_isKreinSkew J T hT
  rw [h_adjT, h_adj_theta]
  have h_sum : - cartanInvolution J T + - T = - (T + cartanInvolution J T) := by abel
  rw [h_sum, smul_neg]

theorem noncompactPart_is_hilbert_self_adjoint
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    adjoint (noncompactPart J T) = noncompactPart J T := by
  unfold noncompactPart
  rw [map_smulₛₗ adjoint, map_sub adjoint]
  rw [starRingEnd_half]
  have h_adjT : adjoint T = - cartanInvolution J T := by
    have h_inv := cartanInvolution_of_isKreinSkew J T hT
    exact neg_eq_iff_eq_neg.mp h_inv.symm
  have h_adj_theta : adjoint (cartanInvolution J T) = - T :=
    adjoint_cartanInvolution_of_isKreinSkew J T hT
  rw [h_adjT, h_adj_theta]
  have h_sub : - cartanInvolution J T - - T = T - cartanInvolution J T := by abel
  rw [h_sub]

end InfoGeometry.Lie.CartanKrein
