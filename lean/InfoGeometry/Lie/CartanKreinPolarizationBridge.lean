import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Lie.CartanKrein

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

structure FundamentalSymmetry
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : H →L[ℂ] H
  is_self_adjoint : adjoint op = op
  is_involution : op.comp op = ContinuousLinearMap.id ℂ H

def kreinAdjoint (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  J.op.comp ((adjoint T).comp J.op)

def IsKreinSkew (J : FundamentalSymmetry H) (T : EndH) : Prop :=
  kreinAdjoint J T = -T

/-- The Cartan involution from the stated Krein convention. -/
def cartanInvolution (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  -(kreinAdjoint J T)

def compactPart (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T + cartanInvolution J T)

def noncompactPart (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T - cartanInvolution J T)

theorem cartan_reconstruction (J : FundamentalSymmetry H) (T : EndH) :
    compactPart J T + noncompactPart J T = T := by
  unfold compactPart noncompactPart
  rw [← smul_add]
  have h : (T + cartanInvolution J T) + (T - cartanInvolution J T) =
      (2 : ℂ) • T := by
    rw [show (2 : ℂ) • T = T + T by rw [two_smul]]
    abel
  rw [h, smul_smul]
  norm_num

/-- Krein-skewness is the `+1` eigenspace of this Cartan involution. -/
theorem cartanInvolution_eq_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH)
    (hT : IsKreinSkew J T) :
    cartanInvolution J T = T := by
  change -(kreinAdjoint J T) = T
  change kreinAdjoint J T = -T at hT
  rw [hT, neg_neg]

theorem compactPart_eq_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH)
    (hT : IsKreinSkew J T) :
    compactPart J T = T := by
  rw [compactPart, cartanInvolution_eq_of_isKreinSkew J T hT]
  rw [show T + T = (2 : ℂ) • T by rw [two_smul], smul_smul]
  norm_num

theorem noncompactPart_eq_zero_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH)
    (hT : IsKreinSkew J T) :
    noncompactPart J T = 0 := by
  rw [noncompactPart, cartanInvolution_eq_of_isKreinSkew J T hT]
  simp

theorem compactPart_is_hilbert_skew_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH)
    (hT : IsKreinSkew J T)
    (hHilbertSkew : adjoint T = -T) :
    adjoint (compactPart J T) = -(compactPart J T) := by
  rw [compactPart_eq_of_isKreinSkew J T hT, hHilbertSkew]

theorem noncompactPart_is_hilbert_self_adjoint_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH)
    (hT : IsKreinSkew J T) :
    adjoint (noncompactPart J T) = noncompactPart J T := by
  rw [noncompactPart_eq_zero_of_isKreinSkew J T hT]
  simp

/-!
The Hilbert-adjoint conclusions do not follow from Krein-skewness alone.
They require additional compatibility hypotheses between `T` and `J`; this
owner therefore does not assert them without those hypotheses.
-/

end InfoGeometry.Lie.CartanKrein

end noncomputable section
