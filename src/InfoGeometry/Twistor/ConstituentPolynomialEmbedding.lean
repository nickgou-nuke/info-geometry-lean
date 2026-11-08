/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorConstituentCCR

/-! # Single-constituent transport into the existing polynomial representation

Contract: native polynomial renaming embeds one constituent and intertwines
coordinate multiplication, differentiation and the conjugate coordinate.
The lower-to-upper translation convention from the incoming branch is kept
explicitly distinct from the existing upper-to-lower collective translation.
-/
noncomputable section
namespace InfoGeometry.Twistor.ConstituentPolynomialEmbedding
open TwistorConstituentCCR
variable {σ : Type*} [DecidableEq σ] {n : ℕ}

/-- Embed the variables of one constituent in the full polynomial algebra. -/
def singleEmbedding (i : Fin n) : Wave σ →ₐ[ℂ] Wave (Fin n × σ) :=
  MvPolynomial.rename (fun a => (i, a))

/-- Coordinate multiplication intertwines with native polynomial renaming. -/
theorem singleEmbedding_coordinate (i : Fin n) (a : σ) (p : Wave σ) :
    singleEmbedding i (coordinate a p) =
      coordinate (i, a) (singleEmbedding i p) := by
  simp [singleEmbedding, coordinate_apply]

/-- The selected constituent derivative intertwines with the source derivative. -/
theorem singleEmbedding_partial (i : Fin n) (a : σ) (p : Wave σ) :
    partialOp (i, a) (singleEmbedding i p) = singleEmbedding i (partialOp a p) :=
  MvPolynomial.pderiv_rename (fun _ _ h => congrArg Prod.snd h) a p

/-- The same transport holds with the exact conjugate-coordinate scalar. -/
theorem singleEmbedding_conjugate (i : Fin n) (h : ℂ) (a : σ) (p : Wave σ) :
    singleEmbedding i (conjugateCoordinate h a p) =
      conjugateCoordinate h (i, a) (singleEmbedding i p) := by
  change singleEmbedding i (-h • partialOp a p) =
    -h • partialOp (i, a) (singleEmbedding i p)
  rw [map_smul, singleEmbedding_partial]

/-- The incoming branch's lower-coordinate/upper-derivative convention. -/
def lowerUpperTranslation (i : Fin n) (a b : Fin 2) : Operator (Fin n × ChiralSlot) :=
  quadratic (i, Sum.inr b) (i, Sum.inl a)

/-- These translations commute even when the constituent labels differ. -/
theorem lowerUpperTranslations_commute (i j : Fin n) (a b c d : Fin 2) :
    lowerUpperTranslation i a b * lowerUpperTranslation j c d =
      lowerUpperTranslation j c d * lowerUpperTranslation i a b := by
  apply sub_eq_zero.mp
  simpa [lowerUpperTranslation, Prod.mk.injEq] using
    quadratic_commutator (i, Sum.inr b) (i, Sum.inl a)
      (j, Sum.inr d) (j, Sum.inl c)

end InfoGeometry.Twistor.ConstituentPolynomialEmbedding
