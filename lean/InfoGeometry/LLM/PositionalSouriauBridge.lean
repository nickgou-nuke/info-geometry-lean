/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.PositionalEncodingRepresentation
import InfoGeometry.QuantumContext.LinShuMajoranaColimitCapstone

/-!
# Positional relative scores and Souriau/KMS weights

This bridge records one precise common carrier between the positional and
thermodynamic transformer lanes.  A finite positional score profile is read as
negative energy, so the Souriau Gibbs weight is the corresponding softmax/KMS
weight.  If the score profile depends only on the relative position, the
thermodynamic weight is invariant under simultaneous translation of both
positions.

No arithmetic Bost--Connes identification or continuum Yang--Mills statement
is inferred here; those remain owned by their respective modules.
-/

namespace InfoGeometry.LLM.PositionalSouriauBridge

open InfoGeometry.LLM.PositionalEncodingRepresentation
open InfoGeometry.QuantumContext.LinShuMajoranaColimitCapstone
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional
open InfoGeometry.QuantumContext.AttentionKMSState

/-- Souriau/KMS weight obtained from a finite positional score profile by the
energy convention `E = -score`. -/
noncomputable def positionalSouriauWeight {n : ℕ} [Fintype (Fin n)]
    (score : ℝ → ℝ → Fin n → ℝ) (β t s : ℝ) (j : Fin n) : ℝ :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.gibbsWeight
    β (fun k => -score t s k) j

/-- Negative-score Souriau weights are exactly the existing KMS softmax
weights on every finite positional slice. -/
theorem positionalSouriauWeight_eq_softmax {n : ℕ} [Fintype (Fin n)]
    (score : ℝ → ℝ → Fin n → ℝ) (β t s : ℝ) (j : Fin n) :
    positionalSouriauWeight score β t s j =
      InfoGeometry.QuantumContext.AttentionKMSState.softmaxWeight
        (score t s) β j := by
  exact InfoGeometry.QuantumContext.LinShuMajoranaColimitCapstone.souriau_gibbsWeight_neg_eq_softmaxWeight
    (score t s) β j

/-- Relative positional score profiles induce simultaneous-translation-invariant
Souriau/KMS weights. -/
theorem positionalSouriauWeight_simultaneous_shift
    {n : ℕ} [Fintype (Fin n)]
    (score : ℝ → ℝ → Fin n → ℝ)
    (hrelative : ∀ t s c, score (t + c) (s + c) = score t s)
    (β t s c : ℝ) (j : Fin n) :
    positionalSouriauWeight score β (t + c) (s + c) j =
      positionalSouriauWeight score β t s j := by
  unfold positionalSouriauWeight
  rw [InfoGeometry.QuantumContext.LinShuMajoranaColimitCapstone.souriau_gibbsWeight_neg_eq_softmaxWeight,
    InfoGeometry.QuantumContext.LinShuMajoranaColimitCapstone.souriau_gibbsWeight_neg_eq_softmaxWeight]
  rw [hrelative]

/-- The theorem applies to any score family already proved to depend only on
` t - s`; this is the exact positional-to-thermal transport step. -/
theorem positionalSouriauWeight_of_difference
    {n : ℕ} [Fintype (Fin n)]
    (score : ℝ → ℝ → Fin n → ℝ)
    (relative : ℝ → Fin n → ℝ)
    (hrelative : ∀ t s, score t s = relative (t - s))
    (β t s c : ℝ) (j : Fin n) :
    positionalSouriauWeight score β (t + c) (s + c) j =
      positionalSouriauWeight score β t s j := by
  apply positionalSouriauWeight_simultaneous_shift score
  intro t s c
  rw [hrelative, hrelative]
  congr 1
  ring

/-- A scalar exponential relative score transports directly to a
translation-invariant Souriau/KMS weight.  This is the concrete decaying
linear-attention boundary, without claiming a training or approximation
result. -/
theorem exponentialDecaySouriauWeight_translation_invariant
    {n : ℕ} [Fintype (Fin n)]
    (base : Fin n → ℝ) (c β t s a : ℝ) (j : Fin n) :
    positionalSouriauWeight
        (fun t s j => Real.exp (c * (t - s)) * base j) β (t + a) (s + a) j =
      positionalSouriauWeight
        (fun t s j => Real.exp (c * (t - s)) * base j) β t s j := by
  apply positionalSouriauWeight_of_difference
    (fun t s j => Real.exp (c * (t - s)) * base j)
    (fun d j => Real.exp (c * d) * base j)
  intro t s
  rfl

/-- The real ALiBi penalty is a relative score and therefore has the same
thermal translation invariance.  The statement isolates the algebraic
representation claim from any engineering claim about routing quality. -/
theorem alibiSouriauWeight_translation_invariant
    {n : ℕ} [Fintype (Fin n)]
    (base : Fin n → ℝ) (p β t s a : ℝ) (j : Fin n) :
    positionalSouriauWeight
        (fun t s j => base j - p * (t - s)) β (t + a) (s + a) j =
      positionalSouriauWeight
        (fun t s j => base j - p * (t - s)) β t s j := by
  apply positionalSouriauWeight_of_difference
    (fun t s j => base j - p * (t - s))
    (fun d j => base j - p * d)
  intro t s
  rfl

end InfoGeometry.LLM.PositionalSouriauBridge
