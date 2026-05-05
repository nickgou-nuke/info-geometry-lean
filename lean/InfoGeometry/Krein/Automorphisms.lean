import InfoGeometry.Krein.KreinSpace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Topology.Algebra.Module.StrongTopology

/-!
# Automorphisms of Krein Space

Centralized dot-notation for conjugation and simp-lemmas.
Uses Mathlib's canonical `conjContinuousAlgEquiv`.
-/

namespace InfoGeometry.Krein

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Canonical conjugation as an `AlgEquiv` (Mathlib). -/
noncomputable abbrev conjEnd (U : H ≃L[ℝ] H) : (H →L[ℝ] H) ≃ₐ[ℝ] (H →L[ℝ] H) :=
  U.conjContinuousAlgEquiv

/-- Canonical conjugation on endomorphisms (CLM). -/
noncomputable abbrev conjugateCLM (U : H ≃L[ℝ] H) (A : H →L[ℝ] H) : H →L[ℝ] H :=
  conjEnd U A

@[simp] lemma conjugateCLM_mul (U : H ≃L[ℝ] H) (A B : H →L[ℝ] H) :
    conjugateCLM U (A * B) = conjugateCLM U A * conjugateCLM U B :=
  (conjEnd U).map_mul A B

@[simp] lemma conjugateCLM_add (U : H ≃L[ℝ] H) (A B : H →L[ℝ] H) :
    conjugateCLM U (A + B) = conjugateCLM U A + conjugateCLM U B :=
  (conjEnd U).map_add A B

@[simp] lemma conjugateCLM_zero (U : H ≃L[ℝ] H) :
    conjugateCLM U (0 : H →L[ℝ] H) = 0 :=
  (conjEnd U).map_zero

@[simp] lemma conjugateCLM_smul (U : H ≃L[ℝ] H) (a : ℝ) (A : H →L[ℝ] H) :
    conjugateCLM U (a • A) = a • conjugateCLM U A :=
  (conjEnd U).toLinearEquiv.map_smul a A

@[simp] lemma conjugateCLM_neg (U : H ≃L[ℝ] H) (A : H →L[ℝ] H) :
    conjugateCLM U (-A) = -conjugateCLM U A :=
  (conjEnd U).map_neg A

@[simp] lemma conjugateCLM_id (U : H ≃L[ℝ] H) :
    conjugateCLM U (ContinuousLinearMap.id ℝ H) = ContinuousLinearMap.id ℝ H :=
  (conjEnd U).map_one

end InfoGeometry.Krein
