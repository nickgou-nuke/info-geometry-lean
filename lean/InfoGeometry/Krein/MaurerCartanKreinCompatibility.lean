/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
import InfoGeometry.Krein.KreinSpace

/-!
# Krein compatibility of a five-graded operator jet

The source Maurer–Cartan jet packages operator-valued derivative and bracket
entries. This file records compatibility assumptions on those entries and
proves that the five curvature sums remain Krein-skew-adjoint. The bracket
entries remain data from the source jet: these results do not identify them
with commutators of underlying connection fields or assert flatness.
-/

namespace InfoGeometry.Krein

open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open _root_.InfoGeometry.Krein.KreinSpace

section KreinMCCompatibility

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [_root_.InfoGeometry.Krein.KreinSpace H]

/-- All sixteen entries of an operator-valued five-grade jet are
Krein-skew-adjoint. -/
structure jetKreCompatible (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H)) : Prop where
  dOmega_m2_skew : IsKreinSkewAdjoint jet.dOmega_m2
  dOmega_m1_skew : IsKreinSkewAdjoint jet.dOmega_m1
  dOmega_0_skew : IsKreinSkewAdjoint jet.dOmega_0
  dOmega_p1_skew : IsKreinSkewAdjoint jet.dOmega_p1
  dOmega_p2_skew : IsKreinSkewAdjoint jet.dOmega_p2
  br_0_m2_skew : IsKreinSkewAdjoint jet.br_0_m2
  br_m1_m1_half_skew : IsKreinSkewAdjoint jet.br_m1_m1_half
  br_0_m1_skew : IsKreinSkewAdjoint jet.br_0_m1
  br_p1_m2_skew : IsKreinSkewAdjoint jet.br_p1_m2
  br_0_0_half_skew : IsKreinSkewAdjoint jet.br_0_0_half
  br_m1_p1_skew : IsKreinSkewAdjoint jet.br_m1_p1
  br_m2_p2_skew : IsKreinSkewAdjoint jet.br_m2_p2
  br_0_p1_skew : IsKreinSkewAdjoint jet.br_0_p1
  br_m1_p2_skew : IsKreinSkewAdjoint jet.br_m1_p2
  br_0_p2_skew : IsKreinSkewAdjoint jet.br_0_p2
  br_p1_p1_half_skew : IsKreinSkewAdjoint jet.br_p1_p1_half

/-- A sum of two Krein-skew-adjoint operators is Krein-skew-adjoint. -/
lemma kreinSkewAdjoint_add {A B : H →L[ℝ] H}
    (hA : IsKreinSkewAdjoint A) (hB : IsKreinSkewAdjoint B) :
    IsKreinSkewAdjoint (A + B) := by
  rw [isKreinSkewAdjoint_iff_eq_neg] at hA hB ⊢
  calc
    kreinAdjoint (A + B) = kreinAdjoint A + kreinAdjoint B := kreinAdjoint_add A B
    _ = -A + -B := by rw [hA, hB]
    _ = -(A + B) := (neg_add A B).symm

/-- Krein-skew-adjoint operators are closed under the operator commutator. -/
lemma kreinSkewAdjoint_commutator {A B : H →L[ℝ] H}
    (hA : IsKreinSkewAdjoint A) (hB : IsKreinSkewAdjoint B) :
    IsKreinSkewAdjoint ⁅A, B⁆ :=
  isKreinSkewAdjoint_lie hA hB

/-- Grade `-2` curvature expression. -/
def mcKreinCurvatureM2 (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H)) : H →L[ℝ] H :=
  jet.dOmega_m2 + jet.br_0_m2 + jet.br_m1_m1_half

/-- Grade `-1` curvature expression. -/
def mcKreinCurvatureM1 (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H)) : H →L[ℝ] H :=
  jet.dOmega_m1 + jet.br_0_m1 + jet.br_p1_m2

/-- Grade `0` curvature expression. -/
def mcKreinCurvature0 (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H)) : H →L[ℝ] H :=
  jet.dOmega_0 + jet.br_0_0_half + (jet.br_m1_p1 + jet.br_m2_p2)

/-- Grade `+1` curvature expression. -/
def mcKreinCurvatureP1 (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H)) : H →L[ℝ] H :=
  jet.dOmega_p1 + jet.br_0_p1 + jet.br_m1_p2

/-- Grade `+2` curvature expression. -/
def mcKreinCurvatureP2 (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H)) : H →L[ℝ] H :=
  jet.dOmega_p2 + jet.br_0_p2 + jet.br_p1_p1_half

theorem mcKreinCurvatureM2_skew (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H))
    (h : jetKreCompatible jet) : IsKreinSkewAdjoint (mcKreinCurvatureM2 jet) := by
  change IsKreinSkewAdjoint (jet.dOmega_m2 + jet.br_0_m2 + jet.br_m1_m1_half)
  exact kreinSkewAdjoint_add (kreinSkewAdjoint_add h.dOmega_m2_skew h.br_0_m2_skew)
    h.br_m1_m1_half_skew

theorem mcKreinCurvatureM1_skew (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H))
    (h : jetKreCompatible jet) : IsKreinSkewAdjoint (mcKreinCurvatureM1 jet) := by
  change IsKreinSkewAdjoint (jet.dOmega_m1 + jet.br_0_m1 + jet.br_p1_m2)
  exact kreinSkewAdjoint_add (kreinSkewAdjoint_add h.dOmega_m1_skew h.br_0_m1_skew)
    h.br_p1_m2_skew

theorem mcKreinCurvature0_skew (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H))
    (h : jetKreCompatible jet) : IsKreinSkewAdjoint (mcKreinCurvature0 jet) := by
  change IsKreinSkewAdjoint
    (jet.dOmega_0 + jet.br_0_0_half + (jet.br_m1_p1 + jet.br_m2_p2))
  exact kreinSkewAdjoint_add
    (kreinSkewAdjoint_add h.dOmega_0_skew h.br_0_0_half_skew)
    (kreinSkewAdjoint_add h.br_m1_p1_skew h.br_m2_p2_skew)

theorem mcKreinCurvatureP1_skew (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H))
    (h : jetKreCompatible jet) : IsKreinSkewAdjoint (mcKreinCurvatureP1 jet) := by
  change IsKreinSkewAdjoint (jet.dOmega_p1 + jet.br_0_p1 + jet.br_m1_p2)
  exact kreinSkewAdjoint_add (kreinSkewAdjoint_add h.dOmega_p1_skew h.br_0_p1_skew)
    h.br_m1_p2_skew

theorem mcKreinCurvatureP2_skew (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H))
    (h : jetKreCompatible jet) : IsKreinSkewAdjoint (mcKreinCurvatureP2 jet) := by
  change IsKreinSkewAdjoint (jet.dOmega_p2 + jet.br_0_p2 + jet.br_p1_p1_half)
  exact kreinSkewAdjoint_add (kreinSkewAdjoint_add h.dOmega_p2_skew h.br_0_p2_skew)
    h.br_p1_p1_half_skew

/-- All five graded curvature expressions are Krein-skew-adjoint. -/
theorem mcKreinCurvatureTower_skew (jet : FiveGradedMaurerCartanJet (H →L[ℝ] H))
    (h : jetKreCompatible jet) :
    IsKreinSkewAdjoint (mcKreinCurvatureM2 jet) ∧
    IsKreinSkewAdjoint (mcKreinCurvatureM1 jet) ∧
    IsKreinSkewAdjoint (mcKreinCurvature0 jet) ∧
    IsKreinSkewAdjoint (mcKreinCurvatureP1 jet) ∧
    IsKreinSkewAdjoint (mcKreinCurvatureP2 jet) := by
  exact ⟨mcKreinCurvatureM2_skew jet h, mcKreinCurvatureM1_skew jet h,
    mcKreinCurvature0_skew jet h, mcKreinCurvatureP1_skew jet h,
    mcKreinCurvatureP2_skew jet h⟩

/-- A Krein-skew-adjoint operator infinitesimally preserves the Krein pairing. -/
theorem kreinPairing_infinitesimal_invariance {A : H →L[ℝ] H}
    (hA : IsKreinSkewAdjoint A) (u v : H) :
    kreinInner (A u) v + kreinInner u (A v) = 0 :=
  (isKreinSkewAdjoint_iff A).mp hA u v

end KreinMCCompatibility
end InfoGeometry.Krein
