/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.ContinuousPeirceSections
import InfoGeometry.Topology.KleinGlideCovering
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinNative
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Continuous Peirce sections over the real Klein double cover

The fibre is the full noncommutative algebra of continuous real operators on
the existing doubled chiral Krein carrier. Its transition automorphism is
conjugation by the existing sheet swap. Continuous fields obey
`a (torusGlide x) = mirror (a x)`. The two local projectors are exchanged,
while their even/odd operator grading preserves this condition.

The base is the existing free `ZMod 2` action and quotient covering. This
owner constructs a continuous section algebra and its grading, not a new
quotient space, a locally trivial vector bundle, or a physical CPT theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinRealKreinPeirceSections

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinNative
open KleinBrillouinBase KleinBottleOrbitQuotient

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full real operator algebra of the doubled Hilbert/Krein carrier. -/
abbrev Operator := DoubledSpace E →L[ℝ] DoubledSpace E

noncomputable local instance operatorNormedRing : NormedRing (Operator (E := E)) :=
  ContinuousLinearMap.toNormedRing

local instance operatorTopologicalRing : IsTopologicalRing (Operator (E := E)) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- Sheet exchange as Mathlib's continuous conjugation algebra equivalence. -/
def mirror : Operator (E := E) ≃A[ℝ] Operator (E := E) :=
  (chiralSwapLIE (E := E)).toContinuousLinearEquiv.conjContinuousAlgEquiv

/-- The native equivalence acts by the concrete cross-sheet involution. -/
theorem mirror_apply (A : Operator (E := E)) :
    mirror A = etaChiral * A * etaChiral := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem continuous_mirror : Continuous (mirror (E := E)) :=
  (mirror (E := E)).continuous_toFun

theorem mirror_involutive : Function.Involutive (mirror (E := E)) := by
  intro A
  have hJ : (etaChiral (E := E) : Operator (E := E)) * etaChiral = 1 :=
    etaChiral_involution
  rw [mirror_apply, mirror_apply]
  calc
    etaChiral * (etaChiral * A * etaChiral) * etaChiral =
        (etaChiral * etaChiral) * A * (etaChiral * etaChiral) := by
      simp only [mul_assoc]
    _ = A := by rw [hJ, one_mul, mul_one]

theorem leftProjector_idempotent :
    IsIdempotentElem (leftChiralProjector (E := E)) :=
  leftChiralProjector_idempotent

theorem rightProjector_eq_complement :
    rightChiralProjector (E := E) = 1 - leftChiralProjector := by
  have hsum : leftChiralProjector (E := E) + rightChiralProjector = 1 :=
    leftChiralProjector_add_rightChiralProjector
  exact eq_sub_of_add_eq' hsum

/-- The actual mirror exchanges the two complementary Peirce projectors. -/
theorem mirror_leftProjector :
    mirror (leftChiralProjector (E := E)) = 1 - leftChiralProjector := by
  rw [mirror_apply, ← rightProjector_eq_complement]
  change (etaChiral (E := E)).comp
      ((leftChiralProjector (E := E)).comp etaChiral) = rightChiralProjector
  exact etaChiral_comp_leftChiralProjector_comp_etaChiral

omit [CompleteSpace E] in
/-- The division-free Peirce reflection is the existing real chiral grading. -/
theorem reflection_leftProjector :
    Core.PeirceGrading.reflection (leftChiralProjector (E := E)) = gamma5 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [Core.PeirceGrading.reflection, two_mul, sub_apply, add_apply,
    one_apply_eq_self, leftChiralProjector, smul_apply, ContinuousLinearMap.id_apply]
  module

/-- The cut changes sign under monodromy. -/
theorem mirror_gamma5 : mirror (gamma5 (E := E)) = -gamma5 := by
  have h :=
    Core.PeirceSheetExchange.map_reflection_of_sheet_exchange
      (mirror (E := E)).toAlgEquiv.toRingHom (mirror_leftProjector (E := E))
  change mirror (Core.PeirceGrading.reflection (leftChiralProjector (E := E))) =
    -Core.PeirceGrading.reflection (leftChiralProjector (E := E)) at h
  simpa only [reflection_leftProjector] using h

/-- Operator parity commutes with the real sheet transition: `rho Pi = Pi rho`. -/
theorem mirror_grading_commute (A : Operator (E := E)) :
    mirror (gamma5 * A * gamma5) = gamma5 * mirror A * gamma5 := by
  have h :=
    Core.PeirceSheetExchange.map_conjugation_of_sheet_exchange
      (mirror (E := E)).toAlgEquiv.toRingHom (mirror_leftProjector (E := E)) A
  change mirror (Core.PeirceGrading.conjugation (leftChiralProjector (E := E)) A) =
    Core.PeirceGrading.conjugation leftChiralProjector (mirror A) at h
  simpa only [Core.PeirceGrading.conjugation_apply, reflection_leftProjector] using h

/-- Continuous operator fields with the nontrivial sheet-transition law. -/
abbrev sectionAlgebra : Subalgebra ℝ C(BrillouinTorus, Operator (E := E)) :=
  ContinuousPeirceSections.equivariantSections torusGlide (mirror (E := E)).toAlgEquiv

abbrev Sections := ↥(sectionAlgebra (E := E))

/-- The transition condition defines a closed subalgebra in the compact-open topology. -/
theorem isClosed_sectionAlgebra :
    IsClosed (sectionAlgebra (E := E) : Set C(BrillouinTorus, Operator (E := E))) :=
  ContinuousPeirceSections.isClosed_equivariantSections torusGlide
    (mirror (E := E)).toAlgEquiv continuous_mirror

/-- Pointwise Peirce parity is a continuous real-linear operator on sections. -/
def sectionGrading : Sections (E := E) →L[ℝ] Sections (E := E) :=
  ContinuousPeirceSections.grading torusGlide (mirror (E := E)).toAlgEquiv
    leftChiralProjector mirror_leftProjector

/-- The same parity, with continuity, multiplicativity and inverse laws bundled. -/
def sectionGradingEquiv : Sections (E := E) ≃A[ℝ] Sections (E := E) :=
  ContinuousPeirceSections.gradingContinuousAlgEquiv torusGlide
    (mirror (E := E)).toAlgEquiv
    leftChiralProjector mirror_leftProjector leftProjector_idempotent

theorem sectionGrading_apply (a : Sections (E := E)) (x : BrillouinTorus) :
    (sectionGrading a).1 x = gamma5 * a.1 x * gamma5 := by
  simp only [sectionGrading, ContinuousPeirceSections.grading_apply,
    Core.PeirceGrading.conjugation_apply, reflection_leftProjector]

/-- The two Peirce projections descend as continuous real-linear maps. -/
def evenProjection : Sections (E := E) →L[ℝ] Sections (E := E) :=
  ContinuousPeirceSections.even torusGlide (mirror (E := E)).toAlgEquiv
    leftChiralProjector mirror_leftProjector

def oddProjection : Sections (E := E) →L[ℝ] Sections (E := E) :=
  ContinuousPeirceSections.odd torusGlide (mirror (E := E)).toAlgEquiv
    leftChiralProjector mirror_leftProjector

theorem evenProjection_apply (a : Sections (E := E)) (x : BrillouinTorus) :
    (evenProjection a).1 x =
      Core.PeirceGrading.even leftChiralProjector (a.1 x) := rfl

theorem oddProjection_apply (a : Sections (E := E)) (x : BrillouinTorus) :
    (oddProjection a).1 x =
      Core.PeirceGrading.odd leftChiralProjector (a.1 x) := rfl

theorem sectionGrading_involutive : Function.Involutive (sectionGrading (E := E)) :=
  ContinuousPeirceSections.grading_involutive torusGlide
    (mirror (E := E)).toAlgEquiv leftChiralProjector mirror_leftProjector
    leftProjector_idempotent

theorem evenProjection_add_oddProjection :
    evenProjection (E := E) + oddProjection = ContinuousLinearMap.id ℝ (Sections (E := E)) :=
  ContinuousPeirceSections.even_add_odd torusGlide
    (mirror (E := E)).toAlgEquiv leftChiralProjector mirror_leftProjector

theorem evenProjection_idempotent :
    (evenProjection (E := E)).comp evenProjection = evenProjection :=
  ContinuousPeirceSections.even_idempotent torusGlide
    (mirror (E := E)).toAlgEquiv leftChiralProjector mirror_leftProjector
    leftProjector_idempotent

theorem oddProjection_idempotent :
    (oddProjection (E := E)).comp oddProjection = oddProjection :=
  ContinuousPeirceSections.odd_idempotent torusGlide
    (mirror (E := E)).toAlgEquiv leftChiralProjector mirror_leftProjector
    leftProjector_idempotent

theorem evenProjection_comp_oddProjection :
    (evenProjection (E := E)).comp oddProjection = 0 :=
  ContinuousPeirceSections.even_comp_odd torusGlide
    (mirror (E := E)).toAlgEquiv leftChiralProjector mirror_leftProjector
    leftProjector_idempotent

theorem oddProjection_comp_evenProjection :
    (oddProjection (E := E)).comp evenProjection = 0 :=
  ContinuousPeirceSections.odd_comp_even torusGlide
    (mirror (E := E)).toAlgEquiv leftChiralProjector mirror_leftProjector
    leftProjector_idempotent

/-- Equivariance for the actual two-element deck action, not a label action. -/
theorem section_deck_equivariance (a : Sections (E := E))
    (d : KleinGlideCovering.Deck2) (x : BrillouinTorus) :
    a.1 (d +ᵥ x) = if d.val = 0 then a.1 x else mirror (a.1 x) := by
  change a.1 (if d.val = 0 then x else torusGlide x) = _
  split_ifs with h
  · rfl
  · exact a.property x

/-- Above one Klein base point, representatives give equal or mirror-related values. -/
theorem section_values_over_same_base (a : Sections (E := E))
    {x y : BrillouinTorus} (h : quotientMap x = quotientMap y) :
    a.1 x = a.1 y ∨ a.1 x = mirror (a.1 y) := by
  have horbit := (KleinGlideCovering.quotientMap_eq_iff_orbit x y).mp h
  rcases (KleinGlideCovering.deck_orbit_relation x y).mp horbit with hxy | hxy
  · exact Or.inl (congrArg a.1 hxy)
  · exact Or.inr (by rw [hxy]; exact a.property y)

/-- The constant cross-sheet mirror is an allowed section. -/
def mirrorSection : Sections (E := E) :=
  ContinuousPeirceSections.constantSection torusGlide (mirror (E := E)).toAlgEquiv
    etaChiral (by
      change mirror (etaChiral (E := E)) = etaChiral
      rw [mirror_apply]
      have hJ : (etaChiral (E := E) : Operator (E := E)) * etaChiral = 1 :=
        etaChiral_involution
      rw [hJ, one_mul])

@[simp] theorem mirrorSection_apply (x : BrillouinTorus) :
    (mirrorSection (E := E)).1 x = etaChiral := rfl

/-- The odd section has square one; oddness does not mean square-zero. -/
theorem mirrorSection_sq :
    mirrorSection (E := E) * mirrorSection = 1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (etaChiral (E := E) : Operator (E := E)) * etaChiral = 1
  exact etaChiral_involution

private theorem gamma5_etaChiral_gamma5 :
    (gamma5 (E := E) : Operator (E := E)) * etaChiral * gamma5 = -etaChiral := by
  let G : Operator (E := E) := gamma5 (E := E)
  let J : Operator (E := E) := etaChiral (E := E)
  have hanti : J * G = -(G * J) := etaChiral_gamma5_anticommute (E := E)
  have hG : G * G = 1 := gamma5_involution (E := E)
  change G * J * G = -J
  calc
    G * J * G = G * (J * G) := mul_assoc G J G
    _ = G * -(G * J) := by rw [hanti]
    _ = -((G * G) * J) := by simp only [mul_neg, mul_assoc]
    _ = -J := by rw [hG, one_mul]

theorem sectionGrading_mirrorSection :
    sectionGrading (mirrorSection (E := E)) = -mirrorSection := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  calc
    (sectionGrading (mirrorSection (E := E))).1 x =
        gamma5 * (mirrorSection (E := E)).1 x * gamma5 :=
      sectionGrading_apply mirrorSection x
    _ = -(etaChiral (E := E)) := by
      rw [mirrorSection_apply]
      exact gamma5_etaChiral_gamma5
    _ = (-mirrorSection (E := E)).1 x := rfl

/-- A nonzero real fibre gives a nonzero section algebra. -/
theorem section_one_ne_zero [Nontrivial E] :
    (1 : Sections (E := E)) ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  intro h
  have h0 : (1 : Operator (E := E)) = 0 :=
    congrArg (fun a : Sections (E := E) => a.1 (0 : BrillouinTorus)) h
  have hv0 := congrArg
    (fun A : Operator (E := E) => WithLp.fst (A (to_doubled v 0))) h0
  exact hv (by simpa using hv0)

theorem mirrorSection_ne_zero [Nontrivial E] :
    mirrorSection (E := E) ≠ 0 := by
  intro h
  have hsq := mirrorSection_sq (E := E)
  rw [h, zero_mul] at hsq
  exact section_one_ne_zero hsq.symm

/-- A fixed local sheet projector does not satisfy the twisted gluing law. -/
theorem constant_leftProjector_not_mem [Nontrivial E] :
    ContinuousMap.const BrillouinTorus (leftChiralProjector (E := E)) ∉
      sectionAlgebra := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  intro h
  have h0 : leftChiralProjector (E := E) = mirror leftChiralProjector :=
    h (0 : BrillouinTorus)
  have hpq : leftChiralProjector (E := E) = rightChiralProjector := by
    rw [mirror_leftProjector, ← rightProjector_eq_complement] at h0
    exact h0
  have hv0 := congrArg
    (fun A : Operator (E := E) => WithLp.fst (A (to_doubled v 0))) hpq
  exact hv (by
    simpa only [leftChiralProjector_to_doubled, rightChiralProjector_to_doubled,
      fst_to_doubled]
      using hv0)

/-- The constant cut fails equivariance even though its operator parity descends. -/
theorem constant_gamma5_not_mem [Nontrivial E] :
    ContinuousMap.const BrillouinTorus (gamma5 (E := E)) ∉ sectionAlgebra := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  intro h
  have h0 : gamma5 (E := E) = -gamma5 := by
    have hglide := h (0 : BrillouinTorus)
    change gamma5 (E := E) = mirror gamma5 at hglide
    simpa only [mirror_gamma5] using hglide
  have hvneg : v = -v := by
    have hfst := congrArg
      (fun A : Operator (E := E) => WithLp.fst (A (to_doubled v 0))) h0
    simpa [gamma5, spectral_epsilon, to_doubled] using hfst
  have hsum : v + v = 0 := by
    calc
      v + v = v + -v := congrArg (fun w => v + w) hvneg
      _ = 0 := add_neg_cancel v
  have htwo : (2 : ℝ) • v = 0 := by simpa only [two_smul] using hsum
  exact hv ((smul_eq_zero.mp htwo).resolve_left (by norm_num))

end InfoGeometry.Topology.KleinRealKreinPeirceSections

end
