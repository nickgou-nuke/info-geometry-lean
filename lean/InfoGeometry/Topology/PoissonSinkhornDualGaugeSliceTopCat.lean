import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.PoissonSinkhornDualGaugeQuotientTopCat

/-!
# Gauge-fixed slice for finite Poisson Sinkhorn dual potentials

The additive dual-potential gauge admits a concrete chart: after choosing one
reference component, subtract its row potential from every row potential and
add it to every column potential.  This produces a representative whose
reference row potential is zero.  The file records the algebraic section and
its continuous factorization through the already defined gauge quotient.
It deliberately does not claim that the resulting chart is a homeomorphism.
-/

namespace InfoGeometry.Topology.PoissonSinkhornDualGaugeSliceTopCat

open CategoryTheory
open InfoGeometry.Inference
open InfoGeometry.Topology.PoissonSinkhornDualTopCat
open InfoGeometry.Topology.PoissonSinkhornDualGaugeQuotientTopCat

variable {n : Nat} [Nonempty (Fin n)]

abbrev DualGaugeSlice (i₀ : Fin n) :=
  {p : DualParameter n // p.2.1 i₀ = 0}

def dualGaugeFix (i₀ : Fin n) (p : DualParameter n) : DualParameter n :=
  (p.1,
    (fun i => p.2.1 i - p.2.1 i₀),
    (fun j => p.2.2 j + p.2.1 i₀))

def dualGaugeFixSlice (i₀ : Fin n) (p : DualParameter n) : DualGaugeSlice i₀ :=
  ⟨dualGaugeFix i₀ p, by simp [dualGaugeFix]⟩

theorem dualGaugeFix_slice_apply (i₀ : Fin n) (p : DualParameter n) :
    (dualGaugeFixSlice i₀ p : DualParameter n) = dualGaugeFix i₀ p :=
  rfl

theorem dualGaugeFix_respects_gauge (i₀ : Fin n) {p q : DualParameter n}
    (hpq : dualGaugeRel p q) :
    dualGaugeFix i₀ p = dualGaugeFix i₀ q := by
  rcases hpq with ⟨t, rfl⟩
  ext <;> simp [dualGaugeFix] <;> ring

theorem dualGaugeFix_is_gauge_equivalent (i₀ : Fin n) (p : DualParameter n) :
    dualGaugeRel (dualGaugeFix i₀ p) p := by
  refine ⟨p.2.1 i₀, ?_⟩
  ext <;> simp [dualGaugeFix]

theorem dualGaugeFix_fixed_on_slice (i₀ : Fin n) (p : DualGaugeSlice i₀) :
    dualGaugeFix i₀ (p : DualParameter n) = p := by
  ext <;> simp [dualGaugeFix, p.property]

theorem continuous_dualGaugeFix (i₀ : Fin n) :
    Continuous (dualGaugeFix i₀ : DualParameter n → DualParameter n) := by
  let hβ : Continuous (fun p : DualParameter n => p.2.1) :=
    continuous_fst.comp continuous_snd
  let hγ : Continuous (fun p : DualParameter n => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hβi (i : Fin n) : Continuous (fun p : DualParameter n => p.2.1 i) :=
    continuous_apply i |>.comp hβ
  have hγj (j : Fin n) : Continuous (fun p : DualParameter n => p.2.2 j) :=
    continuous_apply j |>.comp hγ
  have hβ' : Continuous (fun p : DualParameter n =>
      fun i => p.2.1 i - p.2.1 i₀) :=
    continuous_pi (fun i => (hβi i).sub (hβi i₀))
  have hγ' : Continuous (fun p : DualParameter n =>
      fun j => p.2.2 j + p.2.1 i₀) :=
    continuous_pi (fun j => (hγj j).add (hβi i₀))
  exact continuous_fst.prodMk (hβ'.prodMk hγ')

noncomputable def dualGaugeFixQuotient (i₀ : Fin n) :
    DualGaugeQuotient (n := n) → DualGaugeSlice i₀ :=
  Quotient.lift (dualGaugeFixSlice i₀)
    (fun _ _ h => Subtype.ext (dualGaugeFix_respects_gauge i₀ h))

theorem continuous_dualGaugeFixQuotient (i₀ : Fin n) :
    Continuous (dualGaugeFixQuotient i₀) := by
  have hfix : Continuous (dualGaugeFixSlice i₀) :=
    (continuous_dualGaugeFix i₀).subtype_mk _
  apply Continuous.quotient_lift
  · exact hfix

noncomputable def dualGaugeSliceQuotientMap (i₀ : Fin n) :
    DualGaugeSlice i₀ → DualGaugeQuotient (n := n) :=
  fun p => dualGaugeQuotientMap (p : DualParameter n)

theorem continuous_dualGaugeSliceQuotientMap (i₀ : Fin n) :
    Continuous (dualGaugeSliceQuotientMap i₀) := by
  exact continuous_dualGaugeQuotientMap.comp continuous_subtype_val

noncomputable def dualGaugeFixQuotientTopCatHom (i₀ : Fin n) :
    TopCat.of (DualGaugeQuotient (n := n)) ⟶ TopCat.of (DualGaugeSlice i₀) :=
  TopCat.ofHom
    { toFun := dualGaugeFixQuotient i₀
      continuous_toFun := continuous_dualGaugeFixQuotient i₀ }

noncomputable def dualGaugeSliceQuotientTopCatHom (i₀ : Fin n) :
    TopCat.of (DualGaugeSlice i₀) ⟶ TopCat.of (DualGaugeQuotient (n := n)) :=
  TopCat.ofHom
    { toFun := dualGaugeSliceQuotientMap i₀
      continuous_toFun := continuous_dualGaugeSliceQuotientMap i₀ }

theorem dualGaugeFixQuotient_section_factorization (i₀ : Fin n) :
    dualGaugeQuotientMapTopCatHom (n := n) ≫
        dualGaugeFixQuotientTopCatHom i₀ =
      TopCat.ofHom
        { toFun := dualGaugeFixSlice i₀
          continuous_toFun :=
            (continuous_dualGaugeFix i₀).subtype_mk _ } := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

theorem dualGaugeFixQuotient_after_slice (i₀ : Fin n) :
    dualGaugeSliceQuotientTopCatHom i₀ ≫
        dualGaugeFixQuotientTopCatHom i₀ =
      𝟙 (TopCat.of (DualGaugeSlice i₀)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact dualGaugeFix_fixed_on_slice i₀ p

theorem dualGaugeFixQuotient_before_slice (i₀ : Fin n) :
    dualGaugeFixQuotientTopCatHom i₀ ≫
        dualGaugeSliceQuotientTopCatHom i₀ =
      𝟙 (TopCat.of (DualGaugeQuotient (n := n))) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
      apply Quotient.sound
      exact dualGaugeFix_is_gauge_equivalent i₀ p

noncomputable def dualGaugeSliceHomeomorph (i₀ : Fin n) :
    DualGaugeQuotient (n := n) ≃ₜ DualGaugeSlice i₀ :=
  { toFun := dualGaugeFixQuotient i₀
    invFun := dualGaugeSliceQuotientMap i₀
    left_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ p =>
          apply Quotient.sound
          exact dualGaugeFix_is_gauge_equivalent i₀ p
    right_inv := by
      intro p
      apply Subtype.ext
      exact dualGaugeFix_fixed_on_slice i₀ p
    continuous_toFun := continuous_dualGaugeFixQuotient i₀
    continuous_invFun := continuous_dualGaugeSliceQuotientMap i₀ }

theorem dualGaugeSliceHomeomorph_apply (i₀ : Fin n) (q : DualGaugeQuotient (n := n)) :
    dualGaugeSliceHomeomorph i₀ q = dualGaugeFixQuotient i₀ q :=
  rfl

noncomputable def dualObjectiveGaugeSliceTopCatHom
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (i₀ : Fin n) :
    TopCat.of (DualGaugeSlice i₀) ⟶ TopCat.of ℝ :=
  dualGaugeSliceQuotientTopCatHom i₀ ≫
    dualObjectiveGaugeQuotientTopCatHom C

theorem dualObjectiveGaugeSliceTopCatHom_apply
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (i₀ : Fin n) (p : DualGaugeSlice i₀) :
    dualObjectiveGaugeSliceTopCatHom C i₀ p =
      dualObjectiveReadout C (p : DualParameter n) := by
  rfl

theorem dualObjectiveGaugeSliceTopCatHom_gauge_fix
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (i₀ : Fin n) (p : DualParameter n) :
    dualObjectiveGaugeSliceTopCatHom C i₀ (dualGaugeFixSlice i₀ p) =
      dualObjectiveReadout C p := by
  rw [dualObjectiveGaugeSliceTopCatHom_apply]
  exact dualObjectiveReadout_respects_gauge C
    (dualGaugeFix_is_gauge_equivalent i₀ p)

end InfoGeometry.Topology.PoissonSinkhornDualGaugeSliceTopCat
