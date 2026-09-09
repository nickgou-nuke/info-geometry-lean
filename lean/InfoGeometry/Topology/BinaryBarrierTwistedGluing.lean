import InfoGeometry.Topology.MappingTorusGluing
import InfoGeometry.Convex.BipolarLogitBarrierDuality

/-!
# Reciprocal odds and interval-restricted twisted gluing

The base is the closed unit interval; the probability fibre is the open unit
interval, where the logarithmic barrier is finite. This defines the quotient
topology and a continuous descended barrier. No nonorientability or compact
Möbius-band classification is asserted.
-/

noncomputable section
namespace InfoGeometry.Topology.BinaryBarrierTwistedGluing

open InfoGeometry.Convex.BipolarLogitBarrierDuality

abbrev Base := Set.Icc (0 : ℝ) 1
abbrev Fibre := Set.Ioo (0 : ℝ) 1
abbrev Cylinder := Base × Fibre

def flip (p : Fibre) : Fibre :=
  ⟨1 - p.val, by constructor <;> linarith [p.property.1, p.property.2]⟩

theorem flip_involutive : Function.Involutive flip := by
  intro p
  apply Subtype.ext
  dsimp [flip]
  ring

def flipHomeomorph : Fibre ≃ₜ Fibre where
  toFun := flip
  invFun := flip
  left_inv := flip_involutive
  right_inv := flip_involutive
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.sub continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.sub continuous_subtype_val

def odds (p : Fibre) : ℝ := p.val / (1 - p.val)

theorem odds_flip (p : Fibre) : odds (flip p) = (odds p)⁻¹ := by
  simp [odds, flip]

theorem logit_flip (p : Fibre) :
    logitCoordinate (flip p).val = -logitCoordinate p.val := by
  exact logitCoordinate_one_sub p.val

def fibreBarrier (p : Fibre) : ℝ := intervalBarrier p.val

theorem barrier_flip (p : Fibre) : fibreBarrier (flip p) = fibreBarrier p :=
  intervalBarrier_one_sub p.val

/-- Reuse the existing endpoint rule, restricted to the actual base interval. -/
def step (x y : Cylinder) : Prop :=
  MappingTorusGluing.endpointStep flip (x.1.val, x.2) (y.1.val, y.2)

def gluing : Setoid Cylinder where
  r := Relation.EqvGen step
  iseqv := Relation.EqvGen.is_equivalence step

def TwistedSpace := Quotient gluing

instance : TopologicalSpace TwistedSpace := inferInstanceAs (TopologicalSpace (Quotient gluing))

def project : Cylinder → TwistedSpace := Quotient.mk gluing

theorem project_endpoint (p : Fibre) :
    project (⟨0, by constructor <;> norm_num⟩, p) =
      project (⟨1, by constructor <;> norm_num⟩, flip p) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl, rfl⟩)

theorem barrier_respects_gluing (x y : Cylinder) (h : gluing.r x y) :
    fibreBarrier x.2 = fibreBarrier y.2 := by
  induction h with
  | rel a b h =>
    rcases h with ⟨_, _, hf⟩ | ⟨_, _, hf⟩
    · rw [hf, barrier_flip]
    · rw [hf, barrier_flip]
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def descendedBarrier : TwistedSpace → ℝ :=
  Quotient.lift (fun x : Cylinder => fibreBarrier x.2) barrier_respects_gluing

theorem descendedBarrier_project (x : Cylinder) :
    descendedBarrier (project x) = intervalBarrier x.2.val := rfl

theorem continuous_project : Continuous project := continuous_quotient_mk'

theorem continuous_fibreBarrier : Continuous fibreBarrier := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ((hasDerivAt_intervalBarrier p.property.1 p.property.2).continuousAt).comp
    continuous_subtype_val.continuousAt

theorem continuous_descendedBarrier : Continuous descendedBarrier := by
  exact Continuous.quotient_lift (continuous_fibreBarrier.comp continuous_snd)
    barrier_respects_gluing

/-- The descended observable is uniquely determined by its values on representatives. -/
theorem descendedBarrier_unique (f : TwistedSpace → ℝ)
    (hf : ∀ x : Cylinder, f (project x) = fibreBarrier x.2) :
    f = descendedBarrier := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact hf x

end InfoGeometry.Topology.BinaryBarrierTwistedGluing
