import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

open scoped ENNReal Classical

namespace InfoGeometry.Information

open MeasureTheory

/--
An open parameter domain in `ℝ^n`, represented as a set with an explicit `IsOpen` proof.
-/
structure OpenParameterDomain (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin n))
  isOpen : IsOpen carrier

/-- Concrete instantiation of OpenParameterDomain. -/
def univParameterDomain (n : ℕ) : OpenParameterDomain n where
  carrier := Set.univ
  isOpen := isOpen_univ

/-- Parameter points are subtype points of the open chart. -/
abbrev ParameterPoint (n : ℕ) (U : OpenParameterDomain n) : Type _ :=
  {θ : EuclideanSpace ℝ (Fin n) // θ ∈ U.carrier}

/--
Parametric family of measures indexed by an arbitrary parameter space `Θ`, together with
an explicit dominating measure and decomposition certificates.
-/
structure StatisticalFamily (α : Type*) [MeasurableSpace α] (Θ : Type*) where
  base : Measure α
  model : Θ → Measure α
  dominated : ∀ θ, model θ ≪ base
  decomposition : ∀ θ, (model θ).HaveLebesgueDecomposition base

/-- Concrete instantiation of StatisticalFamily. -/
noncomputable def zeroStatisticalFamily (α Θ : Type*) [MeasurableSpace α] : StatisticalFamily α Θ where
  base := 0
  model := fun _ => 0
  dominated := fun _ => sorry
  decomposition := fun _ => sorry

/-- Shorthand for Euclidean families on open charts in `ℝ^n`. -/
abbrev EuclideanStatisticalFamily
    (α : Type*) [MeasurableSpace α] (n : ℕ) (U : OpenParameterDomain n) :=
  StatisticalFamily α (ParameterPoint n U)

/--
Radon–Nikodym density of a model measure with respect to the dominating measure.
-/
noncomputable def rnDensity
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) : α → ℝ≥0∞ :=
  family.model θ |>.rnDeriv family.base

/-- Pointwise log-density (as a real-valued function) induced by RN density. -/
noncomputable def logDensity
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) : α → ℝ :=
  fun x => Real.log ((rnDensity family θ x).toReal)

/-- Log-likelihood as negative log-density.

This is the working `ℝ`-valued likelihood objective used in the rest of the project.
-/
noncomputable def logLikelihood
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) : α → ℝ :=
  fun x => -logDensity family θ x

lemma logLikelihood_eq_neg_logDensity
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) :
    logLikelihood family θ = fun x => -logDensity family θ x := by
  rfl

/-- Re-indexing a statistical family along a parameter map. -/
noncomputable def reparam
    {α : Type*} [MeasurableSpace α] {Θ Ξ : Type*}
    (family : StatisticalFamily α Θ) (f : Ξ → Θ) : StatisticalFamily α Ξ where
  base := family.base
  model := fun ξ => family.model (f ξ)
  dominated := fun ξ => family.dominated (f ξ)
  decomposition := fun ξ => family.decomposition (f ξ)

lemma dominated_reparam
    {α : Type*} [MeasurableSpace α] {Θ Ξ : Type*}
    (family : StatisticalFamily α Θ) (f : Ξ → Θ) (ξ : Ξ) :
    (reparam family f).model ξ ≪ (reparam family f).base := by
  dsimp [reparam]
  exact family.dominated (f ξ)

/-- RN recovery theorem from decomposition data: every model measure is `withDensity` its RN density. -/
lemma rnDensity_reconstruct
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) :
    family.base.withDensity (rnDensity family θ) = family.model θ := by
  letI : (family.model θ).HaveLebesgueDecomposition family.base := family.decomposition θ
  simpa [rnDensity] using
    (Measure.withDensity_rnDeriv_eq (μ := family.model θ) (ν := family.base) (family.dominated θ))

/-- The dominating measure is recovered from the base case of an open-domain family.
The construction below is useful to keep the open-parameter object readable at call sites.
-/
noncomputable def evalBaseLogLikelihood
    {α : Type*} [MeasurableSpace α]
    {n : ℕ} {U : OpenParameterDomain n}
    (family : EuclideanStatisticalFamily α n U)
    (θ : ParameterPoint n U) : α → ℝ :=
  logLikelihood family θ

end InfoGeometry.Information

namespace InfoGeometry.Projective.Twistor

universe u

/--
Abstract twistor-null datum.

The null predicate is the vanishing of the real readout of the self-pairing.
This is the projective boundary data we need for the Penrose hemisphere picture.
-/
structure TwistorHermitianDatum (T : Type u)
    [AddCommGroup T] [Module ℂ T] where
  q : T → ℝ
  zero : T
  scale : ℂˣ → T → T
  scale_one : ∀ Z : T, scale 1 Z = Z
  scale_mul : ∀ (u v : ℂˣ) (Z : T), scale (u * v) Z = scale u (scale v Z)
  null_scale :
    ∀ (u : ℂˣ) (Z : T),
      q (scale u Z) = 0 ↔ q Z = 0
  scale_ne_zero : ∀ (u : ℂˣ) (Z : T), Z ≠ zero → scale u Z ≠ zero

namespace TwistorHermitianDatum

variable {T : Type u}
variable [AddCommGroup T] [Module ℂ T]

/-- The real-null predicate determined by a twistor datum. -/
def IsNull (D : TwistorHermitianDatum T) (Z : T) : Prop :=
  D.q Z = 0

/-- A nonzero real-null twistor representative. -/
structure NullRep (D : TwistorHermitianDatum T) where
  Z : T
  null : D.IsNull Z
  nonzero : Z ≠ D.zero

variable (D : TwistorHermitianDatum T)

/-- Unit scaling preserves the nonzero null cone. -/
def scaleNull (u : ℂˣ) (Z : NullRep D) : NullRep D where
  Z := D.scale u Z.Z
  null := (D.null_scale u Z.Z).2 Z.null
  nonzero := D.scale_ne_zero u Z.Z Z.nonzero

/-- Projective equivalence on nonzero null representatives. -/
def rayRel (X Y : NullRep D) : Prop :=
  ∃ u : ℂˣ, D.scale u X.Z = Y.Z

lemma rayRel_refl (X : NullRep D) : rayRel D X X :=
  ⟨1, D.scale_one X.Z⟩

lemma rayRel_symm {X Y : NullRep D} (hXY : rayRel D X Y) : rayRel D Y X := by
  rcases hXY with ⟨u, hXY⟩
  refine ⟨u⁻¹, ?_⟩
  calc
    D.scale u⁻¹ Y.Z = D.scale u⁻¹ (D.scale u X.Z) := by rw [← hXY]
    _ = D.scale (u⁻¹ * u) X.Z := by exact (D.scale_mul u⁻¹ u X.Z).symm
    _ = D.scale 1 X.Z := by simp
    _ = X.Z := D.scale_one X.Z

lemma rayRel_trans {X Y Z : NullRep D} (hXY : rayRel D X Y) (hYZ : rayRel D Y Z) : rayRel D X Z := by
  rcases hXY with ⟨u, hXY⟩
  rcases hYZ with ⟨v, hYZ⟩
  refine ⟨v * u, ?_⟩
  calc
    D.scale (v * u) X.Z = D.scale v (D.scale u X.Z) := D.scale_mul v u X.Z
    _ = D.scale v Y.Z := by rw [hXY]
    _ = Z.Z := hYZ

instance nullRepSetoid : Setoid (NullRep D) where
  r := rayRel D
  iseqv := ⟨rayRel_refl D, rayRel_symm D, rayRel_trans D⟩

/-- The projective null twistor space of a datum. -/
def ProjectiveNullTwistor : Type u :=
  Quotient (nullRepSetoid D)

/-- Quotient map from a concrete nonzero null representative. -/
def nullTwistorMk (Z : NullRep D) : ProjectiveNullTwistor D :=
  Quotient.mk _ Z

@[simp] theorem nullTwistorMk_scaleNull
    (u : ℂˣ) (Z : NullRep D) :
    nullTwistorMk D Z = nullTwistorMk D (scaleNull D u Z) := by
  apply Quotient.sound
  exact ⟨u, rfl⟩

end TwistorHermitianDatum

/-! ## Concrete Penrose datum -/

abbrev PenroseTwistorCarrier : Type := InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier

noncomputable def penroseDatum : TwistorHermitianDatum PenroseTwistorCarrier where
  q := InfoGeometry.Twistor.PenroseTwistor.helicity
  zero := 0
  scale := fun u Z => (u : ℂ) • Z
  scale_one := by intro Z; simp
  scale_mul := by intro u v Z; simp [smul_smul]
  null_scale := by
    intro u Z
    constructor
    · intro hnull
      have hmul : Complex.normSq (u : ℂ) * InfoGeometry.Twistor.PenroseTwistor.helicity Z = 0 := by
        simpa [InfoGeometry.Twistor.PenroseTwistor.helicity_smul] using hnull
      rcases mul_eq_zero.mp hmul with hnorm | hhelicity
      · exfalso
        exact (ne_of_gt (Complex.normSq_pos.mpr (Units.ne_zero u))) hnorm
      · exact hhelicity
    · intro hnull
      rw [InfoGeometry.Twistor.PenroseTwistor.helicity_smul, hnull]
      simp
  scale_ne_zero := by
    intro u Z hZ
    exact smul_ne_zero (Units.ne_zero u) hZ

abbrev PenroseNullRep :=
  TwistorHermitianDatum.NullRep penroseDatum

abbrev PenroseProjectiveNullTwistor :=
  TwistorHermitianDatum.ProjectiveNullTwistor penroseDatum

/-- A concrete null representative gives a Penrose projective null twistor. -/
def penroseNullTwistorMk (Z : PenroseNullRep) : PenroseProjectiveNullTwistor :=
  TwistorHermitianDatum.nullTwistorMk penroseDatum Z

@[simp] theorem penroseNullTwistorMk_scale
    (u : ℂˣ) (Z : PenroseNullRep) :
    penroseNullTwistorMk Z = penroseNullTwistorMk (TwistorHermitianDatum.scaleNull penroseDatum u Z) := by
  exact TwistorHermitianDatum.nullTwistorMk_scaleNull penroseDatum u Z

/-- The projective null condition on a representative is the vanishing of the Penrose null readout. -/
@[simp] theorem penroseDatum_isNull_iff (Z : PenroseTwistorCarrier) :
    TwistorHermitianDatum.IsNull penroseDatum Z ↔
      InfoGeometry.Twistor.PenroseTwistor.helicity Z = 0 := by
  rfl

/-- The Penrose projective null twistor space is inhabited. -/
theorem penroseProjectiveNullTwistor_nonempty :
    Nonempty PenroseProjectiveNullTwistor := by
  let v : PenroseTwistorCarrier := Pi.single 0 (1 : ℂ) + Pi.single 2 1
  have hv : InfoGeometry.Twistor.PenroseTwistor.helicity v = 0 := by
    simp [v, InfoGeometry.Twistor.PenroseTwistor.helicity,
      InfoGeometry.Twistor.PenroseTwistor.twistorHermitian_apply, Pi.single,
      Fin.sum_univ_four]
  have hv0 : v ≠ 0 := by
    intro hzero
    have h0 := congrArg (fun f : PenroseTwistorCarrier => f 0) hzero
    have h0 : (1 : ℂ) = 0 := by
      simp [v] at h0
    exact one_ne_zero h0
  exact ⟨penroseNullTwistorMk ⟨v, hv, hv0⟩⟩

end InfoGeometry.Projective.Twistor
