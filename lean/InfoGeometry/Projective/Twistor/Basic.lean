import InfoGeometry.Twistor.PenroseTwistor
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

/-!
# Projective Twistor Null Geometry

This file packages the Penrose twistor carrier together with a projectivized
null cone built from the real null readout of the Hermitian form.

The boundary layer is explicit and honest:

* the carrier is the existing `ℂ^4` twistor space;
* the null condition is the real null readout `Complex.re (h Z Z) = 0`;
* projective null rays are quotient rays modulo unit scaling;
* the concrete Penrose datum is obtained from the existing Hermitian form.

No split-octonion theorem is claimed here.
No definitional equality `TwistorSpace = SplitOctonions` is claimed here.
No quantized twistor CCR realization theorem is claimed here.
-/

open scoped Classical

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

instance nullRepSetoid : Setoid (NullRep D) where
  r := rayRel D
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro X
      exact ⟨1, D.scale_one X.Z⟩
    · intro X Y hXY
      rcases hXY with ⟨u, hXY⟩
      refine ⟨u⁻¹, ?_⟩
      calc
        D.scale u⁻¹ Y.Z = D.scale u⁻¹ (D.scale u X.Z) := by rw [← hXY]
        _ = D.scale (u⁻¹ * u) X.Z := by
          exact (D.scale_mul u⁻¹ u X.Z).symm
        _ = D.scale 1 X.Z := by simp
        _ = X.Z := D.scale_one X.Z
    · intro X Y Z hXY hYZ
      rcases hXY with ⟨u, hXY⟩
      rcases hYZ with ⟨v, hYZ⟩
      refine ⟨v * u, ?_⟩
      calc
        D.scale (v * u) X.Z = D.scale v (D.scale u X.Z) := D.scale_mul v u X.Z
        _ = D.scale v Y.Z := by rw [hXY]
        _ = Z.Z := hYZ

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
  scale_mul := by intro u v Z; simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
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
      InfoGeometry.Twistor.PenroseTwistor.twistorHermitian_apply,
      InfoGeometry.Twistor.PenroseTwistor.twistorMetricMatrix, Pi.single,
      Fin.sum_univ_four]
  have hv0 : v ≠ 0 := by
    intro hzero
    have h0 := congrArg (fun f : PenroseTwistorCarrier => f 0) hzero
    have h0 : (1 : ℂ) = 0 := by
      simpa [v] using h0
    exact one_ne_zero h0
  exact ⟨penroseNullTwistorMk ⟨v, hv, hv0⟩⟩

end InfoGeometry.Projective.Twistor
