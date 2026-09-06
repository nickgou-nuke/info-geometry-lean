import InfoGeometry.Krein.DoubledSpace
import Mathlib.GroupTheory.GroupAction.Quotient
import InfoGeometry.Stratum.Projective

/-!
# InfoGeometry.Projective.Rays

Projective ray quotient of doubled states by nonzero real scaling.
This implements the foundation layer bridging to `Mathlib`'s orbit quotients.
-/

namespace InfoGeometry.Projective

open InfoGeometry.Krein

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Gauge := ℝˣ

instance : SMul Gauge (DoubledSpace E) :=
  ⟨fun u v => (↑u : ℝ) • v⟩

instance : MulAction Gauge (DoubledSpace E) where
  one_smul := by
    intro v
    simp
  mul_smul := by
    intro u v w
    simp [smul_smul]

/-- Cone-projectivization dictionary: vectors represent the same ray
iff they differ by a nonzero real scalar.
This includes the distinguished zero class (vacuum) in the quotient. -/
def same_ray (v w : DoubledSpace E) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ w = a • v

/-- Setoid for projectivized doubled states (rays). -/
abbrev sameRaySetoid {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] : Setoid (DoubledSpace E) :=
  MulAction.orbitRel Gauge (DoubledSpace E)

/-- Cone-projective states: quotient of doubled states by nonzero real rescaling.
Unlike strict projectivization, this retains a distinguished zero class. -/
abbrev ProjectiveState (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Type :=
  Quotient (sameRaySetoid (E := E))

/-- Canonical projection from a doubled state to its projective ray class. -/
def projectivize (v : DoubledSpace E) : ProjectiveState E :=
  Quotient.mk sameRaySetoid v

/-- `same_ray` is exactly the orbit relation for the gauge action by `ℝˣ`. -/
lemma same_ray_iff_gauge {v w : DoubledSpace E} :
    same_ray v w ↔ sameRaySetoid.r v w := by
  constructor
  · rintro ⟨a, ha, hwa⟩
    refine ⟨(Units.mk0 a ha)⁻¹, ?_⟩
    change (a⁻¹ : ℝ) • w = v
    rw [hwa, ← mul_smul, inv_mul_cancel₀ ha, one_smul]
  · rintro ⟨u, hwu⟩
    refine ⟨(↑(u⁻¹) : ℝ), Units.ne_zero u⁻¹, ?_⟩
    change (↑u : ℝ) • w = v at hwu
    calc
      w = 1 • w := by rw [one_smul]
      _ = (↑(u⁻¹ * u) : ℝ) • w := by simp
      _ = (↑(u⁻¹) : ℝ) • (↑u : ℝ) • w := by rw [Units.val_mul, mul_smul]
      _ = (↑(u⁻¹) : ℝ) • v := by rw [hwu]

lemma projectivize_eq_iff {v w : DoubledSpace E} :
    projectivize v = projectivize w ↔ same_ray v w := by
  rw [same_ray_iff_gauge]
  exact Quotient.eq (r := sameRaySetoid)

lemma projectivize_eq_projectivize_smul
    (u : Gauge) (v : DoubledSpace E) :
    projectivize v = projectivize (u • v) := by
  apply Quotient.sound
  exact ⟨u⁻¹, by simp⟩

@[simp] lemma projectivize_smul
    (u : Gauge) (v : DoubledSpace E) :
    projectivize (u • v) = projectivize v := by
  simpa using (projectivize_eq_projectivize_smul u v).symm

end KreinClifford

end InfoGeometry.Projective
