import InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Projective.Rays

Projective ray quotient of doubled states by nonzero real scaling.
-/

namespace InfoGeometry.Projective

open InfoGeometry.Krein

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cone-projectivization dictionary: vectors represent the same ray
iff they differ by a nonzero real scalar.
This includes the distinguished zero class (vacuum) in the quotient. -/
def same_ray (v w : DoubledSpace E) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ w = a • v

lemma same_ray_refl (v : DoubledSpace E) : same_ray v v :=
  ⟨1, one_ne_zero, by simp⟩

lemma same_ray_symm {v w : DoubledSpace E} :
    same_ray v w → same_ray w v := by
  rintro ⟨a, ha, rfl⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  simp [ha]

lemma same_ray_trans {u v w : DoubledSpace E} :
    same_ray u v → same_ray v w → same_ray u w := by
  rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  simp [mul_smul]

/-- Setoid for projectivized doubled states (rays). -/
instance sameRaySetoid {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] : Setoid (DoubledSpace E) where
  r := same_ray
  iseqv := Equivalence.mk same_ray_refl same_ray_symm same_ray_trans

/-- Cone-projective states: quotient of doubled states by nonzero real rescaling.
Unlike strict projectivization, this retains a distinguished zero class. -/
abbrev ProjectiveState (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Type :=
  Quotient (sameRaySetoid (E := E))

/-- Canonical projection from a doubled state to its projective ray class. -/
def projectivize (v : DoubledSpace E) : ProjectiveState E :=
  Quotient.mk sameRaySetoid v

lemma projectivize_eq_iff {v w : DoubledSpace E} :
    projectivize v = projectivize w ↔ same_ray v w := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

abbrev Gauge := Units ℝ

instance : SMul (Gauge) (DoubledSpace E) :=
  ⟨fun u v => (↑u : ℝ) • v⟩

instance : MulAction (Gauge) (DoubledSpace E) where
  one_smul := by
    intro v
    simp
  mul_smul := by
    intro u v w
    simp [smul_smul]

/-- `same_ray` is exactly the orbit relation for the gauge action by `ℝˣ`. -/
lemma same_ray_iff_gauge {v w : DoubledSpace E} :
    same_ray v w ↔ ∃ u : Gauge, w = u • v := by
  constructor
  · rintro ⟨a, ha, hwa⟩
    refine ⟨Units.mk0 a ha, ?_⟩
    simpa using hwa
  · rintro ⟨u, hwu⟩
    refine ⟨(↑u : ℝ), Units.ne_zero u, ?_⟩
    simpa using hwu

lemma projectivize_eq_projectivize_smul
    (u : Gauge) (v : DoubledSpace E) :
    projectivize v = projectivize (u • v) := by
  apply Quotient.sound
  exact same_ray_iff_gauge.2 ⟨u, rfl⟩

@[simp] lemma projectivize_smul
    (u : Gauge) (v : DoubledSpace E) :
    projectivize (u • v) = projectivize v := by
  simpa using (projectivize_eq_projectivize_smul u v).symm

end KreinClifford

end InfoGeometry.Projective
