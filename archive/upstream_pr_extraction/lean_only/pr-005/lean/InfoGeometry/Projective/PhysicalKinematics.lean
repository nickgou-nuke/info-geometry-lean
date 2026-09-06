import InfoGeometry.Projective.Rays

namespace InfoGeometry.Projective

/-- A minimal physics-kinematics interface:
representatives `V`, a gauge group acting on `V`, and physical states as gauge classes. -/
structure PhysicalKinematics (V : Type _) [Zero V] where
  State : Type _
  Gauge : Type _
  [instMonoid : Monoid Gauge]
  [instAct : MulAction Gauge V]
  ray : V → State
  ray_gauge : ∀ (g : Gauge) (v : V), ray (g • v) = ray v

attribute [instance] PhysicalKinematics.instMonoid
attribute [instance] PhysicalKinematics.instAct

section Doubled

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Canonical kinematics for doubled representatives modulo nonzero real scaling. -/
def doubledProjectiveKinematics : PhysicalKinematics (DoubledSpace E) where
  State := ProjectiveState (E := E)
  Gauge := Gauge
  ray := projectivize (E := E)
  ray_gauge := by
    intro g v
    exact projectivize_smul (E := E) g v

variable {β : Type _}

/-- Gauge-invariance predicate for representative-level observables. -/
def GaugeInvariant (φ : DoubledSpace E → β) : Prop :=
  ∀ (a : ℝ) (_ha : a ≠ 0) (v : DoubledSpace E), φ (a • v) = φ v

lemma GaugeInvariant.compat {φ : DoubledSpace E → β}
    (hφ : GaugeInvariant (E := E) φ) :
    ∀ {v w : DoubledSpace E}, SameRayDoubled (E := E) v w → φ v = φ w := by
  intro v w hvw
  rcases hvw with ⟨a, ha, rfl⟩
  simpa using (hφ a ha v).symm

/-- A gauge-invariant representative observable descends to projective states. -/
noncomputable def descend
    (φ : DoubledSpace E → β)
    (hφ : GaugeInvariant (E := E) φ) :
    ProjectiveState (E := E) → β :=
  Quotient.lift φ (by
    intro v w hvw
    exact GaugeInvariant.compat (E := E) hφ hvw)

@[simp] lemma descend_projectivize
    (φ : DoubledSpace E → β)
    (hφ : GaugeInvariant (E := E) φ)
    (v : DoubledSpace E) :
    descend (E := E) φ hφ (projectivize (E := E) v) = φ v := rfl

/-- Backward-compatible alias for quotient descent of gauge-invariant observables. -/
noncomputable abbrev liftGaugeInvariant
    (φ : DoubledSpace E → β)
    (hφ : GaugeInvariant (E := E) φ) :
    ProjectiveState (E := E) → β :=
  descend (E := E) φ hφ

@[simp] lemma liftGaugeInvariant_projectivize
    (φ : DoubledSpace E → β)
    (hφ : GaugeInvariant (E := E) φ)
    (v : DoubledSpace E) :
    liftGaugeInvariant (E := E) φ hφ (projectivize (E := E) v) = φ v := rfl

/-- A simple gauge-invariant toy measurement on representatives. -/
noncomputable def occupancy (v : DoubledSpace E) : ℝ := by
  classical
  exact if v = 0 then 0 else 1

lemma smul_eq_zero_iff_of_ne_zero
    (a : ℝ) (ha : a ≠ 0) (v : DoubledSpace E) :
    a • v = 0 ↔ v = 0 := by
  constructor
  · intro hav
    rcases smul_eq_zero.mp hav with hzero | hv
    · exact (ha hzero).elim
    · exact hv
  · intro hv
    simp [hv]

lemma occupancy_gaugeInvariant :
    GaugeInvariant (E := E) (occupancy (E := E)) := by
  classical
  intro a ha v
  by_cases hv : v = 0
  · subst hv
    simp [occupancy]
  · have hav : a • v ≠ 0 := by
      intro hzero
      exact hv ((smul_eq_zero_iff_of_ne_zero (E := E) a ha v).1 hzero)
    simp [occupancy, hv, hav]

/-- The toy measurement descended to projective states via quotient lifting. -/
noncomputable def occupancyOnProjective : ProjectiveState (E := E) → ℝ :=
  liftGaugeInvariant (E := E) (occupancy (E := E)) (occupancy_gaugeInvariant (E := E))

@[simp] lemma occupancyOnProjective_projectivize (v : DoubledSpace E) :
    occupancyOnProjective (E := E) (projectivize (E := E) v) = occupancy (E := E) v := rfl

omit [NormedSpace ℝ E] in
@[simp] lemma occupancy_zero :
    occupancy (E := E) (0 : DoubledSpace E) = 0 := by
  classical
  simp [occupancy]

omit [NormedSpace ℝ E] in
lemma occupancy_of_ne_zero {v : DoubledSpace E} (hv : v ≠ 0) :
    occupancy (E := E) v = 1 := by
  classical
  simp [occupancy, hv]

omit [NormedSpace ℝ E] in
lemma occupancy_eq_zero_iff (v : DoubledSpace E) :
    occupancy (E := E) v = 0 ↔ v = 0 := by
  classical
  by_cases hv : v = 0
  · simp [occupancy, hv]
  · simp [occupancy, hv]

omit [NormedSpace ℝ E] in
lemma occupancy_eq_one_iff (v : DoubledSpace E) :
    occupancy (E := E) v = 1 ↔ v ≠ 0 := by
  classical
  by_cases hv : v = 0
  · simp [occupancy, hv]
  · simp [occupancy, hv]

@[simp] lemma occupancyOnProjective_zero :
    occupancyOnProjective (E := E)
      (projectivize (E := E) (0 : DoubledSpace E)) = 0 := by
  simp [occupancy]

lemma occupancyOnProjective_of_ne_zero (v : DoubledSpace E) (hv : v ≠ 0) :
    occupancyOnProjective (E := E) (projectivize (E := E) v) = 1 := by
  simp [occupancyOnProjective_projectivize, occupancy, hv]

/-- The descended occupancy is a `{0,1}`-valued observable on projective states. -/
lemma occupancyOnProjective_binary (q : ProjectiveState (E := E)) :
    occupancyOnProjective (E := E) q = 0 ∨ occupancyOnProjective (E := E) q = 1 := by
  refine Quotient.inductionOn q ?_
  intro v
  classical
  by_cases hv : v = 0
  · left
    subst hv
    exact occupancyOnProjective_zero (E := E)
  · right
    exact occupancyOnProjective_of_ne_zero (E := E) v hv

end Doubled

end InfoGeometry.Projective
