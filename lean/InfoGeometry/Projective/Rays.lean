import InfoGeometry.Clifford.Cl11

/-!
# InfoGeometry.Projective.Rays

Projective ray quotient of doubled states by nonzero real scaling.
-/

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cone-projectivization dictionary: vectors represent the same ray
iff they differ by a nonzero real scalar.
This includes the distinguished zero class (vacuum) in the quotient. -/
def SameRayDoubled (v w : DoubledSpace E) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ w = a • v

lemma sameRay_refl {v : DoubledSpace E} : SameRayDoubled v v := by
  refine ⟨1, by norm_num, ?_⟩
  simp

lemma sameRay_symm {v w : DoubledSpace E} :
    SameRayDoubled v w → SameRayDoubled w v := by
  rintro ⟨a, ha, rfl⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  calc
    v = (a⁻¹ * a) • v := by simp [ha]
    _ = a⁻¹ • (a • v) := by simp [smul_smul]

lemma sameRay_trans {u v w : DoubledSpace E} :
    SameRayDoubled u v → SameRayDoubled v w → SameRayDoubled u w := by
  rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  simp [smul_smul, mul_comm]

/-- Setoid for projectivized doubled states (rays). -/
def sameRaySetoid : Setoid (DoubledSpace E) where
  r := SameRayDoubled
  iseqv := ⟨
    by intro x; exact sameRay_refl (E := E),
    by intro x y hxy; exact sameRay_symm (E := E) hxy,
    by intro x y z hxy hyz; exact sameRay_trans (E := E) hxy hyz
  ⟩

/-- Cone-projective states: quotient of doubled states by nonzero real rescaling.
Unlike strict projectivization, this retains a distinguished zero class. -/
def ProjectiveState : Type _ := Quotient (sameRaySetoid (E := E))

/-- Canonical projection from a doubled state to its projective ray class. -/
def projectivize (v : DoubledSpace E) : ProjectiveState (E := E) :=
  Quotient.mk'' v

lemma projectivize_eq_iff {v w : DoubledSpace E} :
    projectivize (E := E) v = projectivize (E := E) w ↔ SameRayDoubled (E := E) v w := by
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

/-- `SameRayDoubled` is exactly the orbit relation for the gauge action by `ℝˣ`. -/
lemma sameRayDoubled_iff_gauge {v w : DoubledSpace E} :
    SameRayDoubled (E := E) v w ↔ ∃ u : Gauge, w = u • v := by
  constructor
  · rintro ⟨a, ha, hwa⟩
    refine ⟨Units.mk0 a ha, ?_⟩
    simpa using hwa
  · rintro ⟨u, hwu⟩
    refine ⟨(↑u : ℝ), Units.ne_zero u, ?_⟩
    simpa using hwu

lemma projectivize_eq_projectivize_smul
    (u : Gauge) (v : DoubledSpace E) :
    projectivize (E := E) v = projectivize (E := E) (u • v) := by
  apply Quotient.sound
  exact (sameRayDoubled_iff_gauge (E := E)).2 ⟨u, rfl⟩

@[simp] lemma projectivize_smul
    (u : Gauge) (v : DoubledSpace E) :
    projectivize (E := E) (u • v) = projectivize (E := E) v := by
  simpa using (projectivize_eq_projectivize_smul (E := E) u v).symm

end KreinClifford
