import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Finset.Lattice.Fold
import InfoGeometry.Canonical.PositiveRayCore

/-!
# Scale-invariant finite positive readouts

This owner keeps the base a projective positive state space.  A raw finite
positive readout is only a representative; ratios and the Hilbert oscillation
are the representative-independent observables.  No spacetime interpretation
is attached to the finite index type.
-/

namespace InfoGeometry.Canonical.ProjectivePositiveReadoutMetric

section

variable {n : ℕ} [NeZero n]

/-- A strictly positive finite readout representative. -/
def PositiveReadout := {h : Fin n → ℝ // ∀ i, 0 < h i}

namespace PositiveReadout

variable (h : PositiveReadout (n := n))

omit [NeZero n] in
@[simp] theorem pos (i : Fin n) : 0 < h.1 i := h.2 i

omit [NeZero n] in
@[simp] theorem ne_zero (i : Fin n) : h.1 i ≠ 0 := ne_of_gt (h.pos i)

end PositiveReadout

/-- The ratio of two coordinates of one representative. -/
noncomputable def coordinateRatio (h : PositiveReadout (n := n)) (i j : Fin n) : ℝ :=
  h.1 i / h.1 j

/-- A ratio of ratios comparing two independently represented readouts. -/
noncomputable def ratioOfRatios (h k : PositiveReadout (n := n)) (i j : Fin n) : ℝ :=
  coordinateRatio h i j / coordinateRatio k i j

theorem ratioOfRatios_eq_crossProduct
    (h k : PositiveReadout (n := n)) (i j : Fin n) :
    ratioOfRatios h k i j = (h.1 i * k.1 j) / (h.1 j * k.1 i) := by
  unfold ratioOfRatios coordinateRatio
  field_simp [h.ne_zero i, h.ne_zero j, k.ne_zero i, k.ne_zero j]

theorem ratioOfRatios_scale_invariant
    (h k : PositiveReadout (n := n)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin n) :
    ratioOfRatios
        ⟨fun t => a * h.1 t, fun t => mul_pos ha (h.pos t)⟩
        ⟨fun t => b * k.1 t, fun t => mul_pos hb (k.pos t)⟩ i j =
      ratioOfRatios h k i j := by
  rw [ratioOfRatios_eq_crossProduct, ratioOfRatios_eq_crossProduct]
  field_simp [h.ne_zero i, h.ne_zero j, k.ne_zero i, k.ne_zero j, ne_of_gt ha,
    ne_of_gt hb]

/-- Logarithmic relative coordinates between two representatives. -/
noncomputable def relativeLog (h k : PositiveReadout (n := n)) (i : Fin n) : ℝ :=
  Real.log (h.1 i / k.1 i)

theorem relativeLog_scale_add
    (h k : PositiveReadout (n := n)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (i : Fin n) :
    relativeLog
        ⟨fun t => a * h.1 t, fun t => mul_pos ha (h.pos t)⟩
        ⟨fun t => b * k.1 t, fun t => mul_pos hb (k.pos t)⟩ i =
      Real.log (a / b) + relativeLog h k i := by
  unfold relativeLog
  change Real.log ((a * h.1 i) / (b * k.1 i)) = _
  have hfactor : (a * h.1 i) / (b * k.1 i) =
      (a / b) * (h.1 i / k.1 i) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, h.ne_zero i, k.ne_zero i]
  rw [hfactor, Real.log_mul (ne_of_gt (div_pos ha hb))
    (ne_of_gt (div_pos (h.pos i) (k.pos i)))]

theorem relativeLog_sub_relativeLog_eq_log_ratioOfRatios
    (h k : PositiveReadout (n := n)) (i j : Fin n) :
    relativeLog h k i - relativeLog h k j =
      Real.log (ratioOfRatios h k i j) := by
  unfold relativeLog ratioOfRatios coordinateRatio
  have hi : 0 < h.1 i / k.1 i := div_pos (h.pos i) (k.pos i)
  have hj : 0 < h.1 j / k.1 j := div_pos (h.pos j) (k.pos j)
  rw [← Real.log_div (ne_of_gt hi) (ne_of_gt hj)]
  congr 1
  field_simp [h.ne_zero i, h.ne_zero j, k.ne_zero i, k.ne_zero j]

theorem relativeLog_compose
    (h k l : PositiveReadout (n := n)) (i : Fin n) :
    relativeLog h l i = relativeLog h k i + relativeLog k l i := by
  unfold relativeLog
  rw [← Real.log_mul (ne_of_gt (div_pos (h.pos i) (k.pos i)))
    (ne_of_gt (div_pos (k.pos i) (l.pos i)))]
  congr 1
  field_simp [h.ne_zero i, k.ne_zero i, l.ne_zero i]

/-- The logarithmic first-order coordinate associated to a raw variation. -/
noncomputable def relativeVariation
    (h : PositiveReadout (n := n)) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  v i / h.1 i

theorem relativeVariation_radial_shift
    (h : PositiveReadout (n := n)) (v : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    relativeVariation h (fun j => v j + c * h.1 j) i =
      relativeVariation h v i + c := by
  unfold relativeVariation
  field_simp [h.ne_zero i]

/-- The differential of a projective coordinate ratio on the positive chart.
It is a genuine linear functional on raw variations. -/
noncomputable def logRatioVariation
    (h : PositiveReadout (n := n)) (i j : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun v => relativeVariation h v i - relativeVariation h v j
    map_add' := by
      intro v w
      simp only [relativeVariation, Pi.add_apply, add_div]
      ring
    map_smul' := by
      intro a v
      simp only [relativeVariation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring }

omit [NeZero n] in
@[simp] theorem logRatioVariation_apply
    (h : PositiveReadout (n := n)) (i j : Fin n) (v : Fin n → ℝ) :
    logRatioVariation h i j v =
      relativeVariation h v i - relativeVariation h v j :=
  rfl

theorem logRatioVariation_radial
    (h : PositiveReadout (n := n)) (i j : Fin n) (c : ℝ) :
    logRatioVariation h i j (fun k => c * h.1 k) = 0 := by
  rw [logRatioVariation_apply]
  simp only [relativeVariation]
  field_simp [h.ne_zero i, h.ne_zero j]
  ring

theorem relativeVariation_difference_radial_invariant
    (h : PositiveReadout (n := n)) (v : Fin n → ℝ) (c : ℝ) (i j : Fin n) :
    relativeVariation h (fun k => v k + c * h.1 k) i -
        relativeVariation h (fun k => v k + c * h.1 k) j =
      relativeVariation h v i - relativeVariation h v j := by
  rw [relativeVariation_radial_shift, relativeVariation_radial_shift]
  ring

private theorem sup_add_const {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (c : ℝ) (f : β → ℝ) :
    s.sup' hs (fun x => c + f x) = c + s.sup' hs f := by
  apply le_antisymm
  · apply Finset.sup'_le hs
    intro x hx
    simpa [add_comm] using add_le_add_left (Finset.le_sup' f hx) c
  · have hle : ∀ x ∈ s, f x ≤ s.sup' hs (fun x => c + f x) - c := by
      intro x hx
      have h := Finset.le_sup' (fun x => c + f x) hx
      linarith
    have := Finset.sup'_le hs f hle
    linarith

private theorem inf_add_const {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (c : ℝ) (f : β → ℝ) :
    s.inf' hs (fun x => c + f x) = c + s.inf' hs f := by
  apply le_antisymm
  · have hle : ∀ x ∈ s, s.inf' hs (fun x => c + f x) - c ≤ f x := by
      intro x hx
      have h := Finset.inf'_le (fun x => c + f x) hx
      linarith
    have := Finset.le_inf' hs f hle
    linarith
  · apply Finset.le_inf' hs
    intro x hx
    simpa [add_comm] using add_le_add_left (Finset.inf'_le f hx) c

private theorem oscillation_add_le {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (f g : β → ℝ) :
    (s.sup' hs (fun x => f x + g x) - s.inf' hs (fun x => f x + g x)) ≤
      (s.sup' hs f - s.inf' hs f) + (s.sup' hs g - s.inf' hs g) := by
  have hupper : s.sup' hs (fun x => f x + g x) ≤
      s.sup' hs f + s.sup' hs g := by
    apply Finset.sup'_le hs
    intro x hx
    exact add_le_add (Finset.le_sup' f hx) (Finset.le_sup' g hx)
  have hlower : s.inf' hs f + s.inf' hs g ≤
      s.inf' hs (fun x => f x + g x) := by
    apply Finset.le_inf' hs
    intro x hx
    exact add_le_add (Finset.inf'_le f hx) (Finset.inf'_le g hx)
  linarith

private theorem oscillation_neg {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (f : β → ℝ) :
    s.sup' hs (fun x => -f x) - s.inf' hs (fun x => -f x) =
      s.sup' hs f - s.inf' hs f := by
  have hsup : s.sup' hs (fun x => -f x) = -(s.inf' hs f) := by
    apply le_antisymm
    · apply Finset.sup'_le hs
      intro x hx
      exact neg_le_neg (Finset.inf'_le f hx)
    · obtain ⟨x, hx, hxf⟩ := Finset.exists_mem_eq_inf' hs f
      rw [hxf]
      exact Finset.le_sup' (fun x => -f x) hx
  have hinf : s.inf' hs (fun x => -f x) = -(s.sup' hs f) := by
    apply le_antisymm
    · obtain ⟨x, hx, hxf⟩ := Finset.exists_mem_eq_sup' hs f
      rw [hxf]
      exact Finset.inf'_le (fun x => -f x) hx
    · apply Finset.le_inf' hs
      intro x hx
      exact neg_le_neg (Finset.le_sup' f hx)
  rw [hsup, hinf]
  ring

/-- The finite Hilbert oscillation of the logarithmic relative readout. -/
noncomputable def hilbertOscillation (h k : PositiveReadout (n := n)) : ℝ :=
  (Finset.univ.sup' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
      (relativeLog h k)) -
    (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
      (relativeLog h k))

theorem hilbertOscillation_nonneg (h k : PositiveReadout (n := n)) :
    0 ≤ hilbertOscillation h k := by
  unfold hilbertOscillation
  have hmem : (0 : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  apply sub_nonneg.mpr
  exact le_trans (Finset.inf'_le _ hmem) (Finset.le_sup' _ hmem)

theorem hilbertOscillation_scale_invariant
    (h k : PositiveReadout (n := n)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    hilbertOscillation
        ⟨fun t => a * h.1 t, fun t => mul_pos ha (h.pos t)⟩
        ⟨fun t => b * k.1 t, fun t => mul_pos hb (k.pos t)⟩ =
      hilbertOscillation h k := by
  unfold hilbertOscillation
  simp_rw [relativeLog_scale_add h k a b ha hb]
  have hs := sup_add_const (s := (Finset.univ : Finset (Fin n)))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
    (Real.log (a / b)) (relativeLog h k)
  have hi := inf_add_const (s := (Finset.univ : Finset (Fin n)))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
    (Real.log (a / b)) (relativeLog h k)
  rw [hs, hi]
  ring

theorem hilbertOscillation_triangle
    (h k l : PositiveReadout (n := n)) :
    hilbertOscillation h l ≤ hilbertOscillation h k + hilbertOscillation k l := by
  have hcompose : relativeLog h l =
      fun i => relativeLog h k i + relativeLog k l i := by
    funext i
    exact relativeLog_compose h k l i
  unfold hilbertOscillation
  rw [hcompose]
  exact oscillation_add_le (s := (Finset.univ : Finset (Fin n)))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
    (relativeLog h k) (relativeLog k l)

theorem hilbertOscillation_swap (h k : PositiveReadout (n := n)) :
    hilbertOscillation k h = hilbertOscillation h k := by
  have hlog (i : Fin n) : relativeLog k h i = -relativeLog h k i := by
    unfold relativeLog
    rw [Real.log_div (ne_of_gt (k.pos i)) (ne_of_gt (h.pos i)),
      Real.log_div (ne_of_gt (h.pos i)) (ne_of_gt (k.pos i))]
    ring
  unfold hilbertOscillation
  simp_rw [hlog]
  exact oscillation_neg (Finset.univ : Finset (Fin n))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
    (relativeLog h k)

theorem hilbertOscillation_eq_zero_iff_relativeLog_constant
    (h k : PositiveReadout (n := n)) :
    hilbertOscillation h k = 0 ↔
      ∃ c : ℝ, ∀ i : Fin n, relativeLog h k i = c := by
  constructor
  · intro hz
    let s := (Finset.univ : Finset (Fin n))
    let hs : s.Nonempty := Finset.univ_nonempty
    refine ⟨s.sup' hs (relativeLog h k), ?_⟩
    intro i
    have hupper := Finset.le_sup' (relativeLog h k) (Finset.mem_univ i)
    have hlower := Finset.inf'_le (relativeLog h k) (Finset.mem_univ i)
    have hzero : s.sup' hs (relativeLog h k) -
        s.inf' hs (relativeLog h k) = 0 := by
      simpa [hilbertOscillation, s, hs] using hz
    linarith
  · rintro ⟨c, hc⟩
    unfold hilbertOscillation
    simp_rw [hc]
    simp

theorem hilbertOscillation_eq_zero_iff_ratio_constant
    (h k : PositiveReadout (n := n)) :
    hilbertOscillation h k = 0 ↔
      ∀ i j : Fin n, h.1 i / k.1 i = h.1 j / k.1 j := by
  constructor
  · intro hz i j
    rcases (hilbertOscillation_eq_zero_iff_relativeLog_constant h k).mp hz with
      ⟨c, hc⟩
    have hlog : relativeLog h k i = relativeLog h k j := by rw [hc, hc]
    have hpos_i : 0 < h.1 i / k.1 i := div_pos (h.pos i) (k.pos i)
    have hpos_j : 0 < h.1 j / k.1 j := div_pos (h.pos j) (k.pos j)
    have hexp := congrArg Real.exp hlog
    simpa [relativeLog, Real.exp_log hpos_i, Real.exp_log hpos_j] using hexp
  · intro hratio
    apply (hilbertOscillation_eq_zero_iff_relativeLog_constant h k).mpr
    refine ⟨relativeLog h k 0, ?_⟩
    intro i
    have hratio' := hratio i 0
    have hpos_i : 0 < h.1 i / k.1 i := div_pos (h.pos i) (k.pos i)
    have hpos_0 : 0 < h.1 0 / k.1 0 := div_pos (h.pos 0) (k.pos 0)
    unfold relativeLog
    exact congrArg Real.log hratio'

end

/-! ### Native projective-ray readouts

The finite representative calculations above are useful for the cone chart,
but the state-space API must use the repository's quotient carrier.  The
following definitions read the canonical representative supplied by
`PositiveRayCore.gaugeSection`; no second projective state space is introduced.
-/

namespace PositiveRay

open InfoGeometry.Canonical.PositiveRayCore

variable {n : ℕ} [NeZero n]

abbrev State (n : ℕ) [NeZero n] := PositiveRay (Fin n)

noncomputable def coordinate (q : State n) (i : Fin n) : ℝ :=
  gaugeSection (α := Fin n) q i

@[simp] theorem coordinate_pos (q : State n) (i : Fin n) :
    0 < coordinate q i := by
  exact chartCoordinates_pos q i

noncomputable def ratio (q : State n) (i j : Fin n) : ℝ :=
  coordinate q i / coordinate q j

@[simp] theorem ratio_scale_left
    (μ : InfoGeometry.PositiveMeasure (Fin n) ℝ)
    (c : ℝ) (hc : 0 < c) (i j : Fin n) :
    ratio (Quotient.mk _
      (InfoGeometry.PositiveMeasure.scale c hc μ)) i j =
      ratio (Quotient.mk _ μ) i j := by
  have hq :
      (Quotient.mk _ (InfoGeometry.PositiveMeasure.scale c hc μ) : State n) =
        Quotient.mk _ μ := by
    refine Quotient.sound ?_
    refine ⟨⟨c⁻¹, inv_pos.mpr hc⟩, ?_⟩
    ext k
    change c⁻¹ * (c * μ k) = μ k
    field_simp [hc.ne']
  rw [hq]

noncomputable def ratioOfRays (q r : State n) (i j : Fin n) : ℝ :=
  ratio q i j / ratio r i j

theorem ratioOfRays_eq_coordinate_crossProduct
    (q r : State n) (i j : Fin n) :
    ratioOfRays q r i j =
      (coordinate q i * coordinate r j) /
        (coordinate q j * coordinate r i) := by
  unfold ratioOfRays ratio
  field_simp [ne_of_gt (coordinate_pos q i),
    ne_of_gt (coordinate_pos q j), ne_of_gt (coordinate_pos r i),
    ne_of_gt (coordinate_pos r j)]

@[simp] theorem ratioOfRays_scale_left
    (μ ν : InfoGeometry.PositiveMeasure (Fin n) ℝ)
    (c : ℝ) (hc : 0 < c) (i j : Fin n) :
    ratioOfRays
      (Quotient.mk _ (InfoGeometry.PositiveMeasure.scale c hc μ))
      (Quotient.mk _ ν) i j =
      ratioOfRays (Quotient.mk _ μ) (Quotient.mk _ ν) i j := by
  have hq :
      (Quotient.mk _ (InfoGeometry.PositiveMeasure.scale c hc μ) : State n) =
        Quotient.mk _ μ := by
    refine Quotient.sound ?_
    refine ⟨⟨c⁻¹, inv_pos.mpr hc⟩, ?_⟩
    ext k
    change c⁻¹ * (c * μ k) = μ k
    field_simp [hc.ne']
  rw [hq]

@[simp] theorem ratioOfRays_scale_right
    (μ ν : InfoGeometry.PositiveMeasure (Fin n) ℝ)
    (c : ℝ) (hc : 0 < c) (i j : Fin n) :
    ratioOfRays (Quotient.mk _ μ)
      (Quotient.mk _ (InfoGeometry.PositiveMeasure.scale c hc ν)) i j =
      ratioOfRays (Quotient.mk _ μ) (Quotient.mk _ ν) i j := by
  have hq :
      (Quotient.mk _ (InfoGeometry.PositiveMeasure.scale c hc ν) : State n) =
        Quotient.mk _ ν := by
    refine Quotient.sound ?_
    refine ⟨⟨c⁻¹, inv_pos.mpr hc⟩, ?_⟩
    ext k
    change c⁻¹ * (c * ν k) = ν k
    field_simp [hc.ne']
  rw [hq]

noncomputable def rayOscillation (q r : State n) : ℝ :=
  ProjectivePositiveReadoutMetric.hilbertOscillation
    ⟨coordinate q, coordinate_pos q⟩
    ⟨coordinate r, coordinate_pos r⟩

theorem rayOscillation_nonneg (q r : State n) :
    0 ≤ rayOscillation q r := by
  exact ProjectivePositiveReadoutMetric.hilbertOscillation_nonneg
    ⟨coordinate q, coordinate_pos q⟩
    ⟨coordinate r, coordinate_pos r⟩

theorem rayOscillation_swap (q r : State n) :
    rayOscillation r q = rayOscillation q r := by
  exact (ProjectivePositiveReadoutMetric.hilbertOscillation_swap
    ⟨coordinate r, coordinate_pos r⟩
    ⟨coordinate q, coordinate_pos q⟩).symm

theorem rayOscillation_triangle (q r s : State n) :
    rayOscillation q s ≤ rayOscillation q r + rayOscillation r s := by
  exact ProjectivePositiveReadoutMetric.hilbertOscillation_triangle
    ⟨coordinate q, coordinate_pos q⟩
    ⟨coordinate r, coordinate_pos r⟩
    ⟨coordinate s, coordinate_pos s⟩

theorem rayOscillation_eq_zero_iff_coordinate_ratio_constant
    (q r : State n) :
    rayOscillation q r = 0 ↔
      ∀ i j : Fin n,
        coordinate q i / coordinate r i =
          coordinate q j / coordinate r j := by
  simpa [rayOscillation] using
    (ProjectivePositiveReadoutMetric.hilbertOscillation_eq_zero_iff_ratio_constant
      ⟨coordinate q, coordinate_pos q⟩
      ⟨coordinate r, coordinate_pos r⟩)

/-! ### Tangent quotient by the radial gauge direction -/

noncomputable def radialSubmodule (q : State n) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ({coordinate q} : Set (Fin n → ℝ))

abbrev Tangent (q : State n) := (Fin n → ℝ) ⧸ radialSubmodule q

private theorem logRatioVariation_radial_mem_ker
    (q : State n) (i j : Fin n) :
    radialSubmodule q ≤
      LinearMap.ker (ProjectivePositiveReadoutMetric.logRatioVariation
        ⟨coordinate q, coordinate_pos q⟩ i j) := by
  refine Submodule.span_le.2 ?_
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst v
  exact LinearMap.mem_ker.mpr
    (by
      simpa [one_smul] using
        (ProjectivePositiveReadoutMetric.logRatioVariation_radial
          ⟨coordinate q, coordinate_pos q⟩ i j 1))

noncomputable def rayLogRatioVariation
    (q : State n) (i j : Fin n) : Tangent q →ₗ[ℝ] ℝ :=
  Submodule.liftQ (radialSubmodule q)
    (ProjectivePositiveReadoutMetric.logRatioVariation
      ⟨coordinate q, coordinate_pos q⟩ i j)
    (logRatioVariation_radial_mem_ker q i j)

@[simp] theorem rayLogRatioVariation_apply
    (q : State n) (i j : Fin n) (v : Fin n → ℝ) :
    rayLogRatioVariation q i j ((radialSubmodule q).mkQ v) =
      ProjectivePositiveReadoutMetric.logRatioVariation
        ⟨coordinate q, coordinate_pos q⟩ i j v := by
  exact Submodule.liftQ_apply (radialSubmodule q)
    (ProjectivePositiveReadoutMetric.logRatioVariation
      ⟨coordinate q, coordinate_pos q⟩ i j) v

theorem radial_variation_is_zero_in_tangent
    (q : State n) (c : ℝ) :
    (radialSubmodule q).mkQ (c • coordinate q) = 0 := by
  change Submodule.Quotient.mk (c • coordinate q) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem (radialSubmodule q) c
    (Submodule.subset_span (Set.mem_singleton (coordinate q)))

end PositiveRay

end InfoGeometry.Canonical.ProjectivePositiveReadoutMetric
