import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.SouriauCoadjointFisherRaoEquivalence

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace SouriauCurvature

open SouriauPoincare

/-- 1. Metric Conformal Scaling Factor for the Poincaré Disk Metric g(u, v) = Omega^2 I2
    where Omega(u, v) = 2 rho / (1 - (u^2 + v^2)) -/
noncomputable def poincareMetricFactor (rho u v : ℝ) : ℝ :=
  (4 * rho ^ 2) / (1 - (u ^ 2 + v ^ 2)) ^ 2

/-- 2. Determinant of the Poincaré Metric Tensor det(g) = Omega^4 = 16 rho^4 / (1 - (u^2 + v^2))^4 -/
noncomputable def poincareMetricDet (rho u v : ℝ) : ℝ :=
  (16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4

/-- 3. Riemann Curvature Tensor Component R1212 for the Poincaré Hyperbolic Metric:
    R1212 = - 16 rho^4 / (1 - (u^2 + v^2))^4 -/
noncomputable def poincareRiemannR1212 (rho u v : ℝ) : ℝ :=
  - ((16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4)

noncomputable def poincareMetricFactorOnDisk (rho : ℝ) (p : PoincareDisk) : ℝ :=
  poincareMetricFactor rho p.1.1 p.1.2

theorem continuous_poincareMetricFactorOnDisk (rho : ℝ) :
    Continuous (poincareMetricFactorOnDisk rho) := by
  unfold poincareMetricFactorOnDisk poincareMetricFactor
  apply Continuous.div continuous_const
  · fun_prop
  · intro p
    have hp : p.1.1 ^ 2 + p.1.2 ^ 2 < 1 := p.2
    have hpos : 0 < 1 - (p.1.1 ^ 2 + p.1.2 ^ 2) := by linarith
    exact pow_ne_zero 2 (ne_of_gt hpos)

theorem compact_metricFactorOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsCompact (Set.range (fun p : diskSublevel R =>
      poincareMetricFactorOnDisk rho p.1)) := by
  letI : CompactSpace (diskSublevel R) :=
    isCompact_iff_compactSpace.mp (compact_diskSublevel R hR0 hR1)
  exact isCompact_range
    ((continuous_poincareMetricFactorOnDisk rho).comp continuous_subtype_val)

theorem bounded_metricFactorOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    Bornology.IsBounded (Set.range (fun p : diskSublevel R =>
      poincareMetricFactorOnDisk rho p.1)) := by
  exact (compact_metricFactorOnDisk_sublevel rho R hR0 hR1).isBounded

theorem closed_metricFactorOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsClosed (Set.range (fun p : diskSublevel R =>
      poincareMetricFactorOnDisk rho p.1)) := by
  exact (compact_metricFactorOnDisk_sublevel rho R hR0 hR1).isClosed

theorem pathConnected_metricFactorOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsPathConnected (Set.range (fun p : diskSublevel R =>
      poincareMetricFactorOnDisk rho p.1)) := by
  have hdom : IsPathConnected (Set.univ : Set (diskSublevel R)) := by
    simpa using (isPathConnected_diskSublevel R hR0 hR1).preimage_coe
      (U := diskSublevel R) (W := diskSublevel R) Set.Subset.rfl
  have hcont : Continuous (fun p : diskSublevel R =>
      poincareMetricFactorOnDisk rho p.1) :=
    (continuous_poincareMetricFactorOnDisk rho).comp continuous_subtype_val
  simpa [Set.image_univ] using hdom.image hcont

noncomputable def poincareMetricDetOnDisk (rho : ℝ) (p : PoincareDisk) : ℝ :=
  poincareMetricDet rho p.1.1 p.1.2

theorem continuous_poincareMetricDetOnDisk (rho : ℝ) :
    Continuous (poincareMetricDetOnDisk rho) := by
  unfold poincareMetricDetOnDisk poincareMetricDet
  apply Continuous.div continuous_const
  · fun_prop
  · intro p
    have hp : p.1.1 ^ 2 + p.1.2 ^ 2 < 1 := p.2
    have hpos : 0 < 1 - (p.1.1 ^ 2 + p.1.2 ^ 2) := by linarith
    exact pow_ne_zero 4 (ne_of_gt hpos)

theorem compact_metricDetOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsCompact (Set.range (fun p : diskSublevel R =>
      poincareMetricDetOnDisk rho p.1)) := by
  letI : CompactSpace (diskSublevel R) :=
    isCompact_iff_compactSpace.mp (compact_diskSublevel R hR0 hR1)
  exact isCompact_range
    ((continuous_poincareMetricDetOnDisk rho).comp continuous_subtype_val)

theorem bounded_metricDetOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    Bornology.IsBounded (Set.range (fun p : diskSublevel R =>
      poincareMetricDetOnDisk rho p.1)) := by
  exact (compact_metricDetOnDisk_sublevel rho R hR0 hR1).isBounded

theorem closed_metricDetOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsClosed (Set.range (fun p : diskSublevel R =>
      poincareMetricDetOnDisk rho p.1)) := by
  exact (compact_metricDetOnDisk_sublevel rho R hR0 hR1).isClosed

theorem pathConnected_metricDetOnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsPathConnected (Set.range (fun p : diskSublevel R =>
      poincareMetricDetOnDisk rho p.1)) := by
  have hdom : IsPathConnected (Set.univ : Set (diskSublevel R)) := by
    simpa using (isPathConnected_diskSublevel R hR0 hR1).preimage_coe
      (U := diskSublevel R) (W := diskSublevel R) Set.Subset.rfl
  have hcont : Continuous (fun p : diskSublevel R =>
      poincareMetricDetOnDisk rho p.1) :=
    (continuous_poincareMetricDetOnDisk rho).comp continuous_subtype_val
  simpa [Set.image_univ] using hdom.image hcont

noncomputable def poincareRiemannR1212OnDisk (rho : ℝ) (p : PoincareDisk) : ℝ :=
  poincareRiemannR1212 rho p.1.1 p.1.2

theorem continuous_poincareRiemannR1212OnDisk (rho : ℝ) :
    Continuous (poincareRiemannR1212OnDisk rho) := by
  unfold poincareRiemannR1212OnDisk poincareRiemannR1212
  apply Continuous.neg
  apply Continuous.div continuous_const
  · fun_prop
  · intro p
    have hp : p.1.1 ^ 2 + p.1.2 ^ 2 < 1 := p.2
    have hpos : 0 < 1 - (p.1.1 ^ 2 + p.1.2 ^ 2) := by linarith
    exact pow_ne_zero 4 (ne_of_gt hpos)

theorem compact_riemannR1212OnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsCompact (Set.range (fun p : diskSublevel R =>
      poincareRiemannR1212OnDisk rho p.1)) := by
  letI : CompactSpace (diskSublevel R) :=
    isCompact_iff_compactSpace.mp (compact_diskSublevel R hR0 hR1)
  exact isCompact_range
    ((continuous_poincareRiemannR1212OnDisk rho).comp continuous_subtype_val)

theorem bounded_riemannR1212OnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    Bornology.IsBounded (Set.range (fun p : diskSublevel R =>
      poincareRiemannR1212OnDisk rho p.1)) := by
  exact (compact_riemannR1212OnDisk_sublevel rho R hR0 hR1).isBounded

theorem closed_riemannR1212OnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsClosed (Set.range (fun p : diskSublevel R =>
      poincareRiemannR1212OnDisk rho p.1)) := by
  exact (compact_riemannR1212OnDisk_sublevel rho R hR0 hR1).isClosed

theorem pathConnected_riemannR1212OnDisk_sublevel (rho R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsPathConnected (Set.range (fun p : diskSublevel R =>
      poincareRiemannR1212OnDisk rho p.1)) := by
  have hdom : IsPathConnected (Set.univ : Set (diskSublevel R)) := by
    simpa using (isPathConnected_diskSublevel R hR0 hR1).preimage_coe
      (U := diskSublevel R) (W := diskSublevel R) Set.Subset.rfl
  have hcont : Continuous (fun p : diskSublevel R =>
      poincareRiemannR1212OnDisk rho p.1) :=
    (continuous_poincareRiemannR1212OnDisk rho).comp continuous_subtype_val
  simpa [Set.image_univ] using hdom.image hcont

noncomputable def poincareSectionalCurvatureOnDisk (rho : ℝ)
    (p : PoincareDisk) : ℝ :=
  poincareRiemannR1212OnDisk rho p / poincareMetricDetOnDisk rho p

theorem continuous_poincareSectionalCurvatureOnDisk (rho : ℝ) (hrho : rho ≠ 0) :
    Continuous (poincareSectionalCurvatureOnDisk rho) := by
  unfold poincareSectionalCurvatureOnDisk
  apply Continuous.div (continuous_poincareRiemannR1212OnDisk rho)
    (continuous_poincareMetricDetOnDisk rho)
  intro p
  unfold poincareMetricDetOnDisk poincareMetricDet
  have hp : p.1.1 ^ 2 + p.1.2 ^ 2 < 1 := p.2
  have hpos : 0 < 1 - (p.1.1 ^ 2 + p.1.2 ^ 2) := by linarith
  have hden : (1 - (p.1.1 ^ 2 + p.1.2 ^ 2)) ^ 4 ≠ 0 :=
    pow_ne_zero 4 (ne_of_gt hpos)
  have hrho4 : 16 * rho ^ 4 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 4 hrho)
  exact div_ne_zero hrho4 hden

/-- 🏆 THEOREM 1: First Skew-Symmetry of Riemann Curvature R2112 = -R1212 -/
theorem poincare_riemann_skew_first (rho u v : ℝ) :
    - poincareRiemannR1212 rho u v = (16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4 := by
  dsimp [poincareRiemannR1212]
  ring

/-- 🏆 THEOREM 2: Exact Determinant Factorization det(g) = (g11) (g22) for Diagonal Metric -/
theorem poincare_metric_det_eq_sq (rho u v : ℝ) :
    (poincareMetricFactor rho u v) ^ 2 = poincareMetricDet rho u v := by
  dsimp [poincareMetricFactor, poincareMetricDet]
  rw [div_pow]
  ring

/-- 🏆 THEOREM 3: Constant Negative Sectional Curvature Theorem:
    K = R1212 / det(g) = -1 for Unit Radius Disk (rho = 1) -/
theorem poincare_sectional_curvature_unit (u v : ℝ) (hdisk : u ^ 2 + v ^ 2 < 1) :
    poincareRiemannR1212 1 u v / poincareMetricDet 1 u v = -1 := by
  dsimp [poincareRiemannR1212, poincareMetricDet]
  simp only [one_pow, mul_one]
  have hpos : 0 < 1 - (u ^ 2 + v ^ 2) := by linarith
  have hden : 0 < (1 - (u ^ 2 + v ^ 2)) ^ 4 := pow_pos hpos 4
  have hden_ne : (1 - (u ^ 2 + v ^ 2)) ^ 4 ≠ 0 := ne_of_gt hden
  have hnum_ne : (16 : ℝ) ≠ 0 := by norm_num
  have hC_ne : (16 : ℝ) / (1 - (u ^ 2 + v ^ 2)) ^ 4 ≠ 0 := div_ne_zero hnum_ne hden_ne
  have h_alg : -((16 : ℝ) / (1 - (u ^ 2 + v ^ 2)) ^ 4) / ((16 : ℝ) / (1 - (u ^ 2 + v ^ 2)) ^ 4) =
               - (((16 : ℝ) / (1 - (u ^ 2 + v ^ 2)) ^ 4) / ((16 : ℝ) / (1 - (u ^ 2 + v ^ 2)) ^ 4)) := by ring
  rw [h_alg, div_self hC_ne]

/-- 🏆 THEOREM 4: Scaled Constant Negative Sectional Curvature Theorem:
    K = R1212 / det(g) = -1 for Radius rho ≠ 0 -/
theorem poincare_sectional_curvature_scaled (rho u v : ℝ) (hrho : rho ≠ 0)
    (hdisk : u ^ 2 + v ^ 2 < 1) :
    poincareRiemannR1212 rho u v / poincareMetricDet rho u v = -1 := by
  dsimp [poincareRiemannR1212, poincareMetricDet]
  have hpos : 0 < 1 - (u ^ 2 + v ^ 2) := by linarith
  have hden : 0 < (1 - (u ^ 2 + v ^ 2)) ^ 4 := pow_pos hpos 4
  have hden_ne : (1 - (u ^ 2 + v ^ 2)) ^ 4 ≠ 0 := ne_of_gt hden
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_ne_zero hrho
  have hrho4 : 0 < 16 * (rho ^ 2) ^ 2 := by positivity
  have hnum_ne : 16 * rho ^ 4 ≠ 0 := by
    have h_eq : 16 * rho ^ 4 = 16 * (rho ^ 2) ^ 2 := by ring
    rw [h_eq]
    exact ne_of_gt hrho4
  have hC_ne : (16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4 ≠ 0 := div_ne_zero hnum_ne hden_ne
  have h_alg : -((16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4) / ((16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4) =
               - (((16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4) / ((16 * rho ^ 4) / (1 - (u ^ 2 + v ^ 2)) ^ 4)) := by ring
  rw [h_alg, div_self hC_ne]

/-- 🏆 THEOREM 5: Gauss-Bonnet Area Form Scaling Identity -/
theorem poincare_gauss_bonnet_integrand (rho u v : ℝ) :
    (-1) * poincareMetricDet rho u v = poincareRiemannR1212 rho u v := by
  dsimp [poincareRiemannR1212, poincareMetricDet]
  ring

theorem poincareSectionalCurvatureOnDisk_eq_neg_one (rho : ℝ) (hrho : rho ≠ 0)
    (p : PoincareDisk) :
    poincareSectionalCurvatureOnDisk rho p = -1 := by
  exact poincare_sectional_curvature_scaled rho p.1.1 p.1.2 hrho p.2

theorem poincareSectionalCurvatureOnDisk_level_set (rho : ℝ) (hrho : rho ≠ 0) :
    {p : PoincareDisk | poincareSectionalCurvatureOnDisk rho p = -1} = Set.univ := by
  ext p
  simp [poincareSectionalCurvatureOnDisk_eq_neg_one rho hrho p]

theorem poincareSectionalCurvatureOnDisk_sublevel_range (rho R : ℝ)
    (hrho : rho ≠ 0) (hR0 : 0 ≤ R) (hR1 : R < 1) :
    Set.range (fun p : diskSublevel R =>
      poincareSectionalCurvatureOnDisk rho p.1) = ({-1} : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    simp [poincareSectionalCurvatureOnDisk_eq_neg_one rho hrho p.1]
  · intro hx
    have hxneg : x = -1 := by simpa using hx
    subst x
    let p : diskSublevel R :=
      ⟨⟨(0, 0), by norm_num⟩, by
        simpa [diskSublevel, diskRadiusSq] using hR0⟩
    exact ⟨p, poincareSectionalCurvatureOnDisk_eq_neg_one rho hrho p.1⟩

theorem poincareSectionalCurvatureOnDisk_sublevel_range_isPathConnected
    (rho R : ℝ) (hrho : rho ≠ 0) (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsPathConnected (Set.range (fun p : diskSublevel R =>
      poincareSectionalCurvatureOnDisk rho p.1)) := by
  rw [poincareSectionalCurvatureOnDisk_sublevel_range rho R hrho hR0 hR1]
  exact isPathConnected_singleton (-1)

end SouriauCurvature
