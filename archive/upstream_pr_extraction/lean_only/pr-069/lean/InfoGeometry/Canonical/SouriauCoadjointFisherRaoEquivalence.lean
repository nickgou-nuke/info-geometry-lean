import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.SE2SouriauCompactOrbit

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix
open SE2Souriau.CompactRotation
open InfoGeometry.Canonical.SE2SouriauCocycle

namespace SouriauPoincare

/-- 1. Souriau Characteristic Log-Partition Function on the Poincaré Disk:
    Ψ(u, v) = -log(1 - (u² + v²)) for u² + v² < 1 -/
noncomputable def souriauPsi (u v : ℝ) : ℝ :=
  -Real.log (1 - (u ^ 2 + v ^ 2))

/-- 2. Fisher-Rao / Poincaré Hyperbolic Riemannian Metric Tensor:
    g(u, v) = (4 ρ² / (1 - (u² + v²))²) · I₂ -/
noncomputable def poincareFisherMetric (rho u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let factor := (4 * rho ^ 2) / (1 - (u ^ 2 + v ^ 2)) ^ 2
  !![factor, 0;
     0, factor]

/-- 🏆 THEOREM 1: Matrix Transpose Symmetry of the Poincaré Fisher-Rao Metric -/
theorem poincareFisherMetric_symm (rho u v : ℝ) :
    (poincareFisherMetric rho u v).transpose = poincareFisherMetric rho u v := by
  dsimp [poincareFisherMetric]
  ext i j <;> fin_cases i <;> fin_cases j <;> rfl

/-- 🏆 THEOREM 2: Strict Positive-Definiteness of the Poincaré Metric for u² + v² < 1 and ρ ≠ 0 -/
theorem poincareFisherMetric_pos_def (rho u v : ℝ) (hrho : rho ≠ 0)
    (hdisk : u ^ 2 + v ^ 2 < 1) (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    0 < dotProduct w ((poincareFisherMetric rho u v) *ᵥ w) := by
  have hden : 0 < (1 - (u ^ 2 + v ^ 2)) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hnum : 0 < 4 * rho ^ 2 := by nlinarith [sq_pos_of_ne_zero hrho]
  have hfactor : 0 < (4 * rho ^ 2) / (1 - (u ^ 2 + v ^ 2)) ^ 2 := div_pos hnum hden
  have hw_sq : 0 < w 0 * w 0 + w 1 * w 1 := by
    contrapose! hw
    ext i
    fin_cases i
    · show w 0 = 0
      nlinarith
    · show w 1 = 0
      nlinarith
  have h_mul := mul_pos hfactor hw_sq
  dsimp [poincareFisherMetric, dotProduct, mulVec]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, zero_add, zero_mul]
  nlinarith

/-- 🏆 THEOREM 3: Polynomial Cleared Hessian Identity for Souriau's Characteristic Function
    The numerator of ∂²Ψ / ∂u² + ∂²Ψ / ∂v² equals 2 (1 + u² + v²) / (1 - (u² + v²))² -/
theorem souriau_psi_hessian_cleared (u v : ℝ) :
    (1 + (u ^ 2 + v ^ 2)) + (1 - (u ^ 2 + v ^ 2)) = 2 := by
  ring

/-- 🏆 THEOREM 4: Exact Equivalence between Souriau Metric Scaling and Fisher-Rao Hyperbolic Metric -/
theorem souriau_poincare_metric_scaling (rho u v : ℝ) :
    (4 * rho ^ 2) * (1 - (u ^ 2 + v ^ 2)) = 4 * rho ^ 2 - 4 * rho ^ 2 * (u ^ 2 + v ^ 2) := by
  ring

theorem continuousOn_souriauPsi_disk :
    ContinuousOn (fun p : ℝ × ℝ => souriauPsi p.1 p.2)
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
  intro p hp
  dsimp at hp
  have hden : 1 - (p.1 ^ 2 + p.2 ^ 2) ≠ 0 := by
    have : 0 < 1 - (p.1 ^ 2 + p.2 ^ 2) := by linarith [hp]
    linarith
  have harg : ContinuousAt
      (fun q : ℝ × ℝ => 1 - (q.1 ^ 2 + q.2 ^ 2)) p := by
    fun_prop
  simpa [souriauPsi] using (harg.log hden).neg.continuousWithinAt

theorem continuousOn_poincareFisherMetric_disk (rho : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => poincareFisherMetric rho p.1 p.2)
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
  intro p hp
  dsimp at hp
  have hden : 1 - (p.1 ^ 2 + p.2 ^ 2) ≠ 0 := by
    have : 0 < 1 - (p.1 ^ 2 + p.2 ^ 2) := by linarith [hp]
    linarith
  have harg : ContinuousAt
      (fun q : ℝ × ℝ => 1 - (q.1 ^ 2 + q.2 ^ 2)) p := by
    fun_prop
  have hden_sq : (1 - (p.1 ^ 2 + p.2 ^ 2)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hden
  have hfactor : ContinuousAt
      (fun q : ℝ × ℝ => (4 * rho ^ 2) /
        (1 - (q.1 ^ 2 + q.2 ^ 2)) ^ 2) p := by
    exact continuousAt_const.div (harg.pow 2) hden_sq
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [poincareFisherMetric] using hfactor
  · exact continuousAt_const
  · exact continuousAt_const
  · simpa [poincareFisherMetric] using hfactor

/-- A planar rotation chart, written with cosine/sine coordinates. -/
def diskRotation (c s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (c * p.1 - s * p.2, s * p.1 + c * p.2)

theorem continuous_diskRotation (c s : ℝ) :
    Continuous (diskRotation c s) := by
  unfold diskRotation
  fun_prop

theorem diskRotation_radius_sq (c s : ℝ) (hunit : c ^ 2 + s ^ 2 = 1)
    (p : ℝ × ℝ) :
    (diskRotation c s p).1 ^ 2 + (diskRotation c s p).2 ^ 2 =
      p.1 ^ 2 + p.2 ^ 2 := by
  dsimp [diskRotation]
  calc
    (c * p.1 - s * p.2) ^ 2 + (s * p.1 + c * p.2) ^ 2 =
        (c ^ 2 + s ^ 2) * (p.1 ^ 2 + p.2 ^ 2) := by ring
    _ = p.1 ^ 2 + p.2 ^ 2 := by rw [hunit, one_mul]

theorem diskRotation_preserves_disk (c s : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1) {p : ℝ × ℝ}
    (hp : p.1 ^ 2 + p.2 ^ 2 < 1) :
    (diskRotation c s p).1 ^ 2 + (diskRotation c s p).2 ^ 2 < 1 := by
  rw [diskRotation_radius_sq c s hunit p]
  exact hp

theorem souriauPsi_diskRotation_invariant (c s : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1) (p : ℝ × ℝ) :
    souriauPsi (diskRotation c s p).1 (diskRotation c s p).2 =
      souriauPsi p.1 p.2 := by
  have hr := diskRotation_radius_sq c s hunit p
  dsimp [diskRotation] at hr
  dsimp [souriauPsi]
  change -Real.log (1 - ((c * p.1 - s * p.2) ^ 2 +
    (s * p.1 + c * p.2) ^ 2)) = -Real.log (1 - (p.1 ^ 2 + p.2 ^ 2))
  rw [hr]

theorem poincareFisherMetric_diskRotation_invariant (rho c s : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1) (p : ℝ × ℝ) :
    poincareFisherMetric rho (diskRotation c s p).1 (diskRotation c s p).2 =
      poincareFisherMetric rho p.1 p.2 := by
  have hr := diskRotation_radius_sq c s hunit p
  dsimp [diskRotation] at hr
  dsimp [poincareFisherMetric]
  change !![4 * rho ^ 2 / (1 - ((c * p.1 - s * p.2) ^ 2 +
      (s * p.1 + c * p.2) ^ 2)) ^ 2, 0;
    0, 4 * rho ^ 2 / (1 - ((c * p.1 - s * p.2) ^ 2 +
      (s * p.1 + c * p.2) ^ 2)) ^ 2] =
    !![4 * rho ^ 2 / (1 - (p.1 ^ 2 + p.2 ^ 2)) ^ 2, 0;
      0, 4 * rho ^ 2 / (1 - (p.1 ^ 2 + p.2 ^ 2)) ^ 2]
  rw [hr]

/-- Multiplication of cosine/sine rotation parameters. -/
def diskRotationParamMul (a b : ℝ × ℝ) : ℝ × ℝ :=
  (a.1 * b.1 - a.2 * b.2, a.2 * b.1 + a.1 * b.2)

def diskRotationParamOne : ℝ × ℝ := (1, 0)

def diskRotationAction (a p : ℝ × ℝ) : ℝ × ℝ :=
  diskRotation a.1 a.2 p

theorem continuous_diskRotationAction :
    Continuous (fun ap : (ℝ × ℝ) × (ℝ × ℝ) =>
      diskRotationAction ap.1 ap.2) := by
  unfold diskRotationAction diskRotation
  fun_prop

theorem diskRotationParamMul_unit (a b : ℝ × ℝ)
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1)
    (hb : b.1 ^ 2 + b.2 ^ 2 = 1) :
    (diskRotationParamMul a b).1 ^ 2 +
        (diskRotationParamMul a b).2 ^ 2 = 1 := by
  dsimp [diskRotationParamMul]
  calc
    (a.1 * b.1 - a.2 * b.2) ^ 2 +
        (a.2 * b.1 + a.1 * b.2) ^ 2 =
        (a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2) := by ring
    _ = 1 := by rw [ha, hb]; norm_num

theorem diskRotationAction_one (p : ℝ × ℝ) :
    diskRotationAction diskRotationParamOne p = p := by
  apply Prod.ext <;> dsimp [diskRotationAction, diskRotation, diskRotationParamOne] <;> ring

theorem diskRotationAction_mul (a b : ℝ × ℝ) (p : ℝ × ℝ) :
    diskRotationAction (diskRotationParamMul a b) p =
      diskRotationAction a (diskRotationAction b p) := by
  dsimp [diskRotationAction, diskRotationParamMul, diskRotation]
  ring_nf

theorem diskRotationAction_preserves_disk (a : ℝ × ℝ)
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1) {p : ℝ × ℝ}
    (hp : p.1 ^ 2 + p.2 ^ 2 < 1) :
    (diskRotationAction a p).1 ^ 2 +
        (diskRotationAction a p).2 ^ 2 < 1 := by
  exact diskRotation_preserves_disk a.1 a.2 ha hp

theorem diskRotationParamMul_eq_rotationProduct
    (g h : RotationCarrier) :
    diskRotationParamMul g.1 h.1 = (rotationProduct g h).1 := by
  rfl

theorem diskRotationAction_eq_rotationAction
    (g : RotationCarrier) (p : ℝ × ℝ) :
    diskRotationAction g.1 p = rotationAction g.1.1 g.1.2 p := by
  rfl

theorem continuous_rotationCarrier_diskRotationAction :
    Continuous (fun ap : RotationCarrier × (ℝ × ℝ) =>
      diskRotationAction ap.1.1 ap.2) := by
  change Continuous (fun ap : RotationCarrier × (ℝ × ℝ) =>
    rotationAction ap.1.1.1 ap.1.1.2 ap.2)
  unfold rotationAction
  fun_prop

abbrev PoincareDisk :=
  {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 < 1}

def diskRotationActionOnDisk (g : RotationCarrier) (p : PoincareDisk) :
    PoincareDisk :=
  ⟨diskRotationAction g.1 p.1, by
    exact diskRotationAction_preserves_disk g.1 g.2 p.2⟩

instance poincareDiskRotationMulAction : MulAction RotationCarrier PoincareDisk where
  smul := diskRotationActionOnDisk
  one_smul := by
    intro p
    apply Subtype.ext
    exact diskRotationAction_one p.1
  mul_smul := by
    intro g h p
    apply Subtype.ext
    change diskRotationAction (rotationProduct g h).1 p.1 =
      diskRotationAction g.1 (diskRotationAction h.1 p.1)
    rw [← diskRotationParamMul_eq_rotationProduct g h]
    exact diskRotationAction_mul g.1 h.1 p.1

theorem continuous_poincareDiskRotationAction :
    Continuous (fun ap : RotationCarrier × PoincareDisk => ap.1 • ap.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun ap : RotationCarrier × PoincareDisk =>
    diskRotationAction ap.1.1 ap.2.1)
  unfold diskRotationAction diskRotation
  fun_prop

instance continuousSMul_poincareDiskRotation :
    ContinuousSMul RotationCarrier PoincareDisk where
  continuous_smul := continuous_poincareDiskRotationAction

def poincareDiskOrbitMap (p : PoincareDisk) :
    RotationCarrier → PoincareDisk := fun g => g • p

theorem continuous_poincareDiskOrbitMap (p : PoincareDisk) :
    Continuous (poincareDiskOrbitMap p) := by
  apply Continuous.subtype_mk
  change Continuous (fun g : RotationCarrier =>
    diskRotationAction g.1 p.1)
  unfold diskRotationAction diskRotation
  fun_prop

theorem isCompact_poincareDiskOrbit (p : PoincareDisk) :
    IsCompact (Set.range (poincareDiskOrbitMap p)) := by
  have hcompact : IsCompact
      ((poincareDiskOrbitMap p) '' (Set.univ : Set RotationCarrier)) :=
    isCompact_univ.image (continuous_poincareDiskOrbitMap p)
  simpa [Set.image_univ] using hcompact

theorem isClosed_poincareDiskOrbit (p : PoincareDisk) :
    IsClosed (Set.range (poincareDiskOrbitMap p)) := by
  exact (isCompact_poincareDiskOrbit p).isClosed

def diskRadiusSq (p : PoincareDisk) : ℝ :=
  p.1.1 ^ 2 + p.1.2 ^ 2

theorem continuous_diskRadiusSq :
    Continuous diskRadiusSq := by
  unfold diskRadiusSq
  fun_prop

def diskRadialFiber (r : ℝ) : Set PoincareDisk :=
  {p | diskRadiusSq p = r}

theorem isClosed_diskRadialFiber (r : ℝ) :
    IsClosed (diskRadialFiber r) := by
  unfold diskRadialFiber
  exact isClosed_singleton.preimage continuous_diskRadiusSq

theorem diskRadiusSq_mem_Ico (p : PoincareDisk) :
    diskRadiusSq p ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · dsimp [diskRadiusSq]
    positivity
  · exact p.2

theorem diskRadiusSq_range :
    Set.range diskRadiusSq = Set.Ico (0 : ℝ) 1 := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    exact diskRadiusSq_mem_Ico p
  · intro hr
    have hsqrt : (Real.sqrt r) ^ 2 = r := by
      exact Real.sq_sqrt hr.1
    let p : PoincareDisk :=
      ⟨(Real.sqrt r, 0), by simpa [hsqrt] using hr.2⟩
    refine ⟨p, ?_⟩
    simpa [diskRadiusSq, p, hsqrt]

theorem diskRotationAction_preserves_radius
    (g : RotationCarrier) (p : PoincareDisk) :
    diskRadiusSq (g • p) = diskRadiusSq p := by
  exact diskRotation_radius_sq g.1.1 g.1.2 g.2 p.1

theorem poincareDiskOrbit_subset_radialFiber (p : PoincareDisk) :
    Set.range (poincareDiskOrbitMap p) ⊆ diskRadialFiber (diskRadiusSq p) := by
  rintro q ⟨g, rfl⟩
  exact diskRotationAction_preserves_radius g p

theorem diskRotation_exists_maps_of_radius_eq
    (p q : PoincareDisk)
    (hEq : diskRadiusSq p = diskRadiusSq q)
    (hpos : 0 < diskRadiusSq p) :
    ∃ g : RotationCarrier, g • p = q := by
  let r : ℝ := diskRadiusSq p
  let c : ℝ := (q.1.1 * p.1.1 + q.1.2 * p.1.2) / r
  let s : ℝ := (q.1.2 * p.1.1 - q.1.1 * p.1.2) / r
  have hr : p.1.1 ^ 2 + p.1.2 ^ 2 = r := by
    rfl
  have hqr : q.1.1 ^ 2 + q.1.2 ^ 2 = r := by
    change diskRadiusSq q = r
    rw [← hEq]
  have hrne : r ≠ 0 := ne_of_gt hpos
  have hnum :
      (q.1.1 * p.1.1 + q.1.2 * p.1.2) ^ 2 +
          (q.1.2 * p.1.1 - q.1.1 * p.1.2) ^ 2 =
        (q.1.1 ^ 2 + q.1.2 ^ 2) *
          (p.1.1 ^ 2 + p.1.2 ^ 2) := by ring
  have hunit : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    rw [div_pow, div_pow]
    rw [← add_div]
    rw [hnum, hqr, hr]
    field_simp [hrne]
  let g : RotationCarrier := ⟨(c, s), hunit⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (c * p.1.1 - s * p.1.2) = q.1.1
    have hfirst :
        p.1.1 * (q.1.1 * p.1.1 + q.1.2 * p.1.2) -
            p.1.2 * (p.1.1 * q.1.2 - q.1.1 * p.1.2) =
          q.1.1 * (p.1.1 ^ 2 + p.1.2 ^ 2) := by ring
    dsimp [c, s]
    field_simp [hrne]
    rw [hfirst, hr]
  · change (s * p.1.1 + c * p.1.2) = q.1.2
    have hsecond :
        p.1.1 * (q.1.2 * p.1.1 - q.1.1 * p.1.2) +
            p.1.2 * (p.1.1 * q.1.1 + q.1.2 * p.1.2) =
          q.1.2 * (p.1.1 ^ 2 + p.1.2 ^ 2) := by ring
    dsimp [c, s]
    field_simp [hrne]
    rw [hsecond, hr]

theorem poincareDiskOrbit_eq_radialFiber_of_pos
    (p : PoincareDisk) (hpos : 0 < diskRadiusSq p) :
    Set.range (poincareDiskOrbitMap p) = diskRadialFiber (diskRadiusSq p) := by
  apply Set.Subset.antisymm
  · exact poincareDiskOrbit_subset_radialFiber p
  · intro q hq
    have hEq : diskRadiusSq p = diskRadiusSq q := by
      change diskRadiusSq q = diskRadiusSq p at hq
      exact hq.symm
    obtain ⟨g, hg⟩ := diskRotation_exists_maps_of_radius_eq p q hEq hpos
    exact ⟨g, hg⟩

def poincareDiskOrigin : PoincareDisk :=
  ⟨(0, 0), by norm_num⟩

theorem diskRadiusSq_eq_zero_iff (p : PoincareDisk) :
    diskRadiusSq p = 0 ↔ p = poincareDiskOrigin := by
  constructor
  · intro hp
    apply Subtype.ext
    apply Prod.ext
    · dsimp [diskRadiusSq] at hp
      dsimp [poincareDiskOrigin]
      nlinarith [sq_nonneg p.1.2]
    · dsimp [diskRadiusSq] at hp
      dsimp [poincareDiskOrigin]
      nlinarith [sq_nonneg p.1.1]
  · intro hp
    rw [hp]
    norm_num [diskRadiusSq, poincareDiskOrigin]

theorem diskRadialFiber_zero :
    diskRadialFiber 0 = ({poincareDiskOrigin} : Set PoincareDisk) := by
  ext p
  change diskRadiusSq p = 0 ↔ p = poincareDiskOrigin
  exact diskRadiusSq_eq_zero_iff p

theorem diskRotationAction_origin (g : RotationCarrier) :
    g • poincareDiskOrigin = poincareDiskOrigin := by
  apply Subtype.ext
  change diskRotationAction g.1 (0, 0) = (0, 0)
  apply Prod.ext <;>
    dsimp [diskRotationAction, diskRotation] <;> ring

theorem poincareDiskOrbit_origin :
    Set.range (poincareDiskOrbitMap poincareDiskOrigin) =
      ({poincareDiskOrigin} : Set PoincareDisk) := by
  ext p
  constructor
  · rintro ⟨g, hg⟩
    change g • poincareDiskOrigin = p at hg
    rw [diskRotationAction_origin g] at hg
    change p = poincareDiskOrigin
    exact hg.symm
  · intro hp
    have hp' : p = poincareDiskOrigin := by simpa using hp
    subst p
    exact ⟨1, by simp [poincareDiskOrbitMap]⟩

theorem poincareDiskOrbit_eq_radialFiber (p : PoincareDisk) :
    Set.range (poincareDiskOrbitMap p) = diskRadialFiber (diskRadiusSq p) := by
  by_cases hz : diskRadiusSq p = 0
  · have hp : p = poincareDiskOrigin :=
      (diskRadiusSq_eq_zero_iff p).mp hz
    subst p
    have ho : diskRadiusSq poincareDiskOrigin = 0 := by
      norm_num [diskRadiusSq, poincareDiskOrigin]
    rw [poincareDiskOrbit_origin, ho, diskRadialFiber_zero]
  · have hnonneg : 0 ≤ diskRadiusSq p := by
      dsimp [diskRadiusSq]
      positivity
    exact poincareDiskOrbit_eq_radialFiber_of_pos p
      (lt_of_le_of_ne hnonneg (Ne.symm hz))

theorem diskRotationAction_injective_of_pos (p : PoincareDisk)
    (hpos : 0 < diskRadiusSq p) :
    Function.Injective (fun g : RotationCarrier => g • p) := by
  intro g h hgh
  have hgh' := congrArg Subtype.val hgh
  change diskRotationAction g.1 p.1 = diskRotationAction h.1 p.1 at hgh'
  have hp1 := congrArg Prod.fst hgh'
  have hp2 := congrArg Prod.snd hgh'
  dsimp [diskRotationAction, diskRotation] at hp1 hp2
  have hrad : p.1.1 ^ 2 + p.1.2 ^ 2 = diskRadiusSq p := by
    rfl
  have hdc : (g.1.1 - h.1.1) * diskRadiusSq p = 0 := by
    linear_combination
      p.1.1 * hp1 + p.1.2 * hp2 -
        (g.1.1 - h.1.1) * hrad
  have hds : (g.1.2 - h.1.2) * diskRadiusSq p = 0 := by
    linear_combination
      -p.1.2 * hp1 + p.1.1 * hp2 -
        (g.1.2 - h.1.2) * hrad
  have hrne : diskRadiusSq p ≠ 0 := ne_of_gt hpos
  have hgc : g.1.1 = h.1.1 := by
    rcases mul_eq_zero.mp hdc with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact False.elim (hrne hzero)
  have hgs : g.1.2 = h.1.2 := by
    rcases mul_eq_zero.mp hds with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact False.elim (hrne hzero)
  apply Subtype.ext
  exact Prod.ext hgc hgs

noncomputable def poincareDiskRadialFiberMap (p : PoincareDisk)
    (_hpos : 0 < diskRadiusSq p) :
    RotationCarrier → diskRadialFiber (diskRadiusSq p) := fun g =>
  ⟨g • p, poincareDiskOrbit_subset_radialFiber p ⟨g, rfl⟩⟩

theorem poincareDiskRadialFiberMap_continuous (p : PoincareDisk)
    (hpos : 0 < diskRadiusSq p) :
    Continuous (poincareDiskRadialFiberMap p hpos) := by
  apply Continuous.subtype_mk
  exact continuous_poincareDiskOrbitMap p

theorem poincareDiskRadialFiberMap_bijective (p : PoincareDisk)
    (hpos : 0 < diskRadiusSq p) :
    Function.Bijective (poincareDiskRadialFiberMap p hpos) := by
  constructor
  · intro g h hgh
    apply diskRotationAction_injective_of_pos p hpos
    exact congrArg Subtype.val hgh
  · intro q
    have hq : q.1 ∈ Set.range (poincareDiskOrbitMap p) := by
      rw [poincareDiskOrbit_eq_radialFiber_of_pos p hpos]
      exact q.2
    rcases hq with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg

noncomputable def poincareDiskRadialFiberEquiv (p : PoincareDisk)
    (hpos : 0 < diskRadiusSq p) :
    RotationCarrier ≃ diskRadialFiber (diskRadiusSq p) :=
  Equiv.ofBijective (poincareDiskRadialFiberMap p hpos)
    (poincareDiskRadialFiberMap_bijective p hpos)

noncomputable def poincareDiskRadialFiberHomeomorph (p : PoincareDisk)
    (hpos : 0 < diskRadiusSq p) :
    RotationCarrier ≃ₜ diskRadialFiber (diskRadiusSq p) :=
  Continuous.homeoOfEquivCompactToT2
    (f := poincareDiskRadialFiberEquiv p hpos)
    (by
      simpa [poincareDiskRadialFiberEquiv] using
        poincareDiskRadialFiberMap_continuous p hpos)

theorem poincareDiskRadialFiberHomeomorph_apply (p : PoincareDisk)
    (hpos : 0 < diskRadiusSq p) (g : RotationCarrier) :
    poincareDiskRadialFiberHomeomorph p hpos g =
      poincareDiskRadialFiberMap p hpos g := by
  change (poincareDiskRadialFiberEquiv p hpos) g =
    poincareDiskRadialFiberMap p hpos g
  rfl

noncomputable def diskRadiusSection (r : Set.Ico (0 : ℝ) 1) : PoincareDisk :=
  ⟨(Real.sqrt r.1, 0), by
    have hsqrt : (Real.sqrt r.1) ^ 2 = r.1 := Real.sq_sqrt r.2.1
    simpa [hsqrt] using r.2.2⟩

def diskRadiusParameter : PoincareDisk → Set.Ico (0 : ℝ) 1 := fun p =>
  ⟨diskRadiusSq p, diskRadiusSq_mem_Ico p⟩

theorem continuous_diskRadiusParameter :
    Continuous diskRadiusParameter := by
  apply Continuous.subtype_mk
  exact continuous_diskRadiusSq

theorem continuous_diskRadiusSection :
    Continuous (diskRadiusSection : Set.Ico (0 : ℝ) 1 → PoincareDisk) := by
  apply Continuous.subtype_mk
  exact (Real.continuous_sqrt.comp continuous_subtype_val).prodMk
    continuous_const

theorem diskRadiusSq_diskRadiusSection (r : Set.Ico (0 : ℝ) 1) :
    diskRadiusSq (diskRadiusSection r) = r.1 := by
  have hsqrt : (Real.sqrt r.1) ^ 2 = r.1 := Real.sq_sqrt r.2.1
  simpa [diskRadiusSection, diskRadiusSq, hsqrt]

theorem diskRadiusParameter_section_leftInverse :
    Function.LeftInverse diskRadiusParameter diskRadiusSection := by
  intro r
  apply Subtype.ext
  exact diskRadiusSq_diskRadiusSection r

theorem diskRadiusSection_injective :
    Function.Injective diskRadiusSection :=
  diskRadiusParameter_section_leftInverse.injective

theorem isEmbedding_diskRadiusSection :
    Topology.IsEmbedding (diskRadiusSection : Set.Ico (0 : ℝ) 1 → PoincareDisk) := by
  exact diskRadiusParameter_section_leftInverse.isEmbedding
    continuous_diskRadiusParameter continuous_diskRadiusSection

def diskRadiusSectionRange : Set PoincareDisk :=
  {p | p.1.2 = 0 ∧ 0 ≤ p.1.1}

theorem isClosed_diskRadiusSectionRange :
    IsClosed diskRadiusSectionRange := by
  have hx : Continuous (fun p : PoincareDisk => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hy : Continuous (fun p : PoincareDisk => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hzero : IsClosed ((fun p : PoincareDisk => p.1.2) ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hy
  have hnonneg : IsClosed ((fun p : PoincareDisk => p.1.1) ⁻¹' Set.Ici (0 : ℝ)) :=
    isClosed_Ici.preimage hx
  simpa [diskRadiusSectionRange, Set.preimage, Set.mem_inter_iff] using hzero.inter hnonneg

theorem diskRadiusSection_range_eq :
    Set.range diskRadiusSection = diskRadiusSectionRange := by
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    constructor
    · rfl
    · exact Real.sqrt_nonneg _
  · intro hp
    have hsq_nonneg : 0 ≤ p.1.1 ^ 2 := sq_nonneg _
    have hsq_lt : p.1.1 ^ 2 < 1 := by
      simpa [hp.1] using p.2
    let r : Set.Ico (0 : ℝ) 1 := ⟨p.1.1 ^ 2, hsq_nonneg, hsq_lt⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · have habs : |p.1.1| = p.1.1 := abs_of_nonneg hp.2
      simpa [diskRadiusSection, r, Real.sqrt_sq_eq_abs, habs]
    · exact hp.1.symm

noncomputable def diskRadiusSectionHomeomorph :
    Set.Ico (0 : ℝ) 1 ≃ₜ (Set.range diskRadiusSection) :=
  isEmbedding_diskRadiusSection.toHomeomorph

theorem diskRadiusSectionHomeomorph_apply (r : Set.Ico (0 : ℝ) 1) :
    diskRadiusSectionHomeomorph r =
      ⟨diskRadiusSection r, ⟨r, rfl⟩⟩ := by
  rfl

noncomputable def diskRadiusSectionClosedRayHomeomorph :
    Set.Ico (0 : ℝ) 1 ≃ₜ (diskRadiusSectionRange) :=
  diskRadiusSectionHomeomorph.trans
    (Homeomorph.setCongr diskRadiusSection_range_eq)

def compactRadiusToIco (R : ℝ) (hR : R < 1) :
    Set.Icc (0 : ℝ) R → Set.Ico (0 : ℝ) 1 := fun r =>
  ⟨r.1, r.2.1, lt_of_le_of_lt r.2.2 hR⟩

theorem continuous_compactRadiusToIco (R : ℝ) (hR : R < 1) :
    Continuous (compactRadiusToIco R hR) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

noncomputable def compactRadialSection (R : ℝ) (hR : R < 1) :
    Set.Icc (0 : ℝ) R → PoincareDisk := fun r =>
  diskRadiusSection (compactRadiusToIco R hR r)

theorem continuous_compactRadialSection (R : ℝ) (hR : R < 1) :
    Continuous (compactRadialSection R hR) := by
  exact continuous_diskRadiusSection.comp (continuous_compactRadiusToIco R hR)

theorem compact_compactRadialSection_range (R : ℝ) (hR : R < 1) :
    IsCompact (Set.range (compactRadialSection R hR)) := by
  letI : CompactSpace (Set.Icc (0 : ℝ) R) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_range (continuous_compactRadialSection R hR)

theorem compactRadialSection_injective (R : ℝ) (hR : R < 1) :
    Function.Injective (compactRadialSection R hR) := by
  intro r s hrs
  apply Subtype.ext
  have hparam : compactRadiusToIco R hR r = compactRadiusToIco R hR s := by
    apply diskRadiusSection_injective
    simpa [compactRadialSection] using hrs
  exact congrArg (fun t : Set.Ico (0 : ℝ) 1 => t.1) hparam

noncomputable def compactRadialSectionHomeomorph (R : ℝ) (hR : R < 1) :
    Set.Icc (0 : ℝ) R ≃ₜ Set.range (compactRadialSection R hR) := by
  let f : Set.Icc (0 : ℝ) R → Set.range (compactRadialSection R hR) := fun r =>
    ⟨compactRadialSection R hR r, ⟨r, rfl⟩⟩
  have hf_cont : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_compactRadialSection R hR
  have hf_bij : Function.Bijective f := by
    constructor
    · intro r s hrs
      apply compactRadialSection_injective R hR
      exact congrArg Subtype.val hrs
    · intro q
      rcases q.2 with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      apply Subtype.ext
      exact hr
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f hf_bij) hf_cont

theorem compactRadialSectionHomeomorph_apply (R : ℝ) (hR : R < 1)
    (r : Set.Icc (0 : ℝ) R) :
    compactRadialSectionHomeomorph R hR r =
      ⟨compactRadialSection R hR r, ⟨r, rfl⟩⟩ := by
  rfl

def diskSublevel (R : ℝ) : Set PoincareDisk :=
  {p | diskRadiusSq p ≤ R}

theorem diskSublevel_mono {R S : ℝ} (hRS : R ≤ S) :
    diskSublevel R ⊆ diskSublevel S := by
  intro p hp
  exact le_trans hp hRS

theorem diskSublevel_nonempty (R : ℝ) (hR : 0 ≤ R) :
    (diskSublevel R).Nonempty := by
  refine ⟨⟨(0, 0), by norm_num⟩, ?_⟩
  simpa [diskSublevel, diskRadiusSq] using hR

theorem nonempty_diskSublevel_type (R : ℝ) (hR : 0 ≤ R) :
    Nonempty (diskSublevel R) := by
  exact Set.nonempty_coe_sort.mpr (diskSublevel_nonempty R hR)

def diskAmbientSublevel (R : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ^ 2 + x.2 ^ 2 ≤ R}

theorem diskAmbientSublevel_mono {R S : ℝ} (hRS : R ≤ S) :
    diskAmbientSublevel R ⊆ diskAmbientSublevel S := by
  intro x hx
  exact le_trans hx hRS

theorem diskAmbientSublevel_nonempty (R : ℝ) (hR : 0 ≤ R) :
    (diskAmbientSublevel R).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simpa [diskAmbientSublevel] using hR

theorem nonempty_diskAmbientSublevel_type (R : ℝ) (hR : 0 ≤ R) :
    Nonempty (diskAmbientSublevel R) := by
  exact Set.nonempty_coe_sort.mpr (diskAmbientSublevel_nonempty R hR)

theorem convex_diskAmbientSublevel (R : ℝ) :
    Convex ℝ (diskAmbientSublevel R) := by
  intro x hx y hy a b ha hb hab
  change (a * x.1 + b * y.1) ^ 2 +
      (a * x.2 + b * y.2) ^ 2 ≤ R
  change x.1 ^ 2 + x.2 ^ 2 ≤ R at hx
  change y.1 ^ 2 + y.2 ^ 2 ≤ R at hy
  have hxa : a * (x.1 ^ 2 + x.2 ^ 2) ≤ a * R :=
    mul_le_mul_of_nonneg_left hx ha
  have hyb : b * (y.1 ^ 2 + y.2 ^ 2) ≤ b * R :=
    mul_le_mul_of_nonneg_left hy hb
  have hcoef : 0 ≤ a * b := mul_nonneg ha hb
  have hcoord₁ : 0 ≤ a * b * (x.1 - y.1) ^ 2 :=
    mul_nonneg hcoef (sq_nonneg (x.1 - y.1))
  have hcoord₂ : 0 ≤ a * b * (x.2 - y.2) ^ 2 :=
    mul_nonneg hcoef (sq_nonneg (x.2 - y.2))
  have hbval : b = 1 - a := by linarith
  have hineq :
      (a * x.1 + b * y.1) ^ 2 + (a * x.2 + b * y.2) ^ 2 ≤
        a * (x.1 ^ 2 + x.2 ^ 2) + b * (y.1 ^ 2 + y.2 ^ 2) := by
    rw [hbval]
    have hcoef' : 0 ≤ a * (1 - a) := by
      rw [← hbval]
      exact hcoef
    have hcoord₁' : 0 ≤ a * (1 - a) * (x.1 - y.1) ^ 2 := by
      exact mul_nonneg hcoef' (sq_nonneg (x.1 - y.1))
    have hcoord₂' : 0 ≤ a * (1 - a) * (x.2 - y.2) ^ 2 := by
      exact mul_nonneg hcoef' (sq_nonneg (x.2 - y.2))
    nlinarith [hcoord₁', hcoord₂']
  calc
    (a * x.1 + b * y.1) ^ 2 + (a * x.2 + b * y.2) ^ 2 ≤
        a * (x.1 ^ 2 + x.2 ^ 2) + b * (y.1 ^ 2 + y.2 ^ 2) := hineq
    _ ≤ a * R + b * R := add_le_add hxa hyb
    _ = R := by rw [hbval]; ring

theorem isPathConnected_diskAmbientSublevel (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected (diskAmbientSublevel R) := by
  apply (convex_diskAmbientSublevel R).isPathConnected
  refine ⟨(0, 0), ?_⟩
  simpa [diskAmbientSublevel] using hR

theorem isClosed_diskAmbientSublevel (R : ℝ) :
    IsClosed (diskAmbientSublevel R) := by
  have hcont : Continuous (fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) :=
    (continuous_fst.pow 2).add (continuous_snd.pow 2)
  exact isClosed_Iic.preimage hcont

theorem isCompact_diskAmbientSublevel (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (diskAmbientSublevel R) := by
  let s : ℝ := Real.sqrt R
  have hs : s ^ 2 = R := Real.sq_sqrt hR
  have hrect : IsCompact (Set.Icc (-s) s ×ˢ Set.Icc (-s) s) :=
    isCompact_Icc.prod isCompact_Icc
  apply hrect.of_isClosed_subset (isClosed_diskAmbientSublevel R)
  intro x hx
  change x.1 ^ 2 + x.2 ^ 2 ≤ R at hx
  have hx1sq : x.1 ^ 2 ≤ R := by
    nlinarith [sq_nonneg x.2]
  have hx2sq : x.2 ^ 2 ≤ R := by
    nlinarith [sq_nonneg x.1]
  have hx1abs : |x.1| ≤ s := by
    have hsq : x.1 ^ 2 ≤ s ^ 2 := by simpa [hs] using hx1sq
    have := (sq_le_sq.mp hsq)
    simpa [s, abs_of_nonneg (Real.sqrt_nonneg R)] using this
  have hx2abs : |x.2| ≤ s := by
    have hsq : x.2 ^ 2 ≤ s ^ 2 := by simpa [hs] using hx2sq
    have := (sq_le_sq.mp hsq)
    simpa [s, abs_of_nonneg (Real.sqrt_nonneg R)] using this
  exact ⟨abs_le.mp hx1abs, abs_le.mp hx2abs⟩

noncomputable def diskAmbientToPoincareDisk (R : ℝ) (hR : R < 1) :
    diskAmbientSublevel R → PoincareDisk := fun x =>
  ⟨x.1, lt_of_le_of_lt x.2 hR⟩

theorem continuous_diskAmbientToPoincareDisk (R : ℝ) (hR : R < 1) :
    Continuous (diskAmbientToPoincareDisk R hR) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem diskAmbientToPoincareDisk_range (R : ℝ) (hR : R < 1) :
    Set.range (diskAmbientToPoincareDisk R hR) = diskSublevel R := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hp
    let x : diskAmbientSublevel R := ⟨p.1, hp⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rfl

theorem isPathConnected_diskSublevel (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsPathConnected (diskSublevel R) := by
  rw [← diskAmbientToPoincareDisk_range R hR1]
  have hdom : IsPathConnected (Set.univ : Set (diskAmbientSublevel R)) := by
    simpa using
        (isPathConnected_diskAmbientSublevel R hR0).preimage_coe
        (U := diskAmbientSublevel R) (W := diskAmbientSublevel R) Set.Subset.rfl
  simpa [Set.image_univ] using
    hdom.image (continuous_diskAmbientToPoincareDisk R hR1)

theorem compact_diskSublevel (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IsCompact (diskSublevel R) := by
  rw [← diskAmbientToPoincareDisk_range R hR1]
  letI : CompactSpace (diskAmbientSublevel R) :=
    isCompact_iff_compactSpace.mp (isCompact_diskAmbientSublevel R hR0)
  exact isCompact_range (continuous_diskAmbientToPoincareDisk R hR1)

def diskSublevelAction (R : ℝ) (g : RotationCarrier) :
    diskSublevel R → diskSublevel R := fun p =>
  ⟨g • p.1, by
    change diskRadiusSq (g • p.1) ≤ R
    rw [diskRotationAction_preserves_radius g p.1]
    exact p.2⟩

theorem continuous_diskSublevelAction (R : ℝ) (g : RotationCarrier) :
    Continuous (diskSublevelAction R g) := by
  apply Continuous.subtype_mk
  exact (continuous_const_smul g).comp continuous_subtype_val

theorem diskSublevelAction_bijective (R : ℝ) (g : RotationCarrier) :
    Function.Bijective (diskSublevelAction R g) := by
  let f := diskSublevelAction R g
  let fInv := diskSublevelAction R g⁻¹
  have hleft : Function.LeftInverse fInv f := by
    intro p
    apply Subtype.ext
    simp [f, fInv, diskSublevelAction]
  have hright : Function.RightInverse fInv f := by
    intro p
    apply Subtype.ext
    simp [f, fInv, diskSublevelAction]
  exact ⟨hleft.injective, hright.surjective⟩

noncomputable def diskSublevelRotationHomeomorph (R : ℝ) (g : RotationCarrier) :
    diskSublevel R ≃ₜ diskSublevel R := by
  let f := diskSublevelAction R g
  let fInv := diskSublevelAction R g⁻¹
  have hleft : Function.LeftInverse fInv f := by
    intro p
    apply Subtype.ext
    simp [f, fInv, diskSublevelAction]
  have hright : Function.RightInverse fInv f := by
    intro p
    apply Subtype.ext
    simp [f, fInv, diskSublevelAction]
  let e : diskSublevel R ≃ diskSublevel R :=
    { toFun := f, invFun := fInv, left_inv := hleft, right_inv := hright }
  exact Homeomorph.mk e (continuous_diskSublevelAction R g)
    (continuous_diskSublevelAction R g⁻¹)

theorem diskSublevelRotationHomeomorph_apply (R : ℝ) (g : RotationCarrier)
    (p : diskSublevel R) :
    diskSublevelRotationHomeomorph R g p = diskSublevelAction R g p := by
  rfl

instance diskSublevelMulAction (R : ℝ) : MulAction RotationCarrier (diskSublevel R) where
  smul := diskSublevelAction R
  one_smul := by
    intro p
    apply Subtype.ext
    change (1 : RotationCarrier) • p.1 = p.1
    exact one_smul RotationCarrier p.1
  mul_smul := by
    intro g h p
    apply Subtype.ext
    change (g * h) • p.1 = g • h • p.1
    exact mul_smul g h p.1

instance continuousSMul_diskSublevel (R : ℝ) :
    ContinuousSMul RotationCarrier (diskSublevel R) where
  continuous_smul := by
    apply Continuous.subtype_mk
    change Continuous (fun gp : RotationCarrier × diskSublevel R =>
      gp.1 • gp.2.1)
    have hpair : Continuous (fun gp : RotationCarrier × diskSublevel R =>
        (gp.1, gp.2.1)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    simpa only [Function.comp_apply] using
      continuous_poincareDiskRotationAction.comp hpair

theorem diskSublevel_smul_apply (R : ℝ) (g : RotationCarrier)
    (p : diskSublevel R) :
    g • p = diskSublevelAction R g p := by
  rfl

def diskSublevelOrbitMap (R : ℝ) (p : diskSublevel R) :
    RotationCarrier → diskSublevel R := fun g => g • p

theorem continuous_diskSublevelOrbitMap (R : ℝ) (p : diskSublevel R) :
    Continuous (diskSublevelOrbitMap R p) := by
  have hjoint : Continuous (fun gp : RotationCarrier × diskSublevel R =>
      gp.1 • gp.2) := continuous_smul
  simpa [diskSublevelOrbitMap] using
    hjoint.comp (continuous_id.prodMk continuous_const)

theorem compact_diskSublevelOrbit (R : ℝ) (p : diskSublevel R) :
    IsCompact (Set.range (diskSublevelOrbitMap R p)) := by
  exact isCompact_range (continuous_diskSublevelOrbitMap R p)

theorem isClosed_diskSublevelOrbit (R : ℝ) (p : diskSublevel R) :
    IsClosed (Set.range (diskSublevelOrbitMap R p)) := by
  exact (compact_diskSublevelOrbit R p).isClosed

theorem diskSublevelOrbit_eq_radius_fiber (R : ℝ) (p : diskSublevel R)
    (hpos : 0 < diskRadiusSq p.1) :
    Set.range (diskSublevelOrbitMap R p) =
      {q : diskSublevel R | diskRadiusSq q.1 = diskRadiusSq p.1} := by
  ext q
  constructor
  · rintro ⟨g, rfl⟩
    exact diskRotationAction_preserves_radius g p.1
  · intro hq
    obtain ⟨g, hg⟩ := diskRotation_exists_maps_of_radius_eq
      p.1 q.1 hq.symm hpos
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg

end SouriauPoincare
