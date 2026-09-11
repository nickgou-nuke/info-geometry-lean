import InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Clifford55
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Topology of the real `Cl(5,5)` projectivization

This owner proves the two ambient facts required by the finite configuration
covering theorem for the native carrier `V55`:

* the repository's quotient topology on `ℙ ℝ V55` is Hausdorff;
* it is compact, hence locally compact.

Hausdorffness is proved by the continuous injective ray-projector readout.
Compactness is proved from the continuous surjection of the unit sphere.  No
manifold, fundamental-group, braid, or monodromy identification is asserted.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.Cl55ProjectivizationTopology

open BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

/-- Positive-definite coordinate pairing used only to normalize real rays. -/
def euclideanDot55 (v w : V55) : ℝ :=
  (∑ i : Fin 5, v.1 i * w.1 i) +
    (∑ i : Fin 5, v.2 i * w.2 i)

theorem euclideanDot55_self_pos {v : V55} (hv : v ≠ 0) :
    0 < euclideanDot55 v v := by
  by_contra h
  have hnonneg : 0 ≤ euclideanDot55 v v := by
    unfold euclideanDot55
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
      (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  have hz : euclideanDot55 v v = 0 := le_antisymm (not_lt.mp h) hnonneg
  have hparts :
      (∑ i : Fin 5, v.1 i ^ 2) = 0 ∧
        (∑ i : Fin 5, v.2 i ^ 2) = 0 := by
    have hz' :
        (∑ i : Fin 5, v.1 i ^ 2) +
          (∑ i : Fin 5, v.2 i ^ 2) = 0 := by
      simpa [euclideanDot55, pow_two] using hz
    exact add_eq_zero_iff_of_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) |>.mp hz'
  apply hv
  apply Prod.ext <;> funext i
  · have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (v.1 j))).mp hparts.1 i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  · have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (v.2 j))).mp hparts.2 i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi

theorem euclideanDot55_smul_left (c : ℝ) (v w : V55) :
    euclideanDot55 (c • v) w = c * euclideanDot55 v w := by
  unfold euclideanDot55
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem euclideanDot55_smul_right (c : ℝ) (v w : V55) :
    euclideanDot55 v (c • w) = c * euclideanDot55 v w := by
  unfold euclideanDot55
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Scale-invariant rank-one projector attached to a nonzero representative. -/
def rayProjectorRep (v : {v : V55 // v ≠ 0}) (x : V55) : V55 :=
  (euclideanDot55 v x / euclideanDot55 v v) • (v : V55)

theorem rayProjectorRep_smul
    (v w : {v : V55 // v ≠ 0}) (c : ℝ)
    (h : (v : V55) = c • (w : V55)) :
    rayProjectorRep v = rayProjectorRep w := by
  have hc : c ≠ 0 := by
    intro hc
    apply v.property
    simp [h, hc]
  have hdot : euclideanDot55 (w : V55) (w : V55) ≠ 0 :=
    ne_of_gt (euclideanDot55_self_pos w.property)
  funext x
  simp only [rayProjectorRep, h, euclideanDot55_smul_left,
    euclideanDot55_smul_right]
  rw [smul_smul]
  congr 1
  field_simp

/-- Continuous rank-one projector readout of a real projective ray. -/
def rayProjector : ℙ ℝ V55 → (V55 → V55) :=
  Projectivization.lift rayProjectorRep rayProjectorRep_smul

theorem rayProjectorRep_continuous : Continuous rayProjectorRep := by
  apply continuous_pi
  intro x
  unfold rayProjectorRep euclideanDot55
  apply Continuous.smul
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · intro v
      exact ne_of_gt (euclideanDot55_self_pos v.property)
  · exact continuous_subtype_val

theorem rayProjector_continuous :
    @Continuous (ℙ ℝ V55) (V55 → V55)
      (projectivizationQuotientTopology (K := ℝ) (V := V55)) inferInstance
      rayProjector := by
  rw [continuous_coinduced_dom]
  simpa [rayProjector, Function.comp_def] using rayProjectorRep_continuous

theorem rayProjector_injective : Function.Injective rayProjector := by
  intro p q
  induction p using Projectivization.ind with
  | _ v hv =>
    induction q using Projectivization.ind with
    | _ w hw =>
      intro h
      apply (Projectivization.mk_eq_mk_iff ℝ v w hv hw).2
      let c0 : ℝ := euclideanDot55 w v / euclideanDot55 w w
      have hc0 : c0 ≠ 0 := by
        intro hc
        have happ := congrFun h v
        change rayProjectorRep ⟨v, hv⟩ v = rayProjectorRep ⟨w, hw⟩ v at happ
        have hvdot : euclideanDot55 v v ≠ 0 :=
          ne_of_gt (euclideanDot55_self_pos hv)
        have hdotwv : euclideanDot55 w v = 0 := by
          have hww : euclideanDot55 w w ≠ 0 :=
            ne_of_gt (euclideanDot55_self_pos hw)
          exact (div_eq_zero_iff.mp hc).resolve_right hww
        have : v = (0 : V55) := by
          simpa [rayProjectorRep, hvdot, hdotwv] using happ
        exact hv this
      let c : ℝˣ := Units.mk0 c0 hc0
      refine ⟨c, ?_⟩
      have happ := congrFun h v
      change rayProjectorRep ⟨v, hv⟩ v = rayProjectorRep ⟨w, hw⟩ v at happ
      have hvdot : euclideanDot55 v v ≠ 0 :=
        ne_of_gt (euclideanDot55_self_pos hv)
      simpa [rayProjectorRep, c, c0, hvdot] using happ.symm

/-- The repository quotient topology on the real `V55` projectivization is
Hausdorff. -/
theorem q55Projectivization_t2Space :
    @T2Space (ℙ ℝ V55)
      (projectivizationQuotientTopology (K := ℝ) (V := V55)) := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  refine ⟨?_⟩
  intro p q hpq
  obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ :=
    t2_separation (show rayProjector p ≠ rayProjector q from
      fun h => hpq (rayProjector_injective h))
  refine ⟨rayProjector ⁻¹' u, rayProjector ⁻¹' v,
    hu.preimage rayProjector_continuous,
    hv.preimage rayProjector_continuous, hpu, hqv, ?_⟩
  rw [Set.disjoint_left]
  intro x hxu hxv
  exact (Set.disjoint_left.mp huv) hxu hxv

/-- The Euclidean unit sphere in the native `V55` carrier. -/
abbrev UnitSphere55 := Metric.sphere (0 : V55) 1

/-- Quotient projection restricted to normalized representatives. -/
def unitSphereProjectivization (v : UnitSphere55) : ℙ ℝ V55 :=
  Projectivization.mk ℝ v (by
    intro hv
    have := v.property
    simp [UnitSphere55, hv] at this)

theorem unitSphereProjectivization_continuous :
    @Continuous UnitSphere55 (ℙ ℝ V55) inferInstance
      (projectivizationQuotientTopology (K := ℝ) (V := V55))
      unitSphereProjectivization := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  let q : {v : V55 // v ≠ 0} → ℙ ℝ V55 :=
    @Quotient.mk' _ (projectivizationSetoid ℝ V55)
  let inc : UnitSphere55 → {v : V55 // v ≠ 0} := fun v =>
    ⟨v, by
      intro hv
      have := v.property
      simp [UnitSphere55, hv] at this⟩
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  change Continuous (q ∘ inc)
  exact continuous_coinduced_rng.comp hinc

theorem unitSphereProjectivization_surjective :
    Function.Surjective unitSphereProjectivization := by
  intro p
  induction p using Projectivization.ind with
  | _ v hv =>
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let w : V55 := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.sphere (0 : V55) 1 := by
      change dist w 0 = 1
      rw [dist_zero_right, norm_smul]
      simp [hvnorm]
    refine ⟨⟨w, hw⟩, ?_⟩
    change Projectivization.mk ℝ w _ = Projectivization.mk ℝ v hv
    apply (Projectivization.mk_eq_mk_iff ℝ w v _ hv).2
    let c : ℝˣ := Units.mk0 ‖v‖⁻¹ (inv_ne_zero hvnorm)
    exact ⟨c, rfl⟩

/-- Compactness of real projectivization follows from the compact unit sphere
and its surjective quotient projection. -/
theorem q55Projectivization_compactSpace :
    @CompactSpace (ℙ ℝ V55)
      (projectivizationQuotientTopology (K := ℝ) (V := V55)) := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  refine ⟨?_⟩
  have hrange : Set.range unitSphereProjectivization = Set.univ :=
    Set.range_eq_univ.mpr unitSphereProjectivization_surjective
  rw [← hrange]
  haveI : CompactSpace UnitSphere55 :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V55) 1)
  simpa [Set.image_univ] using
    isCompact_univ.image unitSphereProjectivization_continuous

/-- Compact Hausdorff real projectivization is locally compact. -/
theorem q55Projectivization_locallyCompactSpace :
    @LocallyCompactSpace (ℙ ℝ V55)
      (projectivizationQuotientTopology (K := ℝ) (V := V55)) := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  letI : CompactSpace (ℙ ℝ V55) := q55Projectivization_compactSpace
  letI : T2Space (ℙ ℝ V55) := q55Projectivization_t2Space
  infer_instance

end InfoGeometry.Twistor.Cl55ProjectivizationTopology
