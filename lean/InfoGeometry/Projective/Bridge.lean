import InfoGeometry.Projective.Projective
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.Orthant
import InfoGeometry.Projective.SelfDualCone
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.DenselyOrdered
set_option linter.unnecessarySimpa false

/-!
# Positive-Measure / Cone Bridge

A non-breaking bridge between the legacy `PositiveMeasure` projectivization
and the canonical self-dual-cone model of the positive orthant.
-/

open scoped Projectivization

namespace InfoGeometry.Projective

section Coordinates

variable {α : Type*}

/-- Convert a positive measure to Euclidean coordinates. -/
noncomputable def positiveMeasureToEuclidean (μ : PositiveMeasure α ℝ) : EuclideanSpace ℝ α :=
  (EuclideanSpace.equiv α ℝ).symm μ

@[simp] lemma positiveMeasureToEuclidean_apply (μ : PositiveMeasure α ℝ) (i : α) :
    positiveMeasureToEuclidean (α := α) μ i = μ i := by
  simp [positiveMeasureToEuclidean]

/-- Compatibility of `PositiveMeasure.scale` with Euclidean scalar multiplication. -/
@[simp] lemma positiveMeasureToEuclidean_scale
    (c : ℝ) (hc : 0 < c) (μ : PositiveMeasure α ℝ) :
    positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c hc μ)
      = c • positiveMeasureToEuclidean (α := α) μ := by
  ext i
  simp [positiveMeasureToEuclidean, PositiveMeasure.scale_apply]

end Coordinates

section OrthantBridge

variable {α : Type*} [Fintype α]

/-- Coordinatewise characterization of the interior of the positive orthant cone. -/
lemma interior_positiveOrthantCone_eq :
    interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α)) =
      {x : EuclideanSpace ℝ α | ∀ i, 0 < x i} := by
  let e : EuclideanSpace ℝ α ≃ₜ (α → ℝ) :=
    (EuclideanSpace.equiv α ℝ).toHomeomorph
  have hset :
      {x : EuclideanSpace ℝ α | ∀ i, 0 ≤ x i}
        = e ⁻¹' (Set.pi Set.univ (fun _ : α => Set.Ici (0 : ℝ))) := by
    ext x
    simp [e, Pi.le_def]
  have hcone :
      (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α))
        = {x : EuclideanSpace ℝ α | ∀ i, 0 ≤ x i} := by
    ext x
    simpa [Set.mem_setOf_eq] using (mem_positiveOrthantCone (α := α) x)
  rw [hcone, hset, ← e.preimage_interior, interior_pi_set Set.finite_univ]
  ext x
  simp [e, Set.mem_pi]

@[simp] lemma mem_interior_positiveOrthantCone_iff (x : EuclideanSpace ℝ α) :
    x ∈ interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α))
      ↔ ∀ i, 0 < x i := by
  rw [interior_positiveOrthantCone_eq (α := α)]
  rfl

/-- Build a positive measure from an interior positive-orthant point. -/
noncomputable def interiorToPositiveMeasure
    (x : {x : EuclideanSpace ℝ α // x ∈ interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α))}) :
    PositiveMeasure α ℝ :=
  ⟨fun i => x.1 i, (mem_interior_positiveOrthantCone_iff (α := α) x.1).1 x.2⟩

@[simp] lemma interiorToPositiveMeasure_apply
    (x : {x : EuclideanSpace ℝ α // x ∈ interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α))})
    (i : α) :
    interiorToPositiveMeasure (α := α) x i = x.1 i := rfl

/-- Convert a positive measure to an interior positive-orthant point. -/
noncomputable def positiveMeasureToInterior
    (μ : PositiveMeasure α ℝ) :
    {x : EuclideanSpace ℝ α // x ∈ interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α))} := by
  refine ⟨positiveMeasureToEuclidean (α := α) μ, ?_⟩
  rw [mem_interior_positiveOrthantCone_iff]
  intro i
  exact μ.pos i

/-- Positive measures are equivalent to interior points of the positive orthant cone. -/
noncomputable def positiveMeasureEquivInterior :
    PositiveMeasure α ℝ ≃
      {x : EuclideanSpace ℝ α // x ∈ interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α))} where
  toFun := positiveMeasureToInterior (α := α)
  invFun := interiorToPositiveMeasure (α := α)
  left_inv μ := by
    ext i
    simp [positiveMeasureToInterior, positiveMeasureToEuclidean]
  right_inv x := by
    ext i
    simp [positiveMeasureToInterior, interiorToPositiveMeasure, positiveMeasureToEuclidean]

section ProjectiveBridge

variable [Nonempty α]

omit [Fintype α] in
lemma positiveMeasureToEuclidean_ne_zero (μ : PositiveMeasure α ℝ) :
    positiveMeasureToEuclidean (α := α) μ ≠ 0 := by
  intro h0
  obtain ⟨i⟩ := ‹Nonempty α›
  have hi : positiveMeasureToEuclidean (α := α) μ i = 0 := by
    simp [h0]
  exact (ne_of_gt (μ.pos i)) ((positiveMeasureToEuclidean_apply (α := α) μ i).trans hi)

/--
Representative-level map from positive-measure rays to interior cone rays.
-/
noncomputable def positiveMeasureToConeInteriorRay
    (μ : PositiveMeasure α ℝ) :
    ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) :=
  let v : EuclideanSpace ℝ α := positiveMeasureToEuclidean (α := α) μ
  let hv0 : v ≠ 0 := positiveMeasureToEuclidean_ne_zero (α := α) μ
  let hvInt : v ∈ interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α)) :=
    (positiveMeasureToInterior (α := α) μ).2
  ⟨Projectivization.mk ℝ v hv0, by
    refine ⟨v, hv0, ?_, rfl⟩
    simpa [positiveOrthant] using hvInt⟩

lemma positiveMeasureToConeInteriorRay_sameRay
    {μ ν : PositiveMeasure α ℝ}
    (h : PositiveMeasure.SameRay μ ν) :
    positiveMeasureToConeInteriorRay (α := α) μ
      = positiveMeasureToConeInteriorRay (α := α) ν := by
  rcases h with ⟨c, rfl⟩
  apply Subtype.ext
  let v : EuclideanSpace ℝ α := positiveMeasureToEuclidean (α := α) μ
  have hv0 : v ≠ 0 := positiveMeasureToEuclidean_ne_zero (α := α) μ
  have hcpos : 0 < c.1 := c.2
  have hcv0 : c.1 • v ≠ 0 := smul_ne_zero (ne_of_gt hcpos) hv0
  have hscaled :
      positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ)
        = c.1 • v := by
    simpa [v] using positiveMeasureToEuclidean_scale (α := α) (c : ℝ) hcpos μ
  have hmkScaled :
      Projectivization.mk ℝ
          (positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ))
          (positiveMeasureToEuclidean_ne_zero (α := α) (PositiveMeasure.scale c.1 c.2 μ))
        =
      Projectivization.mk ℝ (c.1 • v) hcv0 := by
    apply (Projectivization.mk_eq_mk_iff ℝ
      (positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ))
      (c.1 • v)
      (positiveMeasureToEuclidean_ne_zero (α := α) (PositiveMeasure.scale c.1 c.2 μ))
      hcv0).2
    refine ⟨1, ?_⟩
    simpa [one_smul] using hscaled.symm
  have hmkRay :
      Projectivization.mk ℝ (c.1 • v) hcv0 = Projectivization.mk ℝ v hv0 := by
    apply (Projectivization.mk_eq_mk_iff ℝ (c.1 • v) v hcv0 hv0).2
    refine ⟨Units.mk0 c.1 (ne_of_gt hcpos), ?_⟩
    simp
  have hmkGoal :
      Projectivization.mk ℝ v hv0 =
        Projectivization.mk ℝ
          (positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ))
          (positiveMeasureToEuclidean_ne_zero (α := α) (PositiveMeasure.scale c.1 c.2 μ)) := by
    calc
      Projectivization.mk ℝ v hv0 = Projectivization.mk ℝ (c.1 • v) hcv0 := hmkRay.symm
      _ =
        Projectivization.mk ℝ
          (positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ))
          (positiveMeasureToEuclidean_ne_zero (α := α) (PositiveMeasure.scale c.1 c.2 μ)) := hmkScaled.symm
  simpa [v] using hmkGoal

/--
Bridge map from the legacy positive-measure ray quotient to cone-interior projective states.
-/
noncomputable def projectiveClassToConeInteriorStateSpace :
    PositiveMeasure.Proj (α := α) →
      ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) :=
  Quotient.lift
    (positiveMeasureToConeInteriorRay (α := α))
    (fun _ _ h => positiveMeasureToConeInteriorRay_sameRay (α := α) h)

@[simp] lemma projectiveClassToConeInteriorStateSpace_mk (μ : PositiveMeasure α ℝ) :
    projectiveClassToConeInteriorStateSpace (α := α) (Quotient.mk _ μ) =
      positiveMeasureToConeInteriorRay (α := α) μ := rfl

lemma projectiveClassToConeInteriorStateSpace_injective :
    Function.Injective (projectiveClassToConeInteriorStateSpace (α := α)) := by
  intro q₁ q₂ hq
  revert hq
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro μ ν hμν
  apply Quotient.sound
  have hmk :
      Projectivization.mk ℝ
        (positiveMeasureToEuclidean (α := α) μ)
        (positiveMeasureToEuclidean_ne_zero (α := α) μ)
      =
      Projectivization.mk ℝ
        (positiveMeasureToEuclidean (α := α) ν)
        (positiveMeasureToEuclidean_ne_zero (α := α) ν) := by
    exact congrArg Subtype.val hμν
  rcases (Projectivization.mk_eq_mk_iff ℝ
    (positiveMeasureToEuclidean (α := α) μ)
    (positiveMeasureToEuclidean (α := α) ν)
    (positiveMeasureToEuclidean_ne_zero (α := α) μ)
    (positiveMeasureToEuclidean_ne_zero (α := α) ν)).1 hmk with ⟨u, hu⟩
  obtain ⟨i⟩ := ‹Nonempty α›
  have hcoord : (u : ℝ) * ν i = μ i := by
    have := congrArg (fun x => x i) hu
    simpa [positiveMeasureToEuclidean_apply] using this
  have hmul : 0 < ν i * (u : ℝ) := by
    have hmul' : 0 < (u : ℝ) * ν i := by simpa [hcoord] using μ.pos i
    simpa [mul_comm] using hmul'
  have hu_pos : 0 < (u : ℝ) := pos_of_mul_pos_right hmul (le_of_lt (ν.pos i))
  refine ⟨⟨(u : ℝ)⁻¹, inv_pos.mpr hu_pos⟩, ?_⟩
  ext a
  have hcoordA : (u : ℝ) * ν a = μ a := by
    have := congrArg (fun x => x a) hu
    simpa [positiveMeasureToEuclidean_apply] using this
  have hsolve' : (u : ℝ)⁻¹ * μ a = ν a :=
    (inv_mul_eq_iff_eq_mul₀ (Units.ne_zero u)).2 hcoordA.symm
  have hsolve : ν a = (u : ℝ)⁻¹ * μ a := hsolve'.symm
  simpa [PositiveMeasure.scale_apply] using hsolve.symm

lemma projectiveClassToConeInteriorStateSpace_surjective :
    Function.Surjective (projectiveClassToConeInteriorStateSpace (α := α)) := by
  intro s
  rcases s with ⟨ℓ, hℓ⟩
  rcases hℓ with ⟨v, hv0, hvInt, hmk⟩
  let x : {x : EuclideanSpace ℝ α // x ∈ interior (positiveOrthantCone (α := α) : Set (EuclideanSpace ℝ α))} :=
    ⟨v, by simpa [positiveOrthant] using hvInt⟩
  let μ : PositiveMeasure α ℝ := interiorToPositiveMeasure (α := α) x
  refine ⟨Quotient.mk _ μ, ?_⟩
  apply Subtype.ext
  have hμv : positiveMeasureToEuclidean (α := α) μ = v := by
    ext i
    simp [μ, x, interiorToPositiveMeasure, positiveMeasureToEuclidean]
  have hmkμv :
      Projectivization.mk ℝ
          (positiveMeasureToEuclidean (α := α) μ)
          (positiveMeasureToEuclidean_ne_zero (α := α) μ)
        =
      Projectivization.mk ℝ v hv0 := by
    apply (Projectivization.mk_eq_mk_iff ℝ
      (positiveMeasureToEuclidean (α := α) μ)
      v
      (positiveMeasureToEuclidean_ne_zero (α := α) μ)
      hv0).2
    refine ⟨1, ?_⟩
    simpa [one_smul] using hμv.symm
  exact hmkμv.trans hmk

lemma projectiveClassToConeInteriorStateSpace_bijective :
    Function.Bijective (projectiveClassToConeInteriorStateSpace (α := α)) :=
  ⟨projectiveClassToConeInteriorStateSpace_injective (α := α),
    projectiveClassToConeInteriorStateSpace_surjective (α := α)⟩

/-- Canonical equivalence between legacy projective classes and cone-interior rays. -/
noncomputable def projectiveEquivConeInteriorStateSpace :
    PositiveMeasure.Proj (α := α) ≃
      ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) :=
  Equiv.ofBijective
    (projectiveClassToConeInteriorStateSpace (α := α))
    (projectiveClassToConeInteriorStateSpace_bijective (α := α))

/-- Inverse bridge map from cone-interior rays back to legacy projective classes. -/
noncomputable def coneInteriorStateSpaceToProjectiveClass :
    ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) →
      PositiveMeasure.Proj (α := α) :=
  (projectiveEquivConeInteriorStateSpace (α := α)).symm

@[simp] lemma coneInteriorStateSpaceToProjectiveClass_apply
    (s : ConeInteriorStateSpace ((positiveOrthant (α := α)).cone)) :
    projectiveClassToConeInteriorStateSpace (α := α)
      (coneInteriorStateSpaceToProjectiveClass (α := α) s) = s := by
  change (projectiveEquivConeInteriorStateSpace (α := α))
      ((projectiveEquivConeInteriorStateSpace (α := α)).symm s) = s
  exact (projectiveEquivConeInteriorStateSpace (α := α)).apply_symm_apply s

@[simp] lemma coneInteriorStateSpaceToProjectiveClass_projectiveClass
    (q : PositiveMeasure.Proj (α := α)) :
    coneInteriorStateSpaceToProjectiveClass (α := α)
      (projectiveClassToConeInteriorStateSpace (α := α) q) = q := by
  change (projectiveEquivConeInteriorStateSpace (α := α)).symm
      ((projectiveEquivConeInteriorStateSpace (α := α)) q) = q
  exact (projectiveEquivConeInteriorStateSpace (α := α)).symm_apply_apply q

end ProjectiveBridge
end OrthantBridge

end InfoGeometry.Projective
