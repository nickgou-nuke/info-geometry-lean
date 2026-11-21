/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorIncidence
import InfoGeometry.Krein.Metric
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Real phase-compatible null incidence graphs

The existing real incidence submodule is the graph `(A π, π)`.  We use the
existing coordinate Hessian/Krein form, not a new pairing.  Total isotropy
of this graph is equivalent to skewness of `A`; invariance under the
diagonal real phase operator is equivalent to commutation with that phase.

For a skew phase `J` with `J² = -1`, these conditions reconstruct the unique
inner-product-symmetric, phase-commuting operator `X` with `A = J * X`.
The inverse is explicitly `X = -(J * A)`.  Operators `X` and `Y` are not
required to commute with one another.  The statements use arbitrary real
inner-product spaces and algebraic linear maps; no boundedness, completeness,
finite-dimensionality, or analytic adjoint is assumed.

This is the algebraic graph-chart part of the incidence geometry in
Penrose--MacCallum, sections 2.1--2.2, especially equations (2.1), (2.11),
and (2.12).  The existing `translation` is the active plus-sign shear;
the paper's passive change of origin uses its inverse.  No Lorentzian
soldering, complex projective quotient, or Penrose transform is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorIsotropicGraph

open RealTwistorIncidence
open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The existing neutral form evaluated on two vectors of an incidence graph. -/
theorem hessian_incidenceMap (A : Module.End ℝ E) (u v : E) :
    hessian_indefinite_formCoord (incidenceMap A u) (incidenceMap A v) =
      ⟪A u, v⟫_ℝ + ⟪A v, u⟫_ℝ := rfl

/-- Total graph isotropy is exactly skewness for the real inner product. -/
theorem incidenceSpace_isotropic_iff (A : Module.End ℝ E) :
    (∀ z ∈ incidenceSpace A, ∀ w ∈ incidenceSpace A,
      hessian_indefinite_formCoord z w = 0) ↔
      ∀ u v : E, ⟪A u, v⟫_ℝ = -⟪u, A v⟫_ℝ := by
  constructor
  · intro h u v
    have huv := h (incidenceMap A u) ⟨u, rfl⟩ (incidenceMap A v) ⟨v, rfl⟩
    rw [hessian_incidenceMap, real_inner_comm u (A v)] at huv
    exact eq_neg_of_add_eq_zero_left huv
  · intro h z hz w hw
    rcases hz with ⟨u, rfl⟩
    rcases hw with ⟨v, rfl⟩
    rw [hessian_incidenceMap, h u v, real_inner_comm (A v) u]
    exact neg_add_cancel _

/-- Diagonal phase invariance of the native graph detects commutation. -/
theorem incidenceSpace_phase_invariant_iff (J A : Module.End ℝ E) :
    (∀ z ∈ incidenceSpace A, J.prodMap J z ∈ incidenceSpace A) ↔
      Commute J A := by
  constructor
  · intro h
    apply LinearMap.ext
    intro u
    exact (mem_incidenceSpace A _).mp (h (incidenceMap A u) ⟨u, rfl⟩)
  · intro h z hz
    rcases hz with ⟨u, rfl⟩
    apply (mem_incidenceSpace A _).mpr
    exact LinearMap.congr_fun h.eq u

/-- The graph term is the exact defect of neutral-form preservation by a shear. -/
theorem hessian_translation_defect (A : Module.End ℝ E) (z w : E × E) :
    hessian_indefinite_formCoord (translation A z) (translation A w) =
      hessian_indefinite_formCoord z w +
        hessian_indefinite_formCoord (incidenceMap A z.2) (incidenceMap A w.2) := by
  change ⟪z.1 + A z.2, w.2⟫_ℝ + ⟪w.1 + A w.2, z.2⟫_ℝ =
    (⟪z.1, w.2⟫_ℝ + ⟪w.1, z.2⟫_ℝ) + (⟪A z.2, w.2⟫_ℝ + ⟪A w.2, z.2⟫_ℝ)
  simp only [inner_add_left]
  exact add_add_add_comm _ _ _ _

/-- The existing translation is a neutral isometry precisely for skew operators. -/
theorem translation_preserves_hessian_iff (A : Module.End ℝ E) :
    (∀ z w : E × E,
      hessian_indefinite_formCoord (translation A z) (translation A w) =
        hessian_indefinite_formCoord z w) ↔
      ∀ u v : E, ⟪A u, v⟫_ℝ = -⟪u, A v⟫_ℝ := by
  constructor
  · intro h u v
    have huv := h (0, u) (0, v)
    change ⟪0 + A u, v⟫_ℝ + ⟪0 + A v, u⟫_ℝ = ⟪(0 : E), v⟫_ℝ + ⟪(0 : E), u⟫_ℝ at huv
    simp only [zero_add, inner_zero_left] at huv
    rw [real_inner_comm u (A v)] at huv
    exact eq_neg_of_add_eq_zero_left huv
  · intro h z w
    rw [hessian_translation_defect,
      (incidenceSpace_isotropic_iff A).mpr h
        (incidenceMap A z.2) ⟨z.2, rfl⟩ (incidenceMap A w.2) ⟨w.2, rfl⟩,
      add_zero]

/-- A skew graph equals its neutral orthogonal complement, stated pointwise. -/
theorem mem_incidenceSpace_iff_orthogonal (A : Module.End ℝ E)
    (hA : ∀ u v : E, ⟪A u, v⟫_ℝ = -⟪u, A v⟫_ℝ) (z : E × E) :
    z ∈ incidenceSpace A ↔
      ∀ w ∈ incidenceSpace A, hessian_indefinite_formCoord z w = 0 := by
  constructor
  · intro hz
    exact (incidenceSpace_isotropic_iff A).mpr hA z hz
  · intro h
    apply (mem_incidenceSpace A z).mpr
    apply ext_inner_right ℝ
    intro u
    have hu := h (incidenceMap A u) ⟨u, rfl⟩
    change ⟪z.1, u⟫_ℝ + ⟪A u, z.2⟫_ℝ = 0 at hu
    rw [hA u z.2, real_inner_comm (A z.2) u] at hu
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hu)

/-- Maximal total isotropy follows without a finite-dimensional dimension count. -/
theorem incidenceSpace_maximal_isotropic (A : Module.End ℝ E)
    (hA : ∀ u v : E, ⟪A u, v⟫_ℝ = -⟪u, A v⟫_ℝ)
    (L : Submodule ℝ (E × E)) (hAL : incidenceSpace A ≤ L)
    (hL : ∀ z ∈ L, ∀ w ∈ L, hessian_indefinite_formCoord z w = 0) :
    L = incidenceSpace A := by
  apply le_antisymm _ hAL
  intro z hz
  apply (mem_incidenceSpace_iff_orthogonal A hA z).mpr
  intro w hw
  exact hL z hz w (hAL hw)

/-- Pointwise square-minus-one law for the supplied real phase. -/
theorem phase_sq_apply (J : Module.End ℝ E) (hJ : J * J = -1) (u : E) :
    J (J u) = -u := by
  simpa only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply]
    using LinearMap.congr_fun hJ u

/-- Square minus one makes the phase injective on the original real carrier. -/
theorem phase_injective (J : Module.End ℝ E) (hJ : J * J = -1) :
    Function.Injective J := by
  intro u v huv
  have h := congrArg J huv
  simpa only [phase_sq_apply J hJ, neg_inj] using h

/-- Multiplying a symmetric phase-commuting operator by the skew phase is skew. -/
theorem phase_mul_skew (J X : Module.End ℝ E)
    (hJ : ∀ u v : E, ⟪J u, v⟫_ℝ = -⟪u, J v⟫_ℝ)
    (hX : X.IsSymmetric) (hJX : Commute J X) :
    ∀ u v : E, ⟪(J * X) u, v⟫_ℝ = -⟪u, (J * X) v⟫_ℝ := by
  intro u v
  change ⟪J (X u), v⟫_ℝ = -⟪u, J (X v)⟫_ℝ
  rw [hJ (X u) v, hX u (J v)]
  exact congrArg (fun t => -⟪u, t⟫_ℝ) (LinearMap.congr_fun hJX.eq v).symm

/-- The inverse phase rotation produces a symmetric operator from a skew graph. -/
theorem reconstructed_isSymmetric (J A : Module.End ℝ E)
    (hJ : ∀ u v : E, ⟪J u, v⟫_ℝ = -⟪u, J v⟫_ℝ)
    (hA : ∀ u v : E, ⟪A u, v⟫_ℝ = -⟪u, A v⟫_ℝ)
    (hJA : Commute J A) : (-(J * A)).IsSymmetric := by
  intro u v
  change ⟪-(J (A u)), v⟫_ℝ = ⟪u, -(J (A v))⟫_ℝ
  rw [inner_neg_left, hJ (A u) v, neg_neg, hA u (J v), inner_neg_right]
  exact congrArg (fun t => -⟪u, t⟫_ℝ) (LinearMap.congr_fun hJA.eq v).symm

/-- Reconstruction preserves commutation with the phase. -/
theorem reconstructed_commutes (J A : Module.End ℝ E) (hJA : Commute J A) :
    Commute J (-(J * A)) := by
  change J * (-(J * A)) = (-(J * A)) * J
  rw [mul_neg, neg_mul, mul_assoc J A J, hJA.eq]

/-- Explicit reconstruction is a right inverse to the incidence phase rotation. -/
theorem phase_mul_reconstruction (J A : Module.End ℝ E) (hJ : J * J = -1) :
    J * (-(J * A)) = A := by
  rw [mul_neg, ← mul_assoc, hJ, neg_one_mul, neg_neg]

/-- Explicit reconstruction is also a left inverse, giving uniqueness. -/
theorem reconstruction_phase_mul (J X : Module.End ℝ E) (hJ : J * J = -1) :
    -(J * (J * X)) = X := by
  rw [← mul_assoc, hJ, neg_one_mul, neg_neg]

/-- Classify exactly the phase-invariant, totally null graphs in the real chart. -/
theorem isotropic_phase_invariant_iff_existsUnique (J A : Module.End ℝ E)
    (hJsq : J * J = -1)
    (hJskew : ∀ u v : E, ⟪J u, v⟫_ℝ = -⟪u, J v⟫_ℝ) :
    ((∀ z ∈ incidenceSpace A, ∀ w ∈ incidenceSpace A,
        hessian_indefinite_formCoord z w = 0) ∧
      (∀ z ∈ incidenceSpace A, J.prodMap J z ∈ incidenceSpace A)) ↔
      ∃! X : Module.End ℝ E, X.IsSymmetric ∧ Commute J X ∧ A = J * X := by
  rw [incidenceSpace_isotropic_iff, incidenceSpace_phase_invariant_iff]
  constructor
  · rintro ⟨hA, hJA⟩
    refine ⟨-(J * A), ⟨reconstructed_isSymmetric J A hJskew hA hJA,
      reconstructed_commutes J A hJA, (phase_mul_reconstruction J A hJsq).symm⟩, ?_⟩
    intro X hX
    rw [hX.2.2, reconstruction_phase_mul J X hJsq]
  · rintro ⟨X, ⟨hX, hJX, rfl⟩, _⟩
    refine ⟨phase_mul_skew J X hJskew hX hJX, ?_⟩
    change J * (J * X) = (J * X) * J
    calc
      J * (J * X) = J * (X * J) := congrArg (fun T => J * T) hJX.eq
      _ = (J * X) * J := (mul_assoc J X J).symm

/-- The same classification for all subspaces in the transverse graph chart.
The second projection is required to be bijective, not merely injective. -/
theorem transverse_isotropic_phase_iff_existsUnique
    (J : Module.End ℝ E) (hJsq : J * J = -1)
    (hJskew : ∀ u v : E, ⟪J u, v⟫_ℝ = -⟪u, J v⟫_ℝ)
    (L : Submodule ℝ (E × E))
    (hL : Function.Bijective ((LinearMap.snd ℝ E E).comp L.subtype)) :
    ((∀ z ∈ L, ∀ w ∈ L, hessian_indefinite_formCoord z w = 0) ∧
      (∀ z ∈ L, J.prodMap J z ∈ L)) ↔
      ∃! X : Module.End ℝ E,
        X.IsSymmetric ∧ Commute J X ∧ incidenceSpace (J * X) = L := by
  obtain ⟨A, hA, _⟩ := existsUnique_incidenceSpace_of_bijective_snd L hL
  rw [← hA]
  refine (isotropic_phase_invariant_iff_existsUnique J A hJsq hJskew).trans ?_
  apply existsUnique_congr
  intro X
  constructor
  · rintro ⟨hX, hJX, hAX⟩
    exact ⟨hX, hJX, congrArg incidenceSpace hAX.symm⟩
  · rintro ⟨hX, hJX, hXA⟩
    exact ⟨hX, hJX, (incidenceSpace_injective hXA).symm⟩

/-- Cancel the faithful real phase in the already-owned intersection criterion. -/
theorem phase_graph_shared_nonzero_iff (J X Y : Module.End ℝ E)
    (hJ : J * J = -1) :
    (∃ z : E × E, z ≠ 0 ∧ z ∈ incidenceSpace (J * X) ∧
      z ∈ incidenceSpace (J * Y)) ↔
      ∃ u : E, u ≠ 0 ∧ (X - Y) u = 0 := by
  rw [shared_nonzero_twistor_iff]
  constructor
  · rintro ⟨u, hu, hker⟩
    refine ⟨u, hu, ?_⟩
    apply phase_injective J hJ
    simpa only [map_sub, map_zero, LinearMap.sub_apply, Module.End.mul_apply] using hker
  · rintro ⟨u, hu, hker⟩
    refine ⟨u, hu, ?_⟩
    simpa only [map_sub, map_zero, LinearMap.sub_apply, Module.End.mul_apply]
      using congrArg J hker

end InfoGeometry.Twistor.RealTwistorIsotropicGraph
