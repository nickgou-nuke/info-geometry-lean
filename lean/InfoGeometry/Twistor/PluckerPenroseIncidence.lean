/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerInfinityChart
import InfoGeometry.Twistor.TwoTwistorPlucker
import InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency

/-!
# Plücker graph coordinates and native Penrose incidence

The repository incidence map is `(i Xπ,π)`.  An explicit complex linear
equivalence converts it to the graph convention `(Xπ,π)` before taking
Plücker coordinates.  Thus the determinant interval is connected to the
existing incidence subspaces, including both directions of the nullness /
nontrivial-intersection equivalence.

The final sign theorem records what happens if the native `i` factor is left
in the frame.  No real structure is selected by this convention adapter.
-/

namespace InfoGeometry.Twistor.PluckerPenroseIncidence

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorPlucker
open InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency
open InfoGeometry.Twistor.PluckerInfinityChart

/-- Remove the repository's `i` incidence factor by an actual linear equivalence. -/
def penroseToGraph : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (-Complex.I • Z.1, Z.2)
  invFun Z := (Complex.I • Z.1, Z.2)
  left_inv Z := by rcases Z with ⟨ω, π⟩; simp [smul_smul]
  right_inv Z := by rcases Z with ⟨ω, π⟩; simp [smul_smul]
  map_add' Z W := by simp [smul_add]
  map_smul' c Z := by simp [smul_smul, mul_comm]

@[simp] theorem penroseToGraph_apply (Z : Twistor4) :
    penroseToGraph Z = (-Complex.I • Z.1, Z.2) := rfl

@[simp] theorem penroseToGraph_symm_apply (Z : Twistor4) :
    penroseToGraph.symm Z = (Complex.I • Z.1, Z.2) := rfl

/-- The native incidence map transported to the graph convention. -/
def graphIncidence (X : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Twistor4 :=
  penroseToGraph.toLinearMap.comp (incidenceLinearMap X)

@[simp] theorem graphIncidence_apply (X : ComplexSpacetime) (π : Spinor2) :
    graphIncidence X π = (X.mulVec π, π) := by
  simp [graphIncidence, incidenceLinearMap_apply, smul_smul]

theorem graphIncidence_injective (X : ComplexSpacetime) :
    Function.Injective (graphIncidence X) :=
  penroseToGraph.injective.comp (incidenceLinearMap_injective X)

theorem twistorProjectiveVector_graph_first (X : ComplexSpacetime) :
    twistorProjectiveVector (graphIncidence X ![1, 0]) = graphFirst X := by
  simp [twistorProjectiveVector, graphFirst, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

theorem twistorProjectiveVector_graph_second (X : ComplexSpacetime) :
    twistorProjectiveVector (graphIncidence X ![0, 1]) = graphSecond X := by
  simp [twistorProjectiveVector, graphSecond, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- The graph chart is exactly the established Plücker readout of its two twistors. -/
theorem graphPlucker_eq_twistorPairPlucker (X : ComplexSpacetime) :
    graphPlucker X = twistorPairPlucker
      (graphIncidence X ![1, 0]) (graphIncidence X ![0, 1]) := by
  unfold twistorPairPlucker graphPlucker
  rw [twistorProjectiveVector_graph_first, twistorProjectiveVector_graph_second]

theorem incidence_at_snd_of_mem (X : ComplexSpacetime) (Z : Twistor4)
    (hZ : Z ∈ incidencePlane X) : incidenceLinearMap X Z.2 = Z := by
  rcases hZ with ⟨π, rfl⟩
  rfl

theorem snd_ne_zero_of_mem (X : ComplexSpacetime) (Z : Twistor4)
    (hZ : Z ∈ incidencePlane X) (hne : Z ≠ 0) : Z.2 ≠ 0 := by
  intro hπ
  apply hne
  calc
    Z = incidenceLinearMap X Z.2 := (incidence_at_snd_of_mem X Z hZ).symm
    _ = 0 := by rw [hπ, map_zero]

/-- Two native incidence planes share a nonzero twistor exactly when the
matrix difference has a nonzero kernel. -/
theorem det_sub_eq_zero_iff_shared_nonzero_twistor (X Y : ComplexSpacetime) :
    (X - Y).det = 0 ↔
      ∃ Z : Twistor4, Z ≠ 0 ∧ Z ∈ incidencePlane X ∧ Z ∈ incidencePlane Y := by
  constructor
  · intro h
    obtain ⟨π, hπ, hker⟩ := (det_zero_iff_exists_nonzero_kernel (X - Y)).mp h
    have hXY : X.mulVec π = Y.mulVec π := by
      apply sub_eq_zero.mp
      simpa only [Matrix.sub_mulVec] using hker
    refine ⟨incidenceLinearMap X π, ?_, ⟨π, rfl⟩, ⟨π, ?_⟩⟩
    · intro hzero
      exact hπ (congrArg Prod.snd hzero)
    · simp only [incidenceLinearMap_apply, omegaLinearMap_apply, hXY]
  · rintro ⟨Z, hne, hX, hY⟩
    exact det_sub_eq_zero_of_shared_nonzero_twistor Z X Y
      (snd_ne_zero_of_mem X Z hX hne)
      (incidence_at_snd_of_mem X Z hX) (incidence_at_snd_of_mem Y Z hY)

theorem det_sub_eq_zero_iff_incidencePlane_inf_ne_bot (X Y : ComplexSpacetime) :
    (X - Y).det = 0 ↔ incidencePlane X ⊓ incidencePlane Y ≠ ⊥ := by
  rw [det_sub_eq_zero_iff_shared_nonzero_twistor]
  constructor
  · rintro ⟨Z, hne, hX, hY⟩
    exact (Submodule.ne_bot_iff _).2 ⟨Z, ⟨hX, hY⟩, hne⟩
  · intro h
    obtain ⟨Z, hZ, hne⟩ := (Submodule.ne_bot_iff _).1 h
    exact ⟨Z, hne, hZ.1, hZ.2⟩

/-- Plücker-polar nullness is exactly nontrivial intersection of the original
Penrose subspaces, rather than only an equality of coordinate expressions. -/
theorem kleinPolar_graphPlucker_zero_iff_incidencePlane_inf_ne_bot
    (X Y : ComplexSpacetime) :
    kleinPolar (graphPlucker X) (graphPlucker Y) = 0 ↔
      incidencePlane X ⊓ incidencePlane Y ≠ ⊥ := by
  rw [kleinPolar_graphPlucker, det_sub_eq_zero_iff_incidencePlane_inf_ne_bot]

/-- The original two-frame Plücker vector, retaining the native incidence factor. -/
def penroseFramePlucker (X : ComplexSpacetime) : Plucker6 ℂ :=
  twistorPairPlucker (incidenceLinearMap X ![1, 0]) (incidenceLinearMap X ![0, 1])

theorem incidenceLinearMap_eq_graphIncidence_I (X : ComplexSpacetime) (π : Spinor2) :
    incidenceLinearMap X π = graphIncidence (Complex.I • X) π := by
  simp [incidenceLinearMap_apply, Matrix.smul_mulVec]

theorem penroseFramePlucker_eq_graphPlucker_I (X : ComplexSpacetime) :
    penroseFramePlucker X = graphPlucker (Complex.I • X) := by
  simp only [penroseFramePlucker, incidenceLinearMap_eq_graphIncidence_I,
    ← graphPlucker_eq_twistorPairPlucker]

/-- Retaining the native `i` factor reverses this chosen Klein-polar sign. -/
theorem kleinPolar_penroseFramePlucker (X Y : ComplexSpacetime) :
    kleinPolar (penroseFramePlucker X) (penroseFramePlucker Y) = -(X - Y).det := by
  simp only [penroseFramePlucker_eq_graphPlucker_I]
  rw [kleinPolar_graphPlucker, ← smul_sub, Matrix.det_smul]
  norm_num

end InfoGeometry.Twistor.PluckerPenroseIncidence
