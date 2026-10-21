/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge

/-!
# Finite diagonal stages inside the Cantor-boundary `L²` space

The finite diagonal observable `f` is represented by its existing cylinder
function on the concrete Bernoulli boundary.  The main theorem identifies the
native complex `L²` inner product with the normalized finite diagonal trace.
This is a stagewise complex-linear, inner-product-preserving map; no source
Hilbert norm, density, or completion claim for the union of the stages is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding

open MeasureTheory
open scoped ENNReal
open InfoGeometry.Analysis.FractalMeasure.Basic
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
open InfoGeometry.Canonical.CantorKMSState

abbrev Boundary := CantorBoundary
abbrev μC : Measure Boundary := fractalMeasure
abbrev L2Boundary := Lp ℂ 2 μC

theorem cylinder_memLp (n : ℕ) (f : DiagAlg n) :
    MemLp (cylinder n f) 2 μC := by
  refine MemLp.of_bound
    (continuous_cylinder n f).aestronglyMeasurable
    (∑ w : BitWord n, ‖f w‖) ?_
  filter_upwards with x
  change ‖f (boundaryPrefix n x)‖ ≤ ∑ w : BitWord n, ‖f w‖
  exact Finset.single_le_sum (fun w _ => norm_nonneg (f w))
    (Finset.mem_univ _)

noncomputable def diagonalCylinderL2 (n : ℕ) : DiagAlg n →ₗ[ℂ] L2Boundary where
  toFun f := (cylinder_memLp n f).toLp
    (InfoGeometry.Canonical.UHFInductiveColimitBoundary.cylinder n f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply (MemLp.toLp_eq_toLp_iff _ _).2
    filter_upwards with x
    simp [cylinder_add]
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply (MemLp.toLp_eq_toLp_iff _ _).2
    filter_upwards with x
    simp [InfoGeometry.Canonical.UHFInductiveColimitBoundary.cylinder,
      smul_eq_mul]

@[simp] theorem diagonalCylinderL2_coeFn (n : ℕ) (f : DiagAlg n) :
    ((diagonalCylinderL2 n f : L2Boundary) : Boundary → ℂ) =ᵐ[μC]
      cylinder n f :=
  MemLp.coeFn_toLp (cylinder_memLp n f)

/-- The boundary `L²` representations respect the canonical successor maps. -/
theorem diagonalCylinderL2_compatible_succ (n : ℕ) (f : DiagAlg n) :
    diagonalCylinderL2 (n + 1) (diagEmbedSucc n f) =
      diagonalCylinderL2 n f := by
  change
    (cylinder_memLp (n + 1) (diagEmbedSucc n f)).toLp
        (cylinder (n + 1) (diagEmbedSucc n f)) =
      (cylinder_memLp n f).toLp (cylinder n f)
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x =>
    congrFun (cylinder_compatible_succ n f) x

theorem boundaryPrefix_preimage_singleton (n : ℕ) (w : BitWord n) :
    boundaryPrefix n ⁻¹' ({w} : Set (BitWord n)) =
      InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n
        w := rfl

theorem boundaryPrefix_map_singleton (n : ℕ) (w : BitWord n) :
    Measure.map (boundaryPrefix n) μC ({w} : Set (BitWord n)) =
      (1 / 2 : ℝ≥0∞) ^ n := by
  rw [Measure.map_apply (continuous_boundaryPrefix n).measurable
    (measurableSet_singleton w)]
  rw [boundaryPrefix_preimage_singleton]
  have hset :
      InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n
          w =
        InfoGeometry.Analysis.FractalMeasure.Basic.cylinderSet
          (Finset.range n)
            (fun i => if h : i < n then w ⟨i, h⟩ else false) := by
    ext x
    simp only [InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet,
      InfoGeometry.Analysis.FractalMeasure.Basic.cylinderSet,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_range]
    change boundaryPrefix n x = w ↔
      ∀ i ∈ Finset.range n,
        x i = if h : i < n then w ⟨i, h⟩ else false
    constructor
    · intro h i hi
      have hi' := congrFun h ⟨i, Finset.mem_range.mp hi⟩
      rw [dif_pos (Finset.mem_range.mp hi)]
      simpa [boundaryPrefix] using hi'
    · intro h
      funext i
      exact h i.1 (Finset.mem_range.mpr i.2) |>.trans (by simp [i.2])
  rw [hset, measure_cylinderSet]
  simp

theorem diagonalCylinderL2_inner (n : ℕ) (f g : DiagAlg n) :
    inner ℂ (diagonalCylinderL2 n f) (diagonalCylinderL2 n g) =
      DiagTrace n (fun w => star (f w) * g w) := by
  rw [L2.inner_def]
  have hcoef := diagonalCylinderL2_coeFn n f
  have hcoeg := diagonalCylinderL2_coeFn n g
  have hinner :
      (fun a : Boundary =>
        inner ℂ (((diagonalCylinderL2 n f : L2Boundary) : Boundary → ℂ) a)
          (((diagonalCylinderL2 n g : L2Boundary) : Boundary → ℂ) a)) =ᵐ[μC]
        (fun a : Boundary =>
          star (f (boundaryPrefix n a)) * g (boundaryPrefix n a)) := by
    filter_upwards [hcoef, hcoeg] with a hfa hga
    rw [hfa, hga]
    simpa [InfoGeometry.Canonical.UHFInductiveColimitBoundary.cylinder,
      inner, mul_comm]
  rw [integral_congr_ae hinner]
  have hint : Integrable (fun w : BitWord n => star (f w) * g w)
      (Measure.map (boundaryPrefix n) μC) := Integrable.of_finite
  have hmeas : AEStronglyMeasurable
      (fun w : BitWord n => star (f w) * g w)
      (Measure.map (boundaryPrefix n) μC) := hint.aestronglyMeasurable
  have hmap : AEMeasurable (boundaryPrefix n) μC :=
    (continuous_boundaryPrefix n).measurable.aemeasurable
  have hintegral :=
    integral_map hmap hmeas
  rw [← hintegral]
  rw [integral_fintype hint]
  unfold DiagTrace
  simp_rw [Measure.real_def, boundaryPrefix_map_singleton]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  norm_num [ENNReal.toReal_ofNat]

end InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
