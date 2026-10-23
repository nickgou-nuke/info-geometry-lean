/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Streaming.PositiveBoundaryConditioning
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Scalar routing weights and discrete gauge transport are different data

Weights average values; link isomorphisms transport them between local frames.
A covariance law is proved for their combination. No Christoffel connection,
Lorentzian metric, Green function, or Einstein equation is assumed.
-/

noncomputable section
namespace InfoGeometry.Streaming.GaugeCovariantRouting

open scoped BigOperators
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- Discrete link transport from the frame at j to the frame at i. -/
abbrev Links (ι V : Type*) [AddCommGroup V] [Module ℝ V] := ι → ι → (V ≃ₗ[ℝ] V)

/-- Routing weights average independently transported feature values. -/
def routed (K : Matrix ι ι ℝ) (U : Links ι V) (x : ι → V) : ι → V :=
  fun i => ∑ j, K i j • U i j (x j)

/-- Change the frame at each node without identifying node labels. -/
def gaugeValues (g : ι → V ≃ₗ[ℝ] V) (x : ι → V) : ι → V := fun i => g i (x i)

/-- Standard endpoint action: U'_ij = g_i U_ij g_j inverse. -/
def gaugeLinks (g : ι → V ≃ₗ[ℝ] V) (U : Links ι V) : Links ι V :=
  fun i j => (g j).symm.trans ((U i j).trans (g i))

/-- An actual all-node equivariance theorem for connection-equipped attention. -/
theorem routed_gauge_covariant (K : Matrix ι ι ℝ) (g : ι → V ≃ₗ[ℝ] V)
    (U : Links ι V) (x : ι → V) :
    routed K (gaugeLinks g U) (gaugeValues g x) = gaugeValues g (routed K U x) := by
  funext i
  simp [routed, gaugeLinks, gaugeValues, map_sum]

/-- Two paths need not give the same transport. This is a discrete path defect. -/
def pathDefect (U : Links ι V) (i j k : ι) (v : V) : V :=
  U i j (U j k v) - U i k v

/-- The defect is covariant; it is not the gradient of a scalar softmax weight. -/
theorem pathDefect_covariant (g : ι → V ≃ₗ[ℝ] V) (U : Links ι V)
    (i j k : ι) (v : V) :
    pathDefect (gaugeLinks g U) i j k (g k v) = g i (pathDefect U i j k v) := by
  simp [pathDefect, gaugeLinks]

/-- Links obtained from one global family of frames have zero path defect. -/
def pureFrameLinks (g : ι → V ≃ₗ[ℝ] V) : Links ι V :=
  fun i j => (g j).symm.trans (g i)

theorem pureFrameLinks_flat (g : ι → V ≃ₗ[ℝ] V) (i j k : ι) (v : V) :
    pathDefect (pureFrameLinks g) i j k v = 0 := by
  simp [pathDefect, pureFrameLinks]

omit [Fintype ι] in
/-- On the complete node relation, a flat family is reconstructed from
transport out of any reference node. This is discrete trivialization, not
an assertion about a connection on an arbitrary graph or manifold. -/
theorem flat_links_eq_reference_frames (U : Links ι V) (base : ι)
    (hflat : ∀ i j k v, pathDefect U i j k v = 0) :
    U = pureFrameLinks (fun i => U i base) := by
  funext i j
  apply LinearEquiv.ext
  intro v
  have h := sub_eq_zero.mp (hflat i j base ((U j base).symm v))
  simpa [pureFrameLinks, pathDefect] using h

/-- Pure-frame transport sends a parallel section to the same section after normalized routing. -/
theorem routed_parallel_section (K : Matrix ι ι ℝ) (hK : ∀ i, ∑ j, K i j = 1)
    (g : ι → V ≃ₗ[ℝ] V) (v : V) :
    routed K (pureFrameLinks g) (fun j => g j v) = fun i => g i v := by
  funext i
  simp only [routed, pureFrameLinks, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← Finset.sum_smul, hK, one_smul]

/-- A normalized averaging operator can be singular; it is not automatically parallel transport. -/
def twoPointAverage (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun _ => (x 0 + x 1) / 2

/-- Averaging retains exactly the constant component. -/
theorem twoPointAverage_eq_self_iff (x : Fin 2 → ℝ) :
    twoPointAverage x = x ↔ x 0 = x 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    exact h0.symm.trans h1
  · intro h
    funext i
    fin_cases i <;> simp [twoPointAverage, h]

/-- Its kernel is exactly the antisymmetric component. -/
theorem twoPointAverage_eq_zero_iff (x : Fin 2 → ℝ) :
    twoPointAverage x = 0 ↔ x 0 + x 1 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [twoPointAverage] using h0
  · intro h
    funext i
    simp [twoPointAverage, h]

/-- Mean and contrast together reconstruct the original values. Averaging
alone discards the contrast; it does not define invertible transport. -/
theorem twoPointAverage_reconstruction (x : Fin 2 → ℝ) :
    x = twoPointAverage x + ![(x 0 - x 1) / 2, -(x 0 - x 1) / 2] := by
  funext i
  fin_cases i <;> simp [twoPointAverage] <;> ring

/-- The average is a retraction onto the constant-valued subspace. -/
theorem twoPointAverage_idempotent (x : Fin 2 → ℝ) :
    twoPointAverage (twoPointAverage x) = twoPointAverage x := by
  apply (twoPointAverage_eq_self_iff _).mpr
  rfl

theorem twoPointAverage_not_injective : ¬ Function.Injective twoPointAverage := by
  intro h
  have heq : twoPointAverage ![1, -1] = twoPointAverage 0 := by
    funext i
    norm_num [twoPointAverage]
  have bad := congrArg (fun x : Fin 2 → ℝ => x 0) (h heq)
  norm_num at bad

end InfoGeometry.Streaming.GaugeCovariantRouting
