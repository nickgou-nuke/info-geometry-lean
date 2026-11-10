/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedTilt
import InfoGeometry.Canonical.JointCentralizerDynamics

/-!
# The actual Cartan flow of additively tilted seeds

The existing exponential conjugation scales the seed components and fixes
the common-commutant perturbation. Its action is affine on these tilted
generators. Every element of the tilted common commutant is still fixed.

This is a real Banach-algebra similarity, not a new tower shift or a
state-dependent modular flow.
-/

noncomputable section

namespace InfoGeometry.Canonical.JointCentralizerTilt

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Lie.ConcreteSplitCartan
open InfoGeometry.Canonical.JointCentralizerDynamics

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {d b z : A}

/-- The perturbation has zero weight under the actual Cartan exponential. -/
theorem splitCartan_conjugates_tilt_seed (h : IsDualSeedPair d b)
    (hz : z ∈ Subalgebra.centralizer ℝ ({d, b} : Set A)) (ε t : ℝ) :
    let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
    (u : A) * (d + ε • z) * (↑(u⁻¹) : A) = Real.exp (2 * t) • d + ε • z := by
  dsimp only
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [splitCartan_conjugates_seed h t, splitCartan_fixes_jointCentralizer d b z hz t]

/-- The partner's seed term has the opposite weight; the same perturbation is fixed. -/
theorem splitCartan_conjugates_tilt_partner (h : IsDualSeedPair d b)
    (hz : z ∈ Subalgebra.centralizer ℝ ({d, b} : Set A)) (ε t : ℝ) :
    let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
    (u : A) * (b - ε • z) * (↑(u⁻¹) : A) = Real.exp (-(2 * t)) • b - ε • z := by
  dsimp only
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [splitCartan_conjugates_partner h t, splitCartan_fixes_jointCentralizer d b z hz t]

/-- The reduced common commutant is fixed pointwise, so this action cannot
exchange distinct elements inside it. -/
theorem splitCartan_fixes_tilt_centralizer (h : IsDualSeedPair d b)
    (hz : z ∈ Subalgebra.centralizer ℝ ({d, b} : Set A))
    {ε : ℝ} (hε : ε ≠ 0) (a : A)
    (ha : a ∈ Subalgebra.centralizer ℝ ({d + ε • z, b - ε • z} : Set A)) (t : ℝ) :
    let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
    (u : A) * a * (↑(u⁻¹) : A) = a := by
  have hc := (Subalgebra.mem_centralizer_iff ℝ).mp hz
  rw [h.centralizer_tilt
    (hc d (Set.mem_insert d {b})).symm
    (hc b (Set.mem_insert_of_mem d (Set.mem_singleton b))).symm hε (by norm_num)] at ha
  exact splitCartan_fixes_jointCentralizer d b a ha.1 t

end InfoGeometry.Canonical.JointCentralizerTilt
