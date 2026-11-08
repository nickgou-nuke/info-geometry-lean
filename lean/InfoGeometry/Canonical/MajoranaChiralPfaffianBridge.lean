/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
import InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
import InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure

/-!
# Explicit CAR, finite boundary zero modes, and Pfaffian phase

This module is a small owner-aligned bridge.  It keeps distinct:
* the null CAR pair and its real split-Clifford generators;
* kernel vectors of the finite BdG Hamiltonian;
* the bulk high-symmetry Pfaffian product.

The final theorem therefore packages existing proofs without asserting that a
bulk Pfaffian zero is the same object as a finite boundary kernel vector.
-/

namespace InfoGeometry.Canonical.MajoranaChiralPfaffianBridge

open Matrix
open InfoGeometry.MajoranaPfaffianNaturalClosure
open InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
open InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
open InfoGeometry.Canonical.KitaevChainMajoranaZeroModes

/-- The real CAR null pair reconstructs the two split-Clifford generators. -/
theorem real_car_pair_reconstructs_split_generators :
    annihilationR * annihilationR = 0 ∧
    creationR * creationR = 0 ∧
    annihilationR * creationR + creationR * annihilationR = (1 : M2R) ∧
    annihilationR + creationR = splitPos ∧
    annihilationR - creationR = splitNeg := by
  refine ⟨annihilationR_sq, creationR_sq, real_CAR, ?_, ?_⟩
  · rw [annihilationR_eq_null, creationR_eq_null]
    module
  · rw [annihilationR_eq_null, creationR_eq_null]
    module

/-- At the sweet spot, both explicit finite boundary vectors are BdG zero modes,
while the bulk high-symmetry Pfaffian product is strictly negative. -/
theorem sweet_spot_boundary_zero_modes_with_pfaffian_phase
    (t : ℝ) (ht : 0 < t) :
    (kitaevSweetSpot4 t).mulVec majoranaZeroModeLeft = 0 ∧
    (kitaevSweetSpot4 t).mulVec majoranaZeroModeRight = 0 ∧
    kitaevPfaffianProduct 0 t < 0 := by
  refine ⟨left_majorana_zero_mode_energy t, right_majorana_zero_mode_energy t, ?_⟩
  apply topological_phase_pfaffian_neg
  nlinarith

/-- The sweet-spot BdG operator has an explicit nonzero boundary kernel
witness. -/
theorem sweet_spot_boundary_has_nontrivial_kernel (t : ℝ) :
    ∃ v : Vec4C, v ≠ 0 ∧ (kitaevSweetSpot4 t).mulVec v = 0 := by
  refine ⟨majoranaZeroModeLeft, ?_, left_majorana_zero_mode_energy t⟩
  intro hzero
  have hcoord := congrFun hzero 0
  norm_num [majoranaZeroModeLeft] at hcoord

/-- The finite CAR-to-Majorana bridge packages the four kernel-checked layers:
the real null CAR pair, its split generators, the two finite-chain boundary
zero modes, and the Pfaffian criterion for a nontrivial Majorana block kernel.
The bulk phase sign and the finite block-kernel criterion remain separate
components of the statement. -/
theorem car_majorana_chain_pfaffian_bridge
    (t : ℝ) (ht : 0 < t) :
    (annihilationR * annihilationR = 0 ∧
      creationR * creationR = 0 ∧
      annihilationR * creationR + creationR * annihilationR = (1 : M2R) ∧
      annihilationR + creationR = splitPos ∧
      annihilationR - creationR = splitNeg) ∧
    ((kitaevSweetSpot4 t).mulVec majoranaZeroModeLeft = 0 ∧
      (kitaevSweetSpot4 t).mulVec majoranaZeroModeRight = 0) ∧
    (∃ v : Vec4C, v ≠ 0 ∧ (kitaevSweetSpot4 t).mulVec v = 0) ∧
    kitaevPfaffianProduct 0 t < 0 ∧
    ((∃ v : Fin 2 → ℝ, v ≠ 0 ∧
      twoMajoranaCoupling t *ᵥ v = 0) ↔
      twoMajoranaPfaffian t = 0) := by
  rcases real_car_pair_reconstructs_split_generators with
    ⟨ha, hc, hcar, hsum, hdiff⟩
  rcases sweet_spot_boundary_zero_modes_with_pfaffian_phase t ht with
    ⟨hleft, hright, hphase⟩
  exact ⟨⟨ha, hc, hcar, hsum, hdiff⟩,
    ⟨hleft, hright⟩, sweet_spot_boundary_has_nontrivial_kernel t, hphase,
    twoMajoranaPfaffian_kernel_criterion t⟩

end InfoGeometry.Canonical.MajoranaChiralPfaffianBridge
