/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Routing.FactLogicBypassAlgebra
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Rat.Defs

/-!
# Matrix counterexample to the prompt/fact zero-block claim

Three mutually orthogonal coordinate idempotents do not force the
prompt-to-fact block to vanish when that block is allowed by the support
pattern.  The matrix unit from the fact coordinate to the prompt coordinate
is an explicit witness.  The result concerns finite-dimensional operator
support only; it makes no claim about neural-network semantics.
-/

namespace InfoGeometry.Routing.FactLogicBypassAlgebra

abbrev ThreeTrackMatrix := Matrix (Fin 3) (Fin 3) ℚ

/-- The published support pattern has a nonzero prompt-to-fact block in a
three-dimensional operator algebra. -/
theorem publishedMaskSupport_prompt_fact_block_nonzero :
    let P_f : ThreeTrackMatrix := Matrix.single 0 0 1
    let P_l : ThreeTrackMatrix := Matrix.single 1 1 1
    let P_p : ThreeTrackMatrix := Matrix.single 2 2 1
    let R : ThreeTrackMatrix := Matrix.single 2 0 1
    P_p * publishedMaskSupport P_f P_l P_p 0 0 R 0 0 * P_f = R ∧ R ≠ 0 := by
  intro P_f P_l P_p R
  dsimp [ThreeTrackMatrix] at *
  have hpf : P_p * P_f = 0 := by
    dsimp [P_p, P_f]
    exact Matrix.single_mul_single_of_ne (c := (1 : ℚ)) 2 2 0 (by decide) 1
  have hpl : P_p * P_l = 0 := by
    dsimp [P_p, P_l]
    exact Matrix.single_mul_single_of_ne (c := (1 : ℚ)) 2 2 1 (by decide) 1
  have hlf : P_l * P_f = 0 := by
    dsimp [P_l, P_f]
    exact Matrix.single_mul_single_of_ne (c := (1 : ℚ)) 1 1 0 (by decide) 1
  have hff : P_f * P_f = P_f := by
    dsimp [P_f]
    rw [Matrix.single_mul_single_same]
    simp
  have hpp : P_p * P_p = P_p := by
    dsimp [P_p]
    rw [Matrix.single_mul_single_same]
    simp
  have hblock := publishedMaskSupport_prompt_fact_block
    (P_f := P_f) (P_l := P_l) (P_p := P_p)
    (F := 0) (G := 0) (R := R) (S := 0) (Q := 0)
    hpf hpl hlf hff hpp
  have hroute : P_p * R * P_f = R := by
    dsimp [P_p, R, P_f]
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp
  have hR : R ≠ 0 := by
    intro h
    have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M 2 0) h
    simp [R, Matrix.single] at hentry
  refine ⟨?_, hR⟩
  rw [hblock, hroute]

end InfoGeometry.Routing.FactLogicBypassAlgebra
