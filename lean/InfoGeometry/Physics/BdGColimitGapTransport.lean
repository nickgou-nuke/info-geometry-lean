/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit

/-!
# Finite-stage BdG square transport along inductive colimit maps

This module proves that the commuting-mass BdG square identity survives any
unital ring homomorphism, hence in particular the `StarRingHom` maps of the
two-sheeted Yang–Mills inductive colimit cone. It is a finite/algebraic
transport theorem. It does **not** construct a continuum 4D quantum
Yang–Mills theory, does not identify a BdG singular-value gap with a continuum
spectral mass gap, and asserts no Wightman or Osterwalder–Schrader axiom.
-/

namespace InfoGeometry.Physics.BdGColimitGapTransport

open InfoGeometry.Physics
open CanonicalTwoSheetedInductiveColimit

/-- Explicit non-commutativity witness for the `2 × 2` BdG block carrier. -/
private abbrev ncShearA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
private abbrev ncShearB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The two shears generating the BdG block carrier do not commute. -/
theorem bdgBlock_noncommutativity_witness :
    ncShearA * ncShearB ≠ ncShearB * ncShearA := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [ncShearA, ncShearB, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The commuting-mass BdG square identity is preserved by any ring homomorphism.
The transported diagonal is the image of the original diagonal `D² + M²`. -/
theorem massiveBdGHamiltonian_sq_map
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) (D M : A) (hcomm : D * M = M * D) :
    massiveBdGHamiltonian (φ D) (φ M) * massiveBdGHamiltonian (φ D) (φ M) =
      !![φ (D * D + M * M), 0; 0, φ (D * D + M * M)] := by
  rw [massiveBdGHamiltonian_sq]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [map_add, map_mul]
  · simpa [map_mul] using congrArg φ hcomm

/-- The finite-stage BdG square identity transported through one cone map of an
inductive star-colimit. No colimit-level spectrum or continuum gap is claimed. -/
theorem massiveBdGHamiltonian_sq_cone_transport
    (A : ℕ → Type*) [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (cone : InductiveStarColimitCone A A_inf) (k : ℕ) (D M : A k)
    (hcomm : D * M = M * D) :
    massiveBdGHamiltonian ((cone.toColimit k).toRingHom D) ((cone.toColimit k).toRingHom M) *
        massiveBdGHamiltonian ((cone.toColimit k).toRingHom D) ((cone.toColimit k).toRingHom M) =
      !![(cone.toColimit k).toRingHom (D * D + M * M), 0;
         0, (cone.toColimit k).toRingHom (D * D + M * M)] := by
  exact massiveBdGHamiltonian_sq_map (cone.toColimit k).toRingHom D M hcomm

end InfoGeometry.Physics.BdGColimitGapTransport
