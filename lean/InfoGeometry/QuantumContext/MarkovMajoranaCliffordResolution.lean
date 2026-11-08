/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMajoranaLoxodromicObstruction
import InfoGeometry.Clifford.Cl11Matrix

/-!
# Constructive split-Clifford resolution of the Markov–Majorana pair

Contract: on the existing uniform two-state softmax carrier, the actual range
involution and Jordan–Wigner difference represent the existing quadratic form
`Cl11Matrix.q11`. Their native Clifford algebra map is surjective onto the
full matrix algebra. The explicit reconstruction below supplies preimages.
The obstruction owner proves anticommutation, not commuting loxodromic axes;
this module supplies the compatible positive structure without changing either
operator. No assertion about arbitrary Markov kernels or continuum limits is
made. The existing weighted metriplectic bridge remains a separate construction.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovMajoranaCliffordResolution

open Matrix
open InfoGeometry.QuantumContext.MarkovMajoranaLoxodromicObstruction
open InfoGeometry.Clifford.Cl11Matrix (Vec11 q11 q11_apply)

/-- The split-signature generating map uses the source-defined Markov axes. -/
def markovGenerators : Vec11 →ₗ[ℝ] Operator where
  toFun v := v.1 • rangeInvolution + v.2 • firstMajorana
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c v := by
    simp [smul_add, smul_smul]

/-- The Clifford relation for the actual operators, not substitute matrices. -/
theorem markovGenerators_sq (v : Vec11) :
    markovGenerators v * markovGenerators v = q11 v • (1 : Operator) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [markovGenerators, rangeInvolution_explicit, firstMajorana_explicit,
      Matrix.mul_apply, Fin.sum_univ_two, q11_apply] <;> ring

/-- The universal property of mathlib's native Clifford algebra. -/
def markovClifford : CliffordAlgebra q11 →ₐ[ℝ] Operator :=
  CliffordAlgebra.lift q11 ⟨markovGenerators, fun v => by
    simp [Algebra.algebraMap_eq_smul_one, markovGenerators_sq v]⟩

@[simp] theorem markovClifford_iota_pos :
    markovClifford (CliffordAlgebra.ι q11 (1, 0)) = rangeInvolution := by
  simp [markovClifford, markovGenerators]

@[simp] theorem markovClifford_iota_neg :
    markovClifford (CliffordAlgebra.ι q11 (0, 1)) = firstMajorana := by
  simp [markovClifford, markovGenerators]

/-- Every operator is reconstructed from the identity, the two axes, and their
ordered product. In particular this representation retains off-diagonal data. -/
theorem operator_reconstruction (X : Operator) :
    X = ((X 0 0 + X 1 1) / 2) • (1 : Operator) +
      (-(X 0 1 + X 1 0) / 2) • rangeInvolution +
      ((X 0 1 - X 1 0) / 2) • firstMajorana +
      ((X 0 0 - X 1 1) / 2) • (rangeInvolution * firstMajorana) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rangeInvolution_explicit, firstMajorana_explicit] <;> ring

/-- A constructive preimage certificate for every matrix in the full carrier. -/
theorem markovClifford_surjective : Function.Surjective markovClifford := by
  intro X
  refine ⟨((X 0 0 + X 1 1) / 2) • (1 : CliffordAlgebra q11) +
    (-(X 0 1 + X 1 0) / 2) • CliffordAlgebra.ι q11 (1, 0) +
    ((X 0 1 - X 1 0) / 2) • CliffordAlgebra.ι q11 (0, 1) +
    ((X 0 0 - X 1 1) / 2) •
      (CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1)), ?_⟩
  simpa only [map_add, map_smul, map_one, map_mul,
    markovClifford_iota_pos, markovClifford_iota_neg] using
    (operator_reconstruction X).symm

end InfoGeometry.QuantumContext.MarkovMajoranaCliffordResolution
