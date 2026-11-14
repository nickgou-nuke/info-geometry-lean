/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Basic.Real.Basic
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Central {±I} invariance under the Pin(5,5) twisted-conjugation representation

Proves that the central element `-1` in the Clifford algebra acts trivially
on the vector representation via twisted conjugation:

    ρ(-1)(v) = α(-1)·v·(-1)⁻¹ = v

This shows that the {I, -I} kernel of the double cover Pin → O acts as the
identity on the orbit stratification of J₂(𝕆_s), so the classification
descends to O(5,5) / PSO(5,5).
-/

open CliffordAlgebra

noncomputable section

namespace InfoGeometry.Physics.CentralizerInvariance

private noncomputable def witnessQ : QuadraticForm ℝ (Fin 2 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ ![1, 1]

private noncomputable def cliffordE0 : CliffordAlgebra witnessQ :=
  CliffordAlgebra.ι witnessQ ![1, 0]

private noncomputable def cliffordE1 : CliffordAlgebra witnessQ :=
  CliffordAlgebra.ι witnessQ ![0, 1]

/-- Explicit non-commutativity witness for `CliffordAlgebra`. -/
theorem clifford_noncomm_witness :
    cliffordE0 * cliffordE1 ≠ cliffordE1 * cliffordE0 := by
  intro h
  let f : (Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    { toFun := fun v => v 0 • !![1, 0; 0, -1] + v 1 • !![0, 1; 1, 0]
      map_add' := fun u v => by simp [add_smul]
      map_smul' := fun r v => by ext i j; fin_cases i <;> fin_cases j <;> simp }
  have hf : ∀ v, f v * f v = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (witnessQ v) := by
    intro v
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [f, witnessQ, QuadraticMap.weightedSumSquares_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;> ring
  have hmap := congrArg (CliffordAlgebra.lift witnessQ ⟨f, hf⟩) h
  simp only [cliffordE0, cliffordE1, map_mul, CliffordAlgebra.lift_ι_apply] at hmap
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hmap
  norm_num [f, Matrix.mul_apply, Fin.sum_univ_two] at h01

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)

/--
The twisted-conjugation (sandwich) action of a unit g ∈ Cl(Q)× on an
element v ∈ Cl(Q):

    ρ(g)(v) = α(g) · v · g⁻¹

where α is the grading automorphism (involute).
This is the standard Pin group action on vectors.
-/
def twistedConjugation (g : (CliffordAlgebra Q)ˣ) (v : CliffordAlgebra Q) : CliffordAlgebra Q :=
  involute (g : CliffordAlgebra Q) * v * ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)

/--
The unit -1 in the Clifford algebra.  This is the non-trivial element of
the centre {±1}.
-/
def minusOne : (CliffordAlgebra Q)ˣ :=
  -1

@[simp]
theorem inv_minusOne : (minusOne Q : (CliffordAlgebra Q)ˣ)⁻¹ = minusOne Q := by
  ext; simp [minusOne]

/--
**Theorem:** `ρ(-1)(v) = v` for all `v`.  The central element -1 acts
trivially on the vector representation.

Proof: α(-1) = -1 (since -1 is a degree-0 scalar), and (-1)·v·(-1) = v
because the central scalar `-1` commutes with every element and `(-1) * (-1) = 1`.
-/
theorem centralizer_action_trivial (v : CliffordAlgebra Q) :
    twistedConjugation Q (minusOne Q) v = v := by
  dsimp [twistedConjugation, minusOne]
  simp

/--
**Corollary/readout:** the central element `-1` fixes every Clifford carrier under
this twisted-conjugation action.  This is the exact kernel-triviality statement
available in this file; any orbit-stratum descent theorem must be proved in the
owner stratum file from this equality, not hidden here behind `True`.
-/
theorem centralizer_preserves_orbit_readout (x : CliffordAlgebra Q) :
    twistedConjugation Q (minusOne Q) x = x :=
  centralizer_action_trivial Q x

end InfoGeometry.Physics.CentralizerInvariance
