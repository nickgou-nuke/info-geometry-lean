/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCounterexample
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# A global inner-derivation counterexample on a matrix centralizer

This file uses Mathlib's actual centralizer subalgebra
`C = Subalgebra.centralizer ℚ {E₀₂}` inside `Matrix (Fin 3) (Fin 3) ℚ`.
The cut and seed from `ChiralSchwarzCounterexample` belong to `C`, and
their Peirce wings remain the noncommuting operators `E₀₁` and `E₁₂`.

Their commutator and anticommutator both equal the nonzero `E₀₂`. The
centralizer membership law makes `E₀₂` central on this carrier. Hence the
two native inner derivations commute on every element of `C`, while the
Peirce interaction remains nonzero.

The carrier restriction is explicit: the imported full-matrix example
exhibits an input outside `C` that detects the commutator. This countermodel
disproves collapse from global inner-derivation commutation in an arbitrary
associative algebra. It supplies no C-star adjoint pairing.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCentralizer

open ChiralSchwarzCounterexample

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A native matrix subalgebra with its inherited ring and rational algebra. -/
abbrev Carrier := ↥(Subalgebra.centralizer ℚ ({residue} : Set Op))

private theorem mem_residueCentralizer {X : Op} (h : comm residue X = 0) :
    X ∈ Subalgebra.centralizer ℚ ({residue} : Set Op) := by
  rw [Subalgebra.mem_centralizer_iff]
  intro Y hY
  have hY' : Y = residue := Set.mem_singleton_iff.mp hY
  subst Y
  exact sub_eq_zero.mp h

private theorem upper_mem :
    upper ∈ Subalgebra.centralizer ℚ ({residue} : Set Op) := by
  apply mem_residueCentralizer
  simpa only [obstruction_value] using obstruction_comm_upper

private theorem lower_mem :
    lower ∈ Subalgebra.centralizer ℚ ({residue} : Set Op) := by
  apply mem_residueCentralizer
  simpa only [obstruction_value] using obstruction_comm_lower

private theorem cut_mem :
    cut ∈ Subalgebra.centralizer ℚ ({residue} : Set Op) := by
  apply mem_residueCentralizer
  rw [← obstruction_value]
  peirce_nf cut_idempotent

private theorem seed_mem :
    seed ∈ Subalgebra.centralizer ℚ ({residue} : Set Op) := by
  have hseed : seed = upper + lower := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [seed, upper, lower]
  rw [hseed]
  exact (Subalgebra.centralizer ℚ ({residue} : Set Op)).add_mem upper_mem lower_mem

def forward : Carrier := ⟨upper, upper_mem⟩
def backward : Carrier := ⟨lower, lower_mem⟩
def cutOp : Carrier := ⟨cut, cut_mem⟩
def seedOp : Carrier := ⟨seed, seed_mem⟩
def centralResidue : Carrier :=
  ⟨residue, mem_residueCentralizer (by simp only [comm, sub_self])⟩

/-- Both multiplication orders are transported by the subtype inclusion. -/
theorem forward_mul_backward : forward * backward = centralResidue := by
  apply Subtype.ext
  exact upper_mul_lower

theorem backward_mul_forward : backward * forward = 0 := by
  apply Subtype.ext
  exact lower_mul_upper

/-- Restricting the carrier preserves the nonzero ordered product. -/
theorem centralResidue_ne_zero : centralResidue ≠ 0 := by
  intro h
  exact residue_ne_zero (congrArg (fun X : Carrier => (X : Op)) h)

/-- The actual centralizer subalgebra is noncommutative. -/
theorem forward_backward_noncommute : forward * backward ≠ backward * forward := by
  rw [forward_mul_backward, backward_mul_forward]
  exact centralResidue_ne_zero

theorem forward_lie_backward : ⁅forward, backward⁆ = centralResidue := by
  change forward * backward - backward * forward = centralResidue
  rw [forward_mul_backward, backward_mul_forward, sub_zero]

theorem forward_jordan_backward : forward * backward + backward * forward = centralResidue := by
  rw [forward_mul_backward, backward_mul_forward, add_zero]

/-- Centrality is derived from the native centralizer membership condition. -/
theorem centralResidue_commutes (X : Carrier) : centralResidue * X = X * centralResidue := by
  apply Subtype.ext
  change residue * (X : Op) = (X : Op) * residue
  exact ((Subalgebra.mem_centralizer_iff ℚ).mp X.property) residue (by simp)

/-- The nonzero commutator generates the zero inner derivation on this carrier. -/
theorem ad_centralResidue_eq_zero : LieAlgebra.ad ℚ Carrier centralResidue = 0 := by
  apply LinearMap.ext
  intro X
  change centralResidue * X - X * centralResidue = 0
  exact sub_eq_zero.mpr (centralResidue_commutes X)

/-- The two inner derivations commute globally despite their noncommuting generators. -/
theorem native_inner_derivations_commute :
    ⁅LieAlgebra.ad ℚ Carrier forward, LieAlgebra.ad ℚ Carrier backward⁆ = 0 := by
  rw [← (LieAlgebra.ad ℚ Carrier).map_lie, forward_lie_backward]
  exact ad_centralResidue_eq_zero

theorem cutOp_idempotent : cutOp * cutOp = cutOp := by
  apply Subtype.ext
  exact cut_idempotent

theorem conePlus_cutOp_seedOp : conePlus cutOp seedOp = forward := by
  apply Subtype.ext
  exact conePlus_seed

theorem coneMinus_cutOp_seedOp : coneMinus cutOp seedOp = backward := by
  apply Subtype.ext
  exact coneMinus_seed

/-- The embedded generators remain square-zero by the existing Peirce law. -/
theorem forward_square_zero : forward * forward = 0 := by
  rw [← conePlus_cutOp_seedOp]
  exact conePlus_mul_conePlus cutOp_idempotent seedOp seedOp

theorem backward_square_zero : backward * backward = 0 := by
  rw [← coneMinus_cutOp_seedOp]
  exact coneMinus_mul_coneMinus cutOp_idempotent seedOp seedOp

theorem interaction_eq_centralResidue : genV cutOp seedOp seedOp = centralResidue := by
  simp only [genV, anticomm, conePlus_cutOp_seedOp, coneMinus_cutOp_seedOp]
  exact forward_jordan_backward

theorem obstruction_eq_centralResidue : genSig cutOp seedOp seedOp = centralResidue := by
  simp only [genSig, comm, conePlus_cutOp_seedOp, coneMinus_cutOp_seedOp,
    forward_mul_backward, backward_mul_forward, sub_zero]

/-- Every input in the stated carrier has zero mixed inner-derivation defect. -/
theorem obstruction_commutes_globally (X : Carrier) :
    comm (genSig cutOp seedOp seedOp) X = 0 := by
  rw [obstruction_eq_centralResidue, comm]
  exact sub_eq_zero.mpr (centralResidue_commutes X)

/-- A concrete global countermodel to the arbitrary-ring collapse implication. -/
theorem global_schwarz_vanishing_with_nonzero_interaction :
    cutOp * cutOp = cutOp ∧
      ⁅LieAlgebra.ad ℚ Carrier (conePlus cutOp seedOp),
        LieAlgebra.ad ℚ Carrier (coneMinus cutOp seedOp)⁆ = 0 ∧
      genV cutOp seedOp seedOp ≠ 0 ∧
      conePlus cutOp seedOp * coneMinus cutOp seedOp ≠
        coneMinus cutOp seedOp * conePlus cutOp seedOp := by
  refine ⟨cutOp_idempotent, ?_, ?_, ?_⟩
  · rw [conePlus_cutOp_seedOp, coneMinus_cutOp_seedOp]
    exact native_inner_derivations_commute
  · rw [interaction_eq_centralResidue]
    exact centralResidue_ne_zero
  · rw [conePlus_cutOp_seedOp, coneMinus_cutOp_seedOp]
    exact forward_backward_noncommute

end InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCentralizer
