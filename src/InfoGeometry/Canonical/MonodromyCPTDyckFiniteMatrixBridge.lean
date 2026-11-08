/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CPTDyckParseTree
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
import InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Finite-matrix Yangian block labels as CPT-Dyck gates

This module connects the existing concrete two-site block `monodromyB2`
with the existing monoid-valued `DyckTree`.  Its scope is strictly cancellation
of explicit `2 × 2` real matrices.  It does not define or prove an RTT algebra,
Yangian representation, quantum determinant, or grammatical invariant.
-/

namespace InfoGeometry.Canonical.MonodromyCPTDyckFiniteMatrixBridge

open InfoGeometry.Canonical.CPTDyckParseTree
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
open InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset.PlabicTwistedPinCPT

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℝ

/-- Four scalar parameters `(u, theta₁, theta₂, eta)` for the existing
two-site block. This reuses the product type rather than introducing a new
carrier structure. -/
abbrev SpectralLabel := ℝ × ℝ × ℝ × ℝ

private def spectralU (ℓ : SpectralLabel) : ℝ := ℓ.1
private def spectralTheta₁ (ℓ : SpectralLabel) : ℝ := ℓ.2.1
private def spectralTheta₂ (ℓ : SpectralLabel) : ℝ := ℓ.2.2.1
private def spectralEta (ℓ : SpectralLabel) : ℝ := ℓ.2.2.2

/-- The standard first-coordinate Peirce idempotent. -/
def peirceP : M₂ := !![1, 0; 0, 0]

/-- The existing Yangian owner's concrete two-site creation block. -/
def creation (ℓ : SpectralLabel) : M₂ :=
  monodromyB2 (spectralU ℓ) (spectralTheta₁ ℓ) (spectralTheta₂ ℓ) (spectralEta ℓ)

/-- Open a labeled finite-matrix gate with the owner's two-site block. -/
def openGate (ℓ : SpectralLabel) : M₂ := 1 + creation ℓ

/-- Close the gate using the owner's twisted-Pin CPT map. -/
def closeGate (ℓ : SpectralLabel) : M₂ :=
  thetaCPT peirceP sigmaX (openGate ℓ)

/-- Explicit entries of the actual `monodromyB2` owner definition. -/
theorem creation_entries (ℓ : SpectralLabel) :
    creation ℓ = !![0, 0;
      spectralEta ℓ * ((spectralU ℓ - spectralTheta₂ ℓ) +
        (spectralU ℓ - spectralTheta₁ ℓ)), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [creation, monodromyB2, laxBlockA, laxBlockB, laxBlockD]
  all_goals ring

/-- The creation block lies in the lower-left corner `Q B P` for `Q = 1-P`.

The statement uses the actual finite `2 × 2` matrix entries, not a generic
Yangian or operator-algebra carrier. -/
theorem creation_lowerLeft (ℓ : SpectralLabel) :
    creation ℓ = (1 - peirceP) * creation ℓ * peirceP := by
  rw [creation_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceP, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

/-- The lower-left creation block is square-zero. -/
theorem creation_sq_zero (ℓ : SpectralLabel) :
    creation ℓ * creation ℓ = 0 := by
  rw [creation_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The owner's twisted-CPT map sends this lower-left creation block to its
negative. -/
theorem thetaCPT_creation (ℓ : SpectralLabel) :
    thetaCPT peirceP sigmaX (creation ℓ) = -creation ℓ := by
  rw [creation_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaCPT, pinJ1, invS, peirceP, sigmaX,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The opening and CPT-closing gates are two-sided inverses. -/
theorem open_close_inverse (ℓ : SpectralLabel) :
    openGate ℓ * closeGate ℓ = 1 ∧ closeGate ℓ * openGate ℓ = 1 := by
  have hsq := creation_sq_zero ℓ
  have hc : closeGate ℓ = 1 - creation ℓ := by
    change thetaCPT peirceP sigmaX (1 + creation ℓ) = 1 - creation ℓ
    rw [thetaCPT_add, thetaCPT_creation]
    have hone : thetaCPT peirceP sigmaX (1 : M₂) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [thetaCPT, pinJ1, invS, peirceP, sigmaX,
          Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    rw [hone]
    abel
  constructor
  · rw [openGate, hc]
    calc
      (1 + creation ℓ) * (1 - creation ℓ) =
          1 - creation ℓ * creation ℓ := by noncomm_ring
      _ = 1 := by rw [hsq]; simp
  · rw [openGate, hc]
    calc
      (1 - creation ℓ) * (1 + creation ℓ) =
          1 - creation ℓ * creation ℓ := by noncomm_ring
      _ = 1 := by rw [hsq]; simp

/-- Every labeled tree cancels.  This is an instance of the existing
`CPTDyckParseTree` theorem for the concrete finite-matrix gates above. -/
theorem every_tree_eval_eq_one (tree : DyckTree SpectralLabel) :
    DyckTree.eval openGate closeGate tree = 1 := by
  apply DyckTree.eval_eq_one openGate closeGate
  intro ℓ
  exact open_close_inverse ℓ

end InfoGeometry.Canonical.MonodromyCPTDyckFiniteMatrixBridge
