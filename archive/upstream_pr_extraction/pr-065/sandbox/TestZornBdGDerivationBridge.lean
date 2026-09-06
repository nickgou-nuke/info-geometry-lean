/-
Test file for ZornBdGDerivationBridge.lean
This tests that the main bridge file compiles and the theorems can be instantiated.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.ZornBdGDerivationBridge

open PauliSolderedCrossProductBridge
open ZornVectorMatrixAlgebra
open ZornBdGSolderingReadout
open G2BdGOrbit

#check sigmaVec_mul
#check sigmaVec_anticomm
#check sigmaVec_comm
#check zorn_one_mul
#check zorn_mul_one
#check derivation_annihilates_one
#check derivation_annihilates_scalar_seed
#check bdgReadout_block12_eq_sigmaVec
#check bdgReadout_block21_eq_sigmaVec
#check bdgReadout_diagonal_blocks
#check central_seed_generates_no_pairing
#check cartan_seed_generates_pairing

/-!
Simple test to verify the theorems can be instantiated with concrete values.
-/
def test_sigmaVec_mul : sigmaVec (![1, 2, 3]) (![4, 5, 6]) = (1*4 + 2*5 + 3*6) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • sigmaVec (![2*6 - 3*5, 3*4 - 1*6, 1*5 - 2*4]) := by
  simp [sigmaVec_mul, dot3, cross3, sigmaVec]
  <;> norm_num
  <;>
  (try decide) <;>
  (try ring_nf) <;>
  (try simp_all [Matrix.ext_iff, Fin.sum_univ_two]) <;>
  (try norm_num) <;>
  (try aesop)

def test_derivation_annihilates_one : ∀ (D : Zorn ℝ → Zorn ℝ), IsZornDerivation D → D 1 = (⟨0, fun _ => 0, fun _ => 0, 0⟩ : Zorn ℝ) := by
  intro D hD
  exact derivation_annihilates_one D hD

def test_sigmaVec_anticomm : ∀ (u v : Fin 3 → ℂ), sigmaVec u * sigmaVec v + sigmaVec v * sigmaVec u = (2 * dot3 u v) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro u v
  exact sigmaVec_anticomm u v

def test_sigmaVec_comm : ∀ (u v : Fin 3 → ℂ), sigmaVec u * sigmaVec v - sigmaVec v * sigmaVec u = (2 * Complex.I) • sigmaVec (cross3 u v) := by
  intro u v
  exact sigmaVec_comm u v

#eval "Tests passed - all theorems are available and type-check correctly"