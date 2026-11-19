/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import InfoGeometry.Volume.OrientedPfaffian
import InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian

/-!
# Signed finite Kitaev chains

This owner uses the signed matching-sum Pfaffian on finite skew matrices. It
keeps this convention separate from `Quantum.KitaevChain`, whose current
operator Pfaffian is the nonnegative square-root branch.
-/

noncomputable section

namespace InfoGeometry.Quantum.OrientedKitaevChain

open InfoGeometry.Volume.OrientedPfaffian
open InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian

/-- A finite oriented Majorana cell with its actual even-dimensional pairing matrix. -/
structure Cell where
  halfDim : ℕ
  pairing : Matrix (Fin (2 * halfDim)) (Fin (2 * halfDim)) ℝ
  skew : IsSkew pairing

/-- The signed matching-sum Pfaffian of a cell's pairing matrix. -/
noncomputable def Cell.pfaffian (c : Cell) : ℝ :=
  orientedPfaffian c.halfDim c.pairing

/-- Signed Pfaffian volume of a finite chain is the product of its cell Pfaffians. -/
noncomputable def chainVolume (chain : List Cell) : ℝ :=
  (chain.map Cell.pfaffian).prod

/-- Negative-Pfaffian parity; zero remains the gapless diagnostic value. -/
def chainIndexZ2 (chain : List Cell) : ZMod 2 :=
  if chainVolume chain < 0 then 1 else 0

/-- The 2-mode dimer whose signed Pfaffian is `-1`. -/
def negativeGenerator : Cell where
  halfDim := 1
  pairing := !![(0 : ℝ), -1; 1, 0]
  skew := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num

@[simp] theorem negativeGenerator_pfaffian : negativeGenerator.pfaffian = -1 := by
  unfold Cell.pfaffian negativeGenerator
  change orientedPfaffian 1 (!![(0 : ℝ), -1; 1, 0]) = -1
  have hmat : (!![(0 : ℝ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(0 : ℝ), -1; -(-1), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hmat, orientedPfaffian_fin_two]

@[simp] theorem singleton_negativeGenerator_index :
    chainIndexZ2 [negativeGenerator] = 1 := by
  simp [chainIndexZ2, chainVolume, negativeGenerator_pfaffian]

theorem chainVolume_append (chain₁ chain₂ : List Cell) :
    chainVolume (chain₁ ++ chain₂) = chainVolume chain₁ * chainVolume chain₂ := by
  simp [chainVolume, List.map_append, List.prod_append]

theorem chainIndexZ2_append_of_chainVolume_ne_zero
    (chain₁ chain₂ : List Cell)
    (h₁ : chainVolume chain₁ ≠ 0) (h₂ : chainVolume chain₂ ≠ 0) :
    chainIndexZ2 (chain₁ ++ chain₂) = chainIndexZ2 chain₁ + chainIndexZ2 chain₂ := by
  dsimp [chainIndexZ2]
  rw [chainVolume_append]
  exact pfaffianSignParity_mul_of_nonzero h₁ h₂

end InfoGeometry.Quantum.OrientedKitaevChain

end
