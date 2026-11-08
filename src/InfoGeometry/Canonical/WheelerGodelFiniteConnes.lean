/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset

/-!
# Finite block identities for the two-sheet Dirac operator

This file proves algebraic identities in the existing finite Peirce block
model. It does not claim an analytic spectral triple, a Lorentzian Connes
metric, or an APS/zeta invariant. Those require additional Hilbert-space and
analytic hypotheses.
-/

namespace InfoGeometry.Canonical.WheelerGodelFiniteConnes

open InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- The projector onto the first summand in the doubled block carrier. -/
def blockPeirceP : Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks 1 0 0 0

/-- The off-diagonal candidate Dirac operator. -/
def blockDirac (A B : Matrix n n R) : Matrix (Sum n n) (Sum n n) R :=
  blockUpper A + blockLower B

/-- The skew off-diagonal Peirce generator. -/
def blockPeirceJ (A B : Matrix n n R) : Matrix (Sum n n) (Sum n n) R :=
  blockUpper A - blockLower B

/-- Algebraic Dirac square is the finite Fisher block. -/
theorem blockDirac_sq (A B : Matrix n n R) :
    blockDirac A B * blockDirac A B = blockFisher A B := by
  rw [blockDirac, blockFisher_eq_fromBlocks]
  dsimp [blockUpper, blockLower]
  simp [Matrix.fromBlocks_add, Matrix.fromBlocks_multiply]

/-- The commutator of the block Dirac operator with the first-sheet
projector is the negative Peirce generator. -/
theorem blockDirac_comm_peirceP (A B : Matrix n n R) :
    blockDirac A B * blockPeirceP - blockPeirceP * blockDirac A B =
      - blockPeirceJ A B := by
  dsimp [blockDirac, blockPeirceP, blockPeirceJ, blockUpper, blockLower]
  simp [Matrix.fromBlocks_add, Matrix.fromBlocks_multiply]

/-- The block grading anticommutes with the off-diagonal Dirac matrix. -/
theorem blockDirac_anticommutes_grading (A B : Matrix n n R) :
    blockChiralInv * blockDirac A B + blockDirac A B * blockChiralInv = 0 := by
  dsimp [blockChiralInv, blockDirac, blockUpper, blockLower]
  simp [Matrix.fromBlocks_add, Matrix.fromBlocks_multiply]

end InfoGeometry.Canonical.WheelerGodelFiniteConnes
