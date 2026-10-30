/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.WheelerEpilogue
import Lean.Elab.Tactic.Guard

/-!
# Executable regression for the supplied fourteen-law macro

The input vocabulary is isolated here as regression data, not a replacement
API for the existing Peirce owners. ASCII identifiers avoid token conflicts.
Selective unfolding, an absent definition, internal unary negation, and goals
already closed by `simp` are tested explicitly. No tactic-completeness or
Knuth--Bendix confluence theorem is asserted.
-/

namespace InfoGeometry.WheelerEpilogueRegression

variable {B : Type*} [Ring B]

def comm (X Y : B) : B := X * Y - Y * X
def anticomm (X Y : B) : B := X * Y + Y * X
def bit (P : B) : B := P - (1 - P)
def zig (P A : B) : B := P * A * (1 - P)
def zag (P C : B) : B := (1 - P) * C * P
def phiOp (P A C : B) : B := zig P A + zag P C
def jOp (P A C : B) : B := zig P A - zag P C
def vOp (P A C : B) : B := anticomm (zig P A) (zag P C)
def sigmaOp (P A C : B) : B := comm (zig P A) (zag P C)
def mPhi (P A C X : B) : B := -comm (phiOp P A C) (comm (phiOp P A C) X)
def mJ (P A C X : B) : B := comm (jOp P A C) (comm (jOp P A C) X)
def mSigma (P A C X : B) : B := -comm (sigmaOp P A C) (comm (sigmaOp P A C) X)
def piV (P A C X : B) : B := (8 : ℤ) • X + (mPhi P A C X + mJ P A C X + mSigma P A C X)
def piPhi (P A C X : B) : B := mPhi P A C X - mJ P A C X - mSigma P A C X
def piJ (P A C X : B) : B := mJ P A C X - mPhi P A C X - mSigma P A C X
def piSigma (P A C X : B) : B := mSigma P A C X - mPhi P A C X - mJ P A C X

-- A deliberately broad list is the behavior being tested, so unused simp
-- arguments in this regression macro are intentional.
set_option linter.unusedSimpArgs false

macro "peirce_abel" hp:ident : tactic =>
  `(tactic| (simp only [piV, piPhi, piJ, piSigma, mPhi, mJ, mSigma,
    phiOp, jOp, vOp, sigmaOp, bit, comm, anticomm, zig, zag,
    add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg,
    zero_mul, mul_zero, one_mul, mul_one, mul_assoc,
    $hp:ident, InfoGeometry.WheelerEpilogue.idempotent_mul_assoc $hp:ident] <;> abel))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem fourteen_laws_by_normalization {P : B} (hP : P * P = P) (A C X : B) :
    zig P A * zig P A = 0 ∧
    zag P C * zag P C = 0 ∧
    phiOp P A C * phiOp P A C = vOp P A C ∧
    jOp P A C * jOp P A C = -vOp P A C ∧
    phiOp P A C * phiOp P A C + jOp P A C * jOp P A C = 0 ∧
    anticomm (phiOp P A C) (jOp P A C) = 0 ∧
    jOp P A C * phiOp P A C = sigmaOp P A C ∧
    sigmaOp P A C = bit P * vOp P A C ∧
    mPhi P A C (phiOp P A C) = 0 ∧
    mPhi P A C (vOp P A C) = 0 ∧
    mPhi P A C (jOp P A C) = -((4 : ℤ) • (vOp P A C * jOp P A C)) ∧
    mPhi P A C (sigmaOp P A C) = -((4 : ℤ) • (vOp P A C * sigmaOp P A C)) ∧
    zig P A * zag P C * zig P A = vOp P A C * zig P A ∧
    piV P A C X + piPhi P A C X + piJ P A C X + piSigma P A C X = (8 : ℤ) • X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-- The last branch needs neither idempotence nor any multiplication law. -/
theorem partition_without_idempotence (P A C X : B) :
    piV P A C X + piPhi P A C X + piJ P A C X + piSigma P A C X = (8 : ℤ) • X := by
  simp only [piV, piPhi, piJ, piSigma] <;> abel

-- An absent second definition makes the multi-unfold fail. The following
-- `try` must leave the syntactic target unchanged before selective unfolding.
example {P : B} (hP : P * P = P) (A : B) : zig P A * zig P A = 0 := by
  fail_if_success unfold zig mJ
  try unfold zig mJ
  guard_target =ₛ zig P A * zig P A = 0
  peirce_abel hP

-- Internal unary negation is supported by the repaired rule set.
example {P : B} (hP : P * P = P) (A X : B) : (-zig P A) * X = -(zig P A * X) := by
  peirce_abel hP

-- No `no goals to be solved` error after the simplifier closes the goal.
example {P : B} (hP : P * P = P) : P * P = P := by
  peirce_abel hP

end InfoGeometry.WheelerEpilogueRegression
