/-
InfoGeometry/OperatorAlgebra/BoundaryFiveGradingShadow.lean

Finite theorem-facing shadow for the boundary five-grading, chiral, and
tripotent architecture.

This module is intentionally finite and algebraic.  It mirrors the assertion
checker in `tools/sympy/boundary_five_grading_shadow.py`:

* chiral involution and lightcone projectors;
* tripotent plus/minus/zero boundary grading;
* matrix-unit representatives for the five-grade bracket laws.

It does not prove the full O(5,5)/Pin(5,5) bulk theorem, holographic
reconstruction, analytic continuation, or Fibonacci universality.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra


namespace InfoGeometry.OperatorAlgebra.BoundaryFiveGradingShadow

/-! ## 1. Chiral doubled two-sector shadow -/

abbrev M2Z := InfoGeometry.Algebra.FiniteSpin.Mat2Z
abbrev M3Z := InfoGeometry.Algebra.FiniteSpin.Mat3Z
abbrev M5Z := Matrix (Fin 5) (Fin 5) ℤ

def mUnit2 (i j : Fin 2) : M2Z :=
  fun a b => if a = i ∧ b = j then 1 else 0

def mUnit3 (i j : Fin 3) : M3Z :=
  fun a b => if a = i ∧ b = j then 1 else 0

def mUnit5 (i j : Fin 5) : M5Z :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- Chiral parity `ε = diag(1,-1)`. -/
def eps : M2Z :=
  mUnit2 0 0 - mUnit2 1 1

/-- Real Hestenes boost/conjugation swap. -/
def boost : M2Z :=
  mUnit2 0 1 + mUnit2 1 0

/-- Generated real phase axis `K = boost ε`. -/
def Kmod : M2Z :=
  boost * eps

/-- Positive chiral projector. -/
def Pplus : M2Z :=
  mUnit2 0 0

/-- Negative chiral projector. -/
def Pminus : M2Z :=
  mUnit2 1 1

/-- `ε² = 1`. -/
theorem eps_sq : eps * eps = 1 := by
  decide

/-- `boost² = 1`. -/
theorem boost_sq : boost * boost = 1 := by
  decide

/-- The real boost/CPT axis anticommutes with chirality. -/
theorem boost_eps_anticomm : boost * eps = -(eps * boost) := by
  decide

/-- The generated real Hestenes phase axis squares to `-1`. -/
theorem Kmod_sq : Kmod * Kmod = -1 := by
  decide

/-- The positive chiral projector is idempotent. -/
theorem Pplus_idempotent : Pplus * Pplus = Pplus := by
  decide

/-- The negative chiral projector is idempotent. -/
theorem Pminus_idempotent : Pminus * Pminus = Pminus := by
  decide

/-- The chiral projectors resolve the identity. -/
theorem Pplus_add_Pminus : Pplus + Pminus = 1 := by
  decide

/-- Opposite chiral projectors are orthogonal. -/
theorem Pplus_mul_Pminus : Pplus * Pminus = 0 := by
  decide

/-- Opposite chiral projectors are orthogonal in the other order. -/
theorem Pminus_mul_Pplus : Pminus * Pplus = 0 := by
  decide

/-- Chiral parity is the difference of the two lightcone projectors. -/
theorem eps_eq_Pplus_sub_Pminus : eps = Pplus - Pminus := by
  decide

/-! ## 2. Tripotent boundary plus/minus/zero shadow -/

/-- Tripotence predicate `T³ = T`. -/
def IsTripotent {R : Type*} [Mul R] (T : R) : Prop :=
  T * T * T = T

/-- Boundary tripotent with sectors `+1`, `-1`, and `0`. -/
def Ttri : M3Z :=
  mUnit3 0 0 - mUnit3 1 1

/-- Support projector `T²`, killing the zero sector. -/
def Ptrisupport : M3Z :=
  Ttri * Ttri

/-- Zero-mode vector in the tripotent kernel. -/
def zeroMode : Fin 3 → ℤ :=
  fun i => if i = 2 then 1 else 0

/-- The boundary grading is tripotent. -/
theorem Ttri_tripotent : IsTripotent Ttri := by
  change Ttri * Ttri * Ttri = Ttri
  decide

/-- The square of the tripotent is an idempotent support projector. -/
theorem Ptrisupport_idempotent : Ptrisupport * Ptrisupport = Ptrisupport := by
  decide

/-- The support projector preserves the tripotent on the right. -/
theorem Ttri_mul_Ptrisupport : Ttri * Ptrisupport = Ttri := by
  decide

/-- The support projector preserves the tripotent on the left. -/
theorem Ptrisupport_mul_Ttri : Ptrisupport * Ttri = Ttri := by
  decide

/-- The tripotent annihilates its zero-mode sector. -/
theorem Ttri_annihilates_zeroMode : Ttri.mulVec zeroMode = 0 := by
  decide

/-! ## 3. Five-grade matrix-unit bracket shadow -/

/-- Matrix commutator. -/
def commutator5 (A B : M5Z) : M5Z :=
  A * B - B * A

/-- A representative of `g_-1`. -/
def gNegOneA : M5Z := mUnit5 0 1

/-- A second representative of `g_-1`. -/
def gNegOneB : M5Z := mUnit5 1 2

/-- A representative of `g_+1`. -/
def gPosOneA : M5Z := mUnit5 3 2

/-- A second representative of `g_+1`. -/
def gPosOneB : M5Z := mUnit5 4 3

/-- A representative of `g_+2`. -/
def gPosTwo : M5Z := mUnit5 4 2

/-- A representative of `g_-2`. -/
def gNegTwo : M5Z := mUnit5 0 2

/-- Mixed grade `-1` representative for the grade-zero bracket. -/
def mixedNegOne : M5Z := mUnit5 1 2

/-- Mixed grade `+1` representative for the grade-zero bracket. -/
def mixedPosOne : M5Z := mUnit5 2 1

/-- A grade-zero diagonal representative. -/
def gZeroDiag : M5Z := mUnit5 2 2

/-- A grade-zero commutator representative. -/
def gZeroMixedReadout : M5Z := mUnit5 1 1 - mUnit5 2 2

/-- Same positive grade-one bracket lands in grade positive two. -/
theorem pos_one_pos_one_bracket_eq_pos_two :
    commutator5 gPosOneB gPosOneA = gPosTwo := by
  decide

/-- Same negative grade-one bracket lands in grade negative two. -/
theorem neg_one_neg_one_bracket_eq_neg_two :
    commutator5 gNegOneA gNegOneB = gNegTwo := by
  decide

/-- Mixed grade-one bracket lands in grade zero. -/
theorem neg_one_pos_one_bracket_eq_zero_readout :
    commutator5 mixedNegOne mixedPosOne = gZeroMixedReadout := by
  decide

/-- Grade zero acts on the positive grade-two representative. -/
theorem zero_pos_two_bracket_eq_neg_pos_two :
    commutator5 gZeroDiag gPosTwo = -gPosTwo := by
  decide

/-- Grade zero acts on the negative grade-two representative. -/
theorem zero_neg_two_bracket_eq_neg_neg_two :
    commutator5 gZeroDiag gNegTwo = -gNegTwo := by
  decide

/-- The positive extremal representative is abelian with itself. -/
theorem pos_two_self_bracket_eq_zero :
    commutator5 gPosTwo gPosTwo = 0 := by
  decide

/-- The finite synthesis theorem for the checked boundary shadow. -/
theorem boundary_five_grading_shadow_synthesis :
    eps * eps = 1 ∧
    boost * boost = 1 ∧
    boost * eps = -(eps * boost) ∧
    Kmod * Kmod = -1 ∧
    eps = Pplus - Pminus ∧
    IsTripotent Ttri ∧
    Ttri.mulVec zeroMode = 0 ∧
    commutator5 gPosOneB gPosOneA = gPosTwo ∧
    commutator5 gNegOneA gNegOneB = gNegTwo ∧
    commutator5 mixedNegOne mixedPosOne = gZeroMixedReadout ∧
    commutator5 gPosTwo gPosTwo = 0 := by
  exact ⟨eps_sq, boost_sq, boost_eps_anticomm, Kmod_sq,
    eps_eq_Pplus_sub_Pminus, Ttri_tripotent, Ttri_annihilates_zeroMode,
    pos_one_pos_one_bracket_eq_pos_two,
    neg_one_neg_one_bracket_eq_neg_two,
    neg_one_pos_one_bracket_eq_zero_readout,
    pos_two_self_bracket_eq_zero⟩

end InfoGeometry.OperatorAlgebra.BoundaryFiveGradingShadow
