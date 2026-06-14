import InfoGeometry.Algebra.SplitJordanSpinor
import InfoGeometry.Clifford.Arxiv160309063SplitAlgebra
import Mathlib.Tactic

/-!
# Klein spinor orbit representatives over `C_s`

This file formalizes theorem-safe pieces of the Section 5.1 orbit discussion in
Fioresi--Latini--Marrani, *Klein and Conformal Superspaces, Split Algebras and
Spinor Orbits* (arXiv:1603.09063v2).

Scope:

* the split-complex spinor carrier `C_s²`;
* the generic representative `(1,0)^t`;
* the zero-divisor representatives `(E,0)^t` and `(E,E)^t`, with `E = 1+j`;
* exact coordinate stabilizer conditions for raw `2×2` split-complex matrices.

Boundary: this file does not prove the full `SL(2,C_s)` orbit classification,
dimension counts, or the group isomorphism `Spin(2,2) ≃ SL(2,C_s)`.
-/

namespace InfoGeometry.Algebra.KleinSpinorOrbit

open InfoGeometry.Clifford.Arxiv160309063

abbrev Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC

namespace Cs

/-- Multiplication abbreviation for the split-complex coordinate model. -/
def smul (a b : Cs) : Cs :=
  SplitC.mul a b

/-- Addition abbreviation for the split-complex coordinate model. -/
def sadd (a b : Cs) : Cs :=
  SplitC.add a b

/-- Zero in the split-complex coordinate model. -/
def zero : Cs :=
  ⟨0, 0⟩

@[simp]
theorem add_zero (z : Cs) : sadd z zero = z := by
  cases z
  simp [sadd, zero, SplitC.add]

@[simp]
theorem zero_add (z : Cs) : sadd zero z = z := by
  cases z
  simp [sadd, zero, SplitC.add]

@[simp]
theorem mul_zero (z : Cs) : smul z zero = zero := by
  cases z
  simp [smul, zero, SplitC.mul]

@[simp]
theorem zero_mul (z : Cs) : smul zero z = zero := by
  cases z
  simp [smul, zero, SplitC.mul]

/-- Negation in split-complex coordinates. -/
def sneg (z : Cs) : Cs :=
  ⟨-z.re, -z.im⟩

/-- Subtraction in split-complex coordinates. -/
def ssub (z w : Cs) : Cs :=
  sadd z (sneg w)

@[simp]
theorem sub_zero (z : Cs) : ssub z zero = z := by
  cases z
  simp [ssub, sadd, sneg, zero, SplitC.add]

@[simp]
theorem add_neg_self (z : Cs) : ssub z z = zero := by
  cases z
  simp [ssub, sadd, sneg, zero, SplitC.add]

@[simp]
theorem one_mul (z : Cs) : smul SplitC.one z = z := by
  cases z
  simp [smul, SplitC.one, SplitC.scalar, SplitC.mul]

@[simp]
theorem mul_one (z : Cs) : smul z SplitC.one = z := by
  cases z
  simp [smul, SplitC.one, SplitC.scalar, SplitC.mul]

/-- Scalar multiplication by a rational in split-complex coordinates. -/
def qsmul (r : ℚ) (z : Cs) : Cs :=
  ⟨r * z.re, r * z.im⟩

@[simp]
theorem qsmul_Ebar_sum (r : ℚ) :
    (qsmul r SplitC.Ebar).re + (qsmul r SplitC.Ebar).im = 0 := by
  simp [qsmul, SplitC.Ebar]
  ring

@[simp]
theorem one_add_qsmul_Ebar_sum (r : ℚ) :
    (sadd SplitC.one (qsmul r SplitC.Ebar)).re +
      (sadd SplitC.one (qsmul r SplitC.Ebar)).im = 1 := by
  simp [sadd, qsmul, SplitC.add, SplitC.one, SplitC.scalar, SplitC.Ebar]
  ring

/-- `E = 1+j` is a zero divisor: `E * Ebar = 0`. -/
theorem E_zero_divisor : smul SplitC.E SplitC.Ebar = zero := by
  simpa [smul, zero] using SplitC.E_mul_Ebar

/-- Coordinate characterization of `z * E = E`. -/
theorem mul_E_eq_E_iff (z : Cs) :
    smul z SplitC.E = SplitC.E ↔ z.re + z.im = 1 := by
  constructor
  · intro h
    have hre := congrArg SplitC.re h
    cases z with
    | mk a b =>
      simpa [smul, SplitC.E, SplitC.mul] using hre
  · intro h
    cases z with
    | mk a b =>
      dsimp at h
      apply SplitC.ext
      · simp [smul, SplitC.E, SplitC.mul]
        exact h
      · simp [smul, SplitC.E, SplitC.mul]
        exact h

/-- Coordinate characterization of `z * E = 0`. -/
theorem mul_E_eq_zero_iff (z : Cs) :
    smul z SplitC.E = zero ↔ z.re + z.im = 0 := by
  constructor
  · intro h
    have hre := congrArg SplitC.re h
    cases z with
    | mk a b =>
      simpa [smul, SplitC.E, SplitC.mul, zero] using hre
  · intro h
    cases z with
    | mk a b =>
      dsimp at h
      apply SplitC.ext
      · simp [smul, SplitC.E, SplitC.mul, zero]
        exact h
      · simp [smul, SplitC.E, SplitC.mul, zero]
        exact h

end Cs

/-- Split-complex two-component spinor. -/
structure CsSpinor where
  ψ_pos : Cs
  ψ_neg : Cs
  deriving DecidableEq, Repr

namespace CsSpinor

@[ext]
theorem ext {ψ φ : CsSpinor}
    (hpos : ψ.ψ_pos = φ.ψ_pos) (hneg : ψ.ψ_neg = φ.ψ_neg) : ψ = φ := by
  cases ψ
  cases φ
  dsimp at hpos hneg
  cases hpos
  cases hneg
  rfl

end CsSpinor

/-- Raw `2×2` split-complex matrix. -/
structure CsMatrix2 where
  aa : Cs
  ab : Cs
  ba : Cs
  bb : Cs
  deriving DecidableEq, Repr

namespace CsMatrix2

/-- Identity raw matrix. -/
def identity : CsMatrix2 :=
  ⟨SplitC.one, Cs.zero, Cs.zero, SplitC.one⟩

/-- Raw split-complex determinant `aa*bb - ab*ba`. -/
def det (M : CsMatrix2) : Cs :=
  Cs.ssub (Cs.smul M.aa M.bb) (Cs.smul M.ab M.ba)

/-- Raw determinant-one predicate over `C_s`. -/
def DetOne (M : CsMatrix2) : Prop :=
  det M = SplitC.one

/-- Raw matrix action on `C_s²`. -/
def action (M : CsMatrix2) (ψ : CsSpinor) : CsSpinor where
  ψ_pos := Cs.sadd (Cs.smul M.aa ψ.ψ_pos) (Cs.smul M.ab ψ.ψ_neg)
  ψ_neg := Cs.sadd (Cs.smul M.ba ψ.ψ_pos) (Cs.smul M.bb ψ.ψ_neg)

/-- Stabilizer predicate for a raw matrix and a spinor. -/
def Stabilizes (M : CsMatrix2) (ψ : CsSpinor) : Prop :=
  action M ψ = ψ

@[simp]
theorem identity_action (ψ : CsSpinor) :
    action identity ψ = ψ := by
  cases ψ with
  | mk p n =>
  apply CsSpinor.ext <;>
    simp [action, identity]

@[simp]
theorem identity_stabilizes (ψ : CsSpinor) :
    Stabilizes identity ψ := by
  simp [Stabilizes]

@[simp]
theorem det_identity : det identity = SplitC.one := by
  simp [det, identity, Cs.ssub]

@[simp]
theorem identity_detOne : DetOne identity := by
  simp [DetOne]

/-- The unipotent family `[[1,b],[0,1]]` from the generic stabilizer. -/
def genericUnipotent (b : Cs) : CsMatrix2 :=
  ⟨SplitC.one, b, Cs.zero, SplitC.one⟩

@[simp]
theorem det_genericUnipotent (b : Cs) :
    det (genericUnipotent b) = SplitC.one := by
  simp [det, genericUnipotent, Cs.ssub]

@[simp]
theorem genericUnipotent_detOne (b : Cs) :
    DetOne (genericUnipotent b) := by
  simp [DetOne]

/-- A raw family stabilizing `(E,0)^t`: `aa=1+rEbar`, `ba=sEbar`. -/
def nullEbarFamily (r s : ℚ) (b d : Cs) : CsMatrix2 :=
  ⟨Cs.sadd SplitC.one (Cs.qsmul r SplitC.Ebar), b, Cs.qsmul s SplitC.Ebar, d⟩

end CsMatrix2

/-- The generic representative `(1,0)^t`. -/
def genericRep : CsSpinor :=
  ⟨SplitC.one, Cs.zero⟩

/-- The zero-divisor representative `(E,0)^t`. -/
def nullRep : CsSpinor :=
  ⟨SplitC.E, Cs.zero⟩

/-- The equivalent paper representative `(E,E)^t`. -/
def diagonalNullRep : CsSpinor :=
  ⟨SplitC.E, SplitC.E⟩

/-- Raw stabilizer condition for the generic representative: first column fixed. -/
theorem stabilizes_generic_iff (M : CsMatrix2) :
    M.Stabilizes genericRep ↔ M.aa = SplitC.one ∧ M.ba = Cs.zero := by
  constructor
  · intro h
    have hp := congrArg CsSpinor.ψ_pos h
    have hn := congrArg CsSpinor.ψ_neg h
    constructor
    · simpa [CsMatrix2.Stabilizes, CsMatrix2.action, genericRep] using hp
    · simpa [CsMatrix2.Stabilizes, CsMatrix2.action, genericRep] using hn
  · intro h
    rcases h with ⟨haa, hba⟩
    apply CsSpinor.ext
    · simp [CsMatrix2.action, genericRep, haa]
    · simp [CsMatrix2.action, genericRep, hba]

/-- Raw stabilizer condition for `(E,0)^t`. -/
theorem stabilizes_null_iff (M : CsMatrix2) :
    M.Stabilizes nullRep ↔
      M.aa.re + M.aa.im = 1 ∧ M.ba.re + M.ba.im = 0 := by
  constructor
  · intro h
    have hp := congrArg CsSpinor.ψ_pos h
    have hn := congrArg CsSpinor.ψ_neg h
    constructor
    · exact (Cs.mul_E_eq_E_iff M.aa).mp (by
        simpa [CsMatrix2.Stabilizes, CsMatrix2.action, nullRep] using hp)
    · exact (Cs.mul_E_eq_zero_iff M.ba).mp (by
        simpa [CsMatrix2.Stabilizes, CsMatrix2.action, nullRep] using hn)
  · intro h
    rcases h with ⟨haa, hba⟩
    apply CsSpinor.ext
    · have hmul := (Cs.mul_E_eq_E_iff M.aa).mpr haa
      simpa [CsMatrix2.Stabilizes, CsMatrix2.action, nullRep] using hmul
    · have hmul := (Cs.mul_E_eq_zero_iff M.ba).mpr hba
      simpa [CsMatrix2.Stabilizes, CsMatrix2.action, nullRep] using hmul

/-- Raw stabilizer condition for `(E,E)^t`. -/
theorem stabilizes_diagonalNull_iff (M : CsMatrix2) :
    M.Stabilizes diagonalNullRep ↔
      M.aa.re + M.aa.im + (M.ab.re + M.ab.im) = 1 ∧
      M.ba.re + M.ba.im + (M.bb.re + M.bb.im) = 1 := by
  constructor
  · intro h
    have hp := congrArg CsSpinor.ψ_pos h
    have hn := congrArg CsSpinor.ψ_neg h
    constructor
    · simpa [CsMatrix2.Stabilizes, CsMatrix2.action, diagonalNullRep,
        Cs.smul, Cs.sadd, SplitC.mul, SplitC.add, SplitC.E] using hp
    · simpa [CsMatrix2.Stabilizes, CsMatrix2.action, diagonalNullRep,
        Cs.smul, Cs.sadd, SplitC.mul, SplitC.add, SplitC.E] using hn
  · intro h
    rcases h with ⟨hrow₁, hrow₂⟩
    apply CsSpinor.ext
    · simp [CsMatrix2.action, diagonalNullRep,
        Cs.smul, Cs.sadd, SplitC.mul, SplitC.add, SplitC.E]
      linarith
    · simp [CsMatrix2.action, diagonalNullRep,
        Cs.smul, Cs.sadd, SplitC.mul, SplitC.add, SplitC.E]
      linarith

end InfoGeometry.Algebra.KleinSpinorOrbit
