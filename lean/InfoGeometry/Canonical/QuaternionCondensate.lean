import Mathlib.Tactic

/-!
# Quaternion Condensates

#### BUCKET 1: CLOSED FINITE THEOREMS
This file proves finite component-level quaternion identities for a condensate
shadow: multiplication basis laws, conjugation/norm facts, norm preservation
under a unit phase in the `1-i` plane, and antisymmetry of a torsion readout
when the covariant-commutator input is antisymmetric.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The finite `U(1)`-style invariance theorem is conditional on the explicit
unit-circle premise `c^2 + s^2 = 1`.  The torsion antisymmetry theorem is
conditional on an explicit commutator antisymmetry premise.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove `ℍ ≃ Cl(0,2)`, does not embed real quaternions into
`Cl(1,3; ℂ)`, does not construct electromagnetic gauge fields or vector
potentials, and does not derive Einstein-Cartan equations.  Those remain
separate theorem-owned tasks.
-/

namespace InfoGeometry.Canonical.QuaternionCondensate

set_option linter.unusedSectionVars false

/-- Four real components of a quaternion-like finite carrier. -/
structure H4 where
  re : ℝ
  imI : ℝ
  imJ : ℝ
  imK : ℝ

namespace H4

@[ext] theorem ext {p q : H4}
    (hre : p.re = q.re) (hi : p.imI = q.imI)
    (hj : p.imJ = q.imJ) (hk : p.imK = q.imK) : p = q := by
  cases p
  cases q
  simp_all

/-- Quaternion zero. -/
def zero : H4 := ⟨0, 0, 0, 0⟩

/-- Quaternion one. -/
def one : H4 := ⟨1, 0, 0, 0⟩

/-- Quaternion `i`. -/
def i : H4 := ⟨0, 1, 0, 0⟩

/-- Quaternion `j`. -/
def j : H4 := ⟨0, 0, 1, 0⟩

/-- Quaternion `k`. -/
def k : H4 := ⟨0, 0, 0, 1⟩

/-- Componentwise negation. -/
def neg (q : H4) : H4 :=
  ⟨-q.re, -q.imI, -q.imJ, -q.imK⟩

/-- Componentwise addition. -/
def add (p q : H4) : H4 :=
  ⟨p.re + q.re, p.imI + q.imI, p.imJ + q.imJ, p.imK + q.imK⟩

/-- Hamilton quaternion multiplication in components. -/
def mul (p q : H4) : H4 :=
  ⟨p.re * q.re - p.imI * q.imI - p.imJ * q.imJ - p.imK * q.imK,
   p.re * q.imI + p.imI * q.re + p.imJ * q.imK - p.imK * q.imJ,
   p.re * q.imJ - p.imI * q.imK + p.imJ * q.re + p.imK * q.imI,
   p.re * q.imK + p.imI * q.imJ - p.imJ * q.imI + p.imK * q.re⟩

/-- Quaternion conjugation. -/
def conj (q : H4) : H4 :=
  ⟨q.re, -q.imI, -q.imJ, -q.imK⟩

/-- Squared norm. -/
def normSq (q : H4) : ℝ :=
  q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

/-- Real part readout. -/
def realPart (q : H4) : ℝ := q.re

@[simp] theorem one_mul (q : H4) : mul one q = q := by
  ext <;> simp [mul, one]

@[simp] theorem mul_one (q : H4) : mul q one = q := by
  ext <;> simp [mul, one]

@[simp] theorem i_sq : mul i i = neg one := by
  ext <;> norm_num [mul, i, one, neg]

@[simp] theorem j_sq : mul j j = neg one := by
  ext <;> norm_num [mul, j, one, neg]

@[simp] theorem k_sq : mul k k = neg one := by
  ext <;> norm_num [mul, k, one, neg]

@[simp] theorem i_mul_j : mul i j = k := by
  ext <;> norm_num [mul, i, j, k]

@[simp] theorem j_mul_k : mul j k = i := by
  ext <;> norm_num [mul, i, j, k]

@[simp] theorem k_mul_i : mul k i = j := by
  ext <;> norm_num [mul, i, j, k]

@[simp] theorem j_mul_i : mul j i = neg k := by
  ext <;> norm_num [mul, i, j, k, neg]

@[simp] theorem k_mul_j : mul k j = neg i := by
  ext <;> norm_num [mul, i, j, k, neg]

@[simp] theorem i_mul_k : mul i k = neg j := by
  ext <;> norm_num [mul, i, j, k, neg]

@[simp] theorem conj_conj (q : H4) : conj (conj q) = q := by
  ext <;> simp [conj]

theorem normSq_conj (q : H4) : normSq (conj q) = normSq q := by
  simp [normSq, conj]

theorem mul_conj (q : H4) :
    mul q (conj q) = ⟨normSq q, 0, 0, 0⟩ := by
  ext <;> simp [mul, conj, normSq] <;> ring

theorem normSq_mul (p q : H4) :
    normSq (mul p q) = normSq p * normSq q := by
  cases p
  cases q
  simp [normSq, mul]
  ring

/-- Unit complex phase inside the quaternion `1-i` plane. -/
def phase (c s : ℝ) : H4 :=
  ⟨c, s, 0, 0⟩

/-- Left phase rotation of a quaternion condensate. -/
def phaseRotate (c s : ℝ) (q : H4) : H4 :=
  mul (phase c s) q

theorem normSq_phase (c s : ℝ) :
    normSq (phase c s) = c ^ 2 + s ^ 2 := by
  simp [phase, normSq]

theorem normSq_phaseRotate (c s : ℝ) (q : H4) :
    normSq (phaseRotate c s q) = (c ^ 2 + s ^ 2) * normSq q := by
  rw [phaseRotate, normSq_mul, normSq_phase]

/--
Finite `U(1)`-style invariance: a unit phase in the quaternion `1-i` plane
preserves the norm/metric readout of the condensate.
-/
theorem normSq_phaseRotate_of_unit
    {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1) (q : H4) :
    normSq (phaseRotate c s q) = normSq q := by
  rw [normSq_phaseRotate, hunit]
  simp

/-- Commutator in the finite quaternion carrier. -/
def commutator (p q : H4) : H4 :=
  add (mul p q) (neg (mul q p))

theorem commutator_antisymm (p q : H4) :
    commutator q p = neg (commutator p q) := by
  ext <;> simp [commutator, add, neg, mul]

/-- Quaternion condensate components over a finite spacetime carrier. -/
abbrev Condensate (SpaceTime : Type*) := SpaceTime → H4

namespace Condensate

/-- Projection-compatible name for the direct quaternion field. -/
abbrev phi (Φ : Condensate SpaceTime) : SpaceTime → H4 := Φ

end Condensate

/-- Nonvanishing predicate for the condensate, kept out of structure fields. -/
def IsNonVanishing {SpaceTime : Type*} (Φ : Condensate SpaceTime) : Prop :=
  ∀ x, normSq (Φ.phi x) ≠ 0

/-- Finite norm/metric readout of a condensate. -/
def metricReadout {SpaceTime : Type*} (Φ : Condensate SpaceTime) (x : SpaceTime) : ℝ :=
  normSq (Φ.phi x)

/-- Phase rotation preserves the finite metric readout under an explicit unit premise. -/
theorem metricReadout_phase_invariant
    {SpaceTime : Type*} {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1)
    (Φ : Condensate SpaceTime) (x : SpaceTime) :
    metricReadout (fun y => phaseRotate c s (Φ.phi y)) x =
      metricReadout Φ x := by
  exact normSq_phaseRotate_of_unit hunit (Φ.phi x)

/-- Bilinear quaternion vielbein readout. -/
def vielbeinReadout (Φ dΦ axis : H4) : ℝ :=
  realPart (mul (conj Φ) (mul axis dΦ))

/-- Torsion readout from an antisymmetric covariant commutator input. -/
def torsionReadout {idx : Type*}
    (Φ axis : H4) (comm : idx → idx → H4) (mu nu : idx) : ℝ :=
  realPart (mul (conj Φ) (mul axis (comm mu nu)))

/-- Torsion readout is antisymmetric when the commutator input is antisymmetric. -/
theorem torsionReadout_antisymm
    {idx : Type*} (Φ axis : H4) (comm : idx → idx → H4)
    (hcomm : ∀ mu nu, comm nu mu = neg (comm mu nu))
    (mu nu : idx) :
    torsionReadout Φ axis comm nu mu = -torsionReadout Φ axis comm mu nu := by
  rw [torsionReadout, torsionReadout, hcomm mu nu]
  cases Φ
  cases axis
  cases comm mu nu
  simp [realPart, mul, conj, neg]
  ring

end H4

end InfoGeometry.Canonical.QuaternionCondensate
