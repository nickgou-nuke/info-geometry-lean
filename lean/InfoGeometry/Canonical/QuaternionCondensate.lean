import Mathlib

/-!
# Quaternion Condensates

#### BUCKET 1: CLOSED FINITE THEOREMS
This file proves finite component-level quaternion identities for a condensate
shadow: multiplication basis laws, conjugation/norm facts, a bridge into
Mathlib's `Quaternion ℝ`, norm preservation and inverse closure under a unit
phase in the `1-i` plane, and antisymmetry of a torsion readout when the
covariant-commutator input is antisymmetric.  It also proves the finite
induced metric is symmetric whenever the coefficient metric is symmetric.

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

/-- Component bridge from the finite carrier into Mathlib's real quaternions. -/
def toQuaternion (q : H4) : Quaternion ℝ :=
  ⟨q.re, q.imI, q.imJ, q.imK⟩

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

theorem conj_mul (q : H4) :
    mul (conj q) q = ⟨normSq q, 0, 0, 0⟩ := by
  ext <;> simp [mul, conj, normSq] <;> ring

theorem normSq_mul (p q : H4) :
    normSq (mul p q) = normSq p * normSq q := by
  cases p
  cases q
  simp [normSq, mul]
  ring

theorem normSq_nonneg (q : H4) : 0 ≤ normSq q := by
  unfold normSq
  positivity

theorem normSq_eq_zero_iff (q : H4) :
    normSq q = 0 ↔ q = zero := by
  constructor
  · intro h
    cases q with
    | mk a b c d =>
        have hs : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0 := by
          simpa [normSq] using h
        have ha2 : a ^ 2 = 0 := by
          nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
        have hb2 : b ^ 2 = 0 := by
          nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
        have hc2 : c ^ 2 = 0 := by
          nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
        have hd2 : d ^ 2 = 0 := by
          nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
        have ha : a = 0 := sq_eq_zero_iff.mp ha2
        have hb : b = 0 := sq_eq_zero_iff.mp hb2
        have hc : c = 0 := sq_eq_zero_iff.mp hc2
        have hd : d = 0 := sq_eq_zero_iff.mp hd2
        ext <;> simp [zero, ha, hb, hc, hd]
  · intro h
    rw [h]
    norm_num [normSq, zero]

theorem normSq_pos_iff (q : H4) :
    0 < normSq q ↔ q ≠ zero := by
  constructor
  · intro h hzero
    rw [hzero] at h
    norm_num [normSq, zero] at h
  · intro hne
    have hnonneg : 0 ≤ normSq q := normSq_nonneg q
    have hnotzero : normSq q ≠ 0 := by
      intro hzero
      exact hne ((normSq_eq_zero_iff q).mp hzero)
    exact lt_of_le_of_ne' hnonneg hnotzero

@[simp] theorem i_mul_j_mul_k : mul (mul i j) k = neg one := by
  ext <;> norm_num [mul, i, j, k, neg, one]

theorem toQuaternion_one : toQuaternion one = 1 := by
  ext <;> simp [toQuaternion, one]

theorem toQuaternion_mul (p q : H4) :
    toQuaternion (mul p q) = toQuaternion p * toQuaternion q := by
  cases p
  cases q
  ext <;> simp [toQuaternion, mul]

theorem toQuaternion_conj (q : H4) :
    toQuaternion (conj q) = star (toQuaternion q) := by
  cases q
  ext <;> simp [toQuaternion, conj]

theorem toQuaternion_normSq (q : H4) :
    Quaternion.normSq (toQuaternion q) = normSq q := by
  cases q
  simp [toQuaternion, normSq, Quaternion.normSq]
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

theorem phase_mul_phase_neg {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1) :
    mul (phase c (-s)) (phase c s) = one := by
  ext <;> simp [mul, phase, one] <;> nlinarith [hunit]

theorem phaseRotate_inverse
    {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1) (q : H4) :
    phaseRotate c (-s) (phaseRotate c s q) = q := by
  cases q with
  | mk a b d e =>
      ext <;> simp [phaseRotate, phase, mul]
      · calc
          c * (c * a - s * b) + s * (c * b + s * a)
              = (c ^ 2 + s ^ 2) * a := by ring
          _ = a := by rw [hunit]; ring
      · calc
          c * (c * b + s * a) - s * (c * a - s * b)
              = (c ^ 2 + s ^ 2) * b := by ring
          _ = b := by rw [hunit]; ring
      · calc
          c * (c * d - s * e) + s * (c * e + s * d)
              = (c ^ 2 + s ^ 2) * d := by ring
          _ = d := by rw [hunit]; ring
      · calc
          c * (c * e + s * d) - s * (c * d - s * e)
              = (c ^ 2 + s ^ 2) * e := by ring
          _ = e := by rw [hunit]; ring

theorem normSq_phaseRotate_ne_zero
    {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1) {q : H4}
    (hq : normSq q ≠ 0) :
    normSq (phaseRotate c s q) ≠ 0 := by
  rw [normSq_phaseRotate_of_unit hunit]
  exact hq

/-- Commutator in the finite quaternion carrier. -/
def commutator (p q : H4) : H4 :=
  add (mul p q) (neg (mul q p))

theorem commutator_antisymm (p q : H4) :
    commutator q p = neg (commutator p q) := by
  ext <;> simp [commutator, add, neg, mul]

/-- Quaternion condensate components over a finite spacetime carrier. -/
structure Condensate (SpaceTime : Type*) where
  phi : SpaceTime → H4

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
    metricReadout ⟨fun y => phaseRotate c s (Φ.phi y)⟩ x =
      metricReadout Φ x := by
  exact normSq_phaseRotate_of_unit hunit (Φ.phi x)

theorem isNonVanishing_phaseRotate
    {SpaceTime : Type*} {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1)
    {Φ : Condensate SpaceTime} (hΦ : IsNonVanishing Φ) :
    IsNonVanishing ⟨fun x => phaseRotate c s (Φ.phi x)⟩ := by
  intro x
  exact normSq_phaseRotate_ne_zero hunit (hΦ x)

/-- Finite induced metric from frame components and a coefficient metric. -/
def inducedMetric {coord frame : Type*} [Fintype frame]
    (eta : frame → frame → ℝ)
    (e : coord → frame → ℝ) (mu nu : coord) : ℝ :=
  ∑ a, ∑ b, eta a b * e mu a * e nu b

/--
Finite metric symmetry: if the coefficient metric is symmetric, the induced
component expression `eta_ab e_mu^a e_nu^b` is symmetric in `mu, nu`.
-/
theorem inducedMetric_symm
    {coord frame : Type*} [Fintype frame]
    (eta : frame → frame → ℝ)
    (e : coord → frame → ℝ)
    (hη : ∀ a b, eta a b = eta b a) (mu nu : coord) :
    inducedMetric eta e mu nu = inducedMetric eta e nu mu := by
  unfold inducedMetric
  calc
    (∑ a, ∑ b, eta a b * e mu a * e nu b)
        = ∑ b, ∑ a, eta a b * e mu a * e nu b := by
            rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, eta b a * e mu b * e nu a := by
            rfl
    _ = ∑ a, ∑ b, eta a b * e mu b * e nu a := by
            simp [hη]
    _ = ∑ a, ∑ b, eta a b * e nu a * e mu b := by
            simp [mul_comm, mul_left_comm]

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
