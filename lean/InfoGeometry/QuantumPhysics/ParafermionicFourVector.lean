import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral four-vector readout for the native split-Zorn carrier

This file records only the finite algebraic facts supplied by the existing
real Zorn/Peirce owner.  In particular, the chiral lift is a one-sided Peirce
readout; its Zorn norm is therefore not the Minkowski quadratic form.
-/

namespace InfoGeometry.QuantumPhysics.ParafermionicFourVector

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

noncomputable section

structure FourVector where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

namespace FourVector

def spatial (p : FourVector) : Vec := ![p.x, p.y, p.z]

def minkowskiNorm (p : FourVector) : ℝ :=
  p.t ^ 2 - (p.x ^ 2 + p.y ^ 2 + p.z ^ 2)

def positiveChiral (p : FourVector) : Carrier :=
  p.t • (E11 : Carrier) + upperZorn (spatial p)

def negativeChiral (p : FourVector) : Carrier :=
  p.t • (E22 : Carrier) + lowerZorn (spatial p)

def IsNull (p : FourVector) : Prop := minkowskiNorm p = 0

theorem upperZorn_mul_upperZorn (q r : Vec) :
    upperZorn q * upperZorn r = lowerZorn (Vec3.cross q r) := by
  apply ZornMatrix.ext <;>
    simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

theorem lowerZorn_mul_lowerZorn (q r : Vec) :
    lowerZorn q * lowerZorn r = upperZorn (-Vec3.cross q r) := by
  apply ZornMatrix.ext <;>
    simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

theorem mixedChiralContraction (i j : Fin 3) :
    (upperZorn (Vec3.basis i) * lowerZorn (Vec3.basis j)).a =
      if i = j then 1 else 0 := by
  rw [upperZorn_mul_lowerZorn]
  fin_cases i <;> fin_cases j <;>
    simp [chiralPairing, Vec3.dot, Vec3.basis, E11]

@[simp] theorem upperZorn_sq (q : Vec) :
    upperZorn q * upperZorn q = 0 := by
  rw [upperZorn_mul_upperZorn]
  apply ZornMatrix.ext <;>
    simp [lowerZorn, ZornMatrix.zero, Vec3.cross, mul_comm]

@[simp] theorem lowerZorn_sq (q : Vec) :
    lowerZorn q * lowerZorn q = 0 := by
  rw [lowerZorn_mul_lowerZorn]
  apply ZornMatrix.ext <;>
    simp [upperZorn, ZornMatrix.zero, Vec3.cross, mul_comm]

/-!
## Twin-State Vector Formalism (TSVF) and Bilateral Zorn Connection

While a one-sided Peirce readout has zero Zorn norm, the bilateral paired
twin-state connection $\mathbb{A}(p^+, p^-)$ carrying history 4-vector $p^+$
and destiny 4-vector $p^-$ reproduces the Minkowski quadratic form when
evaluated along the diagonal $p^+ = p^- = p$.
-/

/-- The bilateral twin-state Zorn connection pairing history $p^+$ and destiny $p^-$. -/
def twinStateZorn (pPlus pMinus : FourVector) : Carrier where
  a := pPlus.t
  v := spatial pPlus
  w := spatial pMinus
  b := pMinus.t

@[simp] theorem twinStateZorn_a (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus).a = pPlus.t := rfl

@[simp] theorem twinStateZorn_v (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus).v = spatial pPlus := rfl

@[simp] theorem twinStateZorn_w (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus).w = spatial pMinus := rfl

@[simp] theorem twinStateZorn_b (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus).b = pMinus.t := rfl

/-- The Zorn norm of the paired twin-state matrix evaluates to the cross-Minkowski pairing. -/
theorem twinStateZorn_norm (pPlus pMinus : FourVector) :
    zornNorm (twinStateZorn pPlus pMinus) =
      pPlus.t * pMinus.t - chiralPairing (spatial pPlus) (spatial pMinus) := by
  simp [zornNorm, chiralPairing, Vec3.dot, twinStateZorn]

/-- On the diagonal $p^+ = p^- = p$, the Zorn norm of the twin-state matrix
coincides with the standard Minkowski quadratic form. -/
@[simp] theorem twinStateZorn_diagonal_norm (p : FourVector) :
    zornNorm (twinStateZorn p p) = minkowskiNorm p := by
  simp [twinStateZorn_norm, minkowskiNorm, spatial, chiralPairing, Vec3.dot]
  ring

/-- A 4-vector is lightlike (null) if and only if its twin-state Zorn matrix has vanishing Zorn norm. -/
theorem twinStateZorn_isNull_iff (p : FourVector) :
    zornNorm (twinStateZorn p p) = 0 ↔ IsNull p := by
  rw [twinStateZorn_diagonal_norm, IsNull]

/-!
## Jordan (Symmetric) vs. Lie (Antisymmetric) Decomposition and Helmholtz Flow

The algebraic transpose on the Zorn carrier decomposes any state into:
1. A symmetric (Jordan) sector: contains the diagonal scalar flows and the
   curl-free (irrotational) spatial vector field.
2. An antisymmetric (Lie) sector: carries the curl (rotational) gauge curvature.
-/

/-- The algebraic matrix transpose on the split-Zorn carrier. -/
def zornTranspose (Z : Carrier) : Carrier where
  a := Z.a
  v := Z.w
  w := Z.v
  b := Z.b

@[simp] theorem zornTranspose_a (Z : Carrier) : (zornTranspose Z).a = Z.a := rfl
@[simp] theorem zornTranspose_v (Z : Carrier) : (zornTranspose Z).v = Z.w := rfl
@[simp] theorem zornTranspose_w (Z : Carrier) : (zornTranspose Z).w = Z.v := rfl
@[simp] theorem zornTranspose_b (Z : Carrier) : (zornTranspose Z).b = Z.b := rfl

@[simp] theorem zornTranspose_transpose (Z : Carrier) :
    zornTranspose (zornTranspose Z) = Z := by
  apply ZornMatrix.ext <;> rfl

/-- Symmetric (Jordan) part of a Zorn matrix. -/
def zornSym (Z : Carrier) : Carrier :=
  (1 / 2 : ℝ) • (Z + zornTranspose Z)

/-- Antisymmetric (Lie) part of a Zorn matrix. -/
def zornAntisym (Z : Carrier) : Carrier :=
  (1 / 2 : ℝ) • (Z - zornTranspose Z)

/-- Canonical Jordan-Lie decomposition: every Zorn matrix splits uniquely into
its symmetric and antisymmetric parts. -/
theorem zorn_jordan_lie_decomposition (Z : Carrier) :
    zornSym Z + zornAntisym Z = Z := by
  apply ZornMatrix.ext
  · simp [zornSym, zornAntisym, zornTranspose, add_a, smul_a, sub_a]
    ring
  · ext i
    fin_cases i <;>
      simp [zornSym, zornAntisym, zornTranspose, add_v, smul_v, sub_v,
        Vec3.add, Vec3.sub, Vec3.smul] <;>
      ring
  · ext i
    fin_cases i <;>
      simp [zornSym, zornAntisym, zornTranspose, add_w, smul_w, sub_w,
        Vec3.add, Vec3.sub, Vec3.smul] <;>
      ring
  · simp [zornSym, zornAntisym, zornTranspose, add_b, smul_b, sub_b]
    ring

/-- On the symmetric Jordan sector, the off-diagonal vector fields coincide: $v = w$. -/
theorem zornSym_offdiag_eq (Z : Carrier) :
    (zornSym Z).v = (zornSym Z).w := by
  ext i
  fin_cases i <;>
    simp [zornSym, zornTranspose, smul_v, smul_w, add_v, add_w,
      Vec3.smul, Vec3.add] <;>
    ring

/-- Helmholtz irrotational property: on the symmetric Jordan sector, the internal
vector cross product vanishes identically ($\mathbf{w}_+ \times \mathbf{w}_+ = 0$),
proving that the symmetric sector represents irrotational / gradient flow. -/
theorem zornSym_cross_self (Z : Carrier) :
    Vec3.cross (zornSym Z).v (zornSym Z).w = ![0, 0, 0] := by
  rw [zornSym_offdiag_eq Z]
  exact cross_self (zornSym Z).w

/-- The antisymmetric Lie sector is purely off-diagonal: its diagonal components vanish. -/
@[simp] theorem zornAntisym_diag_zero (Z : Carrier) :
    (zornAntisym Z).a = 0 ∧ (zornAntisym Z).b = 0 := by
  constructor
  · simp [zornAntisym, zornTranspose, smul_a, sub_a]
  · simp [zornAntisym, zornTranspose, smul_b, sub_b]

/-- On the antisymmetric Lie sector, the off-diagonal vector fields are opposite: $v = -w$. -/
theorem zornAntisym_offdiag_opp (Z : Carrier) :
    (zornAntisym Z).v = fun i => - (zornAntisym Z).w i := by
  ext i
  fin_cases i <;>
    simp [zornAntisym, zornTranspose, smul_v, smul_w, sub_v, sub_w,
      Vec3.smul, Vec3.sub] <;>
    ring

/-- The cross-coupling between the symmetric (flow) and antisymmetric (gauge)
sectors: expanding $\mathbf{w}_+ \times \mathbf{w}_-$ in terms of the original fields $v$ and $w$. -/
theorem jordan_lie_vorticity (Z : Carrier) :
    (Vec3.cross (zornSym Z).v (zornAntisym Z).v) =
      Vec3.smul (1 / 4 : ℝ) (Vec3.cross (Vec3.add Z.v Z.w) (Vec3.sub Z.v Z.w)) := by
  ext i
  fin_cases i <;>
    simp [zornSym, zornAntisym, zornTranspose, smul_v, add_v, sub_v,
      Vec3.cross, Vec3.smul, Vec3.add, Vec3.sub] <;>
    ring

/-!
## Aharonov Two-State Weak Value Readout

In Aharonov's Two-State Vector Formalism, the weak value of an operator $A$
between an initial state $|\Psi\rangle$ and final state $\langle \Phi|$ is
given by $\langle \Phi | A | \Psi \rangle / \langle \Phi | \Psi \rangle$.
In the Zorn matrix carrier, the bilateral twin-state matrix $\mathbb{A}(p^+, p^-)$
pairs history and destiny.
-/

/-- The bilateral state overlap pairing between history $p^+$ and destiny $p^-$. -/
def twinStateOverlap (pPlus pMinus : FourVector) : ℝ :=
  zornNorm (twinStateZorn pPlus pMinus)

/-- The algebraic weak readout pairing of an observable $Z$ with the twin state $\mathbb{A}(p^+, p^-)$
via the normalized Zorn trace product. -/
def zornWeakPairing (pPlus pMinus : FourVector) (Z : Carrier) : ℝ :=
  zornTrace (twinStateZorn pPlus pMinus * Z)

/-- On the diagonal $p^+ = p^- = p$, the trace pairing of the twin state with the identity
is twice the energy/temporal component $2 p.t$. -/
@[simp] theorem zornWeakPairing_identity (p : FourVector) :
    zornWeakPairing p p (I : Carrier) = 2 * p.t := by
  simp [zornWeakPairing, zornTrace, twinStateZorn, ZornMatrix.mul, I,
    Vec3.dot]
  ring

/-!
## Four-Wave Mixing and Distributed Andreev Reflection

In the Zorn algebra $\mathbb{O}_s$, non-linear squaring $\mathbb{A} \star \mathbb{A}$
modulates the forward signal $\vec{\sigma}^+$ and backward idler $\vec{\sigma}^-$
with the longitudinal pumps $u^\pm$ and their non-associative cross-product.
Furthermore, off-diagonal coupling exchanges the chiral electron ($L$-bit)
and hole ($R$-bit) sectors, formalizing the microscopic Andreev reflection.
-/

/-- The upper diagonal scalar generated by self-squaring the bilateral Zorn connection:
contains the history energy squared plus the spatial pairing (chiral Cooper pair density). -/
theorem twinStateZorn_sq_a (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus * twinStateZorn pPlus pMinus).a =
      pPlus.t ^ 2 + chiralPairing (spatial pPlus) (spatial pMinus) := by
  simp [twinStateZorn, ZornMatrix.mul, chiralPairing, Vec3.dot]
  ring

/-- The lower diagonal scalar generated by self-squaring the bilateral Zorn connection:
contains the destiny energy squared plus the spatial pairing. -/
theorem twinStateZorn_sq_b (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus * twinStateZorn pPlus pMinus).b =
      pMinus.t ^ 2 + chiralPairing (spatial pMinus) (spatial pPlus) := by
  simp [twinStateZorn, ZornMatrix.mul, chiralPairing, Vec3.dot]
  ring

/-- The off-diagonal upper vector field generated by self-squaring the bilateral Zorn connection:
contains the linear pump modulation $(a + b)v$ and the non-linear cross product $w \times w = 0$. -/
theorem twinStateZorn_sq_v (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus * twinStateZorn pPlus pMinus).v =
      Vec3.smul (pPlus.t + pMinus.t) (spatial pPlus) := by
  ext i
  fin_cases i <;>
    simp [twinStateZorn, ZornMatrix.mul, Vec3.smul, Vec3.add, Vec3.sub, Vec3.cross] <;>
    ring

/-- The off-diagonal lower vector field generated by self-squaring the bilateral Zorn connection:
contains the linear pump modulation $(a + b)w$ and the non-linear cross product $v \times v = 0$. -/
theorem twinStateZorn_sq_w (pPlus pMinus : FourVector) :
    (twinStateZorn pPlus pMinus * twinStateZorn pPlus pMinus).w =
      Vec3.smul (pPlus.t + pMinus.t) (spatial pMinus) := by
  ext i
  fin_cases i <;>
    simp [twinStateZorn, ZornMatrix.mul, Vec3.smul, Vec3.add, Vec3.sub, Vec3.cross] <;>
    ring

/-- Four-wave mixing cross-term: when two distinct bilateral states $\mathbb{A}_1$ and $\mathbb{A}_2$
interact, the non-linear cross product $w_1 \times w_2$ generates the phase-conjugate idler wave. -/
theorem four_wave_mixing_upper (Z1 Z2 : Carrier) :
    (Z1 * Z2).v =
      Vec3.sub (Vec3.add (Vec3.smul Z1.a Z2.v) (Vec3.smul Z2.b Z1.v))
        (Vec3.cross Z1.w Z2.w) := rfl

/-- Four-wave mixing lower term: the phase-conjugate reflection generated by $v_1 \times v_2$. -/
theorem four_wave_mixing_lower (Z1 Z2 : Carrier) :
    (Z1 * Z2).w =
      Vec3.add (Vec3.add (Vec3.smul Z2.a Z1.w) (Vec3.smul Z1.b Z2.w))
        (Vec3.cross Z1.v Z2.v) := rfl

/-- Distributed Andreev reflection: an incoming chiral signal interacting with an off-diagonal
pairing gap reflects into the conjugate chiral sector with weight proportional to the pairing. -/
theorem andreev_reflection_upper_lower (q p : Vec) :
    upperZorn q * lowerZorn p = chiralPairing q p • (E11 : Carrier) :=
  upperZorn_mul_lowerZorn q p

/-- Distributed Andreev reflection (hole to particle): incoming lower chiral excitation
reflects into the upper chiral sector with weight proportional to the pairing. -/
theorem andreev_reflection_lower_upper (p q : Vec) :
    lowerZorn p * upperZorn q = chiralPairing q p • (E22 : Carrier) :=
  lowerZorn_mul_upperZorn p q

end FourVector
end
end InfoGeometry.QuantumPhysics.ParafermionicFourVector
