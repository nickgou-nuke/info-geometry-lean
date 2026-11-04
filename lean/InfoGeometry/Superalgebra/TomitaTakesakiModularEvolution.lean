/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Sections 143 and 144: Operator Lift of Surprisal and Tomita-Takesaki Modular Evolution
Target: `InfoGeometry/Superalgebra/TomitaTakesakiModularEvolution.lean`
Ref: `QMS-DIR-SEC143-144-TOMITA-TAKESAKI-REPAIR-2026-OCT-16`

Formalizes:
1. Operator lift of surprisal into the split-octonion algebra: `modularHamiltonian I_surp = scale I_surp paraSymplecticK0`.
2. The Tomita-Takesaki modular rotor `modularDelta c s = ⟨c + s, zero, zero, c - s⟩` and modular flow
   `tomitaTakesakiFlow c s X = mul (mul (modularDelta c s) X) (modularDelta c (-s))`.
3. Theorem 1 (Quark sheet blue-shift):
   `tomitaTakesakiFlow c s (quark u) = quark (smul ((c + s)^2) u)`.
4. Theorem 2 (Antiquark sheet red-shift):
   `tomitaTakesakiFlow c s (antiquark v) = antiquark (smul ((c - s)^2) v)`.
5. Theorem 3 (KMS balance invariance):
   Under the hyperbolic mass-shell relation `c^2 - s^2 = 1`, the anticommutator pairing
   `anticommutator (tomitaTakesakiFlow c s (quark u)) (tomitaTakesakiFlow c s (antiquark v))`
   equals `scale (dot u v) one`.
-/

namespace InfoGeometry.Superalgebra.TomitaTakesaki

/-! ### 1. 3D Color Vector Carrier -/

@[ext]
structure ColorVec3 (R : Type*) where
  c1 : R
  c2 : R
  c3 : R
  deriving DecidableEq, Repr, Inhabited

namespace ColorVec3

variable {R : Type*} [CommRing R]

def zero : ColorVec3 R := ⟨0, 0, 0⟩
def smul (k : R) (u : ColorVec3 R) : ColorVec3 R := ⟨k * u.c1, k * u.c2, k * u.c3⟩
def add (u v : ColorVec3 R) : ColorVec3 R := ⟨u.c1 + v.c1, u.c2 + v.c2, u.c3 + v.c3⟩
def sub (u v : ColorVec3 R) : ColorVec3 R := ⟨u.c1 - v.c1, u.c2 - v.c2, u.c3 - v.c3⟩

def dot (u v : ColorVec3 R) : R :=
  u.c1 * v.c1 + u.c2 * v.c2 + u.c3 * v.c3

def cross (u v : ColorVec3 R) : ColorVec3 R where
  c1 := u.c2 * v.c3 - u.c3 * v.c2
  c2 := u.c3 * v.c1 - u.c1 * v.c3
  c3 := u.c1 * v.c2 - u.c2 * v.c1

theorem dot_smul_smul (a b : R) (u v : ColorVec3 R) :
    dot (smul a u) (smul b v) = (a * b) * dot u v := by
  dsimp [dot, smul]
  ring

end ColorVec3

/-! ### 2. 8D Split-Octonion Algebra and Surprisal Operator Lift (Section 143) -/

@[ext]
structure SplitOctonion (R : Type*) where
  a : R
  u : ColorVec3 R
  v : ColorVec3 R
  b : R
  deriving DecidableEq, Repr, Inhabited

namespace SplitOctonion

variable {R : Type*} [CommRing R]

def zero : SplitOctonion R := ⟨0, ColorVec3.zero, ColorVec3.zero, 0⟩
def one  : SplitOctonion R := ⟨1, ColorVec3.zero, ColorVec3.zero, 1⟩

/-- Para-symplectic generator `K₀ = e₁ - e₂`. -/
def paraSymplecticK0 : SplitOctonion R := ⟨1, ColorVec3.zero, ColorVec3.zero, -1⟩

def scale (k : R) (X : SplitOctonion R) : SplitOctonion R :=
  ⟨k * X.a, ColorVec3.smul k X.u, ColorVec3.smul k X.v, k * X.b⟩

def add (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a + Y.a, ColorVec3.add X.u Y.u, ColorVec3.add X.v Y.v, X.b + Y.b⟩

def sub (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a - Y.a, ColorVec3.sub X.u Y.u, ColorVec3.sub X.v Y.v, X.b - Y.b⟩

def mul (X Y : SplitOctonion R) : SplitOctonion R where
  a := X.a * Y.a + ColorVec3.dot X.u Y.v
  u := ColorVec3.sub (ColorVec3.add (ColorVec3.smul X.a Y.u) (ColorVec3.smul Y.b X.u))
                     (ColorVec3.cross X.v Y.v)
  v := ColorVec3.add (ColorVec3.add (ColorVec3.smul Y.a X.v) (ColorVec3.smul X.b Y.v))
                     (ColorVec3.cross X.u Y.u)
  b := X.b * Y.b + ColorVec3.dot X.v Y.u

def anticommutator (X Y : SplitOctonion R) : SplitOctonion R := add (mul X Y) (mul Y X)

def quark (u : ColorVec3 R) : SplitOctonion R := ⟨0, u, ColorVec3.zero, 0⟩
def antiquark (v : ColorVec3 R) : SplitOctonion R := ⟨0, ColorVec3.zero, v, 0⟩

/-- Operator lift of surprisal: `K_mod = I_surp • K₀`. -/
def modularHamiltonian (I_surp : R) : SplitOctonion R :=
  scale I_surp paraSymplecticK0

/-! ### 3. Tomita-Takesaki Modular Evolution (Section 144) -/

/-- Modular rotor `Δ_t = c • 𝟙 + s • K₀`. -/
def modularDelta (c s : R) : SplitOctonion R :=
  ⟨c + s, ColorVec3.zero, ColorVec3.zero, c - s⟩

/-- The two diagonal products of the modular rotor have scalar coordinate
    `c² - s²`; this does not assume the mass-shell normalization. -/
theorem modularDelta_mul_reverse (c s : R) :
    mul (modularDelta c s) (modularDelta c (-s)) =
      ⟨c^2 - s^2, ColorVec3.zero, ColorVec3.zero, c^2 - s^2⟩ := by
  dsimp [mul, modularDelta, ColorVec3.zero, ColorVec3.dot, ColorVec3.sub,
    ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
  ext <;> ring

/-- On the hyperbolic mass shell, `Δ(c,-s)` is a genuine two-sided inverse
    of `Δ(c,s)` in the defined split-octonion multiplication. -/
theorem modularDelta_has_inverse (c s : R) (h_hyperbolic : c^2 - s^2 = 1) :
    mul (modularDelta c s) (modularDelta c (-s)) = one ∧
    mul (modularDelta c (-s)) (modularDelta c s) = one := by
  constructor
  · rw [modularDelta_mul_reverse, h_hyperbolic]
    rfl
  · have h_reverse := modularDelta_mul_reverse c (-s)
    have h_reverse' :
        mul (modularDelta c (-s)) (modularDelta c s) =
          ⟨c^2 - (-s)^2, ColorVec3.zero, ColorVec3.zero, c^2 - (-s)^2⟩ := by
      simpa only [neg_neg] using h_reverse
    have hs : (-s)^2 = s^2 := by ring
    rw [h_reverse', hs, h_hyperbolic]
    rfl

/-- Two-sided modular automorphism `σ_t(X) = Δ_t · X · (Δ_t)⁻¹`. -/
def tomitaTakesakiFlow (c s : R) (X : SplitOctonion R) : SplitOctonion R :=
  mul (mul (modularDelta c s) X) (modularDelta c (-s))

/--
Blue-shift of the forward quark sheet:
The modular flow scales the forward quark sector by `(c + s)^2`.
-/
theorem tomita_takesaki_quark_blue_shift (c s : R) (u : ColorVec3 R) :
    tomitaTakesakiFlow c s (quark u) = quark (ColorVec3.smul ((c + s)^2) u) := by
  dsimp [tomitaTakesakiFlow, modularDelta, quark, mul, ColorVec3.zero, ColorVec3.smul,
         ColorVec3.dot, ColorVec3.sub, ColorVec3.add, ColorVec3.cross]
  ext <;> ring

/--
Red-shift of the backward antiquark sheet:
The modular flow scales the backward antiquark sector by `(c - s)^2`.
-/
theorem tomita_takesaki_antiquark_red_shift (c s : R) (v : ColorVec3 R) :
    tomitaTakesakiFlow c s (antiquark v) = antiquark (ColorVec3.smul ((c - s)^2) v) := by
  dsimp [tomitaTakesakiFlow, modularDelta, antiquark, mul, ColorVec3.zero, ColorVec3.smul,
         ColorVec3.dot, ColorVec3.sub, ColorVec3.add, ColorVec3.cross]
  ext <;> ring

/-- Anticommutator of a quark state and an antiquark state yields their dot product on `one`. -/
theorem anticommutator_quark_antiquark (u v : ColorVec3 R) :
    anticommutator (quark u) (antiquark v) = scale (ColorVec3.dot u v) one := by
  dsimp [anticommutator, quark, antiquark, mul, add, scale, one,
         ColorVec3.zero, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
         ColorVec3.smul, ColorVec3.cross]
  ext <;> ring

/--
KMS balance condition and invariance of the metric pairing:
When `c^2 - s^2 = 1`, the anticommutator pairing between modular-evolved quark and antiquark
states is invariant and equals `scale (dot u v) one`.
-/
theorem tomita_takesaki_kms_invariant (c s : R) (u v : ColorVec3 R)
    (h_hyperbolic : c^2 - s^2 = 1) :
    anticommutator (tomitaTakesakiFlow c s (quark u))
                   (tomitaTakesakiFlow c s (antiquark v)) =
      scale (ColorVec3.dot u v) one := by
  have h_prod : (c + s)^2 * (c - s)^2 = 1 := by
    calc (c + s)^2 * (c - s)^2 = (c^2 - s^2)^2 := by ring
      _ = 1^2 := by rw [h_hyperbolic]
      _ = 1 := by ring
  rw [tomita_takesaki_quark_blue_shift, tomita_takesaki_antiquark_red_shift]
  rw [anticommutator_quark_antiquark, ColorVec3.dot_smul_smul, h_prod, one_mul]

/-! ### 3a. Real Rapidity Parameterization -/

/-- The hyperbolic rotor's forward chiral weight is exactly `exp (2t)` when
the parameters are `cosh t` and `sinh t`. -/
theorem real_rapidity_forward_weight (t : ℝ) :
    (Real.cosh t + Real.sinh t)^2 = Real.exp (2 * t) := by
  rw [Real.cosh_add_sinh]
  calc (Real.exp t)^2 = Real.exp (t + t) := by rw [pow_two, ← Real.exp_add]
    _ = Real.exp (2 * t) := by congr 1; ring

/-- The opposite chiral weight is `exp (-2t)` under the same real
rapidity parameterization. -/
theorem real_rapidity_backward_weight (t : ℝ) :
    (Real.cosh t - Real.sinh t)^2 = Real.exp (-2 * t) := by
  have hlinear : Real.cosh t - Real.sinh t = Real.exp (-t) := by
    exact Real.cosh_sub_sinh t
  rw [hlinear]
  calc (Real.exp (-t))^2 = Real.exp (-t + -t) := by rw [pow_two, ← Real.exp_add]
    _ = Real.exp (-2 * t) := by congr 1; ring

/-- The real rapidity parameters automatically satisfy the inverse law used
by `modularDelta_has_inverse`. -/
theorem real_rapidity_hyperbolic_identity (t : ℝ) :
    (Real.cosh t)^2 - (Real.sinh t)^2 = 1 :=
  Real.cosh_sq_sub_sinh_sq t

/-- At surprisal rapidity, the modular rotor has the expected exponential
diagonal coordinates. This is a coordinate identity for the defined rotor;
it does not identify the rotor with an exponential of `modularHamiltonian`. -/
theorem modularDelta_surprisal_coordinates (I_surp : ℝ) :
    modularDelta (Real.cosh I_surp) (Real.sinh I_surp) =
      ⟨Real.exp I_surp, ColorVec3.zero, ColorVec3.zero, Real.exp (-I_surp)⟩ := by
  ext <;> simp [modularDelta, ColorVec3.zero, Real.cosh_add_sinh,
    Real.cosh_sub_sinh]

/-- The algebraic blue-shift formula specializes to the forward exponential
weight on the quark sheet. -/
theorem tomita_takesaki_quark_rapidity_shift (t : ℝ) (u : ColorVec3 ℝ) :
    tomitaTakesakiFlow (Real.cosh t) (Real.sinh t) (quark u) =
      quark (ColorVec3.smul (Real.exp (2 * t)) u) := by
  rw [tomita_takesaki_quark_blue_shift, real_rapidity_forward_weight]

/-- The algebraic red-shift formula specializes to the backward exponential
weight on the antiquark sheet. -/
theorem tomita_takesaki_antiquark_rapidity_shift (t : ℝ) (v : ColorVec3 ℝ) :
    tomitaTakesakiFlow (Real.cosh t) (Real.sinh t) (antiquark v) =
      antiquark (ColorVec3.smul (Real.exp (-2 * t)) v) := by
  rw [tomita_takesaki_antiquark_red_shift, real_rapidity_backward_weight]

end SplitOctonion

/-! ### 4. Concrete Integer Instantiations and Non-Commutativity -/

def canonicalColorVec3Int : ColorVec3 ℤ := ⟨1, 2, 3⟩

theorem canonicalColorVec3Int_nondegenerate :
    canonicalColorVec3Int ≠ default := by decide

theorem colorVec3_cross_noncommutative :
    ∃ u v : ColorVec3 ℤ, ColorVec3.cross u v ≠ ColorVec3.cross v u :=
  ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, by decide⟩

def canonicalSplitOctonionInt : SplitOctonion ℤ :=
  SplitOctonion.modularDelta 2 1

theorem canonicalSplitOctonionInt_nondegenerate :
    canonicalSplitOctonionInt ≠ default := by decide

def octonionBasisU1Int : SplitOctonion ℤ := SplitOctonion.quark ⟨1, 0, 0⟩
def octonionBasisU2Int : SplitOctonion ℤ := SplitOctonion.quark ⟨0, 1, 0⟩

theorem splitOctonion_mul_noncommutative_concrete :
    SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int ≠
      SplitOctonion.mul octonionBasisU2Int octonionBasisU1Int := by decide

theorem splitOctonion_mul_noncommutative :
    ∃ A B : SplitOctonion ℤ, SplitOctonion.mul A B ≠ SplitOctonion.mul B A :=
  ⟨octonionBasisU1Int, octonionBasisU2Int, splitOctonion_mul_noncommutative_concrete⟩

/-! ### 5. Master Synthesis of Sections 143 and 144 -/

theorem tomita_takesaki_modular_synthesis {R : Type*} [CommRing R]
    (c s : R) (u v : ColorVec3 R) (h_hyperbolic : c^2 - s^2 = 1) :
    SplitOctonion.tomitaTakesakiFlow c s (SplitOctonion.quark u) =
      SplitOctonion.quark (ColorVec3.smul ((c + s)^2) u) ∧
    SplitOctonion.tomitaTakesakiFlow c s (SplitOctonion.antiquark v) =
      SplitOctonion.antiquark (ColorVec3.smul ((c - s)^2) v) ∧
    SplitOctonion.anticommutator (SplitOctonion.tomitaTakesakiFlow c s (SplitOctonion.quark u))
                                 (SplitOctonion.tomitaTakesakiFlow c s (SplitOctonion.antiquark v)) =
      SplitOctonion.scale (ColorVec3.dot u v) SplitOctonion.one :=
  ⟨SplitOctonion.tomita_takesaki_quark_blue_shift c s u,
   SplitOctonion.tomita_takesaki_antiquark_red_shift c s v,
   SplitOctonion.tomita_takesaki_kms_invariant c s u v h_hyperbolic⟩

end InfoGeometry.Superalgebra.TomitaTakesaki
