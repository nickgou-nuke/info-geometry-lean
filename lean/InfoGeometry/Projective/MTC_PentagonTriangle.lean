import Mathlib
import InfoGeometry.Projective.SplitOctonions.ZornMatrix

/-!
# Modular Tensor Coherence on the `ZornMatrix` Diagonal

Conservative MTC-style skeleton for the split-octonion boundary:
* diagonal states,
* diagonal product simplification, and
* diagonal `F`/`R` coherence equations.

No analytic TQFT completion is claimed in Lean.
-/

namespace InfoGeometry.Projective.MTC

open InfoGeometry.Projective.SplitOctonions
open InfoGeometry.Projective.SplitOctonions.ZornMatrix

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] R)

/-- Diagonal states used as the OP¹ coherence shell. -/
def IsDiag (x : ZornMatrix R V) : Prop := x.x21 = 0 ∧ x.x22 = 0

/-- Diagonal coercion law for diagonal states. -/
lemma isDiag_eq_diag (x : ZornMatrix R V) (hx : IsDiag (R := R) (V := V) x) :
    x = diag (R := R) (V := V) x.x11 x.x12 := by
  rcases x with ⟨x11, x12, x21, x22⟩
  rcases hx with ⟨h21, h22⟩
  subst x21
  subst x22
  rfl

/-- Consequence: multiplication with two diagonal states remains diagonal. -/
lemma mul_diag (a b : ZornMatrix R V)
    (ha : IsDiag (R := R) (V := V) a) (hb : IsDiag (R := R) (V := V) b) :
    mul B a b = diag (R := R) (V := V) (a.x11 * b.x11) (a.x12 * b.x12) := by
  rw [isDiag_eq_diag (R := R) (V := V) a ha, isDiag_eq_diag (R := R) (V := V) b hb]
  simp [ZornMatrix.mul]

/-- Associativity through a right diagonal bridge. -/
lemma mul_assoc_right
    (a b c : ZornMatrix R V)
    (hc : IsDiag (R := R) (V := V) c) :
    mul B (mul B a b) c = mul B a (mul B b c) := by
  simpa [isDiag_eq_diag (R := R) (V := V) c hc] using
    (ZornMatrix.diag_assoc_right (R := R) (V := V) B a b c.x11 c.x12)

/-- Diagonal `F` block on the boundary. -/
def FMatrix (x y z : ZornMatrix R V) : ZornMatrix R V :=
  mul B (mul B x y) z

/-- Diagonal `R` block on the boundary (swap witness). -/
def RMatrix (x y : ZornMatrix R V) : ZornMatrix R V :=
  mul B y x

/-- `((a*b)*c)*d = a*(b*(c*d))` on the diagonal shell. -/
theorem MacLane_Pentagon_Equation
    (a b c d : ZornMatrix R V)
    (ha : IsDiag (R := R) (V := V) a)
    (hb : IsDiag (R := R) (V := V) b)
    (hc : IsDiag (R := R) (V := V) c)
    (hd : IsDiag (R := R) (V := V) d) :
    mul B (mul B (mul B a b) c) d = mul B a (mul B b (mul B c d)) := by
  calc
    mul B (mul B (mul B a b) c) d
        = mul B (mul B a b) (mul B c d) :=
          mul_assoc_right (R := R) (V := V) B (mul B a b) c d hd
    _ = mul B a (mul B b (mul B c d)) := by
      simpa [isDiag_eq_diag (R := R) (V := V) b hb] using
        (ZornMatrix.diag_assoc_mid (R := R) (V := V) B a (mul B c d) b.x11 b.x12)

/-- Triangle identity with diagonal vacuum `diag 1 1`. -/
theorem MacLane_Triangle_Equation
    (a b : ZornMatrix R V)
    (ha : IsDiag (R := R) (V := V) a)
    (hb : IsDiag (R := R) (V := V) b) :
    FMatrix (B := B) a (diag (R := R) (V := V) 1 1) b = mul B a b := by
  calc
    FMatrix (B := B) a (diag (R := R) (V := V) 1 1) b
        = mul B (mul B a (diag (R := R) (V := V) 1 1)) b := rfl
    _ = mul B a (mul B (diag (R := R) (V := V) 1 1) b) := by
      simpa [isDiag_eq_diag (R := R) (V := V) b hb] using
        (ZornMatrix.diag_assoc_mid (R := R) (V := V) B a b 1 1)
    _ = mul B a b := by
      rw [mul_diag (R := R) (V := V) B (diag (R := R) (V := V) 1 1)
        (by simp) (hb)]
      simp

/-- Braiding/Fusion compatibility on the diagonal shell. -/
theorem MacLane_Hexagon_Equation
    (a b c : ZornMatrix R V)
    (ha : IsDiag (R := R) (V := V) a)
    (hb : IsDiag (R := R) (V := V) b)
    (hc : IsDiag (R := R) (V := V) c) :
    RMatrix (B := B) (mul B a b) c = mul B (RMatrix (B := B) a c) b := by
  simpa [RMatrix] using
    (ZornMatrix.diag_assoc_right (R := R) (V := V) B c a b.x11 b.x12
      |> Eq.symm)

end InfoGeometry.Projective.MTC
