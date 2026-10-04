import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import InfoGeometry.Canonical.SylvesterGrading

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.BraidedDerivation

open InfoGeometry.Canonical.SylvesterGrading

variable {R : Type*} [CommRing R]
variable {Γ : Type*} [AddCommMonoid Γ]
variable {A : Type*} [Ring A] [Algebra R A]

/-- A homogeneous element of degree `deg` in the graded algebra A. -/
structure HomogeneousElement (Γ : Type*) (A : Type*) where
  val : A
  deg : Γ

/-- Product of two homogeneous elements with additive grading. -/
def mulHomogeneous (a b : HomogeneousElement Γ A) : HomogeneousElement Γ A :=
  ⟨a.val * b.val, a.deg + b.deg⟩

/-- A Braided Derivation of degree `deg` on an R-algebra A equipped with bicharacter B:
    D(a * b) = D(a) * b + β(|a|, |D|) • (a * D(b)). -/
structure BraidedDerivation (Γ : Type*) [AddCommMonoid Γ] (R : Type*) [CommRing R]
    (A : Type*) [Ring A] [Algebra R A] (B : GradingBicharacter Γ R) where
  toFun : A → A
  deg : Γ
  map_add : ∀ x y : A, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ (r : R) (x : A), toFun (r • x) = r • toFun x
  leibniz_homogeneous : ∀ (a : HomogeneousElement Γ A) (b : A),
    toFun (a.val * b) = toFun a.val * b + (B.β a.deg deg : R) • (a.val * toFun b)

instance (B : GradingBicharacter Γ R) :
    CoeFun (BraidedDerivation Γ R A B) (fun _ => A → A) where
  coe D := D.toFun

theorem braided_derivation_pow_two (B : GradingBicharacter Γ R)
    (D : BraidedDerivation Γ R A B) (x : HomogeneousElement Γ A) :
    D (x.val ^ 2) = D x.val * x.val + (B.β x.deg D.deg : R) • (x.val * D x.val) := by
  have h2 : x.val ^ 2 = x.val * x.val := sq x.val
  rw [h2]
  exact D.leibniz_homogeneous x x.val

theorem braided_derivation_pow_two_comm (B : GradingBicharacter Γ R)
    (D : BraidedDerivation Γ R A B) (x : HomogeneousElement Γ A)
    (hcomm : x.val * D x.val = D x.val * x.val) :
    D (x.val ^ 2) = (1 + (B.β x.deg D.deg : R)) • (D x.val * x.val) := by
  calc
    D (x.val ^ 2) = D x.val * x.val + (B.β x.deg D.deg : R) • (x.val * D x.val) := by rw [braided_derivation_pow_two]
    _ = D x.val * x.val + (B.β x.deg D.deg : R) • (D x.val * x.val) := by rw [hcomm]
    _ = (1 + (B.β x.deg D.deg : R)) • (D x.val * x.val) := by rw [add_smul, one_smul]

theorem braided_leibniz_three (B : GradingBicharacter Γ R)
    (D : BraidedDerivation Γ R A B)
    (a b : HomogeneousElement Γ A) (c : A) :
    D ((a.val * b.val) * c) =
      D a.val * b.val * c +
      (B.β a.deg D.deg : R) • (a.val * D b.val * c) +
      ((B.β a.deg D.deg : R) * (B.β b.deg D.deg : R)) • (a.val * b.val * D c) := by
  calc
    D ((a.val * b.val) * c) = D (a.val * b.val) * c + (B.β (a.deg + b.deg) D.deg : R) • ((a.val * b.val) * D c) := by
      exact D.leibniz_homogeneous (mulHomogeneous a b) c
    _ = (D a.val * b.val + (B.β a.deg D.deg : R) • (a.val * D b.val)) * c + (B.β (a.deg + b.deg) D.deg : R) • ((a.val * b.val) * D c) := by
      rw [D.leibniz_homogeneous a b.val]
    _ = D a.val * b.val * c + ((B.β a.deg D.deg : R) • (a.val * D b.val)) * c + (B.β (a.deg + b.deg) D.deg : R) • ((a.val * b.val) * D c) := by
      rw [add_mul]
    _ = D a.val * b.val * c + (B.β a.deg D.deg : R) • (a.val * D b.val * c) + (B.β (a.deg + b.deg) D.deg : R) • ((a.val * b.val) * D c) := by
      rw [smul_mul_assoc]
    _ = D a.val * b.val * c + (B.β a.deg D.deg : R) • (a.val * D b.val * c) + ((B.β a.deg D.deg : R) * (B.β b.deg D.deg : R)) • (a.val * b.val * D c) := by
      have h_add : (B.β (a.deg + b.deg) D.deg : R) = (B.β a.deg D.deg : R) * (B.β b.deg D.deg : R) := by
        rw [B.map_add_left, Units.val_mul]
      rw [h_add]

def innerBraidedOp (B : GradingBicharacter Γ R)
    (x : HomogeneousElement Γ A) (y : HomogeneousElement Γ A) : A :=
  x.val * y.val - (B.β y.deg x.deg : R) • (y.val * x.val)

theorem inner_braided_derivation_leibniz (B : GradingBicharacter Γ R)
    (x a b : HomogeneousElement Γ A) :
    innerBraidedOp B x (mulHomogeneous a b) =
      innerBraidedOp B x a * b.val +
      (B.β a.deg x.deg : R) • (a.val * innerBraidedOp B x b) := by
  dsimp [innerBraidedOp, mulHomogeneous]
  calc
    x.val * (a.val * b.val) - (B.β (a.deg + b.deg) x.deg : R) • (a.val * b.val * x.val)
      = x.val * (a.val * b.val) - ((B.β a.deg x.deg : R) * (B.β b.deg x.deg : R)) • (a.val * b.val * x.val) := by
        have h_add : (B.β (a.deg + b.deg) x.deg : R) = (B.β a.deg x.deg : R) * (B.β b.deg x.deg : R) := by
          rw [B.map_add_left, Units.val_mul]
        rw [h_add]
    _ = x.val * a.val * b.val - ((B.β a.deg x.deg : R) * (B.β b.deg x.deg : R)) • (a.val * (b.val * x.val)) := by
      rw [← mul_assoc, mul_assoc a.val b.val x.val]
    _ = x.val * a.val * b.val - (B.β a.deg x.deg : R) • ((B.β b.deg x.deg : R) • (a.val * (b.val * x.val))) := by
      rw [smul_smul]
    _ = x.val * a.val * b.val - (B.β a.deg x.deg : R) • (a.val * ((B.β b.deg x.deg : R) • (b.val * x.val))) := by
      rw [Algebra.mul_smul_comm]
    _ = (x.val * a.val - (B.β a.deg x.deg : R) • (a.val * x.val)) * b.val +
        (B.β a.deg x.deg : R) • (a.val * (x.val * b.val - (B.β b.deg x.deg : R) • (b.val * x.val))) := by
      rw [sub_mul, smul_mul_assoc, mul_sub, smul_sub]
      rw [mul_assoc a.val x.val b.val]
      abel

end InfoGeometry.Canonical.BraidedDerivation
