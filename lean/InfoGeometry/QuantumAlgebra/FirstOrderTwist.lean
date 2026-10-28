/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Exact first-order twist algebra

The deformation parameter has square zero. These are exact identities modulo
h^2, not an all-orders star product. A native bilinear cocycle constructs an
associative ring; associativity is proved, not assumed as a field.
-/
noncomputable section
namespace InfoGeometry.QuantumAlgebra.FirstOrderTwist
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

structure Cocycle where
  bilinear : A →ₗ[R] A →ₗ[R] A
  one_left : ∀ b, bilinear 1 b = 0
  one_right : ∀ a, bilinear a 1 = 0
  law : ∀ a b c, bilinear a b*c + bilinear (a*b) c = a*bilinear b c + bilinear a (b*c)

/-- Leading term for the ordered abelian inverse twist exp(h D tensor E). -/
def derivationCocycle (D E : Derivation R A A) : Cocycle (R := R) (A := A) where
  bilinear := (LinearMap.mul R A).compl₁₂ D.toLinearMap E.toLinearMap
  one_left := by intro b; simp
  one_right := by intro a; simp
  law := by
    intro a b c
    change D a * E b * c + D (a*b) * E c = a*(D b*E c)+D a*E (b*c)
    rw [D.leibniz, E.leibniz]
    simp only [smul_eq_mul]
    ring_nf

namespace Cocycle

def Jet (_c : Cocycle (R := R) (A := A)) := A × A
variable (c : Cocycle (R := R) (A := A))
instance instJetNatCast : NatCast c.Jet := ⟨fun n => ((n : A), (0 : A))⟩
instance instJetIntCast : IntCast c.Jet := ⟨fun n => ((n : A), (0 : A))⟩

@[ext] theorem jet_ext {x y : c.Jet} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  apply Prod.ext <;> assumption

instance : AddCommGroup c.Jet := inferInstanceAs (AddCommGroup (A × A))
instance : One c.Jet := ⟨(1,0)⟩

/-- (a + h a1) star (b + h b1), with h^2 = 0. -/
def multiply (x y : c.Jet) : c.Jet :=
  (x.1*y.1, x.1*y.2+x.2*y.1+c.bilinear x.1 y.1)

instance : Mul c.Jet := ⟨c.multiply⟩

theorem multiply_assoc (x y z : c.Jet) : c.multiply (c.multiply x y) z = c.multiply x (c.multiply y z) := by
  apply Prod.ext
  · exact mul_assoc _ _ _
  · change (x.1*y.1)*z.2+(x.1*y.2+x.2*y.1+c.bilinear x.1 y.1)*z.1+
        c.bilinear (x.1*y.1) z.1 =
      x.1*(y.1*z.2+y.2*z.1+c.bilinear y.1 z.1)+x.2*(y.1*z.1)+c.bilinear x.1 (y.1*z.1)
    linear_combination c.law x.1 y.1 z.1

instance : Ring c.Jet where
  __ := (inferInstance : AddCommGroup c.Jet)
  __ := (inferInstance : One c.Jet)
  __ := (inferInstance : Mul c.Jet)
  __ := instJetNatCast c
  __ := instJetIntCast c
  natCast_zero := by
    apply jet_ext
    · change ((0 : ℕ) : A) = 0
      simp
    · rfl
  natCast_succ n := by
    apply Prod.ext
    · change ((n+1 : ℕ) : A)=(n : A)+1
      simp
    · change (0 : A)=0+0
      simp
  intCast_ofNat n := by
    apply Prod.ext
    · change ((n : ℤ) : A)=(n : A)
      simp
    · rfl
  intCast_negSucc n := by
    apply Prod.ext
    · change ((Int.negSucc n : ℤ) : A) = -((n+1 : ℕ) : A)
      simp
    · change (0 : A) = -0
      simp
  mul_assoc := c.multiply_assoc
  npow n x := Nat.rec 1 (fun _ y => y * x) n
  npow_zero := by intro x; rfl
  npow_succ := by intro n x; rfl
  one_mul x := by
    apply Prod.ext
    · change (1 : A)*x.1=x.1
      simp
    · change (1 : A)*x.2+0*x.1+c.bilinear 1 x.1=x.2
      simp [c.one_left]
  mul_one x := by
    apply Prod.ext
    · change x.1*(1 : A)=x.1
      simp
    · change x.1*(0 : A)+x.2*1+c.bilinear x.1 1=x.2
      simp [c.one_right]
  zero_mul x := by
    apply Prod.ext
    · change (0 : A)*x.1=0
      simp
    · change (0 : A)*x.2+0*x.1+c.bilinear 0 x.1=0
      simp
  mul_zero x := by
    apply Prod.ext
    · change x.1*(0 : A)=0
      simp
    · change x.1*(0 : A)+x.2*0+c.bilinear x.1 0=0
      simp
  left_distrib x y z := by
    apply Prod.ext
    · change x.1*(y.1+z.1)=x.1*y.1+x.1*z.1
      exact mul_add _ _ _
    · change x.1*(y.2+z.2)+x.2*(y.1+z.1)+c.bilinear x.1 (y.1+z.1)=
        (x.1*y.2+x.2*y.1+c.bilinear x.1 y.1)+(x.1*z.2+x.2*z.1+c.bilinear x.1 z.1)
      rw [map_add]
      ring
  right_distrib x y z := by
    apply Prod.ext
    · change (x.1+y.1)*z.1=x.1*z.1+y.1*z.1
      exact add_mul _ _ _
    · change (x.1+y.1)*z.2+(x.2+y.2)*z.1+c.bilinear (x.1+y.1) z.1=
        (x.1*z.2+x.2*z.1+c.bilinear x.1 z.1)+(y.1*z.2+y.2*z.1+c.bilinear y.1 z.1)
      simp only [map_add, LinearMap.add_apply]
      ring

@[simp] theorem mul_fst (x y : c.Jet) : (x*y).1=x.1*y.1 := rfl
@[simp] theorem mul_snd (x y : c.Jet) : (x*y).2=x.1*y.2+x.2*y.1+c.bilinear x.1 y.1 := rfl

def constant (a : A) : c.Jet := (a,0)
def parameter : c.Jet := (0,1)

@[simp] theorem constant_mul (a b : A) :
    c.constant a * c.constant b = (a*b, c.bilinear a b) := by
  change c.multiply (a, 0) (b, 0) = (a*b, c.bilinear a b)
  simp [Cocycle.multiply]
  rfl

def classicalLimit : c.Jet →+* A where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' x y := by
    change x.1 + y.1 = x.1 + y.1
    rfl

@[simp] theorem parameter_sq : c.parameter*c.parameter=0 := by
  change c.multiply (0, 1) (0, 1) = (0, 0)
  simp [Cocycle.multiply]
  rfl

theorem parameter_commutes (x : c.Jet) : c.parameter*x=x*c.parameter := by
  apply Prod.ext
  · change (0 : A)*x.1=x.1*0
    simp
  · change (0 : A)*x.2+1*x.1+c.bilinear 0 x.1=x.1*1+x.2*0+c.bilinear x.1 0
    simp

theorem constant_commutator (a b : A) :
    c.constant a*c.constant b-c.constant b*c.constant a =
      ((0,c.bilinear a b-c.bilinear b a) : c.Jet) := by
  rw [constant_mul, constant_mul]
  change ((a*b - b*a, c.bilinear a b - c.bilinear b a) : A × A) =
    (0, c.bilinear a b - c.bilinear b a)
  apply Prod.ext
  · ring
  · rfl

theorem constant_product_of_cocycle_zero (a b : A) (h : c.bilinear a b=0) :
    c.constant a*c.constant b=c.constant (a*b) := by
  rw [constant_mul]
  change (a*b, c.bilinear a b) = (a*b, 0)
  apply Prod.ext <;> simp [h]

end Cocycle

theorem invariant_fibre_product (D E : Derivation R A A) (a b : A) (ha : D a=0) :
    (derivationCocycle D E).constant a * (derivationCocycle D E).constant b =
      (derivationCocycle D E).constant (a*b) := by
  apply Cocycle.constant_product_of_cocycle_zero
  change D a*E b=0
  rw [ha, zero_mul]

theorem invariant_fibre_commutes (D E : Derivation R A A) (a b : A)
    (ha : D a=0) (hb : D b=0) :
    (derivationCocycle D E).constant a * (derivationCocycle D E).constant b =
      (derivationCocycle D E).constant b * (derivationCocycle D E).constant a := by
  rw [invariant_fibre_product D E a b ha, invariant_fibre_product D E b a hb, mul_comm a b]

def liftDifferential (D E Z : Derivation R A A) :
    (derivationCocycle D E).Jet →+ (derivationCocycle D E).Jet where
  toFun x := (Z x.1,Z x.2)
  map_zero' := by
    change (Z 0, Z 0) = (0, 0)
    simp
  map_add' x y := by
    change (Z (x.1 + y.1), Z (x.2 + y.2)) =
      (Z x.1 + Z y.1, Z x.2 + Z y.2)
    exact Prod.ext (map_add Z x.1 y.1) (map_add Z x.2 y.2)

theorem liftDifferential_leibniz (D E Z : Derivation R A A)
    (hZD : ∀ a, Z (D a)=D (Z a)) (hZE : ∀ a, Z (E a)=E (Z a))
    (x y : (derivationCocycle D E).Jet) :
    liftDifferential D E Z (x*y) = liftDifferential D E Z x*y+x*liftDifferential D E Z y := by
  apply Prod.ext
  · change Z (x.1*y.1)=Z x.1*y.1+x.1*Z y.1
    rw [Z.leibniz]
    simp only [smul_eq_mul]
    ring
  · change Z (x.1*y.2+x.2*y.1+D x.1*E y.1) =
      Z x.1*y.2+Z x.2*y.1+D (Z x.1)*E y.1+
        (x.1*Z y.2+x.2*Z y.1+D x.1*E (Z y.1))
    simp only [map_add, Z.leibniz, smul_eq_mul, hZD, hZE]
    ring

end InfoGeometry.QuantumAlgebra.FirstOrderTwist
