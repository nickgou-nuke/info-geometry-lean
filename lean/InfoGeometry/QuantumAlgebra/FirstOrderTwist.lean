import Mathlib

/-!
# Exact first-order twist algebra

The deformation parameter has square zero. These are exact algebra identities
modulo h^2, not an all-orders star product or a numerical approximation. A pair
of native derivations produces the leading inverse-twist term D(f) E(g), and
its Hochschild cocycle identity proves associativity of the constructed ring.
-/
noncomputable section
namespace InfoGeometry.QuantumAlgebra.FirstOrderTwist
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

structure Cocycle where
  bilinear : A →ₗ[R] A →ₗ[R] A
  one_left : ∀ b, bilinear 1 b = 0
  one_right : ∀ a, bilinear a 1 = 0
  law : ∀ a b c, bilinear a b*c + bilinear (a*b) c = a*bilinear b c + bilinear a (b*c)

/-- Leading term for the abelian inverse twist exp(h D tensor E). -/
def derivationCocycle (D E : Derivation R A A) : Cocycle (R := R) (A := A) where
  bilinear := (LinearMap.mul R A).compl₁₂ D.toLinearMap E.toLinearMap
  one_left := by intro b; simp
  one_right := by intro a; simp
  law := by
    intro a b c
    change D a * E b * c + D (a*b) * E c = a*(D b*E c)+D a*E (b*c)
    rw [D.leibniz, E.leibniz]
    simp only [smul_eq_mul]
    ring

namespace Cocycle

/-- The parameter is explicit, so different cocycles cannot share a ring instance. -/
def Jet (_c : Cocycle (R := R) (A := A)) := A × A

variable (c : Cocycle (R := R) (A := A))
instance : AddCommGroup c.Jet := inferInstanceAs (AddCommGroup (A × A))

/-- (a + h a1) star (b + h b1), with h^2 = 0. -/
def multiply (x y : c.Jet) : c.Jet :=
  (x.1*y.1, x.1*y.2+x.2*y.1+c.bilinear x.1 y.1)

theorem multiply_assoc (x y z : c.Jet) : c.multiply (c.multiply x y) z = c.multiply x (c.multiply y z) := by
  apply Prod.ext
  · exact mul_assoc _ _ _
  · change (x.1*y.1)*z.2+(x.1*y.2+x.2*y.1+c.bilinear x.1 y.1)*z.1+
        c.bilinear (x.1*y.1) z.1 =
      x.1*(y.1*z.2+y.2*z.1+c.bilinear y.1 z.1)+x.2*(y.1*z.1)+c.bilinear x.1 (y.1*z.1)
    linear_combination c.law x.1 y.1 z.1

instance : Ring c.Jet where
  __ := (inferInstance : AddCommGroup c.Jet)
  one := (1,0)
  mul := c.multiply
  natCast n := (n,0)
  intCast n := (n,0)
  natCast_zero := rfl
  natCast_succ n := by apply Prod.ext <;> simp [Nat.cast_add, Nat.cast_one]
  intCast_ofNat n := rfl
  intCast_negSucc n := by apply Prod.ext <;> simp
  mul_assoc := c.multiply_assoc
  one_mul x := by apply Prod.ext <;> simp [multiply, c.one_left]
  mul_one x := by apply Prod.ext <;> simp [multiply, c.one_right]
  zero_mul x := by apply Prod.ext <;> simp [multiply]
  mul_zero x := by apply Prod.ext <;> simp [multiply]
  left_distrib x y z := by apply Prod.ext <;> simp [multiply, mul_add, add_mul] <;> abel
  right_distrib x y z := by apply Prod.ext <;> simp [multiply, mul_add, add_mul] <;> abel

@[simp] theorem mul_fst (x y : c.Jet) : (x*y).1=x.1*y.1 := rfl
@[simp] theorem mul_snd (x y : c.Jet) : (x*y).2=x.1*y.2+x.2*y.1+c.bilinear x.1 y.1 := rfl

/-- Constant coefficient inclusion is additive, not in general multiplicative. -/
def constant (a : A) : c.Jet := (a,0)

def parameter : c.Jet := (0,1)

def classicalLimit : c.Jet →+* A where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem parameter_sq : c.parameter*c.parameter=0 := by
  apply Prod.ext
  · change (0 : A)*0=0
    simp
  · change (0 : A)*1+1*0+c.bilinear 0 0=0
    simp

theorem parameter_commutes (x : c.Jet) : c.parameter*x=x*c.parameter := by
  apply Prod.ext
  · change (0 : A)*x.1=x.1*0
    simp
  · change (0 : A)*x.2+1*x.1+c.bilinear 0 x.1=x.1*1+x.2*0+c.bilinear x.1 0
    simp

theorem constant_commutator (a b : A) :
    c.constant a*c.constant b-c.constant b*c.constant a =
      ((0,c.bilinear a b-c.bilinear b a) : c.Jet) := by
  apply Prod.ext
  · change a*b-b*a=0
    ring
  · change a*0+0*b+c.bilinear a b-(b*0+0*a+c.bilinear b a)=_
    simp

/-- Exact undeformed product on an invariant pair. -/
theorem constant_product_of_cocycle_zero (a b : A) (h : c.bilinear a b=0) :
    c.constant a*c.constant b=c.constant (a*b) := by
  apply Prod.ext
  · rfl
  · change a*0+0*b+c.bilinear a b=0
    simp [h]

end Cocycle

/-- The product is undeformed when the translation leg vanishes. -/
theorem invariant_fibre_product (D E : Derivation R A A) (a b : A) (ha : D a=0) :
    (derivationCocycle D E).constant a * (derivationCocycle D E).constant b =
      (derivationCocycle D E).constant (a*b) := by
  apply Cocycle.constant_product_of_cocycle_zero
  change D a*E b=0
  rw [ha, zero_mul]

/-- Commutativity within the fibre is not centrality with arbitrary fields. -/
theorem invariant_fibre_commutes (D E : Derivation R A A) (a b : A)
    (ha : D a=0) (hb : D b=0) :
    (derivationCocycle D E).constant a * (derivationCocycle D E).constant b =
      (derivationCocycle D E).constant b * (derivationCocycle D E).constant a := by
  rw [invariant_fibre_product D E a b ha, invariant_fibre_product D E b a hb, mul_comm a b]

/-- The differential on both coefficients is unchanged. -/
def liftDifferential (D E Z : Derivation R A A) :
    (derivationCocycle D E).Jet →+ (derivationCocycle D E).Jet where
  toFun x := (Z x.1,Z x.2)
  map_zero' := by apply Prod.ext <;> simp
  map_add' x y := by apply Prod.ext <;> simp

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
