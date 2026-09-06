import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Twisted chiral projection corners

This is the algebraic linking layer.  A corner is a sandwich subspace of one
ring; the off-diagonal blocks are bimodule-shaped sandwich subspaces.  No
geometric or differential structure is assumed.
-/

namespace InfoGeometry.Clifford.TwistedChiralProjectionAlgebra

variable {A : Type*} [Ring A]

def corner (p : A) (hp : p * p = p) :=
  {x : A // p * x * p = x}

def cornerProduct {p : A} {hp : p * p = p}
    (x y : corner p hp) : corner p hp :=
  ⟨x.1 * y.1, by
    change p * (x.1 * y.1) * p = x.1 * y.1
    have hx : p * x.1 = x.1 := by
      rw [← x.2]
      calc
        p * (p * x.1 * p) = (p * p) * x.1 * p := by simp [mul_assoc]
        _ = p * x.1 * p := by rw [hp]
    have hy : y.1 * p = y.1 := by
      rw [← y.2]
      calc
        (p * y.1 * p) * p = p * y.1 * (p * p) := by simp [mul_assoc]
        _ = p * y.1 * p := by rw [hp]
    calc
      p * (x.1 * y.1) * p = (p * x.1) * (y.1 * p) := by simp [mul_assoc]
      _ = x.1 * y.1 := by rw [hx, hy]
  ⟩

theorem cornerProduct_value {p : A} {hp : p * p = p}
    (x y : corner p hp) : (cornerProduct x y).1 = x.1 * y.1 := rfl

def linkingBlock (p q x : A) : Prop := p * x * q = x

def twistedTransport (τ : A →+* A) (x : A) : A := τ x

@[simp] theorem twistedTransport_mul (τ : A →+* A) (x y : A) :
    twistedTransport τ (x * y) =
      twistedTransport τ x * twistedTransport τ y := by
  exact τ.map_mul x y

end InfoGeometry.Clifford.TwistedChiralProjectionAlgebra
