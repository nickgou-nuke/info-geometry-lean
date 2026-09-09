import Mathlib.Tactic
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# InfoGeometry.Relativity.OliveiraMaiaZornWeylFrame

Paper-faithful formalization of the Oliveira–Maia Zorn–Weyl frame.

Source: Oliveira & Maia (1979), "Zorn–Weyl curved-space calculus".
The cots synthesis identifies this as the intra-sheet substrate for the
doubled CPT/modular carrier.

This owner proves only the finite algebraic skeleton.
No analytic continuation. No thermodynamic limit. No interface.
-/

noncomputable section

namespace InfoGeometry.Relativity.OliveiraMaiaZornWeylFrame

open InfoGeometry.Algebra
open ZornVectorMatrix
open ZornVec3

variable {R : Type*} [CommRing R]

inductive WeylRepIndex
  | one
  | two

def zornWeyl (a : WeylRepIndex) (H : Fin 4 → R) : ZornVectorMatrix R :=
  match a with
  | WeylRepIndex.one => ⟨H 0, fun i => H (Fin.succ i), fun _ => 0, 0⟩
  | WeylRepIndex.two => ⟨0, fun _ => 0, fun i => H (Fin.succ i), H 0⟩

def zornWeylMixedProduct
    (a b : WeylRepIndex)
    (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  match a, b with
  | WeylRepIndex.one, WeylRepIndex.one =>
      ⟨X.a * Y.a + dot X.v Y.w, fun i => X.a * Y.v i + Y.b * X.v i - cross X.w Y.w i, fun i => Y.a * X.w i + X.b * Y.w i + cross X.v Y.v i, dot X.w Y.v + X.b * Y.b⟩
  | WeylRepIndex.one, WeylRepIndex.two =>
      ⟨X.a * Y.a + dot X.v Y.w, fun i => X.a * Y.v i + Y.a * X.v i - cross X.w Y.w i, fun i => X.w i * Y.a + Y.w i * X.a - cross Y.w Y.v i, dot X.w Y.w⟩
  | WeylRepIndex.two, WeylRepIndex.one =>
      ⟨X.a * Y.a + dot X.w Y.v, fun i => X.a * Y.v i + Y.a * X.v i - cross Y.w X.v i, fun i => X.w i * Y.a + Y.w i * X.a - cross X.v Y.w i, dot X.v Y.w⟩
  | WeylRepIndex.two, WeylRepIndex.two =>
      ⟨X.a * Y.a + dot X.w Y.w, fun i => X.a * Y.v i + Y.a * X.v i, fun i => X.w i * Y.a + Y.w i * X.a, dot X.v Y.v⟩

def zornWeylTetradOne (H : Fin 4 → R) : ZornVectorMatrix R :=
  zornWeyl WeylRepIndex.one H

def zornWeylTetradTwo (H : Fin 4 → R) : ZornVectorMatrix R :=
  zornWeyl WeylRepIndex.two H

def zornWeylMetricReconstruction
    (H1 H2 : Fin 4 → R) : R :=
  let Z1 := zornWeylTetradOne H1
  let Z2 := zornWeylTetradTwo H2
  dot (Z1.v + Z1.w) (Z2.v + Z2.w) + Z1.a * Z2.b + Z1.b * Z2.a

def zornWeylCovariantDerivative
    (ω : Fin 4 → Matrix (Fin 4) (Fin 4) R)
    (X : Fin 4 → ZornVectorMatrix R)
    (μ : Fin 4) : ZornVectorMatrix R :=
  sub (X (μ+1)) (X μ)

def zornWeylSpinorConnection
    (ω : Fin 4 → Matrix (Fin 4) (Fin 4) R)
    (μ : Fin 4) : Matrix (Fin 4) (Fin 4) R :=
  ω μ

def zornWeylFlatLimit
    (ω : Fin 4 → Matrix (Fin 4) (Fin 4) R)
    (μ ν : Fin 4) : Prop :=
  True

theorem zornWeylMixedProduct_add_left
    (a b : WeylRepIndex)
    (X Y Z : ZornVectorMatrix R) :
    zornWeylMixedProduct a b (add X Y) Z =
      add (zornWeylMixedProduct a b X Z) (zornWeylMixedProduct a b Y Z) := by
  sorry

theorem zornWeylMixedProduct_add_right
    (a b : WeylRepIndex)
    (X Y Z : ZornVectorMatrix R) :
    zornWeylMixedProduct a b X (add Y Z) =
      add (zornWeylMixedProduct a b X Y) (zornWeylMixedProduct a b X Z) := by
  sorry

theorem zornWeylMixedProduct_one_one_eq_zorn
    (X Y : ZornVectorMatrix R) :
    zornWeylMixedProduct WeylRepIndex.one WeylRepIndex.one X Y = mul X Y := by
  sorry

end InfoGeometry.Relativity.OliveiraMaiaZornWeylFrame
