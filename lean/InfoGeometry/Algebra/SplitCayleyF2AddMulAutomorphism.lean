import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

/-! An additive and multiplicative automorphism interface for the Cayley
carrier.  This is intentionally separate from `Automorphism`: the latter is
the smaller multiplicative interface used by the explicit finite actions. -/
structure AddMulAutomorphism where
  toEquiv : Cayley ≃ Cayley
  map_zero' : toEquiv zero = zero
  map_add' : ∀ x y, toEquiv (add x y) = add (toEquiv x) (toEquiv y)
  map_mul' : ∀ x y, toEquiv (x * y) = toEquiv x * toEquiv y
  map_one' : toEquiv one = one

instance : CoeFun AddMulAutomorphism (fun _ => Cayley → Cayley) :=
  ⟨fun φ => φ.toEquiv⟩

theorem AddMulAutomorphism.map_add (φ : AddMulAutomorphism) (x y : Cayley) :
    φ (add x y) = add (φ x) (φ y) :=
  φ.map_add' x y

theorem AddMulAutomorphism.map_zero (φ : AddMulAutomorphism) :
    φ zero = zero :=
  φ.map_zero'

theorem AddMulAutomorphism.map_mul (φ : AddMulAutomorphism) (x y : Cayley) :
    φ (x * y) = φ x * φ y :=
  φ.map_mul' x y

theorem AddMulAutomorphism.map_one (φ : AddMulAutomorphism) :
    φ one = one :=
  φ.map_one'

end InfoGeometry.Algebra.SplitCayleyF2
