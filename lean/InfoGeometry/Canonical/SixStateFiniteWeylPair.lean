import InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.HestenesCuntzPhaseSpace

/-!
# The packaged finite Weyl pair on the six-state carrier

The existing order-six matrices are now exposed through the repository's
native `FiniteWeylPair` structure.  This is a Weyl-pair representation
contract; it is deliberately weaker than a separately proved homomorphism
from the coordinate Heisenberg group.
-/

namespace InfoGeometry.Canonical.SixStateFiniteWeylPair

open InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra
open InfoGeometry.Physics.HestenesCuntzPhaseSpace

noncomputable section

def sixWeylPair (ω : ℂ) (hω : ω ^ 3 = 1) :
    FiniteWeylPair 6 SixMatrix where
  coordinate := sixWeylX
  momentum := sixWeylZ ω
  q := sixWeylRoot ω
  q_pow_dim := sixWeylRoot_six ω hω
  weyl_relation := sixWeylZ_mul_sixWeylX ω hω

@[simp] theorem sixWeylPair_coordinate (ω : ℂ) (hω : ω ^ 3 = 1) :
    (sixWeylPair ω hω).coordinate = sixWeylX := rfl

@[simp] theorem sixWeylPair_momentum (ω : ℂ) (hω : ω ^ 3 = 1) :
    (sixWeylPair ω hω).momentum = sixWeylZ ω := rfl

@[simp] theorem sixWeylPair_phase (ω : ℂ) (hω : ω ^ 3 = 1) :
    (sixWeylPair ω hω).q = sixWeylRoot ω := rfl

theorem sixWeylPair_relation (ω : ℂ) (hω : ω ^ 3 = 1) :
    (sixWeylPair ω hω).momentum * (sixWeylPair ω hω).coordinate =
      (sixWeylPair ω hω).q •
        ((sixWeylPair ω hω).coordinate * (sixWeylPair ω hω).momentum) := by
  exact (sixWeylPair ω hω).weyl_relation

theorem sixWeylPair_phase_order
    (ω : ℂ) (hω : ω ^ 3 = 1) (hω_ne_one : ω ≠ 1) :
    orderOf (sixWeylPair ω hω).q = 6 := by
  simpa using sixWeylRoot_order ω hω hω_ne_one

end

end InfoGeometry.Canonical.SixStateFiniteWeylPair
