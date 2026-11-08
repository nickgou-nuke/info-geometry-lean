import Mathlib.Algebra.Ring.Associator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.Algebra

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- THE TEICHMÜLLER IDENTITY (Universal 4-element identity) -/
theorem teichmueller_identity (w x y z : R) :
    associator (w * x) y z - associator w (x * y) z + associator w x (y * z) =
      w * associator x y z + associator w x y * z := by
  dsimp [associator]
  -- Pure expansion and cancellation of terms
  noncomm_ring

end InfoGeometry.Algebra
