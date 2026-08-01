import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import InfoGeometry.Canonical.ChiralConeOctonionicBridge

namespace InfoGeometry.Canonical

variable {R : Type*} [Field R] [CharZero R]

/-- 
**The Octonionic Cuntz Isomorphism**
We define the Cuntz projections P₁ and P₂ via the Weyl lightcone projectors 
of the Split-Octonions.
-/
def CuntzP1 (u : R) : R := lightconePlus u
def CuntzP2 (u : R) : R := lightconeMinus u

/-- 
Theorem: The Octonionic Lightcone projectors exactly satisfy the Cuntz Algebra 
projection axioms: P₁² = P₁, P₂² = P₂, P₁P₂ = 0, P₁ + P₂ = 1.
-/
theorem octonionic_cuntz_isomorphism (u : R) (hu : u * u = 1) :
    CuntzP1 u * CuntzP1 u = CuntzP1 u ∧
    CuntzP2 u * CuntzP2 u = CuntzP2 u ∧
    CuntzP1 u * CuntzP2 u = 0 ∧
    CuntzP1 u + CuntzP2 u = 1 := by
  have h1 : CuntzP1 u * CuntzP1 u = CuntzP1 u := lightconePlus_idempotent u hu
  have h2 : CuntzP2 u * CuntzP2 u = CuntzP2 u := lightconeMinus_idempotent u hu
  have h3 : CuntzP1 u * CuntzP2 u = 0 := lightcone_orthogonality u hu
  have h4 : CuntzP1 u + CuntzP2 u = 1 := lightcone_resolution u
  exact ⟨h1, h2, h3, h4⟩

end InfoGeometry.Canonical
