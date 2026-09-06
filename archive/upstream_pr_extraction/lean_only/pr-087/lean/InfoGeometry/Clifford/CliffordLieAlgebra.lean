import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Clifford.ClNN

noncomputable section

namespace InfoGeometry.Clifford

open CliffordAlgebra

/-- 
The Lie algebra of bivectors in a Clifford algebra Cl(Q).
These span a Lie subalgebra isomorphic to so(Q).
-/
def soLieAlgebra {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) : 
    LieSubalgebra R (CliffordAlgebra Q) :=
  LieSubalgebra.lieSpan R (CliffordAlgebra Q) (Set.range (fun p : M × M => ⁅ι Q p.1, ι Q p.2⁆))

/-- The Lie algebra so(n,n) realized inside Clsplit n. -/
def soNN (n : ℕ) : LieSubalgebra ℝ (InfoGeometry.CliffordTower.Clsplit n) :=
  soLieAlgebra (InfoGeometry.CliffordTower.Qsplit n)

namespace soNN

variable {n : ℕ}

/-- A bivector generator [e_i, e_j] in so(n,n). -/
def bivector (m1 m2 : InfoGeometry.CliffordTower.SplitSpace n) : soNN n :=
  ⟨⁅ι (InfoGeometry.CliffordTower.Qsplit n) m1, ι (InfoGeometry.CliffordTower.Qsplit n) m2⁆, 
   LieSubalgebra.subset_lieSpan (Set.mem_range_self (m1, m2))⟩

end soNN

end InfoGeometry.Clifford

