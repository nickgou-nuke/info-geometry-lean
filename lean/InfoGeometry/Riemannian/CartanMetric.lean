import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

namespace InfoGeometry.Riemannian

open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Дефиниране на следата на произволен паравектор като неговата скаларна част (grade 0).
    Имплементирано строго конструктивно чрез каноничния изоморфизъм с ExteriorAlgebra. -/
def hTrace_cl : CliffordAlgebra Q →ₗ[R] R :=
  (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R).toLinearMap.comp (CliffordAlgebra.equivExterior Q).toLinearMap

def hTrace (X : evenOdd Q 0) : R :=
  hTrace_cl Q X.val

theorem hTrace_add (A B : evenOdd Q 0) : hTrace Q (A + B) = hTrace Q A + hTrace Q B := by
  change hTrace_cl Q (A.val + B.val) = hTrace_cl Q A.val + hTrace_cl Q B.val
  exact map_add (hTrace_cl Q) A.val B.val

theorem hTrace_zero : hTrace Q 0 = 0 := by
  change hTrace_cl Q 0 = 0
  exact map_zero (hTrace_cl Q)

theorem hTrace_one : hTrace Q 1 = 1 := by
  have h1 : (1 : evenOdd Q 0).val = 1 := rfl
  change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R).toLinearMap (CliffordAlgebra.equivExterior Q 1) = 1
  simp

end InfoGeometry.Riemannian
