import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Clifford.SplitOctonionsDualProduct

namespace InfoGeometry.Quantum

open CliffordAlgebra
open InfoGeometry.Clifford.Hestenes

variable {R : Type*} [Field R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- 
Майорановото подпространство (Majorana Subspace).
Това е специфичното подпространство на паравекторите, където елементите са самоадюнгнати 
(γ_i^\dagger = γ_i) и антикомутират помежду си. 
В това подпространство седенионният комутационен дефект се анулира и 
удвояването на Cayley-Dickson запазва мултипликативността на нормата на Хурвиц.
-/
def MajoranaSubspace : Submodule R (ClPlus Q) :=
  sorry

-- Тук ще докажем строгата версия на седенионните аксиоми за елементи от това подпространство.
theorem hTrace_majorana_cancel_one {A B C D : ClPlus Q} 
    (hA : A ∈ MajoranaSubspace Q) (hB : B ∈ MajoranaSubspace Q) 
    (hC : C ∈ MajoranaSubspace Q) (hD : D ∈ MajoranaSubspace Q) :
    InfoGeometry.Riemannian.hTrace Q (D * C * A * hestenesAdjoint Q v0 B) = 
    InfoGeometry.Riemannian.hTrace Q (A * C * hestenesAdjoint Q v0 B * D) := by
  sorry

end InfoGeometry.Quantum
