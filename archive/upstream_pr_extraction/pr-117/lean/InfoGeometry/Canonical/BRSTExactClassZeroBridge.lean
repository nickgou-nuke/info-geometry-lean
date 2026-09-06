import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BRSTExactClassZeroBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Canonical Map Embedding Range into Kernel for Nilpotent Operator Q² = 0. -/
def brstExactToClosed
    (q : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0) :
    LinearMap.range q →ₗ[R] LinearMap.ker q where
  toFun x := ⟨x.1, by
    rcases x.2 with ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    have h_comp : q (q y) = 0 := LinearMap.congr_fun hq2 y
    rw [← hy]
    exact h_comp⟩
  map_add' := by intro x y; rfl
  map_smul' := by intro r x; rfl

/-- **Definition**: Pure BRST Cohomology Module H_Q = ker Q / range(exactToClosed). -/
def brstCohomologyModule
    (q : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0) : Type _ :=
  LinearMap.ker q ⧸ LinearMap.range (brstExactToClosed q hq2)

/-- **Theorem**: Literal BRST Exact State Class Zero [Q χ] = 0 in BRST Cohomology Module H_Q. -/
theorem exact_state_class_eq_zero
    (q : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (chi : ExteriorAlgebra R V) :
    Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨q chi, by
        have h := LinearMap.congr_fun hq2 chi
        rw [LinearMap.mem_ker]
        exact h⟩ = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  use ⟨q chi, LinearMap.mem_range_self q chi⟩
  rfl


end InfoGeometry.Canonical.BRSTExactClassZeroBridge
