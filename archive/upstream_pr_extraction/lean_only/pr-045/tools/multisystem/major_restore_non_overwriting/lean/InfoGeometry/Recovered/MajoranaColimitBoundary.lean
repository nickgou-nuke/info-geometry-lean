import Mathlib
import InfoGeometry.Recovered.MajoranaTensorBridge
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Continuum Limit of Majorana Cuntz Boundaries

Following the Colimit Continuum Mandate, this file projects the finite 
16-dimensional algebraic boundaries (the nilpotent Cuntz generators 
from `MajoranaTensorBridge`) natively up the tensor tower into the 
infinite-dimensional topological colimit.
-/

namespace InfoGeometry.MajoranaColimitBoundary

open InfoGeometry.MajoranaTensorBridge

variable (MajoranaStage : ℕ → Type)
variable [∀ n, AddCommGroup (MajoranaStage n)] [∀ n, Module ℝ (MajoranaStage n)]
variable (iota : ∀ n, MajoranaStage n →ₗ[ℝ] MajoranaStage (n + 1))

/-- The colimit (continuum) boundary algebra (M_{4^∞}(ℝ)). -/
variable (MajoranaContinuum : Type) [AddCommGroup MajoranaContinuum] [Module ℝ MajoranaContinuum]
variable (psi : ∀ n, MajoranaStage n →ₗ[ℝ] MajoranaContinuum)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

/-- 
Assume the stage 1 is strictly isomorphic to our 16-dimensional 
Majorana matrix algebra M_4(ℝ).
-/
variable (baseEquiv : MajoranaStage 1 ≃ₗ[ℝ] MajoranaMatrix)

/--
Pushing the nilpotent Cuntz boundary generator S₊ up the Tensor Tower
into the continuum limit!
-/
noncomputable def continuumCuntzPlus : MajoranaContinuum :=
  psi 1 (baseEquiv.symm cuntzGeneratorPlus)

/--
Pushing the nilpotent Cuntz boundary generator S₋ up the Tensor Tower.
-/
noncomputable def continuumCuntzMinus : MajoranaContinuum :=
  psi 1 (baseEquiv.symm cuntzGeneratorMinus)

/--
The topological protection of the Amplituhedron Cuntz Boundaries.
If the nilpotent boundary states do not algebraically vanish at any finite tensor stage 
(i.e., they are protected by the trace topology), they provably survive 
into the infinite-dimensional colimit.
-/
theorem protected_cuntz_survives
    (colimit_kernel : ∀ (n : ℕ) (x : MajoranaStage n), psi n x = 0 → ∃ m, iota_seq MajoranaStage iota n m x = 0)
    (h_prot : IsTopologicallyProtected MajoranaStage iota 1 (baseEquiv.symm cuntzGeneratorPlus)) :
  continuumCuntzPlus MajoranaStage psi baseEquiv ≠ 0 := by
  apply protected_states_survive_colimit MajoranaStage iota MajoranaContinuum psi psi_comm colimit_kernel
  exact h_prot

end InfoGeometry.MajoranaColimitBoundary
