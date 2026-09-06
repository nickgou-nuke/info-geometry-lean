import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# IsROrK (minimal scaffold)

Lightweight repo-local scaffold mirroring the paper's `is_R_or_C` interface,
but with a real carrier plus an involutive symmetry `sigma`.

This file is intentionally minimal and non-authoritative; constructive owner
results remain in existing Krein modules.
-/

namespace InfoGeometry.OperatorAlgebra

class IsROrK (K : Type*) extends NormedAddCommGroup K, InnerProductSpace ℝ K, CompleteSpace K where
  sigma : K →L[ℝ] K
  sigma_invol : sigma.comp sigma = ContinuousLinearMap.id ℝ K
  sigma_selfAdj : ContinuousLinearMap.adjoint sigma = sigma

namespace IsROrK

variable {K : Type*} [IsROrK K]

@[simp] theorem sigma_invol_apply (x : K) : IsROrK.sigma (IsROrK.sigma x) = x := by
  have h := congrArg (fun T : K →L[ℝ] K => T x) (IsROrK.sigma_invol (K := K))
  simpa using h

end IsROrK

end InfoGeometry.OperatorAlgebra
