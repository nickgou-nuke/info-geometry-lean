import InfoGeometry.Core.Derivatives
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Core Derivatives Smoke

Smoke checks for the legacy import shim `InfoGeometry.Core.Derivatives`.
These examples compile only if declarations from
`InfoGeometry.Core.GrandCanonical` are available through the legacy path.
-/

namespace InfoGeometry.Core

section

variable {α : Type _} [Fintype α] [Nonempty α]
variable (params : GrandCanonicalParams α) (β : ℝ)

example : 0 < partition params β :=
  gc_partition_pos params β

example : deriv (potential params) β = -mean params β :=
  gc_potential_deriv_eq_neg_mean params β

example : hessian params β = variance params β :=
  gc_potential_second_derivative_eq_variance params β

end

end InfoGeometry.Core

