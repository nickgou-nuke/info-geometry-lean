import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Banach

namespace InfoGeometry.Singular.MoorePenrose

postfix:max "†" => star

def IsMoorePenroseInverse (A B : Type*) [Ring A] [StarRing A] : Prop :=
  A * B * A = A ∧
  B * A * B = B ∧
  (A * B)† = A * B ∧
  (B * A)† = B * A

/-- The analytic closed-range Moore-Penrose existence and projector identities (see Mathlib v4.28.0 continuous-linear map API).

This package supersedes the old hand-constructed version and matches modern Mathlib conventions. See `MoorePenroseClosedRange` for details.
-*/
include "./sandbox_mp_authoritative.lean"

end InfoGeometry.Singular.MoorePenrose
