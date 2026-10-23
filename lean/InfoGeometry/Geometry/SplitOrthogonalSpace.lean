/-
InfoGeometry/Geometry/SplitOrthogonalSpace.lean

Explicit split-orthogonal base-space carrier for the Narain / O(n,n) tower.
No complex imports.
-/

import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebraic.SplitQuadraticForm

noncomputable section

namespace InfoGeometry.Geometry.Cartan

open InfoGeometry.Algebraic.SplitSignature

/--
Abstract split-orthogonal Cartan base space.

This is the formal placeholder for the symmetric space
`O(n,n)/(O(n) × O(n))`. The concrete matrix model can be added later without
changing the downstream cocycle or boundary APIs.
-/
structure SplitOrthogonalCartanSpace (n : ℕ) where
  carrier : Type
  instTopologicalSpace : TopologicalSpace carrier

attribute [instance] SplitOrthogonalCartanSpace.instTopologicalSpace

/--
Abstract isotropic boundary carrier for split-orthogonal degeneration.

This is the natural boundary/readout object paired with
`SplitOrthogonalCartanSpace`.
-/
structure SplitOrthogonalBoundary (n : ℕ) where
  carrier : Type
  instTopologicalSpace : TopologicalSpace carrier

attribute [instance] SplitOrthogonalBoundary.instTopologicalSpace

/-! A concrete finite stage model.  The Cartan carrier is the diagonal split
module, while the boundary carrier is its isotropic-vector subtype.  These
are finite algebraic carriers; no quotient or analytic symmetric-space
identification is asserted. -/

def standardSplitOrthogonalCartanSpace (n : ℕ) : SplitOrthogonalCartanSpace n where
  carrier := SplitModule n
  instTopologicalSpace := inferInstance

def standardSplitOrthogonalBoundary (n : ℕ) : SplitOrthogonalBoundary n where
  carrier := {v : SplitModule n // splitQuadraticForm n v = 0}
  instTopologicalSpace := inferInstance

@[simp] theorem standardSplitOrthogonalCartanSpace_carrier (n : ℕ) :
    (standardSplitOrthogonalCartanSpace n).carrier = SplitModule n :=
  rfl

@[simp] theorem standardSplitOrthogonalBoundary_isotropic
    {n : ℕ} (v : (standardSplitOrthogonalBoundary n).carrier) :
    splitQuadraticForm n v.1 = 0 :=
  v.2

theorem standardSplitOrthogonalCartanSpace_nonempty (n : ℕ) :
    Nonempty (standardSplitOrthogonalCartanSpace n).carrier :=
  by
    change Nonempty (SplitModule n)
    exact ⟨0⟩

theorem standardSplitOrthogonalBoundary_nonempty (n : ℕ) :
    Nonempty (standardSplitOrthogonalBoundary n).carrier := by
  change Nonempty {v : SplitModule n // splitQuadraticForm n v = 0}
  exact ⟨⟨0, by simp [splitQuadraticForm]⟩⟩

end InfoGeometry.Geometry.Cartan
