import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SuperchargeHoppingBridge
import Mathlib

/-!
# InfoGeometry.Canonical.SuperchargeOddOddDecomposition

Proof-carrying decomposition of odd-odd supercharge closure into transport,
central, and defect lanes.

This is the honest discrete/quasilattice shadow:

* odd-odd closure is primitive,
* translation/hopping is a distinguished component of that closure,
* central and defect lanes are separated explicitly,
* entropy-production vanishes on the central/BPS kernel lane.

No continuum super-Poincare theorem is claimed here.
-/

namespace InfoGeometry.Canonical.SuperchargeOddOddDecomposition

open InfoGeometry.Canonical.SuperchargeHoppingBridge

section Core

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Norm-based entropy-production shadow of an operator on a state. -/
@[rep_depth operator]
def entropyProductionShadow (A : EndH) (ψ : E) : ℝ :=
  ‖A ψ‖

/--
Proof-carrying odd-odd decomposition data.

`translationCandidate` is the discrete hopping/transport lane,
`centralCandidate` is the protected topological lane,
`defectCandidate` collects the residual nontransport piece.
-/
@[rep_depth operator]
structure OddOddDecompositionData where
  Qi : EndH
  Qj : EndH
  translationCandidate : EndH
  centralCandidate : EndH
  defectCandidate : EndH
  oddOdd_decomposition :
    oddOddBracket Qi Qj =
      translationCandidate + centralCandidate + defectCandidate

namespace OddOddDecompositionData

variable (D : OddOddDecompositionData (E := E))

/-- The central/BPS lane is the kernel of the central candidate. -/
@[rep_depth operator]
noncomputable def centralBPSCore : Submodule ℝ E :=
  D.centralCandidate.ker

/-- The odd-odd bracket decomposes into translation, central, and defect lanes. -/
@[capstone, rep_depth operator]
theorem oddOddBracket_decomposes :
    oddOddBracket D.Qi D.Qj =
      D.translationCandidate + D.centralCandidate + D.defectCandidate :=
  D.oddOdd_decomposition

/-- Entropy production vanishes on the central/BPS kernel lane. -/
@[capstone, rep_depth operator]
theorem entropyProduction_vanishes_on_centralCore
    (ψ : E) (h_core : ψ ∈ D.centralBPSCore) :
    entropyProductionShadow D.centralCandidate ψ = 0 := by
  unfold entropyProductionShadow centralBPSCore at *
  rw [show D.centralCandidate ψ = 0 from h_core]
  simp

/-- Combined packet for the odd-odd decomposition lane. -/
@[rep_depth operator]
theorem oddOdd_decomposition_packet :
    (oddOddBracket D.Qi D.Qj =
      D.translationCandidate + D.centralCandidate + D.defectCandidate)
      ∧
    (∀ ψ : E, ψ ∈ D.centralBPSCore →
      entropyProductionShadow D.centralCandidate ψ = 0) := by
  refine ⟨D.oddOddBracket_decomposes, ?_⟩
  intro ψ hψ
  exact D.entropyProduction_vanishes_on_centralCore ψ hψ

end OddOddDecompositionData

end Core

end InfoGeometry.Canonical.SuperchargeOddOddDecomposition
