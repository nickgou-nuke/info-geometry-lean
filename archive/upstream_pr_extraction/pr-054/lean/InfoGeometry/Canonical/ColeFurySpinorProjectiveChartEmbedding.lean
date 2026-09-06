import InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions

noncomputable section

namespace InfoGeometry.Canonical.ColeFurySpinorProjectiveChartEmbedding

open InfoGeometry.Algebra.ColeFurySpinorBridge
open InfoGeometry.Canonical.ColeFurySpinorProjectiveTopology
open InfoGeometry.Canonical.ColeFurySpinorProjectiveChart
open InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions

/-- The underlying nonzero spinor represented by a chart point. -/
def chartToNonzero (i : Fin 32) : CoordinateChart i → NonzeroSpinor :=
  Subtype.val

/-- The global projective class represented by a local chart class. -/
def projectiveChartToProjective (i : Fin 32) :
    ProjectiveChart i → ProjectiveSpinor :=
  Quotient.lift (fun ψ => projectiveSpinorMap (chartToNonzero i ψ)) (by
    intro a b h
    rcases h with ⟨u, hu⟩
    apply Quotient.sound
    refine ⟨u, ?_⟩
    exact congrArg Subtype.val hu)

theorem continuous_projectiveChartToProjective (i : Fin 32) :
    Continuous (projectiveChartToProjective i) := by
  apply Continuous.quotient_lift
  exact continuous_projectiveSpinorMap.comp continuous_subtype_val

@[simp]
theorem projectiveChartToProjective_map (i : Fin 32)
    (ψ : CoordinateChart i) :
    projectiveChartToProjective i (chartMap i ψ) =
      projectiveSpinorMap (chartToNonzero i ψ) :=
  rfl

end InfoGeometry.Canonical.ColeFurySpinorProjectiveChartEmbedding
