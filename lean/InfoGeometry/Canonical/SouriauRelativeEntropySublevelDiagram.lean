import InfoGeometry.Canonical.SouriauRelativeEntropySublevelTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace SouriauRelativeEntropySublevelDiagram

open SouriauRelativeEntropySublevel
open SouriauRelativeEntropySimplex

variable {n : ℕ}

/-- Canonical inclusion between nested KL sublevels. -/
def relativeEntropyCoreSublevelInclusion
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    relativeEntropyCoreSublevel (n := n) ε c →
      relativeEntropyCoreSublevel (n := n) ε d :=
  fun p => ⟨p.1, relativeEntropyCoreSublevel_mono ε hcd p.2⟩

@[simp] theorem relativeEntropyCoreSublevelInclusion_coe
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d)
    (p : relativeEntropyCoreSublevel (n := n) ε c) :
    (relativeEntropyCoreSublevelInclusion ε hcd p :
      positiveSimplexCorePair (n := n) ε) = p.1 := rfl

theorem continuous_relativeEntropyCoreSublevelInclusion
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    Continuous (relativeEntropyCoreSublevelInclusion (n := n) ε hcd) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem injective_relativeEntropyCoreSublevelInclusion
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    Function.Injective
      (relativeEntropyCoreSublevelInclusion (n := n) ε hcd) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg
    (fun r : relativeEntropyCoreSublevel (n := n) ε d => r.1) hpq

theorem isClosedEmbedding_relativeEntropyCoreSublevelInclusion
    {ε : ℝ} (hεpos : 0 < ε) {c d : ℝ} (hcd : c ≤ d) :
    Topology.IsClosedEmbedding
      (relativeEntropyCoreSublevelInclusion (n := n) ε hcd) := by
  letI : CompactSpace (relativeEntropyCoreSublevel (n := n) ε c) :=
    isCompact_iff_compactSpace.mp
      (isCompact_relativeEntropyCoreSublevel (n := n) hεpos c)
  exact
    (continuous_relativeEntropyCoreSublevelInclusion
      (n := n) ε hcd).isClosedEmbedding
        (injective_relativeEntropyCoreSublevelInclusion
          (n := n) ε hcd)

theorem isEmbedding_relativeEntropyCoreSublevelInclusion
    {ε : ℝ} (hεpos : 0 < ε) {c d : ℝ} (hcd : c ≤ d) :
    Topology.IsEmbedding
      (relativeEntropyCoreSublevelInclusion (n := n) ε hcd) := by
  exact
    (isClosedEmbedding_relativeEntropyCoreSublevelInclusion
      hεpos hcd).isEmbedding

theorem isProperMap_relativeEntropyCoreSublevelInclusion
    {ε : ℝ} (hεpos : 0 < ε) {c d : ℝ} (hcd : c ≤ d) :
    IsProperMap
      (relativeEntropyCoreSublevelInclusion (n := n) ε hcd) := by
  exact
    (isClosedEmbedding_relativeEntropyCoreSublevelInclusion
      hεpos hcd).isProperMap

@[simp] theorem relativeEntropyCoreSublevelInclusion_refl
    (ε c : ℝ)
    (p : relativeEntropyCoreSublevel (n := n) ε c) :
    relativeEntropyCoreSublevelInclusion ε (le_refl c) p = p := by
  rfl

theorem relativeEntropyCoreSublevelInclusion_trans
    (ε : ℝ) {c d e : ℝ} (hcd : c ≤ d) (hde : d ≤ e)
    (p : relativeEntropyCoreSublevel (n := n) ε c) :
    relativeEntropyCoreSublevelInclusion ε hde
        (relativeEntropyCoreSublevelInclusion ε hcd p) =
      relativeEntropyCoreSublevelInclusion ε (hcd.trans hde) p := by
  rfl

end SouriauRelativeEntropySublevelDiagram
