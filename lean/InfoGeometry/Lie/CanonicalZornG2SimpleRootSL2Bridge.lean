import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornCartanRootSystem
import InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy
import InfoGeometry.Lie.CanonicalZornG2LiteratureBridge

/-!
# Simple-root prerequisites for the `𝔰𝔩₂` bridge

The native repository already has the fourteen-dimensional Cartan/root
decomposition and opposite-root nondegeneracy.  This owner packages the two
simple-root indices and the closed consequences available from that API.

The normalized Chevalley relations `[e,f] = h`, `[h,e] = 2e`, and
`[h,f] = -2f` are deliberately not asserted here: their structure constants
are a separate computation.  Thus this file contains no unproved obligation
and does not claim an `𝔰𝔩₂` triple before normalization is proved.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2SimpleRootSL2Bridge

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der

def simpleRootIndex : Fin 2 → nonzeroIndex :=
  ![⟨10, by decide, by decide⟩, ⟨1, by decide, by decide⟩]

def oppositeSimpleRootIndex : Fin 2 → nonzeroIndex :=
  ![⟨0, by decide, by decide⟩, ⟨5, by decide, by decide⟩]

theorem simpleRoot_positive_weight (i : Fin 2) :
    rootWeight (simpleRootIndex i).1 =
      if i = 0 then rootWeight 10 else rootWeight 1 := by
  fin_cases i <;> simp [simpleRootIndex]

theorem simpleRoot_negative_weight (i : Fin 2) :
    rootWeight (oppositeSimpleRootIndex i).1 =
      -rootWeight (simpleRootIndex i).1 := by
  fin_cases i
  · ext k
    have h := rootWeight_neg_pair_0_10 k
    change rootWeight 0 k = -rootWeight 10 k
    linarith
  · ext k
    have h := rootWeight_neg_pair_1_5 k
    change rootWeight 5 k = -rootWeight 1 k
    linarith

theorem simpleRoot_bracket_mem_cartan (i : Fin 2) :
    ⁅rootDerivation (simpleRootIndex i).1,
      rootDerivation (oppositeSimpleRootIndex i).1⁆ ∈ cartanRootSpan := by
  apply rootDerivation_bracket_mem_cartan_of_neg
  exact simpleRoot_negative_weight i

/-- The native opposite-root Cartan candidate, before Chevalley normalization. -/
def simpleRootCartan (i : Fin 2) : Der :=
  ⁅rootDerivation (oppositeSimpleRootIndex i).1,
    rootDerivation (simpleRootIndex i).1⁆

theorem simpleRootCartan_mem_cartan (i : Fin 2) :
    simpleRootCartan i ∈ cartanRootSpan := by
  unfold simpleRootCartan
  apply rootDerivation_bracket_mem_cartan_of_neg
  ext k
  have h := simpleRoot_negative_weight i
  have hk := congrArg (fun w => w k) h
  change rootWeight (oppositeSimpleRootIndex i).1 k =
    -(rootWeight (simpleRootIndex i).1 k) at hk
  change rootWeight (simpleRootIndex i).1 k =
    -rootWeight (oppositeSimpleRootIndex i).1 k
  linarith

set_option maxHeartbeats 800000 in
theorem shortSimpleRoot_double_bracket_nonzero :
    ⁅⁅rootDerivation (oppositeSimpleRootIndex 0).1,
        rootDerivation (simpleRootIndex 0).1⁆,
      rootDerivation (oppositeSimpleRootIndex 0).1⁆ ≠ 0 := by
  simpa [simpleRootIndex, oppositeSimpleRootIndex] using
    opposite_root_double_bracket_0_10

set_option maxHeartbeats 800000 in
theorem longSimpleRoot_double_bracket_nonzero :
    ⁅⁅rootDerivation (simpleRootIndex 1).1,
        rootDerivation (oppositeSimpleRootIndex 1).1⁆,
      rootDerivation (simpleRootIndex 1).1⁆ ≠ 0 := by
  simpa [simpleRootIndex, oppositeSimpleRootIndex] using
    opposite_root_double_bracket_1_5

theorem simpleRootCartan_ne_zero (i : Fin 2) :
    simpleRootCartan i ≠ 0 := by
  intro hzero
  fin_cases i
  · have hdouble :
        ⁅simpleRootCartan 0,
          rootDerivation (oppositeSimpleRootIndex 0).1⁆ ≠ 0 := by
      simpa [simpleRootCartan, simpleRootIndex, oppositeSimpleRootIndex] using
        shortSimpleRoot_double_bracket_nonzero
    have hz : simpleRootCartan 0 = 0 := by simpa using hzero
    apply hdouble
    rw [hz]
    simp
  · have hdouble := longSimpleRoot_double_bracket_nonzero
    have hz : simpleRootCartan 1 = 0 := by simpa using hzero
    apply hdouble
    have hskew :
        ⁅rootDerivation (simpleRootIndex 1).1,
            rootDerivation (oppositeSimpleRootIndex 1).1⁆ =
          -simpleRootCartan 1 := by
      simpa [simpleRootCartan] using
        (lie_skew (rootDerivation (oppositeSimpleRootIndex 1).1)
          (rootDerivation (simpleRootIndex 1).1)).symm
    rw [hskew, hz]
    simp

end InfoGeometry.Lie.CanonicalZornG2SimpleRootSL2Bridge
