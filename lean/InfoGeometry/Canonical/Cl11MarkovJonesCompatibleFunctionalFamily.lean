import InfoGeometry.Canonical.TensorColimitExpectation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
import InfoGeometry.Clifford.Cl11MarkovJonesEngine

/-!
# Compatible functional family for the finite `Cl(1,1)` tower

This owner uses the repository's existing `CompatibleFunctionalFamily`
interface.  The normalized Markov trace is packaged as a finite family, and
its compatibility is proved along the native one-step algebra embedding.  The
TopCat readout is related pointwise to the same family; no global completion or
state is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11MarkovJonesCompatibleFunctionalFamily

open InfoGeometry.Canonical.TensorColimitExpectation
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine

def cl11CompatibleFunctionalFamily :
    CompatibleFunctionalFamily
      (A := MatStage) cl11InductiveAlgebraNet.embed where
  omega := normalizedTraceLinear
  compatible := by
    intro n A
    exact cl11_normalizedTrace_one_step n A

theorem cl11CompatibleFunctionalFamily_compatible
    (n : ℕ) (A : MatStage n) :
    cl11CompatibleFunctionalFamily.omega (n + 1)
        (cl11InductiveAlgebraNet.embed n A) =
      cl11CompatibleFunctionalFamily.omega n A := by
  exact cl11_normalizedTrace_one_step n A

@[simp] theorem cl11CompatibleFunctionalFamily_apply
    (n : ℕ) (A : MatStage n) :
    cl11CompatibleFunctionalFamily.omega n A = normalizedTrace n A :=
  rfl

theorem cl11TopCatReadout_matches_functionalFamily
    (n : ℕ) (A : MatStage n) :
    normalizedTraceTopCatHom (n + 1)
        (stageEmbedTopCatHom n A) =
      cl11CompatibleFunctionalFamily.omega n A := by
  exact cl11_normalizedTrace_one_step n A

end InfoGeometry.Canonical.Cl11MarkovJonesCompatibleFunctionalFamily
