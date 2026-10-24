/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSRepresentation
import InfoGeometry.OperatorAlgebra.TracialGNSCommutator

/-!
# Bonding transport of native tracial GNS commutators

An algebraic commutator compatibility identity gives intertwining on native
PreGNS representatives, then on the existing completed GNS spaces by density.
A centralizing increment is a sufficient algebraic input, not an assumed GNS
transport field. Concrete onsite matrices are a separate consumer.
-/
noncomputable section

namespace CStarStateColimit.Native.FilteredTracialGNSCommutatorTransport

open FilteredGNS
open scoped ComplexOrder
universe u
variable {I : Type u} [Preorder I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

/-- Dense representative intertwining follows directly from the algebraic law. -/
theorem commutator_transport_toPreGNS {i j : I} (hij : i ≤ j)
    (tri : ∀ a b : Stage i, (ω.state i).functional (a * b) = (ω.state i).functional (b * a))
    (trj : ∀ a b : Stage j, (ω.state j).functional (a * b) = (ω.state j).functional (b * a))
    (H : Stage i) (K : Stage j)
    (hcompat : ∀ a : Stage i,
      K * sys.map hij a - sys.map hij a * K = sys.map hij (H * a - a * H))
    (a : Stage i) :
    (ω.state j).functional.tracialCommutatorGNS trj K
      (filteredGNSMapCLM Stage sys ω hij ((ω.state i).functional.toPreGNS a)) =
    filteredGNSMapCLM Stage sys ω hij
      ((ω.state i).functional.tracialCommutatorGNS tri H
        ((ω.state i).functional.toPreGNS a)) := by
  simp only [filteredGNSMapCLM_apply, filteredGNSMap_toPreGNS,
    PositiveLinearMap.tracialCommutatorGNS_toPreGNS, hcompat a]

/-- Equality of continuous maps on the dense native representatives extends to
all completed vectors; no representative-surjectivity claim is made. -/
theorem commutator_transport {i j : I} (hij : i ≤ j)
    (tri : ∀ a b : Stage i, (ω.state i).functional (a * b) = (ω.state i).functional (b * a))
    (trj : ∀ a b : Stage j, (ω.state j).functional (a * b) = (ω.state j).functional (b * a))
    (H : Stage i) (K : Stage j)
    (hcompat : ∀ a : Stage i,
      K * sys.map hij a - sys.map hij a * K = sys.map hij (H * a - a * H)) :
    ((ω.state j).functional.tracialCommutatorGNS trj K).comp
        (filteredGNSMapCLM Stage sys ω hij) =
      (filteredGNSMapCLM Stage sys ω hij).comp
        ((ω.state i).functional.tracialCommutatorGNS tri H) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    obtain ⟨a, rfl⟩ := (ω.state i).functional.toPreGNS.surjective x
    exact commutator_transport_toPreGNS Stage sys ω hij tri trj H K hcompat a

/-- An increment centralizing the old algebra preserves its commutator action. -/
theorem commutator_compatibility_of_centralizing_increment {i j : I} (hij : i ≤ j)
    (H : Stage i) (K : Stage j)
    (hc : ∀ a : Stage i, Commute (K - sys.map hij H) (sys.map hij a))
    (a : Stage i) :
    K * sys.map hij a - sys.map hij a * K = sys.map hij (H * a - a * H) := by
  calc
    K * sys.map hij a - sys.map hij a * K =
        ((K - sys.map hij H) * sys.map hij a - sys.map hij a * (K - sys.map hij H)) +
          (sys.map hij H * sys.map hij a - sys.map hij a * sys.map hij H) := by noncomm_ring
    _ = sys.map hij H * sys.map hij a - sys.map hij a * sys.map hij H := by
      rw [(hc a).eq, sub_self, zero_add]
    _ = sys.map hij (H * a - a * H) := by rw [map_sub, map_mul, map_mul]

/-- Completed transport from a primitive centralizing-increment condition. -/
theorem commutator_transport_of_centralizing_increment {i j : I} (hij : i ≤ j)
    (tri : ∀ a b : Stage i, (ω.state i).functional (a * b) = (ω.state i).functional (b * a))
    (trj : ∀ a b : Stage j, (ω.state j).functional (a * b) = (ω.state j).functional (b * a))
    (H : Stage i) (K : Stage j)
    (hc : ∀ a : Stage i, Commute (K - sys.map hij H) (sys.map hij a)) :
    ((ω.state j).functional.tracialCommutatorGNS trj K).comp
        (filteredGNSMapCLM Stage sys ω hij) =
      (filteredGNSMapCLM Stage sys ω hij).comp
        ((ω.state i).functional.tracialCommutatorGNS tri H) := by
  exact commutator_transport Stage sys ω hij tri trj H K
    (commutator_compatibility_of_centralizing_increment Stage sys hij H K hc)

end CStarStateColimit.Native.FilteredTracialGNSCommutatorTransport
