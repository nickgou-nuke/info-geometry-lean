import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanReflectionEnsembleConsumer

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

variable {State : Type*} [Fintype State] [Nonempty State]

theorem short_reflection_partition_invariant_via_generic
    (W : WeylEquivariantEnsemble State) (beta : Fin 2 → ℝ) :
    realGibbsPartition W.datum (canonicalShortReflectionDualReal beta) =
      realGibbsPartition W.datum beta := by
  exact realGibbsPartition_short_invariant W beta

theorem long_reflection_partition_invariant_via_generic
    (W : WeylEquivariantEnsemble State) (beta : Fin 2 → ℝ) :
    realGibbsPartition W.datum (canonicalLongReflectionDualReal beta) =
      realGibbsPartition W.datum beta := by
  exact realGibbsPartition_long_invariant W beta

end InfoGeometry.Lie.CanonicalZornG2CartanReflectionEnsembleConsumer
