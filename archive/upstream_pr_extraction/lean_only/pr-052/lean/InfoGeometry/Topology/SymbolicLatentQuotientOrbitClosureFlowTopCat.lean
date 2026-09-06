import Mathlib
import InfoGeometry.Topology.SymbolicLatentQuotientFlowTopCat
import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transport of modular-flow orbit closures

The homeomorphic flow slice already transports orbit closures at the set
level.  This owner records the same result for the categorical flow
morphism, without introducing a new orbit or closure construction.
-/

theorem SymbolicLatentFlowQuotient.actTopCatHom_image_orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s : ℝ) (q : Q) :
    K.actTopCatHom s '' K.orbitClosure q =
      K.orbitClosure (K.act s q) := by
  change K.actHomeomorph s '' K.orbitClosure q =
    K.orbitClosure (K.act s q)
  exact K.actHomeomorph_image_orbitClosure s q

theorem SymbolicLatentFlowQuotient.actTopCatHom_image_orbit
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s : ℝ) (q : Q) :
    K.actTopCatHom s '' K.orbit q =
      K.orbit (K.act s q) := by
  change K.actHomeomorph s '' K.orbit q =
    K.orbit (K.act s q)
  exact K.actHomeomorph_image_orbit s q

theorem SymbolicLatentFlowQuotient.isCompact_actTopCatHom_image_orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    [CompactSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s : ℝ) (q : Q) :
    IsCompact (K.actTopCatHom s '' K.orbitClosure q) := by
  rw [K.actTopCatHom_image_orbitClosure s q]
  exact isCompact_symbolicLatentOrbitClosure K (K.act s q)

theorem SymbolicLatentFlowQuotient.isClosed_actTopCatHom_image_orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s : ℝ) (q : Q) :
    IsClosed (K.actTopCatHom s '' K.orbitClosure q) := by
  rw [K.actTopCatHom_image_orbitClosure s q]
  exact K.isClosed_orbitClosure (K.act s q)

end InfoGeometry.Topology
