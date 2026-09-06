import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagActionBijective

/-!
# Explicit witnesses for intrinsic flag orbits

This is the direct orbit interface for the intrinsic dependent flag carrier.
It exposes orbit membership as an explicit group-action witness and keeps
transitivity as a separate theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicFlagOrbitWitness

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction

theorem intrinsicFlag_mem_orbit_iff
    (F₀ F : IntrinsicFlag) :
    F ∈ MulAction.orbit SplitOctF2Aut F₀ ↔
      ∃ g : SplitOctF2Aut, intrinsicFlagMap g F₀ = F := by
  rw [MulAction.mem_orbit_iff]
  simp [smul_intrinsicFlag]

theorem intrinsicFlag_orbit_contains_base
    (F : IntrinsicFlag) :
    baseIntrinsicFlag ∈ MulAction.orbit SplitOctF2Aut F ↔
      ∃ g : SplitOctF2Aut, intrinsicFlagMap g F = baseIntrinsicFlag := by
  exact intrinsicFlag_mem_orbit_iff F baseIntrinsicFlag

end InfoGeometry.Algebra.Zorn.G2IntrinsicFlagOrbitWitness
