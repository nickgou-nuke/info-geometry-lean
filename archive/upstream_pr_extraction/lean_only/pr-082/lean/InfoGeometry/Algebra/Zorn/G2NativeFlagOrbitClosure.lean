import InfoGeometry.Algebra.Zorn.G2NativeCandidateFiberAction

/-!
# Closure of the native full-flag orbit

The native point/fibre assembly gives surjectivity of the action map.  This
owner records the immediate orbit and cardinality consequences without
identifying the native carrier with the separate intrinsic flag carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagOrbitClosure

open InfoGeometry.Algebra.Zorn.G2NativeCandidateFiberAction
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem nativeFlag_orbit_eq_univ :
    MulAction.orbit SplitOctF2Aut nativeBaseFlag = Set.univ := by
  ext F
  rw [nativeFlag_mem_orbit_iff]
  constructor
  · intro h
    exact Set.mem_univ F
  · intro _
    obtain ⟨g, hg⟩ := nativeFlag_orbit_surjective F
    exact ⟨g, hg⟩

/-! The action-theoretic quotient attached to the native orbit.  This is the
    canonical orbit--stabilizer bridge; it does not identify the stabilizer
    with the PC subgroup. -/
noncomputable def nativeFlag_quotientStabilizerEquiv :
    G2NativeFullFlagCarrier.NativeFlag ≃
      SplitOctF2Aut ⧸ MulAction.stabilizer SplitOctF2Aut nativeBaseFlag := by
  exact (Equiv.Set.univ G2NativeFullFlagCarrier.NativeFlag).symm.trans
    ((Equiv.setCongr nativeFlag_orbit_eq_univ).symm.trans
      (MulAction.orbitEquivQuotientStabilizer
        SplitOctF2Aut nativeBaseFlag))

/-! Once the reverse stabilizer inclusion is proved, this same canonical
    equivalence specializes to the quotient by the native unipotent subgroup.
    The equality is an explicit argument rather than a hidden carrier
    identification. -/
noncomputable def nativeFlag_quotientUnipotentEquiv_of_stabilizer_eq
    (hstab :
      MulAction.stabilizer SplitOctF2Aut nativeBaseFlag =
        G2TwoPCSubgroupClosure.unipotentSubgroup) :
    G2NativeFullFlagCarrier.NativeFlag ≃
      SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup := by
  rw [← hstab]
  exact nativeFlag_quotientStabilizerEquiv

end InfoGeometry.Algebra.Zorn.G2NativeFlagOrbitClosure
