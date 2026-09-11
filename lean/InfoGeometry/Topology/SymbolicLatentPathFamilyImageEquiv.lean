import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartEquivalence
import InfoGeometry.Topology.SymbolicLatentPathFamily

namespace InfoGeometry.Topology

/-!
# Homeomorphic transport of path-family images

An equivalence of latent charts transports a jointly continuous family by its
latent homeomorphism.  The induced map on family images is therefore itself a
homeomorphism, with no quotient or metric assumptions.
-/

namespace SymbolicLatentChartEquivalence

def mapFamily
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    SymbolicLatentPathFamily P Y :=
  { toFun := fun q => F.latentEquiv (H q)
    continuous_toFun := F.latentEquiv.continuous_toFun.comp H.continuous }

theorem mapFamily_apply
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X)
    (q : P × SymbolicPathDomain) :
    F.mapFamily H q = F.latentEquiv (H q) :=
  rfl

def imageHomeomorph
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImage H ≃ₜ
      symbolicLatentPathFamilyImage (F.mapFamily H) :=
  { toFun := fun y =>
      ⟨F.latentEquiv y.1, by
        rcases y.2 with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [← hq]
        rfl⟩
    invFun := fun y =>
      ⟨F.latentEquiv.symm y.1, by
        rcases y.2 with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [← hq]
        exact (F.latentEquiv.left_inv (H q)).symm⟩
    left_inv := by
      intro y
      apply Subtype.ext
      simp
    right_inv := by
      intro y
      apply Subtype.ext
      simp
    continuous_toFun := by
      exact (F.latentEquiv.continuous_toFun.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := by
      exact (F.latentEquiv.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk _ }

@[simp] theorem imageHomeomorph_apply
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X)
    (y : symbolicLatentPathFamilyImage H) :
    F.imageHomeomorph H y =
      ⟨F.latentEquiv y.1, by
        rcases y.2 with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [← hq]
        rfl⟩ :=
  rfl

end SymbolicLatentChartEquivalence

end InfoGeometry.Topology
