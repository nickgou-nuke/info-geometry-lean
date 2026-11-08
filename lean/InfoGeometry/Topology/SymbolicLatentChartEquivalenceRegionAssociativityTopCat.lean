import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartEquivalenceRegionTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Associativity of symbolic-latent chart-region transitions

Three successive chart equivalences induce the same `TopCat` transition map
whether their latent/feature equivalences are parenthesised on the left or on
the right.  The statement is made directly on the transported feature region,
so the subtype carriers and their topology are part of the checked theorem.
-/

theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_assoc
    {X Y Z W : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    {Fchart : SymbolicLatentChart W ι}
    (H : SymbolicLatentChartEquivalence E Fchart)
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    ((H.comp G).comp F).latentFeatureRegionTopCatHom R =
      (H.comp (G.comp F)).latentFeatureRegionTopCatHom R := by
  apply TopCat.hom_ext
  ext x
  rfl

end InfoGeometry.Topology
