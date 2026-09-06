import InfoGeometry.Categorical.FibonacciFinitePentagonBridge
import InfoGeometry.Categorical.FibonacciHomSpace
import InfoGeometry.Categorical.FibonacciFusionCategoryData

/-!
# Typed finite Fibonacci pentagon readout

The golden finite `F12` calculation is promoted to the repository's native
`FibHom` carrier.  This is an actual Hom-space composition theorem.  The
carrier is deliberately the finite three-channel block; no global
`MonoidalCategory` or natural associator is inferred from this fixed-sector
readout.
-/

namespace InfoGeometry.Categorical.FibonacciFinitePentagonHom

open InfoGeometry.Categorical.FibonacciFinitePentagonBridge
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciHomSpace

noncomputable def pentagonChannelObject : FibCat :=
  Finsupp.single FibSimple.unit 3

theorem pentagonChannelObject_unit_count :
    pentagonChannelObject FibSimple.unit = 3 := by
  simp [pentagonChannelObject]

theorem pentagonChannelObject_tau_count :
    pentagonChannelObject FibSimple.tau = 0 := by
  simp [pentagonChannelObject]

noncomputable def goldenF12Hom : FibHom pentagonChannelObject pentagonChannelObject := by
  have hu : 3 = pentagonChannelObject FibSimple.unit :=
    pentagonChannelObject_unit_count.symm
  exact
    { unit_comp := Matrix.reindex (Equiv.cast (congrArg Fin hu))
        (Equiv.cast (congrArg Fin hu)) goldenF12Complex
      tau_comp := 0 }

theorem goldenF12Hom_pentagon :
    FibHom.comp (FibHom.comp goldenF12Hom goldenF12Hom) goldenF12Hom =
      goldenF12Hom := by
  have hu : 3 = pentagonChannelObject FibSimple.unit :=
    pentagonChannelObject_unit_count.symm
  let e : Fin 3 ≃ Fin (pentagonChannelObject FibSimple.unit) :=
    Equiv.cast (congrArg Fin hu)
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ =>
      Matrix.reindex e e M) golden_F12_complex_pentagon
  apply FibHom.ext
  · simpa [FibHom.comp, goldenF12Hom, e,
      Matrix.reindexLinearEquiv_mul] using h
  · simp [FibHom.comp, goldenF12Hom]

end InfoGeometry.Categorical.FibonacciFinitePentagonHom
