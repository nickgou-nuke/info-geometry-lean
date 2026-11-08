import InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Pin55ProjectivePureSpinorGrassmannianEquivariance
import InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
import InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

/-!
# Projective annihilator transport for the native split Pin action

This owner records the projective specialization of the already-proved
representative-level annihilator equivariance.  It does not assert a
projective group action or a converse pure-spinor classification.
-/

noncomputable section

namespace InfoGeometry.Twistor.Pin55ProjectiveAnnihilatorTransport

open scoped LinearAlgebra.Projectivization
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Pin55PureSpinorAnnihilatorEquivariance
open InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction
open InfoGeometry.Twistor.Pin55ProjectivePureSpinorGrassmannianEquivariance

theorem realPin55_projectiveAnnihilator_mk
    (g : InfoGeometry.Clifford.Clifford55.RealPin55) (ψ : Spinor) (hψ : ψ ≠ 0) :
    projectivePureSpinorAnnihilator
        (Projectivization.mk ℝ
          (realPin55ExteriorSpinorLinearEquiv g ψ)
          (by
            intro hz
            apply hψ
            apply (realPin55ExteriorSpinorLinearEquiv g).injective
            simpa using hz)) =
      Submodule.map (realPin55NeutralTransport g).toLinearMap
        (projectivePureSpinorAnnihilator
          (Projectivization.mk ℝ ψ hψ)) := by
  rw [projectivePureSpinorAnnihilator_mk,
    projectivePureSpinorAnnihilator_mk]
  exact realPin55_annihilator_equivariant g ψ

theorem realPin55_projectiveGrassmannianPoint_mk
    (g : InfoGeometry.Clifford.Clifford55.RealPin55) (ψ : Spinor)
    (hψ : ψ ≠ 0) (hψg : IsPureSpinor (realPin55ExteriorSpinorLinearEquiv g ψ)) :
    (projectivePureSpinorGrassmannianPoint
        ⟨Projectivization.mk ℝ
            (realPin55ExteriorSpinorLinearEquiv g ψ)
            (by
              intro hz
              apply hψ
              apply (realPin55ExteriorSpinorLinearEquiv g).injective
              simpa using hz),
          (projectivePureSpinor_mk_iff _ _).2 hψg⟩).1 =
      Submodule.map (realPin55NeutralTransport g).toLinearMap
        (projectivePureSpinorAnnihilator
          (Projectivization.mk ℝ ψ hψ)) := by
  rw [projectivePureSpinorGrassmannianPoint_val]
  exact realPin55_projectiveAnnihilator_mk g ψ hψ

end InfoGeometry.Twistor.Pin55ProjectiveAnnihilatorTransport
