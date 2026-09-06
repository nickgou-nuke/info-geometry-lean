import InfoGeometry.Projective.HadjiivanovLogConnectionKleinBridge
import InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge

/-!
# Klein--braid synthesis for algebraic logarithmic connections

Klein inversion acts on the Laurent base and braid transport acts on the
finite fiber.  Hence their lifted actions commute.  Combining the two already
proved connection intertwining laws gives a single coherent transport square.

This remains a finite algebraic theorem on `ℂ[T,T⁻¹] ⊗ V`.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionSynthesisBridge

open scoped TensorProduct
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionKleinBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Base inversion and fiber braid transport commute on every section. -/
theorem sectionInversion_sectionBraidTransport_commute
    (F : LogResidueBraidFrame V) (g : BraidGroup) (x : LogSection V) :
    sectionInversion (sectionBraidTransport F g x) =
      sectionBraidTransport F g (sectionInversion x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro f v
    simp
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Combined Klein--braid connection transport on the full tensor carrier. -/
theorem logarithmicConnection_klein_braid
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3)
    (x : LogSection V) :
    logarithmicConnection
        (reverseResidue (frameResidue F (braidPermutation g a)))
        (sectionInversion (sectionBraidTransport F g x)) =
      -sectionBraidTransport F g
        (sectionInversion (logarithmicConnection (frameResidue F a) x)) := by
  rw [logarithmicConnection_reverse]
  rw [logarithmicConnection_braid]
  rw [sectionInversion_sectionBraidTransport_commute]

/-- The combined transport identity packaged as equality of linear maps. -/
theorem logarithmicConnection_klein_braid_comp
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) :
    (logarithmicConnection
        (reverseResidue (frameResidue F (braidPermutation g a)))).comp
        (sectionInversion.comp (sectionBraidTransport F g)) =
      (-sectionBraidTransport F g).comp
        (sectionInversion.comp (logarithmicConnection (frameResidue F a))) := by
  apply LinearMap.ext
  intro x
  exact logarithmicConnection_klein_braid F g a x

end

end InfoGeometry.Projective.HadjiivanovLogConnectionSynthesisBridge
