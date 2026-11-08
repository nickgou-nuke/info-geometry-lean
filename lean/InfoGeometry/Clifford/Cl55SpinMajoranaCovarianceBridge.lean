import InfoGeometry.Clifford.Cl55CAROperatorLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinOperatorAutomorphism

/-!
# Native `Spin(5,5)` Clifford/Majorana covariance

The native Clifford algebra already carries both ingredients of the
covariance square: `spinAction` on `V55` and the conjugation automorphism
`spinCliffordRingEquiv` on `Cl55`.  This owner records their compatibility on
the existing left Clifford generators.  It does not identify the split Spin
action with a positive-Hilbert Bogoliubov transformation.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinMajoranaCovarianceBridge

open InfoGeometry.Clifford.Clifford55

theorem spin55_majorana_generator_covariance
    (g : Spin55) (v : V55) (x : Cl55) :
    spinCliffordRingEquiv g (leftAction55 (ι55 v) x) =
      leftAction55 (ι55 (spinAction g v))
        (spinCliffordRingEquiv g x) := by
  rw [spinTransport_leftAction55_mul]
  rw [spinCliffordRingEquiv_vector_readback]

theorem spin55_majorana_generator_intertwines
    (g : Spin55) (v : V55) :
    (fun x : Cl55 => spinCliffordRingEquiv g (leftAction55 (ι55 v) x)) =
      (fun x : Cl55 =>
        leftAction55 (ι55 (spinAction g v))
          (spinCliffordRingEquiv g x)) := by
  funext x
  exact spin55_majorana_generator_covariance g v x

end InfoGeometry.Clifford.Cl55SpinMajoranaCovarianceBridge
