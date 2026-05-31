/-
InfoGeometry/Carrier/Bridge.lean

Bridging lemmas connecting the local Carrier abstractions to the projective
Krein infrastructure.
-/

import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import InfoGeometry.Carrier.TripleAlgebra
import InfoGeometry.Carrier.SupergradedHopping
import InfoGeometry.Carrier.HestenesKrein

namespace InfoGeometry.Carrier

open InfoGeometry.Krein

/--
Construct a `HestenesKreinSpace` from an involutive self-dual carrier,
assuming the standard positivity witness for the induced Hilbert pairing.
-/
def hestenesKreinSpaceFromCarrier
    (X : InvolutiveSelfDualCarrier)
    (hpos : ∀ v : X.H, v ≠ 0 → 0 < X.kreinPairing v (X.J v)) :
    HestenesKreinSpace X.H :=
  { krein_form := X.kreinPairing
    J := X.J.toLinearMap
    J_involution := by
      ext x
      simpa [LinearMap.comp_apply] using congrArg (fun f : X.H →L[ℝ] X.H => f x) X.J_sq
    induced_hilbert_identity := hpos }

/-- View a Bogoliubov tilt as a plain linear map. -/
noncomputable def BogoliubovTilt.toLinearMap {V : Type*}
    [AddCommGroup V] [Module ℝ V] [HestenesKreinSpace V]
    (Θ : BogoliubovTilt V) : V →ₗ[ℝ] V := Θ.tilt

/-- The Bogoliubov tilt preserves the chosen Krein form by definition. -/
theorem BogoliubovTilt.preserves_krein_form {V : Type*}
    [AddCommGroup V] [Module ℝ V] [HestenesKreinSpace V]
    (Θ : BogoliubovTilt V) (u v : V) :
    HestenesKreinSpace.krein_form (Θ.toLinearMap u) (Θ.toLinearMap v) =
      HestenesKreinSpace.krein_form u v := by
  exact Θ.preserves_krein u v

/-- If a nonzero square-zero element is declared odd, it is nilpotent-odd in the
`TripleAlgebra` sense. -/
theorem triple_nilpotent_is_odd {A : Type*} [Ring A]
    (T : TripleAlgebra A) [SupergradedHopping A]
    (hN : T.N ≠ 0) :
    SupergradedHopping.grade T.N = 1 := by
  exact SupergradedHopping.nilpotent_is_odd T.is_nilpotent

/-- The `TripleAlgebra` pairing-null witness is ready for graded transport maps. -/
theorem triple_pairing_null_sorry {A : Type*} [Ring A]
    (T : TripleAlgebra A) : T.pairing T.L T.L = 0 :=
  T.pairing_null_L

end InfoGeometry.Carrier
