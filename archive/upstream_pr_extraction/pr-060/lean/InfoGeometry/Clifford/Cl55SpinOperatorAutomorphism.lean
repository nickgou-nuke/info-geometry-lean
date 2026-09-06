import InfoGeometry.Clifford.Cl55WittPinAction
import InfoGeometry.Clifford.ChiralLorentzCARLift

/-!
# The noncommutative `Spin(5,5)` operator automorphism

The native `Spin(5,5)` owner already proves the action on the Witt vector
carrier.  This file packages the same action as conjugation by the
corresponding Clifford unit on the whole Clifford algebra.  Thus the vector
action is a restriction of a genuine algebra automorphism, rather than a
separate matrix or scalar construction.
-/

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.ChiralLorentzCARLift

noncomputable def spinCliffordRingEquiv (g : Spin55) : Cl55 ≃+* Cl55 :=
  unitConjugationRingEquiv (spinGroup.toUnits g)

@[simp] theorem spinCliffordRingEquiv_apply (g : Spin55) (x : Cl55) :
    spinCliffordRingEquiv g x =
      (spinGroup.toUnits g : Cl55) * x *
        (↑((spinGroup.toUnits g)⁻¹) : Cl55) :=
  rfl

theorem spinCliffordRingEquiv_mul (g h : Spin55) (x : Cl55) :
    spinCliffordRingEquiv (g * h) x =
      spinCliffordRingEquiv g (spinCliffordRingEquiv h x) := by
  simp [spinCliffordRingEquiv, unitConjugation, mul_assoc]

theorem spinCliffordRingEquiv_vector_readback (g : Spin55) (v : V55) :
    spinCliffordRingEquiv g (ι55 v) = ι55 (spinAction g v) := by
  symm
  simpa only [spinCliffordRingEquiv, unitConjugation] using
    (show ι55 (spinAction g v) =
        (spinGroup.toUnits g : Cl55) * ι55 v *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55) by
      exact by
        have hι := pinTwistedAction_apply_ι (spinToPin g) v
        have hu : pinToUnits (spinToPin g) = spinGroup.toUnits g := by
          apply Units.ext
          rfl
        have hinv :
            CliffordAlgebra.involute (spinGroup.toUnits g : Cl55) =
              (spinGroup.toUnits g : Cl55) := by
          simpa using (spinGroup.involute_eq g.property)
        simpa only [pinTwistedAdj, hu, hinv] using hι)

theorem spinCliffordRingEquiv_preserves_vector_range (g : Spin55) (v : V55) :
    spinCliffordRingEquiv g (ι55 v) ∈ LinearMap.range ι55 := by
  rw [spinCliffordRingEquiv_vector_readback]
  exact LinearMap.mem_range_self ι55 (spinAction g v)

end InfoGeometry.Clifford.Clifford55
