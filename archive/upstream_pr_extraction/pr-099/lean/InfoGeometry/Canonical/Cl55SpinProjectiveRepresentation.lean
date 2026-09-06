import InfoGeometry.Canonical.ProjectiveFoundation
import InfoGeometry.Clifford.Cl55ProjectiveOperatorAction

/-!
# A genuine projective representation of the noncommutative `Cl(5,5)` carrier

The Spin action is first lifted to a real `LinearEquiv` on the doubled
noncommutative carrier `Fin 2 → Cl55`.  It is then packaged through the
generic projective-representation owner.  No coordinate matrix model or
scalar diagonal surrogate is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55SpinProjectiveRepresentation

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.Canonical.ProjectiveFoundation

abbrev Carrier := Fin 2 → Cl55

noncomputable def spinCarrierLinearEquiv (g : Spin55) : Carrier ≃ₗ[ℝ] Carrier where
  toFun := spinTransportCarrier55 g
  invFun := spinTransportCarrier55 g⁻¹
  left_inv := by
    intro v
    funext i
    change spinCliffordRingEquiv g⁻¹ (spinCliffordRingEquiv g (v i)) = v i
    rw [← spinCliffordRingEquiv_mul]
    simp [spinCARAutomorphism]
  right_inv := by
    intro v
    funext i
    change spinCliffordRingEquiv g (spinCliffordRingEquiv g⁻¹ (v i)) = v i
    rw [← spinCliffordRingEquiv_mul]
    simp [spinCARAutomorphism]
  map_add' := by
    intro v w
    funext i
    change spinCARAutomorphism g (v i + w i) =
      spinCARAutomorphism g (v i) + spinCARAutomorphism g (w i)
    exact (spinCARAutomorphism g).map_add _ _
  map_smul' := by
    intro r v
    funext i
    change unitConjugation (spinGroup.toUnits g) (r • v i) =
      r • unitConjugation (spinGroup.toUnits g) (v i)
    exact unitConjugation_smul (spinGroup.toUnits g) r (v i)

noncomputable def spinCarrierLinearAction :
    Spin55 →* (Carrier ≃ₗ[ℝ] Carrier) where
  toFun := spinCarrierLinearEquiv
  map_one' := by
    ext v i
    change spinCARAutomorphism 1 (v i) = v i
    simp [spinCARAutomorphism]
  map_mul' := by
    intro g h
    ext v i
    change spinCARAutomorphism (g * h) (v i) =
      spinCARAutomorphism g (spinCARAutomorphism h (v i))
    exact spinCliffordRingEquiv_mul g h (v i)

noncomputable def spinCarrierProjectiveRepresentation :
    ProjectiveRepresentation ℝ Spin55 Carrier where
  toLinearEquiv := spinCarrierLinearEquiv
  multiplier := fun _ _ => 1
  map_one := by
    ext v i
    change spinCARAutomorphism 1 (v i) = v i
    simp [spinCARAutomorphism]
  map_mul := by
    intro g h v
    funext i
    simpa [spinCarrierLinearEquiv] using
      spinCliffordRingEquiv_mul g h (v i)
  cocycle := by
    intro g h l
    simp
  one_left := by
    intro g
    simp
  one_right := by
    intro g
    simp

theorem spinCarrierProjectiveRepresentation_multiplier_eq_one
    (g h : Spin55) :
    spinCarrierProjectiveRepresentation.multiplier g h = 1 :=
  rfl

theorem spinCarrierProjectiveRepresentation_map_mul
    (g h : Spin55) (v : Carrier) :
    spinCarrierProjectiveRepresentation (g * h) v =
    spinCarrierProjectiveRepresentation g
        (spinCarrierProjectiveRepresentation h v) := by
  have hmul := congrArg (fun e : Carrier ≃ₗ[ℝ] Carrier => e v)
    (spinCarrierLinearAction.map_mul g h)
  simpa [spinCarrierProjectiveRepresentation, spinCarrierLinearAction] using hmul

end InfoGeometry.Canonical.Cl55SpinProjectiveRepresentation
