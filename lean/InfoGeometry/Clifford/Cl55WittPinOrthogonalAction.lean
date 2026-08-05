import InfoGeometry.Clifford.Cl55WittPinAction
import InfoGeometry.Clifford.Cl55WittReflectionSubgroup
import InfoGeometry.Clifford.Cl55WittOrthogonalNative

namespace InfoGeometry.Clifford.Clifford55

/-!
# The native Pin action on the Witt quadratic carrier

This file uses Mathlib's ordinary conjugation action on the Clifford vector
range.  It gives a genuine homomorphism from the native `pinGroup` into the
orthogonal group represented by `orthogonalGroup55`.  The twisted action used
for individual reflections is kept separate in `Cl55WittPinAction`.
-/

noncomputable def pinConjAmbientLinear (g : Pin55) : Cl55 →ₗ[ℝ] Cl55 where
  toFun x := (pinToUnits g : Cl55) * x *
    (↑((pinToUnits g)⁻¹) : Cl55)
  map_add' x y := by
    rw [mul_add, add_mul]
  map_smul' r x := by
    simp only [Algebra.smul_def]
    calc
      (pinToUnits g : Cl55) * (algebraMap ℝ Cl55 r * x) *
          (↑((pinToUnits g)⁻¹) : Cl55) =
        algebraMap ℝ Cl55 r *
          ((pinToUnits g : Cl55) * x *
            (↑((pinToUnits g)⁻¹) : Cl55)) := by
          have hcomm :
              (pinToUnits g : Cl55) * algebraMap ℝ Cl55 r =
                algebraMap ℝ Cl55 r * (pinToUnits g : Cl55) :=
            (Algebra.commutes r (pinToUnits g : Cl55)).symm
          rw [← mul_assoc, hcomm]
          noncomm_ring
      _ = r • ((pinToUnits g : Cl55) * x *
          (↑((pinToUnits g)⁻¹) : Cl55)) := by
          rw [Algebra.smul_def]

theorem pinConjAmbientLinear_apply (g : Pin55) (x : Cl55) :
    pinConjAmbientLinear g x =
      (pinToUnits g : Cl55) * x *
        (↑((pinToUnits g)⁻¹) : Cl55) :=
  rfl

noncomputable def pinConjRangeEndomorphism (g : Pin55) :
    LinearMap.range (ι55) →ₗ[ℝ] LinearMap.range (ι55) :=
  LinearMap.codRestrict (LinearMap.range (ι55))
    ((pinConjAmbientLinear g).comp (LinearMap.range (ι55)).subtype)
    (fun z => by
      rcases z.property with ⟨v, hv⟩
      change pinConjAmbientLinear g (z : Cl55) ∈ LinearMap.range (ι55)
      rw [← hv]
      simpa only [pinConjAmbientLinear_apply, ConjAct.units_smul_def,
        ConjAct.ofConjAct_toConjAct] using
        (pinGroup.conjAct_smul_ι_mem_range_ι g.property v))

noncomputable def pinConjAction (g : Pin55) : V55 →ₗ[ℝ] V55 :=
  ι55RangeEquiv.symm.toLinearMap.comp
    ((pinConjRangeEndomorphism g).comp ι55RangeEquiv.toLinearMap)

theorem pinConjAction_apply_ι (g : Pin55) (v : V55) :
    ι55 (pinConjAction g v) =
      (pinToUnits g : Cl55) * ι55 v *
        (↑((pinToUnits g)⁻¹) : Cl55) := by
  have h := congrArg
      (fun z : LinearMap.range (ι55) => (z : Cl55))
      (show ι55RangeEquiv (pinConjAction g v) =
          pinConjRangeEndomorphism g (ι55RangeEquiv v) by
        change ι55RangeEquiv
            (ι55RangeEquiv.symm
              (pinConjRangeEndomorphism g (ι55RangeEquiv v))) = _
        exact ι55RangeEquiv.apply_symm_apply _)
  simpa [pinConjRangeEndomorphism, pinConjAmbientLinear] using h

theorem pinConjAction_mul (g h : Pin55) :
    pinConjAction (g * h) =
      (pinConjAction g).comp (pinConjAction h) := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  change ι55 (pinConjAction (g * h) v) =
    ι55 (pinConjAction g (pinConjAction h v))
  rw [pinConjAction_apply_ι, pinConjAction_apply_ι,
    pinConjAction_apply_ι]
  simp [pinToUnits]
  noncomm_ring

theorem pinConjAction_one :
    pinConjAction (1 : Pin55) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [pinConjAction_apply_ι]
  simp [pinToUnits]

noncomputable def pinConjActionEquiv (g : Pin55) : V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.ofLinear
    (pinConjAction g)
    (pinConjAction g⁻¹)
    (by
      rw [← pinConjAction_mul, mul_inv_cancel, pinConjAction_one])
    (by
      rw [← pinConjAction_mul, inv_mul_cancel, pinConjAction_one])

theorem pinConjAction_preserves_Q55 (g : Pin55) (v : V55) :
    Q55 (pinConjAction g v) = Q55 v := by
  have hι := pinConjAction_apply_ι g v
  have hunit :
      (↑((pinToUnits g)⁻¹) : Cl55) * (pinToUnits g : Cl55) = 1 := by
    exact Units.inv_mul (pinToUnits g)
  have hunitRight :
      (pinToUnits g : Cl55) *
          (↑((pinToUnits g)⁻¹) : Cl55) = 1 := by
    exact Units.mul_inv (pinToUnits g)
  have hsquare :
      ((pinToUnits g : Cl55) * ι55 v *
          (↑((pinToUnits g)⁻¹) : Cl55)) *
        ((pinToUnits g : Cl55) * ι55 v *
          (↑((pinToUnits g)⁻¹) : Cl55)) =
      ι55 v * ι55 v := by
    calc
      _ = (pinToUnits g : Cl55) * ι55 v *
          (((↑((pinToUnits g)⁻¹) : Cl55) *
            (pinToUnits g : Cl55))) * ι55 v *
          (↑((pinToUnits g)⁻¹) : Cl55) := by
            noncomm_ring
      _ = (pinToUnits g : Cl55) * ι55 v * 1 * ι55 v *
          (↑((pinToUnits g)⁻¹) : Cl55) := by rw [hunit]
      _ = (pinToUnits g : Cl55) * (ι55 v * ι55 v) *
          (↑((pinToUnits g)⁻¹) : Cl55) := by
            noncomm_ring
      _ = (pinToUnits g : Cl55) *
          algebraMap ℝ Cl55 (Q55 v) *
          (↑((pinToUnits g)⁻¹) : Cl55) := by
            rw [CliffordAlgebra.ι_sq_scalar]
      _ = algebraMap ℝ Cl55 (Q55 v) *
          ((pinToUnits g : Cl55) *
            (↑((pinToUnits g)⁻¹) : Cl55)) := by
            have hcomm :
                (pinToUnits g : Cl55) * algebraMap ℝ Cl55 (Q55 v) =
                  algebraMap ℝ Cl55 (Q55 v) * (pinToUnits g : Cl55) :=
              (Algebra.commutes (Q55 v) (pinToUnits g : Cl55)).symm
            rw [hcomm, mul_assoc]
      _ = algebraMap ℝ Cl55 (Q55 v) := by
            rw [hunitRight]
            simp
      _ = ι55 v * ι55 v := by
            rw [CliffordAlgebra.ι_sq_scalar]
  have hq :
      ι55 (pinConjAction g v) * ι55 (pinConjAction g v) =
        ι55 v * ι55 v := by
    rw [hι, hsquare]
  rw [CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar] at hq
  exact (algebraMap ℝ Cl55).injective hq

noncomputable def pinOrthogonalAction : Pin55 →* orthogonalGroup55 where
  toFun g :=
    ⟨pinConjActionEquiv g, pinConjAction_preserves_Q55 g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change pinConjActionEquiv (1 : Pin55) v = v
    change pinConjAction (1 : Pin55) v = v
    rw [pinConjAction_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change pinConjActionEquiv (g * h) v =
      (pinConjActionEquiv g * pinConjActionEquiv h) v
    change pinConjAction (g * h) v =
      pinConjAction g (pinConjAction h v)
    rw [pinConjAction_mul]
    rfl

noncomputable def pinNativeOrthogonalAction :
    Pin55 →* Q55.IsometryEquiv Q55 :=
  orthogonalGroup55MulEquiv.toMonoidHom.comp pinOrthogonalAction

@[simp] theorem pinNativeOrthogonalAction_apply (g : Pin55) :
    pinNativeOrthogonalAction g =
      orthogonalGroup55IsometryEquiv (pinOrthogonalAction g) :=
  rfl

end InfoGeometry.Clifford.Clifford55
