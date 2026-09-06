import InfoGeometry.Exceptional.FreudenthalHeisenbergZeroGradeAction

/-!
# The zero-grade Heisenberg representation

The existing symplectic zero-grade action is now packaged as a genuine Lie
homomorphism into endomorphisms of the Heisenberg carrier.  This is the
concrete representation-theoretic part of the five-grade boundary that is
available without claiming an identification of the zero-grade algebra with
`𝔢₇`.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

noncomputable def zeroGradeHeisenbergActionLinear :
    symplecticOperatorLieSubalgebra D →ₗ[ℝ]
      Module.End ℝ (HeisenbergElement J) where
  toFun T :=
    { toFun := zeroGradeHeisenbergAction (T : Module.End ℝ (FreudenthalCharge J))
      map_add' := by
        intro X Y
        exact zeroGradeHeisenbergAction_add
          (T : Module.End ℝ (FreudenthalCharge J)) X Y
      map_smul' := by
        intro r X
        exact zeroGradeHeisenbergAction_smul
          (T : Module.End ℝ (FreudenthalCharge J)) r X }
  map_add' := by
    intro T U
    apply LinearMap.ext
    intro X
    apply HeisenbergElement.ext
    · apply FreudenthalCharge.ext <;> rfl
    · change (0 : ℝ) = 0 + 0
      ring
  map_smul' := by
    intro r T
    apply LinearMap.ext
    intro X
    apply HeisenbergElement.ext
    · apply FreudenthalCharge.ext <;> rfl
    · change (0 : ℝ) = r • 0
      simp

@[simp] theorem zeroGradeHeisenbergActionLinear_apply
    (T : symplecticOperatorLieSubalgebra D) (X : HeisenbergElement J) :
    zeroGradeHeisenbergActionLinear D T X =
      zeroGradeHeisenbergAction
        (T : Module.End ℝ (FreudenthalCharge J)) X := rfl

noncomputable def zeroGradeHeisenbergLieHom :
    symplecticOperatorLieSubalgebra D →ₗ⁅ℝ⁆
      Module.End ℝ (HeisenbergElement J) where
  __ := zeroGradeHeisenbergActionLinear D
  map_lie' := by
    intro T U
    apply LinearMap.ext
    intro X
    change zeroGradeHeisenbergAction
        ((⁅T, U⁆ : Module.End ℝ (FreudenthalCharge J))) X = _
    simpa [zeroGradeHeisenbergActionLinear, Ring.lie_def,
      Module.End.mul_apply] using
      (zeroGradeHeisenbergAction_commutator
        (T : Module.End ℝ (FreudenthalCharge J))
        (U : Module.End ℝ (FreudenthalCharge J)) X)

theorem zeroGradeHeisenbergLieHom_apply
    (T : symplecticOperatorLieSubalgebra D) :
    zeroGradeHeisenbergLieHom D T =
      zeroGradeHeisenbergActionLinear D T := rfl

theorem zeroGradeHeisenbergLieHom_injective :
    Function.Injective (zeroGradeHeisenbergLieHom D) := by
  intro T U h
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have hX := congrArg
    (fun F : Module.End ℝ (HeisenbergElement J) =>
      (F ⟨X, 0⟩).charge) h
  exact hX

end InfoGeometry.Exceptional.Freudenthal
