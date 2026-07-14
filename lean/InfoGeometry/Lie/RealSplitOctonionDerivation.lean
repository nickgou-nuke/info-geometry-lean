import InfoGeometry.Lie.RealSplitOctonionDerivationWitness

/-!
# Typed real split-Cayley derivation surface

This file promotes the existing native `rot01Real` additivity and Leibniz
proofs into a typed additive derivation object.  The owner does not add an
unproved scalar-linearity claim.
-/

namespace InfoGeometry.Lie.RealSplitOctonionDerivation

open InfoGeometry.Lie.RealSplitOctonionDerivationWitness

abbrev SplitCayley := SplitOctReal

/-- The zero readout of the canonical real split-Cayley rotation. -/
theorem rot01Real_zero : rot01Real (0 : SplitCayley) = 0 := by
  change rot01Real ({ a := 0, b := 0, x := 0, y := 0 } : SplitCayley) =
    ({ a := 0, b := 0, x := 0, y := 0 } : SplitCayley)
  ext i
  · simp [rot01Real]
  · simp [rot01Real]
  · fin_cases i <;> simp [rot01Real]
  · fin_cases i <;> simp [rot01Real]

/-- The canonical real split-Cayley rotation as an additive endomorphism. -/
noncomputable def rot01Add : SplitCayley →+ SplitCayley where
  toFun := rot01Real
  map_zero' := rot01Real_zero
  map_add' := rot01Real_add

/-- An additive endomorphism satisfying the ordinary nonassociative Leibniz law. -/
structure SplitCayleyDerivation where
  toAddHom : SplitCayley →+ SplitCayley
  leibniz' : ∀ X Y,
    toAddHom (X * Y) = toAddHom X * Y + X * toAddHom Y

instance : CoeFun (SplitCayleyDerivation) (fun _ => SplitCayley → SplitCayley) :=
  ⟨fun D => D.toAddHom⟩

/-- The existing native `0-1` derivation as a typed derivation object. -/
noncomputable def rot01Derivation : SplitCayleyDerivation where
  toAddHom := rot01Add
  leibniz' := by
    intro X Y
    exact rot01Real_mul X Y

@[simp] theorem rot01Derivation_apply (X : SplitCayley) :
    rot01Derivation X = rot01Real X := rfl

theorem rot01Derivation_nonzero :
    ∃ X : SplitCayley, rot01Derivation X ≠ 0 := by
  exact ⟨up0, rot01Real_nonzero_on_up0⟩

end InfoGeometry.Lie.RealSplitOctonionDerivation
