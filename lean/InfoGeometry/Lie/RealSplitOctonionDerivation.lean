import InfoGeometry.Lie.RealSplitOctonionDerivationWitness
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Typed real split-Cayley derivation surface

This file promotes the existing native `rot01Real` additivity, real-linearity,
and Leibniz proofs into typed derivation objects.
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

private theorem zorn_smul_a (r : ℝ) (X : SplitCayley) : (r • X).a = r * X.a := by
  cases X
  rfl

private theorem zorn_smul_b (r : ℝ) (X : SplitCayley) : (r • X).b = r * X.b := by
  cases X
  rfl

private theorem zorn_smul_x (r : ℝ) (X : SplitCayley) (i : Fin 3) :
    (r • X).x i = r * X.x i := by
  cases X
  rfl

private theorem zorn_smul_y (r : ℝ) (X : SplitCayley) (i : Fin 3) :
    (r • X).y i = r * X.y i := by
  cases X
  rfl

/-- The concrete real split-Cayley `0-1` rotation is real-linear. -/
theorem rot01Real_smul (r : ℝ) (X : SplitCayley) : rot01Real (r • X) = r • rot01Real X := by
  ext
  · simp [rot01Real, zorn_smul_a]
  · simp [rot01Real, zorn_smul_b]
  · rename_i i
    fin_cases i <;> simp [rot01Real, zorn_smul_x]
  · rename_i i
    fin_cases i <;> simp [rot01Real, zorn_smul_y]

/-- The existing split-Cayley coordinate rotation as a real-linear endomorphism. -/
noncomputable def rot01Linear : Module.End ℝ SplitCayley where
  toFun := rot01Real
  map_add' := rot01Real_add
  map_smul' := rot01Real_smul

/-- The real-linear `0-1` rotation satisfies the split-Cayley Leibniz rule. -/
theorem rot01Linear_isLeibniz :
    ∀ X Y : SplitCayley, rot01Linear (X * Y) = rot01Linear X * Y + X * rot01Linear Y := by
  intro X Y
  exact rot01Real_mul X Y

/-- Real-linear endomorphisms satisfying the split-Cayley Leibniz rule. -/
abbrev SplitCayleyLinearDerivation :=
  {D : Module.End ℝ SplitCayley // ∀ X Y : SplitCayley, D (X * Y) = D X * Y + X * D Y}

/-- The canonical real-linear split-Cayley derivation. -/
noncomputable def rot01LinearDerivation : SplitCayleyLinearDerivation :=
  ⟨rot01Linear, rot01Linear_isLeibniz⟩

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
