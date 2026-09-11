import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.QuadraticJordanH3Zorn

/-!
# H₃ Zorn coordinate probes for the split-Albert route

This file contains only concrete carrier-level probes.  It does not claim that
these probes form a basis of the F₄ derivation algebra; that requires a proved
derivation theory and is not installed here.
-/

namespace InfoGeometry.Algebra.H3Zorn

variable {R : Type*} [CommRing R]

/-- The ordinary diagonal trace of a matrix in the H₃ Zorn carrier. -/
def trace (X : H3Zorn R) : R := X.α₁ + X.α₂ + X.α₃

/-- Trace is additive on the H₃ Zorn carrier. -/
@[simp] theorem trace_add (X Y : H3Zorn R) :
    trace (X + Y) = trace X + trace Y := by
  change (X.α₁ + Y.α₁) + (X.α₂ + Y.α₂) + (X.α₃ + Y.α₃) =
    (X.α₁ + X.α₂ + X.α₃) + (Y.α₁ + Y.α₂ + Y.α₃)
  ring

/-- Trace is homogeneous on the H₃ Zorn carrier. -/
theorem trace_smul (r : R) (X : H3Zorn R) :
    trace (r • X) = r * trace X := by
  change r * X.α₁ + r * X.α₂ + r * X.α₃ =
    r * (X.α₁ + X.α₂ + X.α₃)
  ring

/-- The zero H₃ Zorn matrix has zero trace. -/
@[simp] theorem trace_zero :
    trace (0 : H3Zorn R) = 0 := by
  change (0 : R) + 0 + 0 = 0
  simp

/-- The submodule of trace-zero elements in the additive H₃ Zorn carrier. -/
def traceZero : Submodule R (H3Zorn R) where
  carrier := { X | trace X = 0 }
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq, trace] at hX hY ⊢
    change (X.α₁ + Y.α₁) + (X.α₂ + Y.α₂) + (X.α₃ + Y.α₃) = 0
    calc
      (X.α₁ + Y.α₁) + (X.α₂ + Y.α₂) + (X.α₃ + Y.α₃)
          = (X.α₁ + X.α₂ + X.α₃) + (Y.α₁ + Y.α₂ + Y.α₃) := by ring
      _ = 0 := by rw [hX, hY]; simp
  zero_mem' := by
    simp only [Set.mem_setOf_eq, trace]
    change (0 : R) + 0 + 0 = 0
    simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq, trace] at hX ⊢
    change c * X.α₁ + c * X.α₂ + c * X.α₃ = 0
    calc
      c * X.α₁ + c * X.α₂ + c * X.α₃ = c * (X.α₁ + X.α₂ + X.α₃) := by ring
      _ = 0 := by rw [hX]; simp

/-- Standard coordinate probes for `ZornVectorMatrix ℝ`. -/
noncomputable def zornBasis (i : Fin 8) : ZornVectorMatrix ℝ :=
  match i with
  | 0 => ZornVectorMatrix.E11
  | 1 => ZornVectorMatrix.E22
  | 2 => ZornVectorMatrix.U 0
  | 3 => ZornVectorMatrix.U 1
  | 4 => ZornVectorMatrix.U 2
  | 5 => ZornVectorMatrix.V 0
  | 6 => ZornVectorMatrix.V 1
  | 7 => ZornVectorMatrix.V 2

/-- Off-diagonal coordinate probes in the first Zorn block. -/
noncomputable def X1 (i : Fin 8) : H3Zorn ℝ :=
  ⟨0, 0, 0, zornBasis i, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

/-- Off-diagonal coordinate probes in the second Zorn block. -/
noncomputable def X2 (i : Fin 8) : H3Zorn ℝ :=
  ⟨0, 0, 0, ZornVectorMatrix.zero, zornBasis i, ZornVectorMatrix.zero⟩

/-- Off-diagonal coordinate probes in the third Zorn block. -/
noncomputable def X3 (i : Fin 8) : H3Zorn ℝ :=
  ⟨0, 0, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, zornBasis i⟩

/-- First diagonal coordinate probe. -/
noncomputable def E1 : H3Zorn ℝ :=
  ⟨1, 0, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

/-- Second diagonal coordinate probe. -/
noncomputable def E2 : H3Zorn ℝ :=
  ⟨0, 1, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

/-- Third diagonal coordinate probe. -/
noncomputable def E3 : H3Zorn ℝ :=
  ⟨0, 0, 1, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

@[simp] theorem trace_X1 (i : Fin 8) : trace (X1 i) = 0 := by
  simp [trace, X1]

@[simp] theorem trace_X2 (i : Fin 8) : trace (X2 i) = 0 := by
  simp [trace, X2]

@[simp] theorem trace_X3 (i : Fin 8) : trace (X3 i) = 0 := by
  simp [trace, X3]

@[simp] theorem trace_E1 : trace E1 = 1 := by
  simp [trace, E1]

@[simp] theorem trace_E2 : trace E2 = 1 := by
  simp [trace, E2]

@[simp] theorem trace_E3 : trace E3 = 1 := by
  simp [trace, E3]

end InfoGeometry.Algebra.H3Zorn
