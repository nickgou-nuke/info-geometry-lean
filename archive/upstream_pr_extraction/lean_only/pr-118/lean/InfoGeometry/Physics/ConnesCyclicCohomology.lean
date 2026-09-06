import InfoGeometry.Physics.CyclicCohomologyChernCharacter

namespace InfoGeometry.Physics

/-!
# Low-degree Hochschild shadow of cyclic cohomology

This owner keeps the scope honest.  It records the basic Hochschild
operators in degrees 0 and 1, proves the low-degree identity
`b₁ ∘ b₀ = 0`, and packages the trace-as-0-cocycle statement under an
explicit cyclicity property.

It does not claim a full cyclic complex, periodicity operator, or a global
cyclic-cohomology theorem.
-/

set_option autoImplicit false

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- 0-cochains as linear functionals. -/
abbrev Cochain0 (A : Type*) [Ring A] [Algebra ℝ A] := A →ₗ[ℝ] ℝ

/-- 1-cochains. -/
abbrev Cochain1 (A : Type*) [Ring A] [Algebra ℝ A] := A → A → ℝ

/-- 2-cochains. -/
abbrev Cochain2 (A : Type*) [Ring A] [Algebra ℝ A] := A → A → A → ℝ

/-- Hochschild `b` on 0-cochains. -/
def hochschild_b0 (phi : Cochain0 A) : Cochain1 A :=
  fun a0 a1 => phi (a0 * a1) - phi (a1 * a0)

/-- Hochschild `b` on 1-cochains. -/
def hochschild_b1 (psi : Cochain1 A) : Cochain2 A :=
  fun a0 a1 a2 => psi (a0 * a1) a2 - psi a0 (a1 * a2) + psi (a2 * a0) a1

/-- The low-degree Hochschild identity `b₁ ∘ b₀ = 0`. -/
theorem hochschild_b1_comp_b0_zero (phi : Cochain0 A) (a0 a1 a2 : A) :
    hochschild_b1 (hochschild_b0 phi) a0 a1 a2 = 0 := by
  dsimp [hochschild_b1, hochschild_b0]
  simp [mul_assoc]

/-- A trace that is cyclic on binary products. -/
abbrev CyclicTraceData (A : Type*) [Ring A] [Algebra ℝ A] :=
  {Tr : A →ₗ[ℝ] ℝ // ∀ X Y, Tr (X * Y) = Tr (Y * X)}

namespace CyclicTraceData

variable {A : Type*} [Ring A] [Algebra ℝ A]

abbrev Tr (data : CyclicTraceData A) : A →ₗ[ℝ] ℝ := data.1
abbrev Tr_comm (data : CyclicTraceData A) :
    ∀ X Y, data.Tr (X * Y) = data.Tr (Y * X) := data.2

/-- The trace is a Hochschild 0-cocycle under cyclicity. -/
theorem trace_is_hochschild_cocycle (data : CyclicTraceData A) (a0 a1 : A) :
    hochschild_b0 data.Tr a0 a1 = 0 := by
  dsimp [hochschild_b0]
  rw [data.Tr_comm a0 a1]
  exact sub_self _

end CyclicTraceData

/-- The second Chern-character shadow as a 2-cochain. -/
def chernCharacterCochain2
    (Tr : A →ₗ[ℝ] ℝ) (Gamma D : A) : Cochain2 A :=
  fun a0 a1 a2 => superTrace Tr Gamma (a0 * diracCommutator D a1 * diracCommutator D a2)

theorem chernCharacterCochain2_eval
    (Tr : A →ₗ[ℝ] ℝ) (Gamma D : A) (a0 a1 a2 : A) :
    chernCharacterCochain2 (A := A) Tr Gamma D a0 a1 a2 =
      superTrace Tr Gamma (a0 * diracCommutator D a1 * diracCommutator D a2) :=
  rfl

theorem connes_cyclic_cohomology_synthesis
    (phi : Cochain0 A) (data : CyclicTraceData A) (a0 a1 a2 : A) :
    (hochschild_b1 (hochschild_b0 phi) a0 a1 a2 = 0) ∧
    (hochschild_b0 data.Tr a0 a1 = 0) :=
  ⟨hochschild_b1_comp_b0_zero (A := A) phi a0 a1 a2,
   CyclicTraceData.trace_is_hochschild_cocycle data a0 a1⟩

end InfoGeometry.Physics
