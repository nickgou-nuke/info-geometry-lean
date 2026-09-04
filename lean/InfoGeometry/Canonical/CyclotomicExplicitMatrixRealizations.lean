import Mathlib
import InfoGeometry.Canonical.Cyclotomic24OperatorSpine

/-!
# Explicit finite matrix realizations of the cyclotomic stages

This owner supplies concrete integer matrices in standard bases whose powers
realize the algebraic stages used by `Cyclotomic24OperatorSpine`.

The matrices are deliberately representation-neutral.  In particular, the
order-6, order-12, and order-24 matrices below are not asserted to be a Cartan
adjoint action of `G₂`, a split-`G₂` representation, or an automorphism of the
Leech lattice.  They are exact finite matrix witnesses for the corresponding
cyclotomic polynomial equations.

The companion-matrix choice avoids analytic square roots and trigonometric
normalizations.  All identities are finite integer computations.
-/

namespace InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations

open Matrix

abbrev M1Z := Matrix (Fin 1) (Fin 1) ℤ
abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev M3Z := Matrix (Fin 3) (Fin 3) ℤ
abbrev M4Z := Matrix (Fin 4) (Fin 4) ℤ
abbrev M8Z := Matrix (Fin 8) (Fin 8) ℤ

/-- Ground-center witness. -/
def zeroStage : M1Z := 0

@[simp] theorem zeroStage_eq_zero : zeroStage = 0 := rfl

/-- Pure tripotent-spectrum witness with eigenvalues `1,-1,0`. -/
def tripotentStage : M3Z :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, 0]

/-- Exact tripotency. -/
theorem tripotentStage_cube : tripotentStage ^ 3 = tripotentStage := by
  native_decide

/-- Consequently the master 25-potent equation also holds. -/
theorem tripotentStage_master25 : tripotentStage ^ 25 = tripotentStage := by
  native_decide

/-- Standard real complex-structure block together with a one-dimensional
zero/radical sector. -/
def complexStage : M3Z :=
  !![0, -1, 0;
     1,  0, 0;
     0,  0, 0]

/-- The nonzero block squares to `-I`, hence the full block satisfies
`T^3 = -T`. -/
theorem complexStage_cube_neg : complexStage ^ 3 = -complexStage := by
  native_decide

/-- The complex stage is also annihilated by the master 25-potent equation. -/
theorem complexStage_master25 : complexStage ^ 25 = complexStage := by
  native_decide

/-- Companion matrix of `Φ₆(X)=X²-X+1`. -/
def phi6Companion : M2Z :=
  !![0, -1;
     1,  1]

/-- Exact `Φ₆` relation. -/
theorem phi6Companion_polynomial :
    phi6Companion ^ 2 - phi6Companion + 1 = 0 := by
  native_decide

/-- The `Φ₆` companion has order six. -/
theorem phi6Companion_pow_six : phi6Companion ^ 6 = 1 := by
  native_decide

/-- Hence it satisfies the master 25-potent equation. -/
theorem phi6Companion_master25 : phi6Companion ^ 25 = phi6Companion := by
  native_decide

/-- Companion matrix of `Φ₈(X)=X⁴+1`.  Unlike a real complex-structure block,
this is a genuine primitive-8 cyclotomic witness: its fourth power is `-I`. -/
def phi8Companion : M4Z :=
  !![0, 0, 0, -1;
     1, 0, 0,  0;
     0, 1, 0,  0;
     0, 0, 1,  0]

/-- Exact `Φ₈` relation. -/
theorem phi8Companion_polynomial : phi8Companion ^ 4 + 1 = 0 := by
  native_decide

/-- Equivalent fourth-power form. -/
theorem phi8Companion_pow_four : phi8Companion ^ 4 = -1 := by
  native_decide

/-- The companion therefore has order dividing eight. -/
theorem phi8Companion_pow_eight : phi8Companion ^ 8 = 1 := by
  native_decide

/-- It satisfies the master 25-potent equation. -/
theorem phi8Companion_master25 : phi8Companion ^ 25 = phi8Companion := by
  native_decide

/-- Companion matrix of `Φ₁₂(X)=X⁴-X²+1`. -/
def phi12Companion : M4Z :=
  !![0, 0, 0, -1;
     1, 0, 0,  0;
     0, 1, 0,  1;
     0, 0, 1,  0]

/-- Exact `Φ₁₂` relation. -/
theorem phi12Companion_polynomial :
    phi12Companion ^ 4 - phi12Companion ^ 2 + 1 = 0 := by
  native_decide

/-- The `Φ₁₂` companion has order dividing twelve. -/
theorem phi12Companion_pow_twelve : phi12Companion ^ 12 = 1 := by
  native_decide

/-- It satisfies the master 25-potent equation. -/
theorem phi12Companion_master25 : phi12Companion ^ 25 = phi12Companion := by
  native_decide

/-- Companion matrix of `Φ₂₄(X)=X⁸-X⁴+1`. -/
def phi24Companion : M8Z :=
  !![0, 0, 0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0,  0;
     0, 1, 0, 0, 0, 0, 0,  0;
     0, 0, 1, 0, 0, 0, 0,  0;
     0, 0, 0, 1, 0, 0, 0,  1;
     0, 0, 0, 0, 1, 0, 0,  0;
     0, 0, 0, 0, 0, 1, 0,  0;
     0, 0, 0, 0, 0, 0, 1,  0]

/-- Exact primitive-24 cyclotomic relation. -/
theorem phi24Companion_polynomial :
    phi24Companion ^ 8 - phi24Companion ^ 4 + 1 = 0 := by
  native_decide

/-- The primitive-24 companion has order dividing twenty-four. -/
theorem phi24Companion_pow_twenty_four : phi24Companion ^ 24 = 1 := by
  native_decide

/-- It satisfies the common master 25-potent equation. -/
theorem phi24Companion_master25 : phi24Companion ^ 25 = phi24Companion := by
  native_decide

/-- Compact concrete realization packet. -/
theorem explicit_cyclotomic_matrix_packet :
    tripotentStage ^ 3 = tripotentStage ∧
    complexStage ^ 3 = -complexStage ∧
    phi6Companion ^ 6 = 1 ∧
    phi8Companion ^ 4 = -1 ∧
    phi12Companion ^ 12 = 1 ∧
    phi24Companion ^ 24 = 1 := by
  exact ⟨tripotentStage_cube,
    complexStage_cube_neg,
    phi6Companion_pow_six,
    phi8Companion_pow_four,
    phi12Companion_pow_twelve,
    phi24Companion_pow_twenty_four⟩

end InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations
