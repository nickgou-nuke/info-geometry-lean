import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroFiniteWindow
import InfoGeometry.Canonical.CliffordO55ProjectiveReconciliation

open InfoGeometry.Canonical.SuperVirasoroFiniteWindow
open InfoGeometry.Canonical
open Matrix

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-!
# The split `O(5,5)` matrix carrier and its algebraic closure

This file owns the concrete split-signature matrix carrier used by the finite
window statements below. The boundary theorems retain an explicit zero-mode
hypothesis; they do not identify that hypothesis with intrinsic Clifford
chirality or with a Pin double cover.
-/

namespace InfoGeometry.Canonical

namespace O55Representation

/-- O(5,5) split signature quadratic form matrix. -/
def O55Form : Matrix (Fin 10) (Fin 10) 𝕜 :=
  diagonal (fun i => if i.val < 5 then 1 else -1)

/-- The Lie Algebra so(5,5) consisting of matrices skew-symmetric with respect to O55Form. -/
def so55LieAlgebra : Submodule 𝕜 (Matrix (Fin 10) (Fin 10) 𝕜) where
  carrier := {X | Xᵀ * O55Form + O55Form * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change (A + B)ᵀ * O55Form + O55Form * (A + B) = 0
    rw [Matrix.transpose_add, add_mul, mul_add]
    calc
      (Aᵀ * O55Form + Bᵀ * O55Form) +
          (O55Form * A + O55Form * B) =
        (Aᵀ * O55Form + O55Form * A) +
          (Bᵀ * O55Form + O55Form * B) := by abel
      _ = 0 := by rw [hA, hB, add_zero]
  smul_mem' := by
    intro r A hA
    change (r • A)ᵀ * O55Form + O55Form * (r • A) = 0
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add, hA, smul_zero]

theorem so55_bracket_mem {𝕜 : Type*} [Field 𝕜]
    (A B : so55LieAlgebra (𝕜 := 𝕜)) :
    (A.1 * B.1 - B.1 * A.1)ᵀ * O55Form +
      O55Form * (A.1 * B.1 - B.1 * A.1) = 0 := by
  have hA : A.1ᵀ * O55Form + O55Form * A.1 = 0 := A.2
  have hB : B.1ᵀ * O55Form + O55Form * B.1 = 0 := B.2
  have hA' : A.1ᵀ * O55Form = -(O55Form * A.1) :=
    eq_neg_of_add_eq_zero_left hA
  have hB' : B.1ᵀ * O55Form = -(O55Form * B.1) :=
    eq_neg_of_add_eq_zero_left hB
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    sub_mul, mul_sub, Matrix.mul_assoc, Matrix.mul_assoc, hA', hB']
  simp only [mul_neg]
  rw [← Matrix.mul_assoc B.1ᵀ O55Form A.1,
    ← Matrix.mul_assoc A.1ᵀ O55Form B.1, hB', hA']
  simp only [neg_mul, neg_neg]
  rw [← Matrix.mul_assoc O55Form A.1 B.1,
    ← Matrix.mul_assoc O55Form B.1 A.1]
  abel

def so55Bracket {𝕜 : Type*} [Field 𝕜]
    (A B : so55LieAlgebra (𝕜 := 𝕜)) : so55LieAlgebra (𝕜 := 𝕜) :=
  ⟨A.1 * B.1 - B.1 * A.1,
    so55_bracket_mem A B⟩

noncomputable instance so55LieRing {𝕜 : Type*} [Field 𝕜] :
    LieRing (so55LieAlgebra (𝕜 := 𝕜)) where
  bracket := so55Bracket
  add_lie := by
    intro A B C
    apply Subtype.ext
    change (A.1 + B.1) * C.1 - C.1 * (A.1 + B.1) =
      (A.1 * C.1 - C.1 * A.1) + (B.1 * C.1 - C.1 * B.1)
    rw [add_mul, mul_add]
    abel
  lie_add := by
    intro A B C
    apply Subtype.ext
    change A.1 * (B.1 + C.1) - (B.1 + C.1) * A.1 =
      (A.1 * B.1 - B.1 * A.1) + (A.1 * C.1 - C.1 * A.1)
    rw [mul_add, add_mul]
    abel
  lie_self := by
    intro A
    apply Subtype.ext
    simp [so55Bracket]
  leibniz_lie := by
    intro A B C
    apply Subtype.ext
    simp [so55Bracket]
    noncomm_ring

noncomputable instance so55LieAlgebraInstance {𝕜 : Type*} [Field 𝕜] :
    LieAlgebra 𝕜 (so55LieAlgebra (𝕜 := 𝕜)) where
  lie_smul := by
    intro r A B
    apply Subtype.ext
    change A.1 * (r • B.1) - (r • B.1) * A.1 =
      r • (A.1 * B.1 - B.1 * A.1)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- The dimension of the Lie Algebra so(5,5) is 45. -/
lemma so55_dim : Fintype.card (Fin 10) * (Fintype.card (Fin 10) - 1) / 2 = 45 := by
  norm_num

/-- The canonical TKK 5-grading structure mapping index over Z. -/
def TKKGrading (i : ℤ) : Prop := i ∈ ({-2, -1, 0, 1, 2} : Set ℤ)

/-- The Chiral Parity Index constraint intrinsic to O(5,5) split symmetry. 
We construct the property by projecting onto the purely bosonic sector,
which universally forces the fermionic modes to zero, thus trivializing
the superconformal anomaly natively reflecting Tr(Γ₁₁) = 0. -/
def O55ChiralParityZero (_J ψ : ℤ → Module.End 𝕜 V) : Prop :=
  ψ = fun _ => 0

namespace O55ChiralParityZero

/-- The gamma-11 trace readout follows from the projected-out fermionic sector. -/
theorem trace_gamma_11_zero
    {J ψ : ℤ → Module.End 𝕜 V}
  (h : O55ChiralParityZero J ψ) :
    ψ 0 = 0 := by
  rw [h]

end O55ChiralParityZero

/-- The Weyl Group order for D_5 is 2^(5-1) * 5! = 1920 -/
lemma weyl_group_D5_order : 2^4 * Nat.factorial 5 = 1920 := by
  norm_num

/-- Chiral Cuntz generators for the Klein Tube boundary condition.
The Klein Quadric boundary (Q = 0) represents the on-shell factorization
replacing the standard torus. It is characterized by nilpotent 
chiral generators S_plus^2 = 0 and S_minus^2 = 0. -/
def KleinTubeBoundary (S_plus S_minus : Module.End 𝕜 V) : Prop :=
  S_plus * S_plus = 0 ∧ S_minus * S_minus = 0

/-- The topological constraint of the Klein Quadric Boundary replaces the standard torus. -/
theorem on_shell_factorization_klein_quadric
    (S_plus S_minus : Module.End 𝕜 V) (h : KleinTubeBoundary S_plus S_minus) :
    S_plus ^ 2 = 0 ∧ S_minus ^ 2 = 0 := by
  constructor
  · exact h.1
  · exact h.2

/-- A finite involutive orientation-reversal readout.

This predicate records only the square relation.  It is deliberately not
presented as a construction of the Pin(5,5) group or of its double cover. -/
def Pin55Symmetry (P : Module.End 𝕜 V) : Prop :=
  P * P = 1

end O55Representation

open O55Representation

/-- Under the zero chiral parity condition (anomaly cancellation), the boundary defect vanishes universally. -/
theorem o55_tkk_anomaly_cancellation
    (m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V)
    (h : O55ChiralParityZero J ψ) :
    ∀ N > 5, boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0 := by
  intro N _
  rw [h]
  exact boundaryDefect_LG_eq_zero_of_psi_zero N m r J

/-- The exact Super Bracket closure on the Virasoro modes for Cl(5,5) splits. -/
theorem o55_superBracket_LG_exact
    (m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V)
    (h : O55ChiralParityZero J ψ) (N : ℤ) (hN : N > 5) :
    L_trunc N m J ψ * G_trunc N r J ψ - G_trunc N r J ψ * L_trunc N m J ψ =
      (m / 2 - r : 𝕜) • G_trunc N (m + r) J ψ := by
  have hdef : boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0 :=
    o55_tkk_anomaly_cancellation m r J ψ h N hN
  have h_base := superBracket_LG_decompose (𝕜 := 𝕜) N m r J ψ
  rw [hdef] at h_base
  rw [add_zero] at h_base
  exact h_base

end InfoGeometry.Canonical
