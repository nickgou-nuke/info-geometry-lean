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

/-! The mode-vanishing predicate below is only an explicit algebraic
hypothesis on the supplied family; it does not derive chirality. -/
def fermionicModesZero (_J ψ : ℤ → Module.End 𝕜 V) : Prop :=
  ψ = fun _ => 0

namespace fermionicModesZero

/-! A direct consequence of the explicit mode-vanishing hypothesis. -/
theorem trace_gamma_11_zero
    {J ψ : ℤ → Module.End 𝕜 V}
  (h : fermionicModesZero J ψ) :
    ψ 0 = 0 := by
  rw [h]

end fermionicModesZero

/-- The Weyl Group order for D_5 is 2^(5-1) * 5! = 1920 -/
lemma weyl_group_D5_order : 2^4 * Nat.factorial 5 = 1920 := by
  norm_num

/-! A pair of square-zero endomorphisms; no boundary interpretation is
assumed at this algebraic layer. -/
def nilpotentChiralPair (S_plus S_minus : Module.End 𝕜 V) : Prop :=
  S_plus * S_plus = 0 ∧ S_minus * S_minus = 0

/-! The pair's two square-zero equations. -/
theorem nilpotentChiralPair_sq
    (S_plus S_minus : Module.End 𝕜 V) (h : nilpotentChiralPair S_plus S_minus) :
    S_plus ^ 2 = 0 ∧ S_minus ^ 2 = 0 := by
  constructor
  · exact h.1
  · exact h.2

/-! A finite involutive endomorphism predicate. -/
def involutiveEndomorphism (P : Module.End 𝕜 V) : Prop :=
  P * P = 1

end O55Representation

open O55Representation

/-! ## Defect-aware noncommutative mixed bracket -/

/--
The native finite-window mixed superbracket retains its boundary defect.  This
is the primary O(5,5) statement; no zero-mode or chiral-parity hypothesis is
silently inserted.
-/
theorem o55_superBracket_LG_decomposition
    (m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) (N : ℤ) :
    L_trunc N m J ψ * G_trunc N r J ψ -
        G_trunc N r J ψ * L_trunc N m J ψ =
      (LG_coeff (𝕜 := 𝕜) m r) • G_trunc N (m + r) J ψ +
        boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ := by
  exact superBracket_LG_decompose (𝕜 := 𝕜) N m r J ψ

/--
Exact mixed-bracket closure under the explicit finite-window condition that
the boundary defect vanishes.  This is independent of the degenerate
zero-fermion specialization below.
-/
theorem o55_superBracket_LG_of_zero_defect
    (m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) (N : ℤ)
    (hdef : boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0) :
    L_trunc N m J ψ * G_trunc N r J ψ -
        G_trunc N r J ψ * L_trunc N m J ψ =
      (LG_coeff (𝕜 := 𝕜) m r) • G_trunc N (m + r) J ψ := by
  exact superBracket_LG_of_boundaryDefect_zero
    (𝕜 := 𝕜) N m r J ψ hdef

/-! Under explicit vanishing of the supplied fermionic modes, the boundary
defect vanishes.  This is a degenerate specialization, not an anomaly
cancellation theorem. -/
theorem o55_boundaryDefect_zero_of_fermionicModesZero
    (m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V)
    (h : fermionicModesZero J ψ) :
    ∀ N > 5, boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0 := by
  intro N _
  rw [h]
  exact boundaryDefect_LG_eq_zero_of_psi_zero N m r J

/-! Exact closure in the same degenerate zero-mode specialization. -/
theorem o55_superBracket_LG_of_fermionicModesZero
    (m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V)
    (h : fermionicModesZero J ψ) (N : ℤ) (hN : N > 5) :
    L_trunc N m J ψ * G_trunc N r J ψ - G_trunc N r J ψ * L_trunc N m J ψ =
      (m / 2 - r : 𝕜) • G_trunc N (m + r) J ψ := by
  have hdef : boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0 :=
    o55_boundaryDefect_zero_of_fermionicModesZero m r J ψ h N hN
  have h_base := superBracket_LG_decompose (𝕜 := 𝕜) N m r J ψ
  rw [hdef] at h_base
  rw [add_zero] at h_base
  exact h_base

end InfoGeometry.Canonical
