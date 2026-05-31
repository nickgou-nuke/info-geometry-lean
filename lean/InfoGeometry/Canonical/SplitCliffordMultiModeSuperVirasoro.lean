import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroFiniteWindow

/-!
# InfoGeometry.Canonical.SplitCliffordMultiModeSuperVirasoro

Concrete multi-mode finite truncation readouts for the mixed Super-Virasoro
bracket at shifted modes.

This file specializes the finite-window owner surface to the explicit shifted
configuration `(m,r) = (1,0)` and keeps the boundary defect as an explicit
operator remainder.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordMultiModeSuperVirasoro

open InfoGeometry.Canonical.SuperVirasoroFiniteWindow

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

local notation "EndV" => Module.End 𝕜 V

/-- Explicit mixed-mode boundary remainder at `(m,r)=(1,0)`. -/
def boundaryDefect_m1_r0
    (N : ℤ) (J ψ : ℤ → EndV) : EndV :=
  boundaryDefect_LG N 1 0 J ψ

/--
Finite-window mixed bracket at shifted modes:
`[L₁^N, G₀^N] = (1/2) • G₁^N + boundary defect`.
-/
theorem mixedBracket_m1_r0_decompose
    (N : ℤ) (J ψ : ℤ → EndV) :
    (L_trunc N 1 J ψ) * (G_trunc N 0 J ψ)
      - (G_trunc N 0 J ψ) * (L_trunc N 1 J ψ)
    = ((1 : 𝕜) / 2) • (G_trunc N 1 J ψ)
      + boundaryDefect_m1_r0 (𝕜 := 𝕜) N J ψ := by
  simpa [boundaryDefect_m1_r0, LG_coeff] using
    (superBracket_LG_decompose N 1 0 J ψ)

/--
If the shifted-mode boundary defect vanishes, the shifted finite mixed bracket
closes exactly with coefficient `1/2`.
-/
theorem mixedBracket_m1_r0_of_boundary_zero
    (N : ℤ) (J ψ : ℤ → EndV)
    (hdef : boundaryDefect_m1_r0 N J ψ = 0) :
    (L_trunc N 1 J ψ) * (G_trunc N 0 J ψ)
      - (G_trunc N 0 J ψ) * (L_trunc N 1 J ψ)
    = ((1 : 𝕜) / 2) • (G_trunc N 1 J ψ) := by
  simpa [boundaryDefect_m1_r0, LG_coeff] using
    (superBracket_LG_of_boundaryDefect_zero N 1 0 J ψ hdef)

/-- Witness current family concentrated at mode `0`. -/
def J_sorry (A : EndV) : ℤ → EndV :=
  fun n => if n = 0 then A else 0

/-- Witness fermion family concentrated at mode `1`. -/
def psi_sorry (B : EndV) : ℤ → EndV :=
  fun n => if n = 1 then B else 0

/--
Concrete witness evaluation of the shifted boundary defect.

For the witness families `J_sorry A` (mode `0`) and `psi_sorry B` (mode `1`),
the shifted defect is exactly `- (1/2) • (A * B)`.
-/
theorem boundaryDefect_m1_r0_witness_eq
    (N : ℤ) (A B : EndV) (hN : 0 ≤ N) :
    boundaryDefect_m1_r0 N (J_sorry A) (psi_sorry B)
    = -((1 : 𝕜) / 2) • (A * B) := by
  unfold boundaryDefect_m1_r0 boundaryDefect_LG
  have hG0 : G_trunc N 0 (J_sorry A) (psi_sorry B) = 0 := by
    simpa [J_sorry, psi_sorry, J_mode0, psi_mode1] using
      (G_trunc_r0_mode01_eq_zero (𝕜 := 𝕜) N A B)
  have hG1 : G_trunc N 1 (J_sorry A) (psi_sorry B) = A * B := by
    simpa [J_sorry, psi_sorry, J_mode0, psi_mode1] using
      (G_trunc_r1_mode01_eq (𝕜 := 𝕜) N A B hN)
  simp [hG0, hG1, LG_coeff]

/--
Under the explicit witness lane and algebraic side condition `A * B = 0`,
the shifted boundary defect vanishes.
-/
theorem boundaryDefect_m1_r0_witness_eq_zero_of_mul_zero
    (N : ℤ) (A B : EndV) (hN : 0 ≤ N) (hAB : A * B = 0) :
    boundaryDefect_m1_r0 N (J_sorry A) (psi_sorry B) = 0 := by
  rw [boundaryDefect_m1_r0_witness_eq N A B hN, hAB]
  simp

/--
Concrete shifted-mode exact closure in the witness lane under `A * B = 0`.
-/
theorem mixedBracket_m1_r0_witness_of_mul_zero
    (N : ℤ) (A B : EndV) (hN : 0 ≤ N) (hAB : A * B = 0) :
    (L_trunc N 1 (J_sorry A) (psi_sorry B))
        * (G_trunc N 0 (J_sorry A) (psi_sorry B))
      - (G_trunc N 0 (J_sorry A) (psi_sorry B))
        * (L_trunc N 1 (J_sorry A) (psi_sorry B))
    = ((1 : 𝕜) / 2) •
        (G_trunc N 1 (J_sorry A) (psi_sorry B)) := by
  exact mixedBracket_m1_r0_of_boundary_zero N
    (J_sorry A) (psi_sorry B)
    (boundaryDefect_m1_r0_witness_eq_zero_of_mul_zero N A B hN hAB)

end InfoGeometry.Canonical.SplitCliffordMultiModeSuperVirasoro

