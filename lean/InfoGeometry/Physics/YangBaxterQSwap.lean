import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Yang–Baxter q-Swap — explicit 8×8 verification

The q-scaled swap matrix `C_q` on `Fin 4` (isomorphic to `M₂⊗M₂`),
and its 3-site embeddings `C₁₂`, `C₂₃` on `Fin 8`. Direct 8×8
computation proves the Artin/Yang–Baxter relation at any q.

Strategy: same `ext i j; fin_cases i <;> fin_cases j; simp; norm_num`
pattern that successfully proved TL₃(2) in TLChain.lean.
-/

noncomputable section

namespace InfoGeometry.Physics.YangBaxterQSwap

open Matrix

variable (q : ℂ)

/-- The q-scaled swap on Fin 4: maps basis (a,b) → q·(b,a). -/
def C_q : Matrix (Fin 4) (Fin 4) ℂ :=
  q • !![1, 0, 0, 0;
         0, 0, 1, 0;
         0, 1, 0, 0;
         0, 0, 0, 1]

/-- C₁₂ = C_q ⊗ I₂ acting on slots (0,1) of the 3-site chain (Fin 2×Fin 2×Fin 2 ≅ Fin 8). -/
def C12 : Matrix (Fin 8) (Fin 8) ℂ :=
  q • !![1, 0, 0, 0, 0, 0, 0, 0;
         0, 1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 1, 0, 0;
         0, 0, 1, 0, 0, 0, 0, 0;
         0, 0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 0, 0, 1]

/-- C₂₃ = I₂ ⊗ C_q acting on slots (1,2) of the 3-site chain. -/
def C23 : Matrix (Fin 8) (Fin 8) ℂ :=
  q • !![1, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0, 0;
         0, 1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 0, 0, 1]

/-- Yang–Baxter / Artin relation: C₁₂·C₂₃·C₁₂ = C₂₃·C₁₂·C₂₃.
Proved by explicit 8×8 computation — same pattern as TLChain.lean. -/
theorem yang_baxter_relation (q : ℂ) :
    C12 q * C23 q * C12 q = C23 q * C12 q * C23 q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [C12, C23, C_q, Matrix.mul_apply, Matrix.smul_apply]
    <;> simp [Fin.sum_univ_eight]

#check yang_baxter_relation

end InfoGeometry.Physics.YangBaxterQSwap
