import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Clifford.CliffordBott
import DAG.ChiralDiracAnticommutation

/-!
# DAG.GradedBottInclusion — Jordan-Wigner via Graded Tensor Product

The graded Bott periodicity inclusion for the split Clifford tower.

## The Graded Inclusion

```
bottInclusionEven (x) = I₂ ⊗ x  = [[x, 0], [0, x]]    (even = commutes)
bottInclusionOdd  (x) = Γ ⊗ x   = [[x, 0], [0, -x]]   (odd = anticommutes)
```

The minus sign on the bottom right of `bottInclusionOdd` IS the
Jordan-Wigner string — the non-local tail of -1's that maps local
spins into anticommuting fermions, generated recursively by the
inductive colimit step.

## The Recursive Dirac Operator

D_{n+1} = (D_n ⊗ I₂) + (Γ_n ⊗ D_new)
        = bottInclusionEven(D_n) + bottInclusionOdd(D_new)

The graded inclusion ensures new edges anticommute with the entire
causal past, preserving ΓD + DΓ = 0 through the direct limit.

## Key Theorem

If {D_n, X} = 0 in Cl(n,n), then {I₂⊗D_n, Γ⊗X} = 0 in Cl(n+1,n+1).

Proof: (I₂⊗D_n)(Γ⊗X) + (Γ⊗X)(I₂⊗D_n)
     = (D_n⊗X) + (-D_n⊗X)   [by the graded commutation rule]
     = 0
-/

open Matrix

namespace DAG.GradedBottInclusion

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.CliffordBott

/-! ## The graded inclusions -/

/-- Even graded inclusion: I₂ ⊗ x. Ring homomorphism. -/
def bottInclusionEven {n : ℕ} (x : SplitClNNAlg n) : Matrix (Fin 2) (Fin 2) (SplitClNNAlg n) :=
  λ i j =>
    match i, j with
    | 0, 0 => x
    | 1, 1 => x
    | _, _ => 0

/-- Odd graded inclusion: Γ ⊗ x. Carries the Jordan-Wigner string (-1 on bottom right). -/
def bottInclusionOdd {n : ℕ} (x : SplitClNNAlg n) : Matrix (Fin 2) (Fin 2) (SplitClNNAlg n) :=
  λ i j =>
    match i, j with
    | 0, 0 => x
    | 1, 1 => -x
    | _, _ => 0

/-! ## Theorem: Graded anticommutation preserved -/

/--
**Theorem.** If {D, X} = 0 in Cl(n,n), then
{bottInclusionEven(D), bottInclusionOdd(X)} = 0 in Cl(n+1,n+1).

The proof is a direct entrywise computation on the 2×2 matrix blocks.
The key entry is (0,0): D·X + X·D = h_anticomm = 0.
The entry (1,1): D·(-X) + (-X)·D = -(D·X + X·D) = -0 = 0.
All other entries are zero.
-/
theorem graded_anticommutation_preserved {n : ℕ}
    (D X : SplitClNNAlg n)
    (h_anticomm : D * X + X * D = 0) :
    bottInclusionEven D * bottInclusionOdd X
    + bottInclusionOdd X * bottInclusionEven D = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · -- (0,0): D*X + X*D = h_anticomm = 0
    simp [bottInclusionEven, bottInclusionOdd, Matrix.mul_apply, Matrix.add_apply, h_anticomm]
  · -- (0,1): all zero
    simp [bottInclusionEven, bottInclusionOdd, Matrix.mul_apply, Matrix.add_apply]
  · -- (1,0): all zero
    simp [bottInclusionEven, bottInclusionOdd, Matrix.mul_apply, Matrix.add_apply]
  · -- (1,1): D*(-X) + (-X)*D = -(D*X + X*D) = 0
    simp [bottInclusionEven, bottInclusionOdd, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two]
    simpa [neg_add, add_comm] using congrArg Neg.neg h_anticomm

/-! ## The recursive Dirac construction -/

/--
The Dirac operator at stage (n+1) built from the past Dirac D_n
and the new edge contribution D_new.

    D_{n+1} = bottInclusionEven(D_n) + bottInclusionOdd(D_new)

where D_new encodes the 2×2 incidence of the new edge. The
bottInclusionOdd applies the Jordan-Wigner string to ensure
anticommutation with the causal past.
-/
def diracStep {n : ℕ}
    (D_past : SplitClNNAlg n)
    (D_new : SplitClNNAlg n) :
    Matrix (Fin 2) (Fin 2) (SplitClNNAlg n) :=
  bottInclusionEven D_past + bottInclusionOdd D_new

end DAG.GradedBottInclusion
