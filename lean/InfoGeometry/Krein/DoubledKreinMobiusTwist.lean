/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import InfoGeometry.Clifford.SplitQ11

open ContinuousLinearMap

namespace InfoGeometry.Krein

/-!
# Doubled Krein Space, Krein-Dirac Adjoint, Split Clifford CAR, and Möbius Twist

This module formalizes:
1. **Fundamental Symmetry & Krein-Dirac Adjoint:**
   Intrinsic Krein adjoint $A^\sharp = J A^* J$ on a Hilbert-Krein space with fundamental symmetry $J^2 = 1, J^* = J$.
   Properties: $(A^\sharp)^\sharp = A$, $(A B)^\sharp = B^\sharp A^\sharp$, and Krein self-adjointness $A^\sharp = A$.
2. **Krein Projector Geometry ($P_+, P_-$) & Bogoliubov Metric Preservation:**
   Orthogonal positive and negative projectors $P_+ + P_- = 1$, $P_- P_+ = 0$, $P_\pm^2 = P_\pm$, $P_\pm^* = P_\pm$.
   Fundamental symmetry $J = P_+ - P_-$ with $J^2 = 1$.
   Bogoliubov components $\Phi = P_+ T P_+$, $\Psi = P_- T P_+$.
   Theorem: If $T$ is a Krein isometry on the positive cone ($P_+ T^\sharp T P_+ = P_+$),
   then $\Phi^* \Phi - \Psi^* \Psi = P_+$.
3. **Symmetrically Split Doubled Space $\mathcal{K}_{\mathrm{dbl}} = E \times E$:**
   Modular swap involution $J(x, y) = (y, x)$.
   $2 \times 2$ continuous linear block operator algebra `fromBlocks A11 A12 A21 A22`.
   Block Krein-Dirac adjoint:
   $$\begin{pmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{pmatrix}^\sharp = \begin{pmatrix} A_{22}^* & A_{12}^* \\ A_{21}^* & A_{11}^* \end{pmatrix}$$
   Exact characterization of Krein-self-adjointness ($A^\sharp = A$) and Krein-isometry ($A^\sharp A = 1$).
4. **Split Clifford Base $\mathrm{Cl}(1, 1)$ & Isotropic Null CAR Generators:**
   Signature $(1, -1)$ quadratic form $Q_{\mathrm{split}}$.
   Generators $e_1^2 = 1$, $e_2^2 = -1$, $\{e_1, e_2\} = 0$.
   CAR-normalized null generators $u = \frac{1}{2}(e_1 + e_2)$, $v = \frac{1}{2}(e_1 - e_2)$ satisfying
   $u^2 = 0$, $v^2 = 0$, and $\{u, v\} = 1$.
5. **Categorical Colimit for the Möbius Twist:**
   Mapping torus / circle bundle colimit via categorical coequalizer in any category.
-/

/-! ### 1. Fundamental Symmetry and Intrinsic Krein-Dirac Adjoint -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A Fundamental Symmetry on a Hilbert space, inducing a Krein structure. -/
structure FundamentalSymmetry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] where
  J : E →L[𝕜] E
  involutive : J.comp J = 1
  isSelfAdjoint : adjoint J = J

namespace FundamentalSymmetry

variable (symm : FundamentalSymmetry (𝕜 := 𝕜) E)

/-- The canonical Krein-Dirac adjoint: A♯ = J ∘ A* ∘ J -/
noncomputable def kreinDiracAdjoint (A : E →L[𝕜] E) : E →L[𝕜] E :=
  symm.J.comp ((adjoint A).comp symm.J)

@[simp]
theorem krein_adjoint_involutive (A : E →L[𝕜] E) :
    kreinDiracAdjoint symm (kreinDiracAdjoint symm A) = A := by
  have hJ (x : E) : symm.J (symm.J x) = x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) symm.involutive
    simpa using h
  ext x
  simp [kreinDiracAdjoint, ContinuousLinearMap.adjoint_comp,
    symm.isSelfAdjoint, hJ]

theorem krein_adjoint_mul (A B : E →L[𝕜] E) :
    kreinDiracAdjoint symm (A.comp B) = (kreinDiracAdjoint symm B).comp (kreinDiracAdjoint symm A) := by
  have hJ (x : E) : symm.J (symm.J x) = x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) symm.involutive
    simpa using h
  ext x
  simp [kreinDiracAdjoint, ContinuousLinearMap.adjoint_comp, hJ]

/-- A Krein-self-adjoint (or Dirac-Hermitian) operator: A♯ = A. -/
def IsKreinSelfAdjoint (A : E →L[𝕜] E) : Prop :=
  kreinDiracAdjoint symm A = A

end FundamentalSymmetry

/-! ### 2. Krein Projector Geometry: P+, P- and Bogoliubov Subspace Split -/

/-- A Krein projection pair P+, P- satisfying the canonical resolution of identity and orthogonality. -/
structure KreinProjections (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] where
  P_plus  : E →L[𝕜] E
  P_minus : E →L[𝕜] E
  res_id  : P_plus + P_minus = 1
  orthog  : P_minus.comp P_plus = 0
  p_plus_proj  : P_plus.comp P_plus = P_plus
  p_minus_proj : P_minus.comp P_minus = P_minus
  p_plus_selfadj  : adjoint P_plus = P_plus
  p_minus_selfadj : adjoint P_minus = P_minus

namespace KreinProjections

variable (kp : KreinProjections (𝕜 := 𝕜) E)

/-- Dual orthogonality: P+ ∘L P- = 0. -/
theorem orthog_symm : kp.P_plus.comp kp.P_minus = 0 := by
  have h := congrArg adjoint kp.orthog
  rw [ContinuousLinearMap.adjoint_comp, kp.p_plus_selfadj,
    kp.p_minus_selfadj] at h
  simpa using h

/-- The fundamental symmetry J = P+ - P-. -/
def J : E →L[𝕜] E := kp.P_plus - kp.P_minus

@[simp]
theorem J_sq : kp.J.comp kp.J = 1 := by
  dsimp [J]
  calc
    (kp.P_plus - kp.P_minus).comp (kp.P_plus - kp.P_minus)
      = kp.P_plus.comp kp.P_plus - kp.P_plus.comp kp.P_minus - kp.P_minus.comp kp.P_plus + kp.P_minus.comp kp.P_minus := by
        simp only [comp_sub, sub_comp, sub_add_eq_add_sub, add_sub_assoc]
        abel
    _ = kp.P_plus - 0 - 0 + kp.P_minus := by
        rw [kp.p_plus_proj, kp.orthog_symm, kp.orthog, kp.p_minus_proj]
    _ = kp.P_plus + kp.P_minus := by
        abel
    _ = 1 := kp.res_id

@[simp]
theorem J_selfadj : adjoint kp.J = kp.J := by
  have h : adjoint kp.J = star kp.J := (star_eq_adjoint kp.J).symm
  rw [h]
  change star (kp.P_plus - kp.P_minus) = kp.J
  rw [star_sub]
  rw [star_eq_adjoint, star_eq_adjoint]
  rw [kp.p_plus_selfadj, kp.p_minus_selfadj]
  rfl

/-- The canonical FundamentalSymmetry induced by a Krein projection pair. -/
def toFundamentalSymmetry : FundamentalSymmetry (𝕜 := 𝕜) E where
  J := kp.J
  involutive := kp.J_sq
  isSelfAdjoint := kp.J_selfadj

/-- The Krein-Dirac adjoint induced by the projection pair. -/
noncomputable def kreinAdjoint (A : E →L[𝕜] E) : E →L[𝕜] E :=
  kp.toFundamentalSymmetry.kreinDiracAdjoint A

/-- Bogoliubov transmission component: Φ = P+ T P+. -/
def Phi (T : E →L[𝕜] E) : E →L[𝕜] E := kp.P_plus.comp (T.comp kp.P_plus)

/-- Bogoliubov reflection / leakage component: Ψ = P- T P+. -/
def Psi (T : E →L[𝕜] E) : E →L[𝕜] E := kp.P_minus.comp (T.comp kp.P_plus)

@[simp]
theorem adjoint_Phi (T : E →L[𝕜] E) :
    adjoint (kp.Phi T) = kp.P_plus.comp ((adjoint T).comp kp.P_plus) := by
  simp [Phi, ContinuousLinearMap.adjoint_comp, kp.p_plus_selfadj,
    ContinuousLinearMap.comp_assoc]

@[simp]
theorem adjoint_Psi (T : E →L[𝕜] E) :
    adjoint (kp.Psi T) = kp.P_plus.comp ((adjoint T).comp kp.P_minus) := by
  simp [Psi, ContinuousLinearMap.adjoint_comp, kp.p_plus_selfadj,
    kp.p_minus_selfadj, ContinuousLinearMap.comp_assoc]

theorem P_plus_comp_J : kp.P_plus.comp kp.J = kp.P_plus := by
  dsimp [J]
  calc
    kp.P_plus.comp (kp.P_plus - kp.P_minus)
      = kp.P_plus.comp kp.P_plus - kp.P_plus.comp kp.P_minus := by rw [comp_sub]
    _ = kp.P_plus - 0 := by rw [kp.p_plus_proj, kp.orthog_symm]
    _ = kp.P_plus := by rw [sub_zero]

theorem P_minus_comp_J : kp.P_minus.comp kp.J = -kp.P_minus := by
  dsimp [J]
  calc
    kp.P_minus.comp (kp.P_plus - kp.P_minus)
      = kp.P_minus.comp kp.P_plus - kp.P_minus.comp kp.P_minus := by rw [comp_sub]
    _ = 0 - kp.P_minus := by rw [kp.orthog, kp.p_minus_proj]
    _ = -kp.P_minus := by rw [zero_sub]

/-- Fundamental Theorem of Krein-Bogoliubov Subspace Geometry:
    If T is a Krein isometry on the positive cone (P+ T♯ T P+ = P+),
    then Φ*Φ - Ψ*Ψ = P+. -/
theorem bogoliubov_subspace_split (T : E →L[𝕜] E)
    (hT : kp.P_plus.comp ((kp.kreinAdjoint T).comp (T.comp kp.P_plus)) = kp.P_plus) :
    (adjoint (kp.Phi T)).comp (kp.Phi T) - (adjoint (kp.Psi T)).comp (kp.Psi T) = kp.P_plus := by
  have hJ_decomp : kp.J.comp (T.comp kp.P_plus) = kp.Phi T - kp.Psi T := by
    dsimp [J, Phi, Psi]
    rw [sub_comp]
  have hT_decomp : T.comp kp.P_plus = kp.Phi T + kp.Psi T := by
    dsimp [Phi, Psi]
    rw [← add_comp, kp.res_id]
    ext x
    simp
  have hadj : adjoint (T.comp kp.P_plus) = adjoint (kp.Phi T) + adjoint (kp.Psi T) := by
    rw [hT_decomp]
    have h_adj_star : adjoint (kp.Phi T + kp.Psi T) = star (kp.Phi T + kp.Psi T) :=
      (star_eq_adjoint _).symm
    rw [h_adj_star, star_add, star_eq_adjoint, star_eq_adjoint]
  have h_orth1 : (adjoint (kp.Phi T)).comp (kp.Psi T) = 0 := by
    rw [adjoint_Phi, Psi]
    calc
      (kp.P_plus.comp ((adjoint T).comp kp.P_plus)).comp (kp.P_minus.comp (T.comp kp.P_plus))
        = (kp.P_plus.comp (adjoint T)).comp ((kp.P_plus.comp kp.P_minus).comp (T.comp kp.P_plus)) := by
          simp only [comp_assoc]
      _ = (kp.P_plus.comp (adjoint T)).comp ((0 : E →L[𝕜] E).comp (T.comp kp.P_plus)) := by
          rw [kp.orthog_symm]
      _ = 0 := by simp only [zero_comp, comp_zero]
  have h_orth2 : (adjoint (kp.Psi T)).comp (kp.Phi T) = 0 := by
    rw [adjoint_Psi, Phi]
    calc
      (kp.P_plus.comp ((adjoint T).comp kp.P_minus)).comp (kp.P_plus.comp (T.comp kp.P_plus))
        = (kp.P_plus.comp (adjoint T)).comp ((kp.P_minus.comp kp.P_plus).comp (T.comp kp.P_plus)) := by
          simp only [comp_assoc]
      _ = (kp.P_plus.comp (adjoint T)).comp ((0 : E →L[𝕜] E).comp (T.comp kp.P_plus)) := by
          rw [kp.orthog]
      _ = 0 := by simp only [zero_comp, comp_zero]
  have h_eval :
      kp.P_plus.comp ((kp.kreinAdjoint T).comp (T.comp kp.P_plus)) =
        (adjoint (kp.Phi T)).comp (kp.Phi T) - (adjoint (kp.Psi T)).comp (kp.Psi T) := by
    dsimp [kreinAdjoint, FundamentalSymmetry.kreinDiracAdjoint, toFundamentalSymmetry]
    have h1 : kp.P_plus.comp ((kp.J.comp ((adjoint T).comp kp.J)).comp (T.comp kp.P_plus))
            = (adjoint (T.comp kp.P_plus)).comp (kp.J.comp (T.comp kp.P_plus)) := by
      calc
        kp.P_plus.comp ((kp.J.comp ((adjoint T).comp kp.J)).comp (T.comp kp.P_plus))
          = (kp.P_plus.comp kp.J).comp ((adjoint T).comp (kp.J.comp (T.comp kp.P_plus))) := by
            simp only [comp_assoc]
        _ = kp.P_plus.comp ((adjoint T).comp (kp.J.comp (T.comp kp.P_plus))) := by
            rw [kp.P_plus_comp_J]
        _ = (adjoint kp.P_plus).comp ((adjoint T).comp (kp.J.comp (T.comp kp.P_plus))) := by
            rw [kp.p_plus_selfadj]
        _ = (adjoint (T.comp kp.P_plus)).comp (kp.J.comp (T.comp kp.P_plus)) := by
            simp only [adjoint_comp, comp_assoc]
    have h2 : (adjoint (T.comp kp.P_plus)).comp (kp.J.comp (T.comp kp.P_plus))
            = (adjoint (kp.Phi T) + adjoint (kp.Psi T)).comp (kp.Phi T - kp.Psi T) := by
      rw [hadj, hJ_decomp]
    have h3 : (adjoint (kp.Phi T) + adjoint (kp.Psi T)).comp (kp.Phi T - kp.Psi T)
            = (adjoint (kp.Phi T)).comp (kp.Phi T) - (adjoint (kp.Psi T)).comp (kp.Psi T) := by
      calc
        (adjoint (kp.Phi T) + adjoint (kp.Psi T)).comp (kp.Phi T - kp.Psi T)
          = (adjoint (kp.Phi T)).comp (kp.Phi T) - (adjoint (kp.Phi T)).comp (kp.Psi T) +
            (adjoint (kp.Psi T)).comp (kp.Phi T) - (adjoint (kp.Psi T)).comp (kp.Psi T) := by
            simp only [add_comp, comp_sub, sub_add_eq_add_sub, add_sub_assoc]
            abel
        _ = (adjoint (kp.Phi T)).comp (kp.Phi T) - 0 + 0 - (adjoint (kp.Psi T)).comp (kp.Psi T) := by
            rw [h_orth1, h_orth2]
        _ = (adjoint (kp.Phi T)).comp (kp.Phi T) - (adjoint (kp.Psi T)).comp (kp.Psi T) := by
            abel
    rw [h1, h2, h3]
  rw [← h_eval, hT]

end KreinProjections

/-! ### 3. Symmetrically Split Doubled Space E × E and Block Matrix Operator Algebra -/

/-- The modular swap involution J(x, y) = (y, x) on E × E. -/
def modularJ : (E × E) →L[𝕜] (E × E) :=
  (ContinuousLinearMap.snd 𝕜 E E).prod (ContinuousLinearMap.fst 𝕜 E E)

omit [CompleteSpace E] in
@[simp]
theorem modularJ_apply (p : E × E) :
    modularJ (𝕜 := 𝕜) (E := E) p = (p.2, p.1) := rfl

omit [CompleteSpace E] in
@[simp]
theorem modularJ_involutive :
    (modularJ (𝕜 := 𝕜) (E := E)).comp (modularJ (𝕜 := 𝕜) (E := E)) = 1 := by
  apply ContinuousLinearMap.ext
  intro p
  simp [modularJ]

/-- Assembles a 2x2 block matrix of continuous linear maps into an operator on E × E. -/
def fromBlocks (A11 A12 A21 A22 : E →L[𝕜] E) : (E × E) →L[𝕜] (E × E) :=
  (A11.comp (ContinuousLinearMap.fst 𝕜 E E) + A12.comp (ContinuousLinearMap.snd 𝕜 E E)).prod
  (A21.comp (ContinuousLinearMap.fst 𝕜 E E) + A22.comp (ContinuousLinearMap.snd 𝕜 E E))

omit [CompleteSpace E] in
@[simp]
theorem fromBlocks_apply (A11 A12 A21 A22 : E →L[𝕜] E) (p : E × E) :
    fromBlocks A11 A12 A21 A22 p = (A11 p.1 + A12 p.2, A21 p.1 + A22 p.2) := rfl

omit [CompleteSpace E] in
theorem fromBlocks_inj {A11 A12 A21 A22 B11 B12 B21 B22 : E →L[𝕜] E}
    (h : fromBlocks A11 A12 A21 A22 = fromBlocks B11 B12 B21 B22) :
    A11 = B11 ∧ A12 = B12 ∧ A21 = B21 ∧ A22 = B22 := by
  have h_x (x : E) : fromBlocks A11 A12 A21 A22 (x, 0) = fromBlocks B11 B12 B21 B22 (x, 0) :=
    congrArg (· (x, 0)) h
  have h_y (y : E) : fromBlocks A11 A12 A21 A22 (0, y) = fromBlocks B11 B12 B21 B22 (0, y) :=
    congrArg (· (0, y)) h
  simp only [fromBlocks_apply, map_zero, add_zero, zero_add, Prod.mk.injEq] at h_x h_y
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x; exact (h_x x).1
  · ext y; exact (h_y y).1
  · ext x; exact (h_x x).2
  · ext y; exact (h_y y).2

omit [CompleteSpace E] in
/-- Composition of two 2x2 block operators adheres to block matrix multiplication. -/
theorem fromBlocks_comp (A11 A12 A21 A22 B11 B12 B21 B22 : E →L[𝕜] E) :
    (fromBlocks A11 A12 A21 A22).comp (fromBlocks B11 B12 B21 B22) =
      fromBlocks
        (A11.comp B11 + A12.comp B21)
        (A11.comp B12 + A12.comp B22)
        (A21.comp B11 + A22.comp B21)
        (A21.comp B12 + A22.comp B22) := by
  apply ContinuousLinearMap.ext
  intro p
  ext
  · simp only [ContinuousLinearMap.comp_apply, fromBlocks_apply, map_add, add_apply]
    abel
  · simp only [ContinuousLinearMap.comp_apply, fromBlocks_apply, map_add, add_apply]
    abel

omit [CompleteSpace E] in
/-- The identity operator on E × E in 2x2 block form. -/
theorem fromBlocks_one :
    (1 : (E × E) →L[𝕜] (E × E)) = fromBlocks 1 0 0 1 := by
  apply ContinuousLinearMap.ext
  intro p
  ext <;> simp [fromBlocks_apply]

/-- The block Hilbert adjoint: (fromBlocks A11 A12 A21 A22)* = fromBlocks A11* A21* A12* A22*. -/
noncomputable def blockAdjoint (A11 A12 A21 A22 : E →L[𝕜] E) : (E × E) →L[𝕜] (E × E) :=
  fromBlocks (adjoint A11) (adjoint A21) (adjoint A12) (adjoint A22)

/-- Krein-Dirac adjoint on E × E induced by modular swap J sandwiching the block adjoint. -/
noncomputable def blockKreinAdjoint (A11 A12 A21 A22 : E →L[𝕜] E) : (E × E) →L[𝕜] (E × E) :=
  (modularJ (𝕜 := 𝕜) (E := E)).comp ((blockAdjoint A11 A12 A21 A22).comp (modularJ (𝕜 := 𝕜) (E := E)))

/-- Fundamental block Krein-Dirac adjoint identity:
    (fromBlocks A11 A12 A21 A22)♯ = fromBlocks A22* A12* A21* A11* -/
theorem blockKreinAdjoint_eq (A11 A12 A21 A22 : E →L[𝕜] E) :
    blockKreinAdjoint A11 A12 A21 A22 =
      fromBlocks (adjoint A22) (adjoint A12) (adjoint A21) (adjoint A11) := by
  apply ContinuousLinearMap.ext
  intro p
  ext
  · simp only [blockKreinAdjoint, ContinuousLinearMap.comp_apply, modularJ_apply, blockAdjoint, fromBlocks_apply]
    abel
  · simp only [blockKreinAdjoint, ContinuousLinearMap.comp_apply, modularJ_apply, blockAdjoint, fromBlocks_apply]
    abel

/-- The block Krein adjoint reverses composition on the native doubled-space
    operator algebra. -/
theorem blockKreinAdjoint_comp
    (A11 A12 A21 A22 B11 B12 B21 B22 : E →L[𝕜] E) :
    blockKreinAdjoint
        (A11.comp B11 + A12.comp B21)
        (A11.comp B12 + A12.comp B22)
        (A21.comp B11 + A22.comp B21)
        (A21.comp B12 + A22.comp B22) =
      (blockKreinAdjoint B11 B12 B21 B22).comp
        (blockKreinAdjoint A11 A12 A21 A22) := by
  have h_add (S T : E →L[𝕜] E) : adjoint (S + T) = adjoint S + adjoint T := by
    rw [← star_eq_adjoint, star_add, star_eq_adjoint, star_eq_adjoint]
  rw [blockKreinAdjoint_eq, blockKreinAdjoint_eq, blockKreinAdjoint_eq,
    fromBlocks_comp]
  apply ContinuousLinearMap.ext
  intro p
  ext
  · simp only [ContinuousLinearMap.comp_apply, fromBlocks_apply,
      h_add, ContinuousLinearMap.adjoint_comp]
    abel
  · simp only [ContinuousLinearMap.comp_apply, fromBlocks_apply,
      h_add, ContinuousLinearMap.adjoint_comp]
    abel

/-- The block Krein adjoint is involutive on the native doubled-space
    operator algebra. -/
theorem blockKreinAdjoint_involutive
    (A11 A12 A21 A22 : E →L[𝕜] E) :
    blockKreinAdjoint
        (adjoint A22) (adjoint A12) (adjoint A21) (adjoint A11) =
      fromBlocks A11 A12 A21 A22 := by
  rw [blockKreinAdjoint_eq]
  simp only [ContinuousLinearMap.adjoint_adjoint]

/-- Krein-Dirac self-adjointness equivalence:
    A block operator is Krein-self-adjoint iff the diagonal blocks are adjoint reflections
    and the off-diagonal blocks are Hermitian. -/
theorem isKreinSelfAdjoint_fromBlocks_iff (A11 A12 A21 A22 : E →L[𝕜] E) :
    blockKreinAdjoint A11 A12 A21 A22 = fromBlocks A11 A12 A21 A22 ↔
      adjoint A22 = A11 ∧ adjoint A12 = A12 ∧ adjoint A21 = A21 ∧ adjoint A11 = A22 := by
  rw [blockKreinAdjoint_eq]
  constructor
  · intro h
    exact fromBlocks_inj h
  · rintro ⟨h22, h12, h21, h11⟩
    rw [h22, h12, h21, h11]

/-- Krein isometry equivalence on block operators:
    A♯ ∘L A = 1 iff the 4 canonical metric-preservation equations hold. -/
theorem isKreinIsometry_fromBlocks_iff (A11 A12 A21 A22 : E →L[𝕜] E) :
    (blockKreinAdjoint A11 A12 A21 A22).comp (fromBlocks A11 A12 A21 A22) = 1 ↔
      (adjoint A22).comp A11 + (adjoint A12).comp A21 = 1 ∧
      (adjoint A22).comp A12 + (adjoint A12).comp A22 = 0 ∧
      (adjoint A21).comp A11 + (adjoint A11).comp A21 = 0 ∧
      (adjoint A21).comp A12 + (adjoint A11).comp A22 = 1 := by
  rw [blockKreinAdjoint_eq, fromBlocks_comp, fromBlocks_one]
  constructor
  · intro h
    exact fromBlocks_inj h
  · rintro ⟨h11, h12, h21, h22⟩
    rw [h11, h12, h21, h22]

/-! ### 4. Split Clifford Algebra Cl(1, 1) and Isotropic CAR Null Generators -/

/-- Split signature (1, -1) quadratic form on ℝ × ℝ. -/
noncomputable def Q_split : QuadraticForm ℝ (ℝ × ℝ) :=
  -- Reuse the existing canonical split-signature owner.
  InfoGeometry.Clifford.splitQ11

@[simp]
theorem Q_split_apply (v : ℝ × ℝ) : Q_split v = v.1 ^ 2 - v.2 ^ 2 := by
  simp [Q_split, InfoGeometry.Clifford.splitQ11_apply, sq]

abbrev Cl11 := CliffordAlgebra (Q_split)

/-- First split generator e₁ with e₁² = +1. -/
noncomputable def e1 : Cl11 := CliffordAlgebra.ι (Q_split) (1, 0)

/-- Second split generator e₂ with e₂² = -1. -/
noncomputable def e2 : Cl11 := CliffordAlgebra.ι (Q_split) (0, 1)

@[simp]
theorem e1_sq : e1 * e1 = 1 := by
  rw [e1, CliffordAlgebra.ι_sq_scalar]
  simp [Q_split_apply]

@[simp]
theorem e2_sq : e2 * e2 = -1 := by
  rw [e2, CliffordAlgebra.ι_sq_scalar]
  simp [Q_split_apply]

theorem e1_e2_anticomm : e1 * e2 + e2 * e1 = 0 := by
  rw [e1, e2, CliffordAlgebra.ι_mul_ι_add_swap]
  have hpolar : QuadraticMap.polar Q_split (1, 0) (0, 1) = 0 := by
    simp [QuadraticMap.polar, Q_split_apply]
  rw [hpolar, map_zero]

theorem e1_e2_mul_neg : e1 * e2 = -(e2 * e1) := by
  exact eq_neg_of_add_eq_zero_left e1_e2_anticomm

/-- CAR-normalized isotropic creation/annihilation generator u. -/
noncomputable def u_null : Cl11 := (1 / 2 : ℝ) • (e1 + e2)

/-- Dual isotropic generator v. -/
noncomputable def v_null : Cl11 := (1 / 2 : ℝ) • (e1 - e2)

/-- Nilpotency of the creation operator: u² = 0. -/
@[simp]
theorem u_sq_zero : u_null * u_null = 0 := by
  dsimp [u_null]
  rw [mul_smul_comm, smul_mul_assoc]
  have hsq : (e1 + e2) * (e1 + e2) = 0 := by
    calc
      (e1 + e2) * (e1 + e2) = e1 * (e1 + e2) + e2 * (e1 + e2) := by rw [add_mul]
      _ = e1 * e1 + e1 * e2 + (e2 * e1 + e2 * e2) := by rw [mul_add, mul_add]
      _ = e1 * e1 + (e1 * e2 + e2 * e1) + e2 * e2 := by abel
      _ = 1 + 0 + (-1) := by rw [e1_sq, e1_e2_anticomm, e2_sq]
      _ = 0 := by abel
  rw [hsq, smul_zero, smul_zero]

/-- Nilpotency of the dual operator: v² = 0. -/
@[simp]
theorem v_sq_zero : v_null * v_null = 0 := by
  dsimp [v_null]
  rw [mul_smul_comm, smul_mul_assoc]
  have hsq : (e1 - e2) * (e1 - e2) = 0 := by
    calc
      (e1 - e2) * (e1 - e2) = e1 * (e1 - e2) - e2 * (e1 - e2) := by rw [sub_mul]
      _ = e1 * e1 - e1 * e2 - (e2 * e1 - e2 * e2) := by rw [mul_sub, mul_sub]
      _ = e1 * e1 - (e1 * e2 + e2 * e1) + e2 * e2 := by abel
      _ = 1 - 0 + (-1) := by rw [e1_sq, e1_e2_anticomm, e2_sq]
      _ = 0 := by abel
  rw [hsq, smul_zero, smul_zero]

/-- Exact Canonical Anticommutation Relation (CAR): {u, v} = uv + vu = 1. -/
theorem uv_car_anticomm : u_null * v_null + v_null * u_null = 1 := by
  have huv : (e1 + e2) * (e1 - e2) = (1 : Cl11) + 1 - e1 * e2 + e2 * e1 := by
    calc
      (e1 + e2) * (e1 - e2) = e1 * (e1 - e2) + e2 * (e1 - e2) := by rw [add_mul]
      _ = e1 * e1 - e1 * e2 + (e2 * e1 - e2 * e2) := by rw [mul_sub, mul_sub]
      _ = 1 - e1 * e2 + (e2 * e1 - (-1)) := by simp only [e1_sq, e2_sq]
      _ = (1 : Cl11) + 1 - e1 * e2 + e2 * e1 := by abel
  have hvu : (e1 - e2) * (e1 + e2) = (1 : Cl11) + 1 + e1 * e2 - e2 * e1 := by
    calc
      (e1 - e2) * (e1 + e2) = e1 * (e1 + e2) - e2 * (e1 + e2) := by rw [sub_mul]
      _ = e1 * e1 + e1 * e2 - (e2 * e1 + e2 * e2) := by rw [mul_add, mul_add]
      _ = 1 + e1 * e2 - (e2 * e1 + (-1)) := by simp only [e1_sq, e2_sq]
      _ = (1 : Cl11) + 1 + e1 * e2 - e2 * e1 := by abel
  have hsum : ((e1 + e2) * (e1 - e2)) + ((e1 - e2) * (e1 + e2)) = (4 : ℝ) • (1 : Cl11) := by
    rw [huv, hvu]
    have h1 : ((1 : Cl11) + 1 - e1 * e2 + e2 * e1) + ((1 : Cl11) + 1 + e1 * e2 - e2 * e1)
            = (1 : Cl11) + 1 + 1 + 1 := by abel
    rw [h1]
    have h4 : (1 : Cl11) + 1 + 1 + 1 = 4 := by norm_num
    rw [h4]
    have hsmul : (4 : Cl11) = (4 : ℝ) • (1 : Cl11) := by
      rw [← map_ofNat (algebraMap ℝ Cl11) 4, Algebra.algebraMap_eq_smul_one]
    exact hsmul
  dsimp [u_null, v_null]
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
  rw [← smul_add, ← smul_add, hsum]
  rw [smul_smul, smul_smul]
  have h_scalar : (1 / 2 : ℝ) * (1 / 2 : ℝ) * (4 : ℝ) = 1 := by norm_num
  rw [h_scalar, one_smul]

/-! ### 5. Categorical Colimit for the Möbius Twist -/

section MoebiusTwist

open CategoryTheory Limits

variable {C : Type*} [Category C]

/-- The parallel pair diagram encoding the twisted mapping torus over S¹.
    One leg is identity; the second leg applies the global CPT / (-1)^F twist. -/
def moebiusDiagram (K : C) (cpt_twist : K ≅ K) :
    WalkingParallelPair ⥤ C :=
  parallelPair (𝟙 K) cpt_twist.hom

/-- The Möbius twisted state space as the categorical coequalizer (colimit) of the diagram. -/
noncomputable abbrev MoebiusColimit (K : C) (cpt_twist : K ≅ K) [HasColimit (moebiusDiagram K cpt_twist)] : C :=
  colimit (moebiusDiagram K cpt_twist)

/-- Canonical quotient projection to the Möbius colimit. -/
noncomputable def toMoebius (K : C) (cpt_twist : K ≅ K) [HasColimit (moebiusDiagram K cpt_twist)] :
    K ⟶ MoebiusColimit K cpt_twist :=
  colimit.ι (moebiusDiagram K cpt_twist) WalkingParallelPair.one

/-- The twisting identity on the Möbius colimit: the CPT twist acts as identity on the colimit. -/
theorem toMoebius_twist (K : C) (cpt_twist : K ≅ K) [HasColimit (moebiusDiagram K cpt_twist)] :
    cpt_twist.hom ≫ toMoebius K cpt_twist = toMoebius K cpt_twist := by
  have h := colimit.w (moebiusDiagram K cpt_twist) WalkingParallelPairHom.right
  have h_left := colimit.w (moebiusDiagram K cpt_twist) WalkingParallelPairHom.left
  dsimp [moebiusDiagram, toMoebius] at h h_left ⊢
  rw [Category.id_comp] at h_left
  exact h.trans h_left.symm

end MoebiusTwist

end InfoGeometry.Krein
