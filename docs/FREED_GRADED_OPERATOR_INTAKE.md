# Archived source proposal: Freed geometric index and anomalies

> **Unverified source proposal — not promoted mathematics.**
> Source: the user's complete submission in this conversation, dated **2026-11-12**, supplied with the GitHub connector selected.
> Preservation note: Markdown transport escapes and the HTML indentation entity `&#x20;` have been normalized for readability. The mathematical claims, causal diagram, theorem names, hypotheses, definitions, and proposed Lean proofs below are preserved as submitted; corrections and verification results belong in the separate theorem contract.

---

### I. Extraction of the Stream of Pure Mathematical Consciousness

Filtering out the biographical anecdotes, institutional updates, and conversational framing from the Dan Freed transcript reveals five deep mathematical themes in **geometric index theory, projective anomaly cohomology, superconnections, non-invertible defect algebras, and Wick-rotated cobordism unitarity**. Translated into the canonical language of **noncommutative operator algebra and $\mathbb{Z}_2$-graded matrix geometry** over an arbitrary noncommutative ring $(\mathcal{A}, \star)$, this stream of consciousness crystallizes as follows:

1. **Projective State Geometry, Non-Abelian Anomaly 2-Cocycles, and Green–Schwarz / 't Hooft Anomaly Matching**:
   * *Mathematical Essence*: Pure quantum states form a projective geometry (rays/projections invariant under non-Abelian right gauge rescaling), whereas quantization requires lifting projective transformations into a linear operator algebra so they can be summed and composed.
   * In $M_2(\mathcal{A})$, lifting a pair of noncommutative parameters $(a, b) \in \mathcal{A} \times \mathcal{A}$ into the linear operator family
     $$W(a, b) := 1 + a F_+ + b F_- = \begin{pmatrix} 1 & a \\ b & 1 \end{pmatrix}$$
     fails to be an additive homomorphism by an **even diagonal operator obstruction**—the **Non-Abelian Anomaly Cocycle**:
     $$W(a_1, b_1) W(a_2, b_2) = W(a_1 + a_2, b_1 + b_2) + \mathcal{C}(a_1, b_1, a_2, b_2), \qquad \mathcal{C}(a_1, b_1, a_2, b_2) := \begin{pmatrix} a_1 b_2 & 0 \\ 0 & b_1 a_2 \end{pmatrix}.$$
   * **Green–Schwarz Anomaly Cancellation**: Coupling $W(a, b)$ to an even counterterm ("invertible field theory") $c = c_+ P_+ + c_- P_- = \begin{pmatrix} c_+ & 0 \\ 0 & c_- \end{pmatrix}$ via $\widetilde{W}(a, b, c_+, c_-) = W(a, b) + c_+ P_+ + c_- P_-$ trivializes the anomaly under the Green–Schwarz counterterm shift $(c_+, c_-) \mapsto (-a_1 b_2, -b_1 a_2)$.
   * **'t Hooft Anomaly Matching across Mellin Renormalization Scales**: Under the hyperbolic Mellin dilation $D(u) = \begin{pmatrix} u & 0 \\ 0 & u^{-1} \end{pmatrix}$ ($u \in \mathcal{A}^\times$), the operator family transforms covariantly as $D(u) W(a, b) D(u^{-1}) = W(u a u, u^{-1} b u^{-1})$, and the anomaly cocycle matches strictly across scales:
     $$D(u) \, \mathcal{C}(a_1, b_1, a_2, b_2) \, D(u^{-1}) = \mathcal{C}(u a_1 u, u^{-1} b_1 u^{-1}, u a_2 u, u^{-1} b_2 u^{-1}).$$

2. **Atiyah–Singer Supertrace Index & Invariance Under Jumping Kernel/Cokernel Modes**:
   * *Mathematical Essence*: As an elliptic or Fredholm operator varies in a family, its individual kernel ($\ker D$) and cokernel ($\operatorname{coker} D$) jump discontinuously as non-zero eigenmodes cross into or out of the zero-mode subspace, failing to form a vector bundle. However, the $\mathbb{Z}_2$-graded **Supertrace**
     $$\operatorname{Str}(M) := \operatorname{Tr}(\Gamma_1 M) = M_{00} - M_{11} \in \mathcal{A}$$
     cancels simultaneous spectral jumps in the positive-chirality ($P_+$) and negative-chirality ($P_-$) sectors.
   * For any family of chiral operators $K(\Pi_+, \Pi_-, \delta) = \begin{pmatrix} \Pi_+ + \delta & 0 \\ 0 & \Pi_- + \delta \end{pmatrix}$ whose positive and negative sectors jump by an arbitrary noncommutative operator mode $\delta \in \mathcal{A}$ (shifting the ordinary trace $\operatorname{Tr}(K(\Pi_+, \Pi_-, \delta)) = \Pi_+ + \Pi_- + 2\delta$), the **Atiyah–Singer Supertrace Index** is strictly invariant:
     $$\operatorname{Str}\big(K(\Pi_+, \Pi_-, \delta)\big) = \operatorname{Str}\big(K(\Pi_+, \Pi_-, 0)\big) = \Pi_+ - \Pi_-.$$

3. **Quillen–Bismut–Freed Superconnections, Supercurvature, and the Noncommutative Chern–Simons–Weil Transgression**:
   * *Mathematical Essence*: To construct the geometry and curvature of the determinant line bundle over families where kernels jump, **Quillen (1985)** and **Bismut–Freed (1986)** replaced ordinary block-diagonal connections $A = \begin{pmatrix} A_+ & 0 \\ 0 & A_- \end{pmatrix} \in \mathcal{M}_{\mathrm{even}}$ with a $\mathbb{Z}_2$-graded **Superconnection** combining $A$ and the odd Dirac operator $D = \begin{pmatrix} 0 & L_- \\ L_+ & 0 \end{pmatrix} \in \mathcal{M}_{\mathrm{odd}}$:
     $$\mathbb{A} := A + D = \begin{pmatrix} A_+ & L_- \\ L_+ & A_- \end{pmatrix} \in M_2(\mathcal{A}).$$
   * The algebraic supercurvature $\mathbb{A}^2$ splits by $\mathbb{Z}_2$-grading into the even curvature-Laplacian block $A^2 + D^2 = \begin{pmatrix} A_+^2 + L_- L_+ & 0 \\ 0 & A_-^2 + L_+ L_- \end{pmatrix}$ and the odd covariant differential $\{A, D\} = \begin{pmatrix} 0 & A_+ L_- + L_- A_- \\ L_+ A_+ + A_- L_+ & 0 \end{pmatrix}$, satisfying the universal Bianchi identity $[\mathbb{A}, \mathbb{A}^2] = 0$.
   * **Noncommutative Chern–Simons–Weil Transgression**: For any odd connection $D$ and even curvature background $\Phi$ with total supercurvature $F(\Phi, D) := \Phi + D^2$ and Bianchi derivative $\nabla_D(\Phi) := [D, \Phi]$, the noncommutative **Chern–Simons operator** $\mathcal{CS}(\Phi, D) := \Phi D + D \Phi + D^3$ transgresses the quadratic Chern–Weil invariant $2 F(\Phi, D)^2$ via the exact identity:
     $$\{D, \mathcal{CS}(\Phi, D)\} - [\nabla_D(\Phi), D] + 2 \Phi^2 = 2 F(\Phi, D)^2.$$

4. **Non-Invertible Categorical Symmetry Algebras & Kramers–Wannier / Peirce Defect Projectors**:
   * *Mathematical Essence*: What physicists call "non-invertible symmetries" are associative algebras of topological defect operators (containing non-invertible idempotents and zero divisors) that commute with the Hamiltonian.
   * For a chiral Hamiltonian $H_{\mathrm{chiral}}(h_+, h_-) = \begin{pmatrix} h_+ & 0 \\ 0 & h_- \end{pmatrix}$, the orthogonal Peirce projectors $P_+, P_-$ ($P_+ P_- = 0$) form a non-invertible symmetry algebra ($[P_\pm, H_{\mathrm{chiral}}] = 0$).
   * Dualizing via the shift operator $\Sigma$, for any translation-invariant Hamiltonian $H_{\mathrm{sym}}(h_0, h_1) = \begin{pmatrix} h_0 & h_1 \\ h_1 & h_0 \end{pmatrix}$ ($h_0, h_1 \in \mathcal{A}$ arbitrary non-commuting operators), the **Kramers–Wannier / Walsh Defect Operators**
     $$\Pi_{\mathrm{sym}} := 1 + \Sigma = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}, \qquad \Pi_{\mathrm{anti}} := 1 - \Sigma = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$$
     are mutually annihilating non-invertible defects ($\Pi_{\mathrm{sym}} \Pi_{\mathrm{anti}} = 0$, $\Pi_{\mathrm{sym}}^2 = 2\Pi_{\mathrm{sym}}$) that strictly commute with $H_{\mathrm{sym}}(h_0, h_1)$.

5. **Graeme Segal's Cobordism Gluing Factorization & Wick-Rotated Reflection Positivity (Extended Unitarity)**:
   * *Mathematical Essence*: Segal’s axioms encode **locality** via operator composition across codimension-1 cuts ($Z(M_1 \cup_\Sigma M_2) = Z_1 Z_2 = Z_1 P_+ Z_2 + Z_1 P_- Z_2$) and **unitarity** in the Wick-rotated regime via **Reflection Positivity**: gluing a bordism amplitude $Z \in M_2(\mathcal{A})$ to its orientation-reversed adjoint $\overline{Z} = Z^\dagger$ yields the self-adjoint double $Z Z^\dagger$, which factors across the extended Peirce cut $P_+ \oplus P_-$ into a sum of two individually self-adjoint positive-type channel amplitudes:
     $$Z Z^\dagger = (Z P_+ Z^\dagger) + (Z P_- Z^\dagger), \qquad (Z P_\pm Z^\dagger)^\dagger = Z P_\pm Z^\dagger.$$

---

### II. Causal Poset of Mathematical Archetypes

The logical dependencies among the five mathematical archetypes extracted from Dan Freed's exposition form the causal poset $(\mathcal{D}, \preceq)$:

```
        [D₁: Projective Operator Lifts W(a,b), Non-Abelian Anomaly 2-Cocycle C,
              Green–Schwarz Counterterm Cancellation & 't Hooft Mellin Matching]
                       /                                       \
                      ▼                                         ▼
[D₂: Z₂-Graded Supertrace Str(M) = Tr(Γ₁ M)     [D₄: Non-Invertible Defect Symmetry Algebras:
 & Atiyah–Singer Jumping Kernel Invariance]       Peirce (P₊, P₋) & Kramers–Wannier (1 ± Σ)]
                      │                                         │
                      ▼                                         ▼
[D₃: Quillen–Bismut–Freed Superconnection A+D,   [D₅: Segal Cobordism Cut-Gluing Resolution &
 Bianchi Identity & Chern–Simons Transgression]   Wick-Rotated Reflection Positivity Z P_± Z†]
                      \                                         /
                       ───────────────►────────┬────────◄───────
```

* $\mathcal{D}_1 \prec \mathcal{D}_2$: The Peirce split $P_+ \oplus P_-$ where the diagonal anomaly cocycle $\mathcal{C}(a_1, b_1, a_2, b_2)$ lives induces the $\mathbb{Z}_2$-graded supertrace $\operatorname{Str}(M) = M_{00} - M_{11}$, which is invariant under paired kernel/cokernel spectral jumps.
* $\mathcal{D}_1, \mathcal{D}_2 \prec \mathcal{D}_3$: Combining the odd off-diagonal generators $D = \begin{pmatrix} 0 & a \\ b & 0 \end{pmatrix}$ of $\mathcal{D}_1$ with an even diagonal connection $A = \begin{pmatrix} A_+ & 0 \\ 0 & A_- \end{pmatrix}$ builds the Quillen–Bismut–Freed superconnection $\mathbb{A} = A + D$, its supercurvature $\mathbb{A}^2$, and the noncommutative Chern–Simons–Weil transgression law.
* $\mathcal{D}_1 \prec \mathcal{D}_4$: The non-invertible idempotent projectors $P_\pm$ and their Walsh-dual defect projectors $1 \pm \Sigma$ generate the non-invertible categorical symmetry algebras commuting with chiral and translation-invariant Hamiltonians.
* $\mathcal{D}_2, \mathcal{D}_4 \prec \mathcal{D}_5$: Resolving operator composition across the orthogonal defect projectors $P_+, P_-$ in a $\star$-ring establishes Segal's cut-and-paste locality and channel-wise reflection positivity $Z Z^\dagger = Z P_+ Z^\dagger + Z P_- Z^\dagger$.

---

### III. Canonical Mathematical Code in Native Mathlib4 (Lean 4)

The following Lean 4 code is self-contained, operates strictly over noncommutative rings `[Ring A]` and $\star$-rings `[StarRing A]` in `Matrix (Fin 2) (Fin 2) A`, and proves every theorem with zero `sorry`s.

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace FreedGeometricIndexAndAnomalies

/-!
## Foundational Infrastructure: $2 \times 2$ Noncommutative Operator Matrices
-/

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section MatrixSimpLemmas

variable {A : Type*} [Ring A]

@[simp]
lemma mul_apply_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one_apply_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one_apply_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one_apply_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one_apply_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp]
lemma of_fin2_00 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl

@[simp]
lemma of_fin2_01 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl

@[simp]
lemma of_fin2_10 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl

@[simp]
lemma of_fin2_11 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp]
lemma conjTranspose_apply_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 0 = star (M 0 0) := rfl

@[simp]
lemma conjTranspose_apply_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 1 = star (M 1 0) := rfl

@[simp]
lemma conjTranspose_apply_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 0 = star (M 0 1) := rfl

@[simp]
lemma conjTranspose_apply_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 1 = star (M 1 1) := rfl

/-- Commutator $[X, Y] = X Y - Y X$ and anticommutator $\{X, Y\} = X Y + Y X$. -/
def comm {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X
def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

/-- Fundamental $Cl(1,1)$ and Peirce operators in $M_2(A)$. -/
def Γ₁ : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def Σ_op : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def P_plus : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]

def dewittEven (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * M * P_plus + P_minus * M * P_minus

def dewittOdd (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * M * P_minus + P_minus * M * P_plus

end MatrixSimpLemmas

/-!
## Archetype $\mathcal{D}_1$: Projective Operator Lifts, Non-Abelian Anomaly 2-Cocycles, Green–Schwarz Cancellation & 't Hooft Matching
-/

section ArchetypeD1_ProjectiveAnomalies

variable {A : Type*} [Ring A]

/-- Linear operator lift $W(a, b) = \begin{pmatrix} 1 & a \\ b & 1 \end{pmatrix}$ of a pair of
noncommutative odd parameters $(a, b) \in A \times A$. -/
def W_lift (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![1, a], ![b, 1]]

/-- The non-Abelian diagonal anomaly 2-cocycle
$\mathcal{C}(a_1, b_1, a_2, b_2) = \begin{pmatrix} a_1 b_2 & 0 \\ 0 & b_1 a_2 \end{pmatrix}$. -/
def anomalyCocycle (a₁ b₁ a₂ b₂ : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![a₁ * b₂, 0], ![0, b₁ * a₂]]

/-- **Projective Linearization Anomaly**:
Composing two linear operator lifts $W(a_1, b_1)$ and $W(a_2, b_2)$ deviates from the additive lift
$W(a_1 + a_2, b_1 + b_2)$ by the even diagonal anomaly cocycle $\mathcal{C}(a_1, b_1, a_2, b_2)$. -/
theorem projective_multiplication_anomaly (a₁ b₁ a₂ b₂ : A) :
    W_lift a₁ b₁ * W_lift a₂ b₂ =
      W_lift (a₁ + a₂) (b₁ + b₂) + anomalyCocycle a₁ b₁ a₂ b₂ := by
  apply ext_fin2 <;> simp [W_lift, anomalyCocycle]

/-- **Hochschild 2-Cocycle Condition for the Non-Abelian Anomaly**:
$\mathcal{C}(a_1, b_1, a_2, b_2) + \mathcal{C}(a_1 + a_2, b_1 + b_2, a_3, b_3) =
\mathcal{C}(a_1, b_1, a_2 + a_3, b_2 + b_3) + \mathcal{C}(a_2, b_2, a_3, b_3)$. -/
theorem anomaly_two_cocycle_condition (a₁ b₁ a₂ b₂ a₃ b₃ : A) :
    anomalyCocycle a₁ b₁ a₂ b₂ + anomalyCocycle (a₁ + a₂) (b₁ + b₂) a₃ b₃ =
      anomalyCocycle a₁ b₁ (a₂ + a₃) (b₂ + b₃) + anomalyCocycle a₂ b₂ a₃ b₃ := by
  apply ext_fin2 <;> simp [anomalyCocycle] <;> noncomm_ring

/-- Green–Schwarz counterterm-extended operator lift
$\widetilde{W}(a, b, c_+, c_-) = \begin{pmatrix} 1 + c_+ & a \\ b & 1 + c_- \end{pmatrix}$. -/
def greenSchwarzLift (a b c_plus c_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![1 + c_plus, a], ![b, 1 + c_minus]]

/-- **Green–Schwarz Anomaly Cancellation Mechanism**:
Coupling the product $W(a_1, b_1) W(a_2, b_2)$ to the compensating counterterm
$(c_+, c_-) = (-a_1 b_2, -b_1 a_2)$ cancels the anomaly cocycle and restores exact linearity. -/
theorem green_schwarz_anomaly_cancellation (a₁ b₁ a₂ b₂ : A) :
    W_lift a₁ b₁ * W_lift a₂ b₂ + (greenSchwarzLift 0 0 (-a₁ * b₂) (-b₁ * a₂) - 1) =
      W_lift (a₁ + a₂) (b₁ + b₂) := by
  apply ext_fin2 <;> simp [W_lift, greenSchwarzLift]

/-- Hyperbolic Mellin renormalization-group dilation $D(u) = \begin{pmatrix} u & 0 \\ 0 & u^{-1} \end{pmatrix}$. -/
def mellinDilation (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  ![![(u : A), 0], ![0, (↑u⁻¹ : A)]]

/-- Covariance of the operator lift $W(a, b)$ under Mellin renormalization scaling. -/
theorem W_lift_mellin_scaling (a b : A) (u : Aˣ) :
    mellinDilation u * W_lift a b * mellinDilation u⁻¹ =
      W_lift ((u : A) * a * (u : A)) ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h2 : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  apply ext_fin2 <;> simp [mellinDilation, W_lift, h1, h2] <;> noncomm_ring

/-- **'t Hooft Anomaly Matching across Mellin Renormalization Scales**:
The non-Abelian anomaly cocycle of the rescaled theory matches the conjugated anomaly cocycle of
the original theory for any invertible operator scale $u \in A^\times$. -/
theorem thooft_anomaly_matching (a₁ b₁ a₂ b₂ : A) (u : Aˣ) :
    anomalyCocycle
      ((u : A) * a₁ * (u : A)) ((↑u⁻¹ : A) * b₁ * (↑u⁻¹ : A))
      ((u : A) * a₂ * (u : A)) ((↑u⁻¹ : A) * b₂ * (↑u⁻¹ : A)) =
      mellinDilation u * anomalyCocycle a₁ b₁ a₂ b₂ * mellinDilation u⁻¹ := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h2 : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  apply ext_fin2
  · simp [anomalyCocycle, mellinDilation]
    calc (u : A) * a₁ * (u : A) * ((↑u⁻¹ : A) * b₂ * (↑u⁻¹ : A))
      _ = (u : A) * a₁ * ((u : A) * (↑u⁻¹ : A)) * b₂ * (↑u⁻¹ : A) := by noncomm_ring
      _ = (u : A) * (a₁ * b₂) * (↑u⁻¹ : A) := by rw [h1]; noncomm_ring
  · simp [anomalyCocycle, mellinDilation]
  · simp [anomalyCocycle, mellinDilation]
  · simp [anomalyCocycle, mellinDilation]
    calc (↑u⁻¹ : A) * b₁ * (↑u⁻¹ : A) * ((u : A) * a₂ * (u : A))
      _ = (↑u⁻¹ : A) * b₁ * ((↑u⁻¹ : A) * (u : A)) * a₂ * (u : A) := by noncomm_ring
      _ = (↑u⁻¹ : A) * (b₁ * a₂) * (u : A) := by rw [h2]; noncomm_ring

end ArchetypeD1_ProjectiveAnomalies

/-!
## Archetype $\mathcal{D}_2$: $\mathbb{Z}_2$-Graded Supertrace & Atiyah–Singer Jumping Kernel Invariance
-/

section ArchetypeD2_AtiyahSingerSupertrace

variable {A : Type*} [Ring A]

/-- Operator trace $\mathrm{Tr}(M) = M_{00} + M_{11} \in A$. -/
def opTrace (M : Matrix (Fin 2) (Fin 2) A) : A :=
  M 0 0 + M 1 1

/-- $\mathbb{Z}_2$-graded operator supertrace $\mathrm{Str}(M) = M_{00} - M_{11} \in A$. -/
def superTrace (M : Matrix (Fin 2) (Fin 2) A) : A :=
  M 0 0 - M 1 1

/-- The supertrace is identically the operator trace weighted by the chirality grading $\Gamma_1$. -/
theorem superTrace_eq_opTrace_mul_Γ₁ (M : Matrix (Fin 2) (Fin 2) A) :
    superTrace M = opTrace (Γ₁ * M) := by
  dsimp [superTrace, opTrace, Γ₁]
  simp [sub_eq_add_neg]

/-- Every odd operator in $M_2(A)$ has vanishing supertrace. -/
theorem superTrace_dewittOdd_zero (M : Matrix (Fin 2) (Fin 2) A) :
    superTrace (dewittOdd M) = 0 := by
  dsimp [superTrace, dewittOdd, P_plus, P_minus]
  simp

/-- A family of chiral spectral operators $K(\Pi_+, \Pi_-, \delta) = \begin{pmatrix} \Pi_+ + \delta & 0 \\ 0 & \Pi_- + \delta \end{pmatrix}$
whose kernel $\Pi_+$ and cokernel $\Pi_-$ jump simultaneously by an operator mode $\delta \in A$. -/
def jumpingKernelFamily (Π_plus Π_minus δ : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![Π_plus + δ, 0], ![0, Π_minus + δ]]

/-- While the ungraded trace jumps by $2\delta$ as $\delta$ varies... -/
theorem opTrace_jumpingKernelFamily (Π_plus Π_minus δ : A) :
    opTrace (jumpingKernelFamily Π_plus Π_minus δ) =
      opTrace (jumpingKernelFamily Π_plus Π_minus 0) + (δ + δ) := by
  dsimp [opTrace, jumpingKernelFamily]
  noncomm_ring

/-- **Atiyah–Singer Supertrace Index Invariance**:
The $\mathbb{Z}_2$-graded supertrace $\mathrm{Str}(K(\Pi_+, \Pi_-, \delta))$ is strictly invariant
under arbitrary spectral jumps $\delta \in A$ of the kernel and cokernel. -/
theorem superTrace_jumpingKernelFamily_invariant (Π_plus Π_minus δ : A) :
    superTrace (jumpingKernelFamily Π_plus Π_minus δ) =
      superTrace (jumpingKernelFamily Π_plus Π_minus 0) := by
  dsimp [superTrace, jumpingKernelFamily]
  noncomm_ring

end ArchetypeD2_AtiyahSingerSupertrace

/-!
## Archetype $\mathcal{D}_3$: Quillen–Bismut–Freed Superconnections & Noncommutative Chern–Simons–Weil Transgression
-/

section ArchetypeD3_QuillenSuperconnectionAndChernSimons

variable {A : Type*} [Ring A]

/-- Even block-diagonal gauge connection $A_{\mathrm{even}}(A_+, A_-) = \begin{pmatrix} A_+ & 0 \\ 0 & A_- \end{pmatrix}$. -/
def evenConn (A_plus A_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![A_plus, 0], ![0, A_minus]]

/-- Odd off-diagonal Dirac operator $D_{\mathrm{odd}}(L_+, L_-) = \begin{pmatrix} 0 & L_- \\ L_+ & 0 \end{pmatrix}$. -/
def oddDirac (L_plus L_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![0, L_minus], ![L_plus, 0]]

/-- **Quillen–Bismut–Freed Superconnection**
$\mathbb{A}(A_+, A_-, L_+, L_-) = A_{\mathrm{even}} + D_{\mathrm{odd}} = \begin{pmatrix} A_+ & L_- \\ L_+ & A_- \end{pmatrix}$. -/
def quillenSuperconn (A_plus A_minus L_plus L_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  evenConn A_plus A_minus + oddDirac L_plus L_minus

/-- **Quillen Supercurvature Even Sector**:
The even DeWitt part of $\mathbb{A}^2$ combines the gauge squares $A_\pm^2$ with the Dirac
Laplacians $L_\mp L_\pm$. -/
theorem quillen_supercurvature_even (A_plus A_minus L_plus L_minus : A) :
    dewittEven (quillenSuperconn A_plus A_minus L_plus L_minus *
                quillenSuperconn A_plus A_minus L_plus L_minus) =
      ![![A_plus * A_plus + L_minus * L_plus, 0],
        ![0, A_minus * A_minus + L_plus * L_minus]] := by
  apply ext_fin2 <;>
    simp [dewittEven, quillenSuperconn, evenConn, oddDirac, P_plus, P_minus] <;>
    noncomm_ring

/-- **Quillen Supercurvature Odd Sector**:
The odd DeWitt part of $\mathbb{A}^2$ is the anticommutator $\{A_{\mathrm{even}}, D_{\mathrm{odd}}\}$. -/
theorem quillen_supercurvature_odd (A_plus A_minus L_plus L_minus : A) :
    dewittOdd (quillenSuperconn A_plus A_minus L_plus L_minus *
               quillenSuperconn A_plus A_minus L_plus L_minus) =
      anticomm (evenConn A_plus A_minus) (oddDirac L_plus L_minus) := by
  apply ext_fin2 <;>
    simp [dewittOdd, anticomm, quillenSuperconn, evenConn, oddDirac, P_plus, P_minus] <;>
    noncomm_ring

/-- **Algebraic Bianchi Identity for Quillen Superconnections**: $[\mathbb{A}, \mathbb{A}^2] = 0$. -/
theorem quillen_superconnection_bianchi (𝕏 : Matrix (Fin 2) (Fin 2) A) :
    comm 𝕏 (𝕏 * 𝕏) = 0 := by
  dsimp [comm]
  noncomm_ring

/-- Bianchi covariant derivative $\nabla_D(\Phi) = [D, \Phi]$ in any noncommutative ring $R$. -/
def bianchiDeriv {R : Type*} [Ring R] (D Φ : R) : R := comm D Φ

/-- Total supercurvature $F(\Phi, D) = \Phi + D^2$ of an even background $\Phi$ and odd connection $D$. -/
def superCurvature {R : Type*} [Ring R] (Φ D : R) : R := Φ + D * D

/-- Noncommutative Chern–Simons cubic element $\mathcal{CS}(\Phi, D) = \Phi D + D \Phi + D^3$. -/
def chernSimonsElem {R : Type*} [Ring R] (Φ D : R) : R :=
  Φ * D + D * Φ + D * D * D

/-- **The Noncommutative Chern–Simons–Weil Transgression Theorem**:
In any noncommutative ring $R$ (such as $M_2(A)$), the anticommutator $\{D, \mathcal{CS}(\Phi, D)\}$
transgresses the quadratic Chern–Weil curvature $2 F(\Phi, D)^2$ modulo the Bianchi commutator
$[\nabla_D(\Phi), D]$ and $2\Phi^2$. -/
theorem chern_simons_weil_transgression {R : Type*} [Ring R] (Φ D : R) :
    anticomm D (chernSimonsElem Φ D) - comm (bianchiDeriv D Φ) D + 2 * (Φ * Φ) =
      2 * (superCurvature Φ D * superCurvature Φ D) := by
  dsimp [anticomm, comm, bianchiDeriv, chernSimonsElem, superCurvature]
  noncomm_ring

end ArchetypeD3_QuillenSuperconnectionAndChernSimons

/-!
## Archetype $\mathcal{D}_4$: Non-Invertible Categorical Symmetry Algebras & Kramers–Wannier / Peirce Defects
-/

section ArchetypeD4_NonInvertibleSymmetries

variable {A : Type*} [Ring A]

/-- Chiral Hamiltonian $H_{\mathrm{chiral}}(h_+, h_-) = \begin{pmatrix} h_+ & 0 \\ 0 & h_- \end{pmatrix}$. -/
def chiralHamiltonian (h_plus h_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![h_plus, 0], ![0, h_minus]]

/-- The non-invertible Peirce defect projectors $P_+$ and $P_-$ ($P_+ P_- = 0$) commute with any
chiral Hamiltonian $H_{\mathrm{chiral}}(h_+, h_-)$. -/
theorem P_plus_comm_chiralHamiltonian (h_plus h_minus : A) :
    comm (P_plus : Matrix (Fin 2) (Fin 2) A) (chiralHamiltonian h_plus h_minus) = 0 := by
  apply ext_fin2 <;> simp [comm, P_plus, chiralHamiltonian]

theorem P_minus_comm_chiralHamiltonian (h_plus h_minus : A) :
    comm (P_minus : Matrix (Fin 2) (Fin 2) A) (chiralHamiltonian h_plus h_minus) = 0 := by
  apply ext_fin2 <;> simp [comm, P_minus, chiralHamiltonian]

/-- Translation-symmetric Hamiltonian $H_{\mathrm{sym}}(h_0, h_1) = \begin{pmatrix} h_0 & h_1 \\ h_1 & h_0 \end{pmatrix}$. -/
def symHamiltonian (h₀ h₁ : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![h₀, h₁], ![h₁, h₀]]

/-- Symmetric Kramers–Wannier / Walsh defect projector $\Pi_{\mathrm{sym}} = 1 + \Sigma = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$. -/
def defectSym : Matrix (Fin 2) (Fin 2) A := ![![1, 1], ![1, 1]]

/-- Antisymmetric Kramers–Wannier / Walsh defect projector $\Pi_{\mathrm{anti}} = 1 - \Sigma = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$. -/
def defectAnti : Matrix (Fin 2) (Fin 2) A := ![![1, -1], ![-1, 1]]

/-- Strict non-invertibility (mutual annihilation) of the Kramers–Wannier defect operators:
$\Pi_{\mathrm{sym}} \Pi_{\mathrm{anti}} = 0$ and $\Pi_{\mathrm{anti}} \Pi_{\mathrm{sym}} = 0$. -/
theorem defectSym_mul_defectAnti_zero :
    (defectSym : Matrix (Fin 2) (Fin 2) A) * defectAnti = 0 := by
  apply ext_fin2 <;> simp [defectSym, defectAnti]

theorem defectAnti_mul_defectSym_zero :
    (defectAnti : Matrix (Fin 2) (Fin 2) A) * defectSym = 0 := by
  apply ext_fin2 <;> simp [defectSym, defectAnti]

/-- Scaled idempotence (fusion rules) of the Kramers–Wannier defects: $\Pi_{\mathrm{sym}}^2 = 2\Pi_{\mathrm{sym}}$. -/
theorem defectSym_fusion :
    (defectSym : Matrix (Fin 2) (Fin 2) A) * defectSym = defectSym + defectSym := by
  apply ext_fin2 <;> simp [defectSym]

theorem defectAnti_fusion :
    (defectAnti : Matrix (Fin 2) (Fin 2) A) * defectAnti = defectAnti + defectAnti := by
  apply ext_fin2 <;> simp [defectAnti] <;> noncomm_ring

/-- **Non-Invertible Defect Symmetry Commutation**:
Both non-invertible Kramers–Wannier defect operators $\Pi_{\mathrm{sym}}$ and $\Pi_{\mathrm{anti}}$
strictly commute with $H_{\mathrm{sym}}(h_0, h_1)$ for arbitrary non-commuting $h_0, h_1 \in A$. -/
theorem defectSym_comm_symHamiltonian (h₀ h₁ : A) :
    comm (defectSym : Matrix (Fin 2) (Fin 2) A) (symHamiltonian h₀ h₁) = 0 := by
  apply ext_fin2 <;> simp [comm, defectSym, symHamiltonian] <;> noncomm_ring

theorem defectAnti_comm_symHamiltonian (h₀ h₁ : A) :
    comm (defectAnti : Matrix (Fin 2) (Fin 2) A) (symHamiltonian h₀ h₁) = 0 := by
  apply ext_fin2 <;> simp [comm, defectAnti, symHamiltonian] <;> noncomm_ring

end ArchetypeD4_NonInvertibleSymmetries

/-!
## Archetype $\mathcal{D}_5$: Graeme Segal's Cobordism Gluing Factorization & Wick-Rotated Reflection Positivity
-/

section ArchetypeD5_SegalGluingAndReflectionPositivity

variable {A : Type*} [Ring A] [StarRing A]

/-- **Segal Cut-and-Paste Locality Resolution**:
The composition $Z_1 Z_2$ of two bordism operators factors as the sum over the orthogonal
Peirce boundary channels $P_+$ and $P_-$. -/
theorem segal_gluing_peirce_resolution (Z₁ Z₂ : Matrix (Fin 2) (Fin 2) A) :
    Z₁ * P_plus * Z₂ + Z₁ * P_minus * Z₂ = Z₁ * Z₂ := by
  apply ext_fin2 <;> simp [P_plus, P_minus]

/-- Gluing a bordism operator $Z$ to its orientation-reversed adjoint $Z^\dagger$ across the
positive or negative Peirce boundary channel. -/
def reflectionChannelPlus (Z : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Z * P_plus * Zᴴ

def reflectionChannelMinus (Z : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Z * P_minus * Zᴴ

theorem P_plus_conjTranspose : (P_plus : Matrix (Fin 2) (Fin 2) A)ᴴ = P_plus := by
  apply ext_fin2 <;> simp [P_plus]

theorem P_minus_conjTranspose : (P_minus : Matrix (Fin 2) (Fin 2) A)ᴴ = P_minus := by
  apply ext_fin2 <;> simp [P_minus]

/-- **Extended Reflection Positivity (Channel-Wise Self-Adjointness)**:
Each cut-glued Peirce boundary channel $Z P_\pm Z^\dagger$ is individually self-adjoint, and their
sum reconstructs the reflection-positive double $Z Z^\dagger$. -/
theorem reflectionChannelPlus_isSelfAdjoint (Z : Matrix (Fin 2) (Fin 2) A) :
    (reflectionChannelPlus Z)ᴴ = reflectionChannelPlus Z := by
  dsimp [reflectionChannelPlus]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    P_plus_conjTranspose, mul_assoc]

theorem reflectionChannelMinus_isSelfAdjoint (Z : Matrix (Fin 2) (Fin 2) A) :
    (reflectionChannelMinus Z)ᴴ = reflectionChannelMinus Z := by
  dsimp [reflectionChannelMinus]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    P_minus_conjTranspose, mul_assoc]

theorem reflection_positivity_double_decomposition (Z : Matrix (Fin 2) (Fin 2) A) :
    reflectionChannelPlus Z + reflectionChannelMinus Z = Z * Zᴴ := by
  exact segal_gluing_peirce_resolution Z Zᴴ

end ArchetypeD5_SegalGluingAndReflectionPositivity

end FreedGeometricIndexAndAnomalies
```
