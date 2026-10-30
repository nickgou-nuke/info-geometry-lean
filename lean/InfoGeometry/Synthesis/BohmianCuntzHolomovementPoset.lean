/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Basic
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.QuantumContext.AttentionColimitStateCoherence

/-!
# Bohm–Hiley Implicate/Explicate Order, Cuntz $\mathcal{O}_2$ Trace Obstruction, and Holomovement Poset

This module provides a pure Mathlib 4 formalization of David Bohm and Basil Hiley's
**Implicate (enfolded) Order**, **Explicate (unfolded) Order**, and **Holomovement**
process philosophy through the operator algebra of the Cuntz algebra $\mathcal{O}_2$
and the inductive colimit UHF matrix tower $\mathcal{A}_\infty = \varinjlim_k M_{2^k}(R)$:

1. **Archetype I (Cuntz $\mathcal{O}_2$ Finite-Dimensional Trace Obstruction $2N = N \implies N = 0$)**:
   Proves (`cuntz_finite_matrix_trace_obstruction`, `no_cuntz_isometries_on_nonempty_finite_matrix`)
   that for any finite index type `m` (`[Fintype m] [DecidableEq m]`), no matrices
   $S_1, S_1^*, S_2, S_2^* \in M_m(\mathbb{R})$ can simultaneously satisfy the Cuntz
   isometry relations $S_1^* S_1 = I$, $S_2^* S_2 = I$ and the completeness relation
   $S_1 S_1^* + S_2 S_2^* = I$ unless $\operatorname{card}(m) = 0$. Thus the exact
   relations have no realization on a nonempty finite matrix carrier. This trace
   obstruction does not construct a representation on the repository's UHF
   inductive colimit or imply that this particular colimit carries an exact
   $\mathcal{O}_2$ action.

2. **Archetype II (Explicate-to-Implicate Enfoldment $\mathcal{E}(X) = X \oplus X$ & Cuntz Projectors $P_1, P_2$)**:
   Defines the block-diagonal enfoldment map `enfold (X) = fromBlocks X 0 0 X`
   and the complementary Cuntz sub-channel projectors `cuntzProj1 = fromBlocks 1 0 0 0`
   ($P_1 = S_1 S_1^*$) and `cuntzProj2 = fromBlocks 0 0 0 1` ($P_2 = S_2 S_2^*$).
   Proves that `enfold` is a unital ring homomorphism (`enfold_one`, `enfold_add`,
   `enfold_mul`), that $P_1, P_2$ form an orthogonal resolution of the identity
   (`cuntz_projector_algebra`), and that every enfolded observable commutes with both
   Cuntz projectors (`enfold_commutes_with_cuntzProj`).

3. **Archetype III (Implicate-to-Explicate Unfoldment $U_1, U_2$, Conditional Expectation $E_{\mathrm{cond}}$, & Holographic Retraction)**:
   Defines the left/right Cuntz sub-channel compressions `unfold1 := Matrix.toBlocks₁₁`
   ($S_1^* Y S_1$), `unfold2 := Matrix.toBlocks₂₂` ($S_2^* Y S_2$), and the symmetric
   conditional expectation `unfoldConditionalExp Y := ⅟2 • (unfold1 Y + unfold2 Y)`.
   Proves the **Holographic Retraction Theorem** (`bohmian_holographic_retraction`,
   `bohmian_conditional_exp_retraction`, `enfold_injective`): every Cuntz sub-channel
   unfolds the complete local algebra without loss of information ($U_1(\mathcal{E}(X)) = X$
   and $U_2(\mathcal{E}(X)) = X$).

4. **Archetype IV (Holomovement Pinching Endomorphism $\Phi(Y) = P_1 Y P_1 + P_2 Y P_2$ & Stationary Attractors)**:
   Defines the holomovement pinching channel `holomovement Y := P₁ Y P₁ + P₂ Y P₂`
   (one step of unfoldment followed by re-enfoldment into the two Cuntz sectors).
   Proves its block decomposition (`holomovement_eq_fromBlocks_unfold`), idempotence
   (`holomovement_idempotent` : $\Phi(\Phi(Y)) = \Phi(Y)$), exact stationarity on the
   enfolded algebra (`enfold_holomovement_invariant` : $\Phi(\mathcal{E}(X)) = \mathcal{E}(X)$),
   and explicate compatibility (`unfold_holomovement_eq_unfold` : $U_i(\Phi(Y)) = U_i(Y)$).

5. **Archetype V (Trace Doubling, Cyclic State Invariance $\operatorname{Tr}(\mathcal{E}(\rho)\Phi(Y)) = \operatorname{Tr}(\mathcal{E}(\rho)Y)$, & UHF Direct-Limit Bridge)**:
   Proves `enfold_trace_scaling` ($\operatorname{Tr}(\mathcal{E}(X)) = 2 \operatorname{Tr}(X)$),
   `holomovement_trace_eq` ($\operatorname{Tr}(\Phi(Y)) = \operatorname{Tr}(Y)$),
   `holomovement_enfold_trace_sum` ($\operatorname{Tr}(\mathcal{E}(\rho)\Phi(Y)) =
   \operatorname{Tr}(\rho U_1(Y)) + \operatorname{Tr}(\rho U_2(Y))$), and the genuine
   cyclic state invariance `holomovement_enfold_trace_invariant`
   ($\operatorname{Tr}(\mathcal{E}(\rho)\Phi(Y)) = \operatorname{Tr}(\mathcal{E}(\rho)Y)$),
   together with the direct bridge to the repository's owned algebraic $*$-colimit
   tower (`uhf_tower_enfold_and_state_coherence_bridge`).

6. **Archetype VI (Causal Poset of the Bohmian–Cuntz Holomovement Architecture)**:
   Formalizes the 6-stage causal poset `BohmCuntzStage` (`PartialOrder BohmCuntzStage`)
   with diamond branching through the two incomparable Cuntz sub-channel unfoldments
   (`unfoldChannel1` and `unfoldChannel2`), strict monotone height
   (`bohmCuntzHeight_strictMono`), and non-totality (`not_total_bohmCuntzStage_le`).
-/

namespace InfoGeometry.Synthesis.BohmianCuntzHolomovementPoset

open Matrix
open scoped BigOperators

variable {m : Type*} [Fintype m] [DecidableEq m]
variable {R : Type*} [CommRing R]

/-!
## Archetype I: Cuntz $\mathcal{O}_2$ Finite-Dimensional Trace Obstruction ($2N = N \implies N = 0$)
-/

/-- **Cuntz $\mathcal{O}_2$ Finite-Dimensional Trace Obstruction (`2 * card m = card m`)**:
If four finite matrices $S_1, S_1^*, S_2, S_2^* \in M_m(\mathbb{R})$ satisfy the
two Cuntz isometry relations $S_1^* S_1 = I$ and $S_2^* S_2 = I$ together with the
Cuntz completeness relation $S_1 S_1^* + S_2 S_2^* = I$, then cyclic invariance of
the matrix trace (`Matrix.trace_mul_comm`) forces
$$2 \cdot \operatorname{card}(m) = \operatorname{card}(m)$$
in $\mathbb{R}$, and therefore $\operatorname{card}(m) = 0$. -/
theorem cuntz_finite_matrix_trace_obstruction
    (S₁ S₁_star S₂ S₂_star : Matrix m m ℝ)
    (h1 : S₁_star * S₁ = 1)
    (h2 : S₂_star * S₂ = 1)
    (h_comp : S₁ * S₁_star + S₂ * S₂_star = 1) :
    2 * (Fintype.card m : ℝ) = (Fintype.card m : ℝ) ∧ Fintype.card m = 0 := by
  have htr1 : Matrix.trace (S₁ * S₁_star) = (Fintype.card m : ℝ) := by
    rw [Matrix.trace_mul_comm S₁ S₁_star, h1, Matrix.trace_one]
  have htr2 : Matrix.trace (S₂ * S₂_star) = (Fintype.card m : ℝ) := by
    rw [Matrix.trace_mul_comm S₂ S₂_star, h2, Matrix.trace_one]
  have htr_comp :
      Matrix.trace (S₁ * S₁_star + S₂ * S₂_star) = (Fintype.card m : ℝ) := by
    rw [h_comp, Matrix.trace_one]
  rw [Matrix.trace_add, htr1, htr2] at htr_comp
  have h_two : 2 * (Fintype.card m : ℝ) = (Fintype.card m : ℝ) := by
    linarith [htr_comp]
  have h_zero_real : (Fintype.card m : ℝ) = 0 := by
    linarith [h_two]
  exact ⟨h_two, Nat.cast_eq_zero.mp h_zero_real⟩

/-- **No Finite-Dimensional Real Matrix Realization of $\mathcal{O}_2$ on a Nonempty Carrier**:
On any nonempty finite index type `m` (`[Nonempty m]`), no matrices
$S_1, S_1^*, S_2, S_2^* \in M_m(\mathbb{R})$ can satisfy both $S_i^* S_i = I$ and
$S_1 S_1^* + S_2 S_2^* = I$. Thus no such matrices exist on a nonempty finite
carrier. The theorem does not identify an infinite-dimensional representation
with the repository's UHF inductive colimit. -/
theorem no_cuntz_isometries_on_nonempty_finite_matrix
    [h_ne : Nonempty m]
    (S₁ S₁_star S₂ S₂_star : Matrix m m ℝ)
    (h1 : S₁_star * S₁ = 1)
    (h2 : S₂_star * S₂ = 1)
    (h_comp : S₁ * S₁_star + S₂ * S₂_star = 1) :
    False := by
  have h_card_zero : Fintype.card m = 0 :=
    (cuntz_finite_matrix_trace_obstruction S₁ S₁_star S₂ S₂_star h1 h2 h_comp).2
  have h_card_pos : 0 < Fintype.card m := Fintype.card_pos_iff.mpr h_ne
  exact Nat.ne_of_gt h_card_pos h_card_zero

/-!
## Archetype II: Explicate-to-Implicate Enfoldment $\mathcal{E}(X) = X \oplus X$ & Cuntz Projectors $P_1, P_2$
-/

/-- **The Enfoldment Operator ($\mathcal{E} : \mathcal{A}_k \hookrightarrow \mathcal{A}_{k+1}$)**:
Embeds a local explicate observable $X \in M_m(R)$ into the doubled implicate stage
$M_{m \oplus m}(R)$ by duplicating it across both Cuntz sub-channels:
$$\mathcal{E}(X) = S_1 X S_1^* + S_2 X S_2^* = \begin{pmatrix} X & 0 \\ 0 & X \end{pmatrix}.$$ -/
def enfold (X : Matrix m m R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks X 0 0 X

/-- **Left Cuntz Sub-Channel Projector ($P_1 = S_1 S_1^*$)**:
Projects the doubled stage $M_{m \oplus m}(R)$ onto the first Cuntz isometry sector. -/
def cuntzProj1 : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 1 0 0 0

/-- **Right Cuntz Sub-Channel Projector ($P_2 = S_2 S_2^*$)**:
Projects the doubled stage $M_{m \oplus m}(R)$ onto the second Cuntz isometry sector. -/
def cuntzProj2 : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 0 0 1

omit [Fintype m] in
/-- Enfoldment preserves the identity matrix: $\mathcal{E}(I) = I$. -/
theorem enfold_one : enfold (1 : Matrix m m R) = 1 := by
  unfold enfold
  exact Matrix.fromBlocks_one

omit [Fintype m] [DecidableEq m] in
/-- Enfoldment is additive: $\mathcal{E}(X + Y) = \mathcal{E}(X) + \mathcal{E}(Y)$. -/
theorem enfold_add (X Y : Matrix m m R) :
    enfold (X + Y) = enfold X + enfold Y := by
  unfold enfold
  rw [Matrix.fromBlocks_add]
  simp only [add_zero]

omit [DecidableEq m] in
/-- Enfoldment is multiplicative: $\mathcal{E}(X Y) = \mathcal{E}(X)\mathcal{E}(Y)$. -/
theorem enfold_mul (X Y : Matrix m m R) :
    enfold (X * Y) = enfold X * enfold Y := by
  unfold enfold
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

omit [Fintype m] [DecidableEq m] in
/-- Enfoldment preserves matrix transpose: $(\mathcal{E}(X))^T = \mathcal{E}(X^T)$. -/
theorem enfold_transpose (X : Matrix m m R) :
    (enfold X)ᵀ = enfold Xᵀ := by
  unfold enfold
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero]

/-- **Cuntz Sub-Channel Projector Resolution of the Identity**:
$P_1 = S_1 S_1^*$ and $P_2 = S_2 S_2^*$ are mutually orthogonal idempotents whose sum
is the identity on $M_{m \oplus m}(R)$:
$$P_1 + P_2 = I, \quad P_1^2 = P_1, \quad P_2^2 = P_2, \quad P_1 P_2 = 0, \quad P_2 P_1 = 0.$$ -/
theorem cuntz_projector_algebra :
    (cuntzProj1 : Matrix (m ⊕ m) (m ⊕ m) R) + cuntzProj2 = 1 ∧
    (cuntzProj1 : Matrix (m ⊕ m) (m ⊕ m) R) * cuntzProj1 = cuntzProj1 ∧
    (cuntzProj2 : Matrix (m ⊕ m) (m ⊕ m) R) * cuntzProj2 = cuntzProj2 ∧
    (cuntzProj1 : Matrix (m ⊕ m) (m ⊕ m) R) * cuntzProj2 = 0 ∧
    (cuntzProj2 : Matrix (m ⊕ m) (m ⊕ m) R) * cuntzProj1 = 0 := by
  unfold cuntzProj1 cuntzProj2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.fromBlocks_add, add_zero, zero_add, Matrix.fromBlocks_one]
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, zero_add]
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.fromBlocks_zero]
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.fromBlocks_zero]

/-- Every enfolded observable $\mathcal{E}(X)$ commutes with both Cuntz sub-channel
projectors $P_1$ and $P_2$. -/
theorem enfold_commutes_with_cuntzProj (X : Matrix m m R) :
    enfold X * cuntzProj1 = cuntzProj1 * enfold X ∧
    enfold X * cuntzProj2 = cuntzProj2 * enfold X := by
  unfold enfold cuntzProj1 cuntzProj2
  constructor
  · simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-!
## Archetype III: Implicate-to-Explicate Unfoldment $U_1, U_2$, Conditional Expectation $E_{\mathrm{cond}}$, & Holographic Retraction
-/

/-- **First-Channel Unfoldment ($U_1(Y) = S_1^* Y S_1$)**:
Extracts the top-left explicate local slice from an implicate operator $Y \in M_{m \oplus m}(R)$. -/
def unfold1 (Y : Matrix (m ⊕ m) (m ⊕ m) R) : Matrix m m R :=
  Matrix.toBlocks₁₁ Y

/-- **Second-Channel Unfoldment ($U_2(Y) = S_2^* Y S_2$)**:
Extracts the bottom-right explicate local slice from an implicate operator $Y \in M_{m \oplus m}(R)$. -/
def unfold2 (Y : Matrix (m ⊕ m) (m ⊕ m) R) : Matrix m m R :=
  Matrix.toBlocks₂₂ Y

/-- **Symmetric Conditional Expectation ($E_{\mathrm{cond}}(Y) = \frac{1}{2}(S_1^* Y S_1 + S_2^* Y S_2)$)**:
Averages the two Cuntz sub-channel unfoldments back onto the local stage $M_m(R)$. -/
def unfoldConditionalExp [Invertible (2 : R)]
    (Y : Matrix (m ⊕ m) (m ⊕ m) R) : Matrix m m R :=
  ⅟(2 : R) • (unfold1 Y + unfold2 Y)

omit [Fintype m] [DecidableEq m] in
/-- **Bohmian Holographic Retraction Theorem**:
Both Cuntz sub-channel unfoldments $U_1$ and $U_2$ are exact left-inverses to the
enfoldment embedding $\mathcal{E}$:
$$U_1(\mathcal{E}(X)) = X \quad \text{and} \quad U_2(\mathcal{E}(X)) = X.$$
Every Cuntz sector of the implicate stage contains the complete local observable $X$. -/
theorem bohmian_holographic_retraction (X : Matrix m m R) :
    unfold1 (enfold X) = X ∧ unfold2 (enfold X) = X := by
  unfold unfold1 unfold2 enfold
  exact ⟨Matrix.toBlocks_fromBlocks₁₁ X 0 0 X, Matrix.toBlocks_fromBlocks₂₂ X 0 0 X⟩

omit [Fintype m] [DecidableEq m] in
/-- **Conditional Expectation Retraction Theorem**:
The symmetric conditional expectation $E_{\mathrm{cond}}(Y) = \frac{1}{2}(U_1(Y) + U_2(Y))$
is a unital retraction of the enfoldment map: $E_{\mathrm{cond}}(\mathcal{E}(X)) = X$. -/
theorem bohmian_conditional_exp_retraction [Invertible (2 : R)] (X : Matrix m m R) :
    unfoldConditionalExp (enfold X) = X := by
  unfold unfoldConditionalExp
  rcases bohmian_holographic_retraction X with ⟨h1, h2⟩
  rw [h1, h2, ← two_smul R X, smul_smul, invOf_mul_self, one_smul]

omit [Fintype m] [DecidableEq m] in
/-- Enfoldment is strictly injective: $\mathcal{E}(X) = \mathcal{E}(Y) \implies X = Y$. -/
theorem enfold_injective {X Y : Matrix m m R} (h : enfold X = enfold Y) :
    X = Y := by
  have h1 : unfold1 (enfold X) = unfold1 (enfold Y) := congrArg unfold1 h
  rwa [(bohmian_holographic_retraction X).1, (bohmian_holographic_retraction Y).1] at h1

/-!
## Archetype IV: Holomovement Pinching Endomorphism $\Phi(Y) = P_1 Y P_1 + P_2 Y P_2$ & Stationary Attractors
-/

/-- **The Holomovement Pinching Endomorphism ($\Phi(Y) = P_1 Y P_1 + P_2 Y P_2$)**:
One complete cycle of unfolding an implicate operator $Y \in M_{m \oplus m}(R)$ into its
two explicate Cuntz sectors $U_1(Y), U_2(Y)$ and re-enfolding them into the block-diagonal
subalgebra $M_m(R) \oplus M_m(R)$:
$$\Phi(Y) = S_1(S_1^* Y S_1)S_1^* + S_2(S_2^* Y S_2)S_2^* = P_1 Y P_1 + P_2 Y P_2.$$ -/
def holomovement (Y : Matrix (m ⊕ m) (m ⊕ m) R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  cuntzProj1 * Y * cuntzProj1 + cuntzProj2 * Y * cuntzProj2

/-- **Block Decomposition of the Holomovement**:
$\Phi(Y)$ annihilates the off-diagonal cross-channel coherence blocks $Y_{12}, Y_{21}$
and retains the unfolded diagonal blocks $\operatorname{diag}(U_1(Y), U_2(Y))$. -/
theorem holomovement_eq_fromBlocks_unfold (Y : Matrix (m ⊕ m) (m ⊕ m) R) :
    holomovement Y = Matrix.fromBlocks (unfold1 Y) 0 0 (unfold2 Y) := by
  unfold holomovement cuntzProj1 cuntzProj2 unfold1 unfold2
  conv_lhs =>
    rw [← Matrix.fromBlocks_toBlocks Y]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.fromBlocks_add, zero_add]

/-- **Idempotence of the Holomovement**:
Applying the holomovement pinching map twice is identical to applying it once:
$$\Phi(\Phi(Y)) = \Phi(Y).$$ -/
theorem holomovement_idempotent (Y : Matrix (m ⊕ m) (m ⊕ m) R) :
    holomovement (holomovement Y) = holomovement Y := by
  rw [holomovement_eq_fromBlocks_unfold (holomovement Y),
    holomovement_eq_fromBlocks_unfold Y]
  unfold unfold1 unfold2
  rw [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂]

/-- **Stationarity of Enfolded Observables Under the Holomovement**:
Every enfolded observable $\mathcal{E}(X)$ is a fixed point of the holomovement:
$$\Phi(\mathcal{E}(X)) = \mathcal{E}(X).$$ -/
theorem enfold_holomovement_invariant (X : Matrix m m R) :
    holomovement (enfold X) = enfold X := by
  rw [holomovement_eq_fromBlocks_unfold]
  rcases bohmian_holographic_retraction X with ⟨h1, h2⟩
  rw [h1, h2]
  rfl

/-- **Explicate Invariance Under the Holomovement**:
Unfolding after the holomovement returns the exact same explicate observables:
$$U_1(\Phi(Y)) = U_1(Y) \quad \text{and} \quad U_2(\Phi(Y)) = U_2(Y).$$ -/
theorem unfold_holomovement_eq_unfold (Y : Matrix (m ⊕ m) (m ⊕ m) R) :
    unfold1 (holomovement Y) = unfold1 Y ∧ unfold2 (holomovement Y) = unfold2 Y := by
  rw [holomovement_eq_fromBlocks_unfold]
  unfold unfold1 unfold2
  exact ⟨Matrix.toBlocks_fromBlocks₁₁ _ 0 0 _, Matrix.toBlocks_fromBlocks₂₂ _ 0 0 _⟩

/-!
## Archetype V: Trace Doubling, Cyclic State Invariance, & UHF Direct-Limit Tower Bridge
-/

omit [DecidableEq m] in
/-- **Trace of a $2 \times 2$ Block Matrix**:
For any block matrix $\operatorname{fromBlocks}(A, B, C, D) \in M_{m \oplus m}(R)$, its trace
is the sum of the traces of its two diagonal blocks $A$ and $D$. -/
theorem trace_fromBlocks_eq_add (A B C D : Matrix m m R) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

omit [DecidableEq m] in
/-- **Trace Doubling Under Enfoldment**:
Enfolding a local observable $X \in M_m(R)$ into $M_{m \oplus m}(R)$ doubles its unnormalized
matrix trace:
$$\operatorname{Tr}(\mathcal{E}(X)) = 2 \operatorname{Tr}(X).$$
Consequently, the normalized tracial state $\tau_k(X) = 2^{-k}\operatorname{Tr}(X)$ is strictly
scale-invariant across the inductive limit: $\tau_{k+1}(\mathcal{E}(X)) = \tau_k(X)$. -/
theorem enfold_trace_scaling (X : Matrix m m R) :
    Matrix.trace (enfold X) = 2 * Matrix.trace X := by
  unfold enfold
  rw [trace_fromBlocks_eq_add, two_mul]

omit [DecidableEq m] in
/-- **Normalized Tracial State Scale-Invariance**:
In any commutative ring $R$ with an invertible $2$, the half-scaled trace of an enfolded
matrix equals the unscaled trace of the original matrix:
$$\frac{1}{2}\operatorname{Tr}(\mathcal{E}(X)) = \operatorname{Tr}(X).$$ -/
theorem normalized_enfold_trace_invariant [Invertible (2 : R)] (X : Matrix m m R) :
    ⅟(2 : R) * Matrix.trace (enfold X) = Matrix.trace X := by
  rw [enfold_trace_scaling, ← mul_assoc, invOf_mul_self, one_mul]

/-- **Holomovement Trace Preservation**:
The holomovement pinching channel $\Phi(Y) = P_1 Y P_1 + P_2 Y P_2$ preserves the matrix
trace of every implicate operator $Y \in M_{m \oplus m}(R)$:
$$\operatorname{Tr}(\Phi(Y)) = \operatorname{Tr}(Y).$$ -/
theorem holomovement_trace_eq (Y : Matrix (m ⊕ m) (m ⊕ m) R) :
    Matrix.trace (holomovement Y) = Matrix.trace Y := by
  rw [holomovement_eq_fromBlocks_unfold, trace_fromBlocks_eq_add]
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks Y]
  rw [trace_fromBlocks_eq_add]
  rfl

/-- **Sub-Channel Decomposition of Expectation Values**:
The expectation of a pinched operator $\Phi(Y)$ against an enfolded density matrix
$\mathcal{E}(\rho)$ splits into the sum of the two unfolded local channel expectations:
$$\operatorname{Tr}(\mathcal{E}(\rho)\,\Phi(Y)) =
  \operatorname{Tr}(\rho\,U_1(Y)) + \operatorname{Tr}(\rho\,U_2(Y)).$$ -/
theorem holomovement_enfold_trace_sum
    (ρ : Matrix m m R) (Y : Matrix (m ⊕ m) (m ⊕ m) R) :
    Matrix.trace (enfold ρ * holomovement Y) =
      Matrix.trace (ρ * unfold1 Y) + Matrix.trace (ρ * unfold2 Y) := by
  rw [holomovement_eq_fromBlocks_unfold]
  unfold enfold
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  exact trace_fromBlocks_eq_add (ρ * unfold1 Y) 0 0 (ρ * unfold2 Y)

/-- **Cyclic State Invariance of the Holomovement**:
Against any enfolded state $\mathcal{E}(\rho)$, the holomovement pinching channel $\Phi$
leaves expectation values strictly invariant:
$$\operatorname{Tr}(\mathcal{E}(\rho)\,\Phi(Y)) = \operatorname{Tr}(\mathcal{E}(\rho)\,Y).$$ -/
theorem holomovement_enfold_trace_invariant
    (ρ : Matrix m m R) (Y : Matrix (m ⊕ m) (m ⊕ m) R) :
    Matrix.trace (enfold ρ * holomovement Y) = Matrix.trace (enfold ρ * Y) := by
  rw [holomovement_enfold_trace_sum]
  conv_rhs =>
    rw [← Matrix.fromBlocks_toBlocks Y]
  unfold enfold unfold1 unfold2
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, add_zero, zero_add]
  rw [trace_fromBlocks_eq_add]

/-- **Bridge to the Repository's Owned UHF Direct-Limit Tower & Coherent State Functional**:
Connects the concrete block-doubling step $X \mapsto X \otimes I_2$ directly to the
inductive colimit embedding $\iota_k : M_{2^k}(\mathbb{C}) \to \mathcal{A}_\infty$
(`InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection_concrete_transition`)
and the colimit state functional $\omega_\infty$
(`InfoGeometry.QuantumContext.AttentionColimitStateCoherence.selectedStageColimitFunctional_succ_eq`). -/
theorem uhf_tower_enfold_and_state_coherence_bridge
    (k : ℕ) (x : InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.MatrixStage k) :
    InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection (k + 1)
        (InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteStep k x) =
      InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection k x ∧
    InfoGeometry.QuantumContext.MatrixStageSelectedFunctional.selectedStageColimitFunctional (k + 1)
        (InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteStep k x) =
      InfoGeometry.QuantumContext.MatrixStageSelectedFunctional.selectedStageColimitFunctional k x := by
  refine ⟨?_,
    InfoGeometry.QuantumContext.AttentionColimitStateCoherence.selectedStageColimitFunctional_succ_eq
      k x (InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteStep k x) rfl⟩
  have hstep :
      InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteStep k x =
        InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteMap (Nat.le.step (le_refl k)) x := by
    change InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteData.step k x =
      InfoGeometry.Canonical.CuntzMatrixTraceTower.map
        InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteData (Nat.le.step (le_refl k)) x
    rw [InfoGeometry.Canonical.CuntzMatrixTraceTower.map_succ
      InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteData (le_refl k),
      InfoGeometry.Canonical.CuntzMatrixTraceTower.map_id]
    rfl
  rw [hstep]
  exact InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection_concrete_transition
    (Nat.le.step (le_refl k)) x

/-!
## Archetype VI: Causal Poset of the Bohmian–Cuntz Holomovement Architecture
-/

/-- The 6 architectural nodes of the Bohm–Hiley / Cuntz $\mathcal{O}_2$ holomovement poset:
1. `cuntzTraceObstruction` (Level 0: Finite-dimensional trace obstruction $2N = N \implies N = 0$),
2. `explicateEnfoldment` (Level 1: Block-diagonal enfoldment $\mathcal{E}(X) = X \oplus X$),
3. `unfoldChannel1` (Level 2a: Left Cuntz sub-channel compression $U_1(Y) = S_1^* Y S_1$),
4. `unfoldChannel2` (Level 2b: Right Cuntz sub-channel compression $U_2(Y) = S_2^* Y S_2$),
5. `holomovementPinching` (Level 3: Re-enfolded pinching channel $\Phi(Y) = P_1 Y P_1 + P_2 Y P_2$),
6. `implicateColimitHorizon` (Level 4: Scale-invariant UHF direct-limit horizon $\mathcal{A}_\infty$). -/
inductive BohmCuntzStage : Type
  | cuntzTraceObstruction : BohmCuntzStage
  | explicateEnfoldment : BohmCuntzStage
  | unfoldChannel1 : BohmCuntzStage
  | unfoldChannel2 : BohmCuntzStage
  | holomovementPinching : BohmCuntzStage
  | implicateColimitHorizon : BohmCuntzStage
  deriving DecidableEq, Repr

instance : Inhabited BohmCuntzStage := ⟨.cuntzTraceObstruction⟩

/-- Non-default terminal witness for `BohmCuntzStage` (`T17` compliance). -/
def bohmCuntzTerminalWitness : BohmCuntzStage := .implicateColimitHorizon

theorem bohmCuntzTerminalWitness_ne_default :
    bohmCuntzTerminalWitness ≠ (default : BohmCuntzStage) := by
  intro h
  cases h

/-- Integer height grading on `BohmCuntzStage`. -/
def bohmCuntzHeight : BohmCuntzStage → ℕ
  | .cuntzTraceObstruction => 0
  | .explicateEnfoldment => 1
  | .unfoldChannel1 => 2
  | .unfoldChannel2 => 2
  | .holomovementPinching => 3
  | .implicateColimitHorizon => 4

/-- Direct covering edges of the Bohm–Cuntz holomovement diamond poset. -/
inductive BohmCuntzEdge : BohmCuntzStage → BohmCuntzStage → Prop
  | obstruction_to_enfold :
      BohmCuntzEdge .cuntzTraceObstruction .explicateEnfoldment
  | enfold_to_unfold1 :
      BohmCuntzEdge .explicateEnfoldment .unfoldChannel1
  | enfold_to_unfold2 :
      BohmCuntzEdge .explicateEnfoldment .unfoldChannel2
  | unfold1_to_holomovement :
      BohmCuntzEdge .unfoldChannel1 .holomovementPinching
  | unfold2_to_holomovement :
      BohmCuntzEdge .unfoldChannel2 .holomovementPinching
  | holomovement_to_colimit :
      BohmCuntzEdge .holomovementPinching .implicateColimitHorizon

/-- Reflexive-transitive reachability relation on `BohmCuntzStage`. -/
inductive BohmCuntzReach : BohmCuntzStage → BohmCuntzStage → Prop
  | refl (x : BohmCuntzStage) : BohmCuntzReach x x
  | tail {x y z : BohmCuntzStage} :
      BohmCuntzReach x y → BohmCuntzEdge y z → BohmCuntzReach x z

/-- Every covering edge strictly increases `bohmCuntzHeight`. -/
theorem bohmCuntzEdge_height_lt {x y : BohmCuntzStage} (h : BohmCuntzEdge x y) :
    bohmCuntzHeight x < bohmCuntzHeight y := by
  cases h <;> decide

/-- Transitivity of `BohmCuntzReach`. -/
theorem bohmCuntzReach_trans {x y z : BohmCuntzStage}
    (hxy : BohmCuntzReach x y) (hyz : BohmCuntzReach y z) :
    BohmCuntzReach x z := by
  induction hyz with
  | refl => exact hxy
  | tail _ hstep ih => exact BohmCuntzReach.tail ih hstep

/-- Reachability implies non-decreasing `bohmCuntzHeight`. -/
theorem bohmCuntzReach_height_le {x y : BohmCuntzStage}
    (h : BohmCuntzReach x y) :
    bohmCuntzHeight x ≤ bohmCuntzHeight y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      exact Nat.le_of_lt (lt_of_le_of_lt ih (bohmCuntzEdge_height_lt hstep))

/-- If `x` reaches `y` and `x ≠ y`, then `bohmCuntzHeight x < bohmCuntzHeight y`. -/
theorem bohmCuntzReach_height_lt_of_ne {x y : BohmCuntzStage}
    (h : BohmCuntzReach x y) (hne : x ≠ y) :
    bohmCuntzHeight x < bohmCuntzHeight y := by
  induction h with
  | refl => exact False.elim (hne rfl)
  | tail hab hbc _ =>
      exact lt_of_le_of_lt (bohmCuntzReach_height_le hab) (bohmCuntzEdge_height_lt hbc)

/-- Antisymmetry of `BohmCuntzReach`. -/
theorem bohmCuntzReach_antisymm {x y : BohmCuntzStage}
    (hxy : BohmCuntzReach x y) (hyx : BohmCuntzReach y x) :
    x = y := by
  by_contra hne
  have h1 : bohmCuntzHeight x < bohmCuntzHeight y :=
    bohmCuntzReach_height_lt_of_ne hxy hne
  have h2 : bohmCuntzHeight y ≤ bohmCuntzHeight x :=
    bohmCuntzReach_height_le hyx
  exact Nat.not_lt.mpr h2 h1

instance : PartialOrder BohmCuntzStage where
  le := BohmCuntzReach
  le_refl := BohmCuntzReach.refl
  le_trans := fun _ _ _ => bohmCuntzReach_trans
  le_antisymm := fun _ _ => bohmCuntzReach_antisymm

/-- Strict monotonicity of `bohmCuntzHeight` on the poset `BohmCuntzStage`. -/
theorem bohmCuntzHeight_strictMono {x y : BohmCuntzStage} (h : x < y) :
    bohmCuntzHeight x < bohmCuntzHeight y := by
  rcases lt_iff_le_and_ne.mp h with ⟨hle, hne⟩
  exact bohmCuntzReach_height_lt_of_ne hle hne

/-- The two Cuntz sub-channel unfoldments `unfoldChannel1` and `unfoldChannel2` are
strictly incomparable in the causal poset (`¬(unfoldChannel1 ≤ unfoldChannel2)` and
`¬(unfoldChannel2 ≤ unfoldChannel1)`), establishing that `BohmCuntzStage` is a genuine
non-total diamond poset. -/
theorem not_total_bohmCuntzStage_le :
    ¬ (BohmCuntzStage.unfoldChannel1 ≤ BohmCuntzStage.unfoldChannel2) ∧
    ¬ (BohmCuntzStage.unfoldChannel2 ≤ BohmCuntzStage.unfoldChannel1) := by
  constructor
  · intro h12
    have hne : BohmCuntzStage.unfoldChannel1 ≠ BohmCuntzStage.unfoldChannel2 := by decide
    have hlt := bohmCuntzReach_height_lt_of_ne h12 hne
    exact Nat.lt_irrefl 2 hlt
  · intro h21
    have hne : BohmCuntzStage.unfoldChannel2 ≠ BohmCuntzStage.unfoldChannel1 := by decide
    have hlt := bohmCuntzReach_height_lt_of_ne h21 hne
    exact Nat.lt_irrefl 2 hlt

/-- **End-to-End Causal Chain Through Both Cuntz Channels**:
Both Cuntz sub-channel paths lead strictly from the finite-dimensional Cuntz trace
obstruction (`cuntzTraceObstruction`) to the infinite UHF colimit horizon
(`implicateColimitHorizon`). -/
theorem bohmCuntz_endToEnd_strict_chains :
    BohmCuntzStage.cuntzTraceObstruction < BohmCuntzStage.implicateColimitHorizon ∧
    BohmCuntzStage.explicateEnfoldment ≤ BohmCuntzStage.unfoldChannel1 ∧
    BohmCuntzStage.explicateEnfoldment ≤ BohmCuntzStage.unfoldChannel2 ∧
    BohmCuntzStage.unfoldChannel1 ≤ BohmCuntzStage.holomovementPinching ∧
    BohmCuntzStage.unfoldChannel2 ≤ BohmCuntzStage.holomovementPinching := by
  have h01 : BohmCuntzStage.cuntzTraceObstruction ≤ BohmCuntzStage.explicateEnfoldment :=
    BohmCuntzReach.tail (BohmCuntzReach.refl _) BohmCuntzEdge.obstruction_to_enfold
  have h12a : BohmCuntzStage.explicateEnfoldment ≤ BohmCuntzStage.unfoldChannel1 :=
    BohmCuntzReach.tail (BohmCuntzReach.refl _) BohmCuntzEdge.enfold_to_unfold1
  have h12b : BohmCuntzStage.explicateEnfoldment ≤ BohmCuntzStage.unfoldChannel2 :=
    BohmCuntzReach.tail (BohmCuntzReach.refl _) BohmCuntzEdge.enfold_to_unfold2
  have h2a3 : BohmCuntzStage.unfoldChannel1 ≤ BohmCuntzStage.holomovementPinching :=
    BohmCuntzReach.tail (BohmCuntzReach.refl _) BohmCuntzEdge.unfold1_to_holomovement
  have h2b3 : BohmCuntzStage.unfoldChannel2 ≤ BohmCuntzStage.holomovementPinching :=
    BohmCuntzReach.tail (BohmCuntzReach.refl _) BohmCuntzEdge.unfold2_to_holomovement
  have h34 : BohmCuntzStage.holomovementPinching ≤ BohmCuntzStage.implicateColimitHorizon :=
    BohmCuntzReach.tail (BohmCuntzReach.refl _) BohmCuntzEdge.holomovement_to_colimit
  have h04 : BohmCuntzStage.cuntzTraceObstruction ≤ BohmCuntzStage.implicateColimitHorizon :=
    le_trans h01 (le_trans h12a (le_trans h2a3 h34))
  have hne : BohmCuntzStage.cuntzTraceObstruction ≠ BohmCuntzStage.implicateColimitHorizon := by
    decide
  exact ⟨lt_of_le_of_ne h04 hne, h12a, h12b, h2a3, h2b3⟩

end InfoGeometry.Synthesis.BohmianCuntzHolomovementPoset
