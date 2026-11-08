import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Clifford.Cl55RoPEAttentionPairing

/-!
# RoPE Invariant Bilinear Pairing & Exact Relative-Position Attention

This module formalizes the exact representation-theoretic proof that a
rotor-invariant bilinear form on the spin module intertwines query/key projections
into the canonical relative-position Transformer attention score:

$$\boxed{
\begin{aligned}
&\textbf{1. Invariant Pairing Hypothesis:}\\
&\quad B_S(R(\theta) u, R(\theta) v) = B_S(u, v)\\
&\textbf{2. Relative-Position Invariant:}\\
&\quad B_S(R(m\theta_0) u, R(n\theta_0) v) = B_S(u, R((n - m)\theta_0) v)\\
&\textbf{3. Full Query/Key Attention Intertwining:}\\
&\quad q_m = W_Q x_m, \qquad k_n = W_K x_n\\
&\quad \langle R(m\theta_0) q_m, R(n\theta_0) k_n \rangle = \langle q_m, R((n - m)\theta_0) k_n \rangle.
\end{aligned}}
$$

All proofs are complete in native Mathlib 4 with zero `sorry`s.
-/

variable {V X : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]

/-- Structure defining a 1-parameter rotor representation with an invariant bilinear pairing. -/
structure InvariantRotorPairing (V : Type*) [AddCommGroup V] [Module ℝ V] where
  R : ℝ → V →ₗ[ℝ] V
  R_zero : R 0 = LinearMap.id
  R_add : ∀ s t, R (s + t) = R s ∘ₗ R t
  inner : V → V → ℝ
  inner_inv : ∀ theta u v, inner (R theta u) (R theta v) = inner u v

namespace InvariantRotorPairing

variable (P : InvariantRotorPairing V)

/-- Inverse rotor relation: $R(-\theta) \circ R(\theta) = \mathrm{id}$. -/
theorem R_neg_mul_self (theta : ℝ) : P.R (-theta) ∘ₗ P.R theta = LinearMap.id := by
  have h : P.R (-theta + theta) = P.R (-theta) ∘ₗ P.R theta := P.R_add (-theta) theta
  rw [neg_add_cancel, P.R_zero] at h
  exact h.symm

/-- Inverse rotor action on vector: $R(-\theta) (R(\theta) u) = u$. -/
theorem R_neg_apply (theta : ℝ) (u : V) : P.R (-theta) (P.R theta u) = u := by
  have h := LinearMap.congr_fun (P.R_neg_mul_self theta) u
  rw [LinearMap.id_apply] at h
  exact h

/-- **Theorem (Relative-Position Law for Bilinear Pairing)**:
    $B_S(R(s) u, R(t) v) = B_S(u, R(t - s) v)$. -/
theorem inner_relative_shift (s t : ℝ) (u v : V) :
    P.inner (P.R s u) (P.R t v) = P.inner u (P.R (t - s) v) := by
  have h_inv := P.inner_inv (-s) (P.R s u) (P.R t v)
  rw [P.R_neg_apply s u] at h_inv
  have h_comp : P.R (-s) (P.R t v) = P.R (t - s) v := by
    have h := LinearMap.congr_fun (P.R_add (-s) t) v
    rw [add_comm (-s) t] at h
    exact h.symm
  rw [h_comp] at h_inv
  exact h_inv.symm

/-- **Theorem (Discrete Integer Position Shift)**:
    $B_S(R(m\theta_0) u, R(n\theta_0) v) = B_S(u, R((n - m)\theta_0) v)$. -/
theorem inner_discrete_relative_shift (theta0 : ℝ) (m n : ℤ) (u v : V) :
    P.inner (P.R ((m : ℝ) * theta0) u) (P.R ((n : ℝ) * theta0) v) =
    P.inner u (P.R (((n - m : ℤ) : ℝ) * theta0) v) := by
  have h := P.inner_relative_shift ((m : ℝ) * theta0) ((n : ℝ) * theta0) u v
  have h_diff : (n : ℝ) * theta0 - (m : ℝ) * theta0 = ((n - m : ℤ) : ℝ) * theta0 := by
    push_cast; ring
  rw [h_diff] at h
  exact h

/-! ## Query / Key Attention Intertwining -/

/-- Attention score with RoPE rotary positional embedding:
    $\mathrm{Att}(m, n, x_m, x_n) = B_S(R(m\theta_0) (W_Q x_m), R(n\theta_0) (W_K x_n))$. -/
def attentionScore
    (W_Q W_K : X →ₗ[ℝ] V) (theta0 : ℝ)
    (m n : ℤ) (xm xn : X) : ℝ :=
  P.inner (P.R ((m : ℝ) * theta0) (W_Q xm)) (P.R ((n : ℝ) * theta0) (W_K xn))

/-- **Theorem (Master Transformer Attention Relative-Position Intertwining)**:
    $\mathrm{Att}(m, n, x_m, x_n) = B_S(W_Q x_m, R((n - m)\theta_0) (W_K x_n))$. -/
theorem attentionScore_eq_relative
    (W_Q W_K : X →ₗ[ℝ] V) (theta0 : ℝ)
    (m n : ℤ) (xm xn : X) :
    P.attentionScore W_Q W_K theta0 m n xm xn =
    P.inner (W_Q xm) (P.R (((n - m : ℤ) : ℝ) * theta0) (W_K xn)) :=
  P.inner_discrete_relative_shift theta0 m n (W_Q xm) (W_K xn)

end InvariantRotorPairing

/-! ## Master Synthesis -/

/--
🏆 **GRAND SYNTHESIS THEOREM: RoPE Invariant Pairing & Attention Intertwining**

Unifies:
1. Exact rotor inversion $R(-\theta) R(\theta) = \mathrm{id}$.
2. General continuous relative shift $B_S(R(s) u, R(t) v) = B_S(u, R(t - s) v)$.
3. Discrete integer position relative shift $B_S(R(m\theta_0) u, R(n\theta_0) v) = B_S(u, R((n - m)\theta_0) v)$.
4. Master Transformer attention identity $\mathrm{Att}(m, n, x_m, x_n) = B_S(W_Q x_m, R((n - m)\theta_0) W_K x_n)$.
-/
theorem grand_rope_attention_pairing_synthesis
    (P : InvariantRotorPairing V)
    (W_Q W_K : X →ₗ[ℝ] V) (theta0 s t : ℝ)
    (m n : ℤ) (u v : V) (xm xn : X) :
    (P.R (-s) (P.R s u) = u ∧
     P.inner (P.R s u) (P.R t v) = P.inner u (P.R (t - s) v) ∧
     P.inner (P.R ((m : ℝ) * theta0) u) (P.R ((n : ℝ) * theta0) v) =
       P.inner u (P.R (((n - m : ℤ) : ℝ) * theta0) v)) ∧
    (P.attentionScore W_Q W_K theta0 m n xm xn =
     P.inner (W_Q xm) (P.R (((n - m : ℤ) : ℝ) * theta0) (W_K xn))) :=
  ⟨⟨P.R_neg_apply s u,
     P.inner_relative_shift s t u v,
     P.inner_discrete_relative_shift theta0 m n u v⟩,
   P.attentionScore_eq_relative W_Q W_K theta0 m n xm xn⟩

end InfoGeometry.Clifford.Cl55RoPEAttentionPairing

