import InfoGeometry.Quantum.Fock
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.DoubledSpace

/-!
# Fierz Identities for Information Geometry

This module formalizes the Fierz identities for the doubled Krein space $E \oplus E$,
interpreted as identities between different informational channels:
1. **Scalar Channel**: Hessian/Krein pairing (Information Density).
2. **Symplectic Channel**: Induced symplectic form (Information Phase).
3. **Hilbert Channel**: Euclidean pairing (Total Information Power).

Fierz identities provide the "conservation of information power" across these channels.
-/

namespace InfoGeometry.Quantum.Fierz

open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Information Scalar Channel**: $S(\psi) = \langle \psi, J \psi \rangle = 2 \langle x, \xi \rangle$. -/
noncomputable def infoScalar (ψ : DoubledSpace E) : ℝ :=
  hessian_indefinite_form (E := E) ψ ψ

/-- **Information Symplectic Channel**: $\omega(\psi) = \langle \psi, \epsilon \psi \rangle = \|x\|^2 - \|\xi\|^2$. -/
noncomputable def infoSymplectic (ψ : DoubledSpace E) : ℝ :=
  inducedSymplecticForm (E := E) ψ ψ

/-- **Information Hilbert Channel**: $H(\psi) = \langle \psi, \psi \rangle = \|x\|^2 + \|\xi\|^2$. -/
noncomputable def infoHilbert (ψ : DoubledSpace E) : ℝ :=
  inner ℝ (WithLp.fst ψ) (WithLp.fst ψ) + inner ℝ (WithLp.snd ψ) (WithLp.snd ψ)

theorem infoHilbert_nonneg (ψ : DoubledSpace E) :
    0 ≤ infoHilbert ψ := by
  unfold infoHilbert
  exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg

/-- **Information Area (Uncertainty)**: The squared area spanned by the data and model components.
Identified with the Gram determinant of the state components. -/
noncomputable def infoArea (ψ : DoubledSpace E) : ℝ :=
  inner ℝ (WithLp.fst ψ) (WithLp.fst ψ) * inner ℝ (WithLp.snd ψ) (WithLp.snd ψ) -
    (inner ℝ (WithLp.fst ψ) (WithLp.snd ψ))^2

/-! ### The Informational Fierz Identity -/

private lemma hessian_indefinite_form_explicit (u v : DoubledSpace E) :
    hessian_indefinite_form (E := E) u v
      = inner ℝ (WithLp.fst u) (WithLp.fst v) - inner ℝ (WithLp.snd u) (WithLp.snd v) := by
  unfold hessian_indefinite_form
  unfold KreinSpace.kreinInner
  change
    inner ℝ (WithLp.fst (spectral_epsilon (E := E) u)) (WithLp.fst v) +
      inner ℝ (WithLp.snd (spectral_epsilon (E := E) u)) (WithLp.snd v)
      =
    inner ℝ (WithLp.fst u) (WithLp.fst v) - inner ℝ (WithLp.snd u) (WithLp.snd v)
  simp [spectral_epsilon, sub_eq_add_neg]

/--
**The Information Power Conservation Theorem**:
The total Hilbert power of a belief state is distributed across the
scalar and symplectic channels, with the remainder being the information uncertainty (Area).

$H(\psi)^2 = S(\psi)^2 + \omega(\psi)^2 + 4 \cdot \text{Area}(\psi)$
-/
theorem information_fierz_identity (ψ : DoubledSpace E) :
    (infoHilbert ψ)^2 = (infoScalar ψ)^2 + (infoSymplectic ψ)^2 + 4 * (infoArea ψ) := by
  have hS : infoScalar (E := E) ψ
      = inner ℝ (WithLp.fst ψ) (WithLp.fst ψ) - inner ℝ (WithLp.snd ψ) (WithLp.snd ψ) := by
    simpa [infoScalar] using hessian_indefinite_form_explicit (E := E) ψ ψ
  have hW : infoSymplectic (E := E) ψ = -2 * inner ℝ (WithLp.fst ψ) (WithLp.snd ψ) := by
    unfold infoSymplectic inducedSymplecticForm
    rw [hessian_indefinite_form_explicit (E := E) ψ (complex_i (E := E) ψ)]
    have hcomm : inner ℝ (WithLp.snd ψ) (WithLp.fst ψ) = inner ℝ (WithLp.fst ψ) (WithLp.snd ψ) := by
      simpa using (real_inner_comm (WithLp.fst ψ) (WithLp.snd ψ))
    simp [complex_i_apply, hcomm, sub_eq_add_neg]
    ring
  rw [hS, hW]
  unfold infoHilbert infoArea
  ring

/--
**Majorana Information Condition**:
A belief state is 'Majorana' if its data and model components are perfectly aligned
(zero uncertainty/area). For such states, the conservation identity simplifies to a sum of squares.
-/
def IsMajoranaBelief (ψ : DoubledSpace E) : Prop :=
  infoArea ψ = 0

theorem information_fierz_majorana (ψ : DoubledSpace E) (hM : IsMajoranaBelief ψ) :
    (infoHilbert ψ)^2 = (infoScalar ψ)^2 + (infoSymplectic ψ)^2 := by
  rw [information_fierz_identity (E := E) ψ, hM]
  ring

/-- On a Majorana belief state, the Hilbert channel is the square root of the
scalar-plus-symplectic power. -/
theorem information_fierz_majorana_sqrt (ψ : DoubledSpace E) (hM : IsMajoranaBelief ψ) :
    infoHilbert ψ =
      Real.sqrt ((infoScalar ψ)^2 + (infoSymplectic ψ)^2) := by
  have hsq_nonneg : 0 ≤ (infoScalar ψ)^2 + (infoSymplectic ψ)^2 := by
    rw [← information_fierz_majorana (E := E) ψ hM]
    exact sq_nonneg (infoHilbert ψ)
  have h1 : infoHilbert ψ ≤ Real.sqrt ((infoScalar ψ)^2 + (infoSymplectic ψ)^2) := by
    rw [Real.le_sqrt (infoHilbert_nonneg ψ) hsq_nonneg]
    rw [information_fierz_majorana (E := E) ψ hM]
  have h2 : Real.sqrt ((infoScalar ψ)^2 + (infoSymplectic ψ)^2) ≤ infoHilbert ψ := by
    rw [Real.sqrt_le_iff]
    refine ⟨infoHilbert_nonneg ψ, ?_⟩
    rw [information_fierz_majorana (E := E) ψ hM]
  exact le_antisymm h1 h2

end InfoGeometry.Quantum.Fierz
