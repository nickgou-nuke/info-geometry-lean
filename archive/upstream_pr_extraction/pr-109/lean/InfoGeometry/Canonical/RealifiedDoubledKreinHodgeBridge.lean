/-
# RealifiedDoubledKreinHodgeBridge.lean

Realified Tomita–Takesaki in a Doubled Krein Space — Hodge Connection.
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Meta.Architecture

set_option linter.dupNamespace false

noncomputable section

namespace InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge

open InfoGeometry.Krein

/-! ## 1. Krein indefinite form on the doubled space -/

/--
The Krein indefinite form on the doubled space: `[u, v] = ⟨Pu, v⟩`.
-/
noncomputable def kreinForm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : DoubledSpace E) : ℝ :=
  inner ℝ (spectral_epsilon (E := E) u) v

lemma kreinForm_apply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x₁ x₂ ξ₁ ξ₂ : E) :
    kreinForm (E := E) (to_doubled x₁ ξ₁) (to_doubled x₂ ξ₂) = inner ℝ x₁ x₂ - inner ℝ ξ₁ ξ₂ := by
  simp [kreinForm, spectral_epsilon, to_doubled, WithLp.prod_inner_apply, sub_eq_add_neg]

/-- `P² = id`. -/
lemma spectral_epsilon_sq_apply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (u : DoubledSpace E) :
    spectral_epsilon (E := E) (spectral_epsilon (E := E) u) = u := by
  apply DoubledSpace.ext <;> simp [spectral_epsilon]

/-! ## 2. Realified modular conjugation and its transport -/

structure RealModularConjugation (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  J_R : E → E
  J_R_add : ∀ x y : E, J_R (x + y) = J_R x + J_R y
  J_R_smul : ∀ (r : ℝ) (x : E), J_R (r • x) = r • J_R x
  involutive : ∀ x : E, J_R (J_R x) = x
  isometric : ∀ x y : E, inner ℝ (J_R x) (J_R y) = inner ℝ y x

def doubleModularConjugation (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : RealModularConjugation E) (u : DoubledSpace E) : DoubledSpace E :=
  to_doubled (J.J_R (WithLp.fst u)) (-(J.J_R (WithLp.snd u)))

lemma doubleModularConjugation_involutive (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : RealModularConjugation E) (u : DoubledSpace E) :
    doubleModularConjugation E J (doubleModularConjugation E J u) = u := by
  apply DoubledSpace.ext
  · simp [doubleModularConjugation, to_doubled, J.involutive]
  · have h : J.J_R (-(J.J_R (WithLp.snd u))) = -(J.J_R (J.J_R (WithLp.snd u))) := by
      calc
        J.J_R (-(J.J_R (WithLp.snd u))) = J.J_R ((-1 : ℝ) • (J.J_R (WithLp.snd u))) := by simp
        _ = (-1 : ℝ) • J.J_R (J.J_R (WithLp.snd u)) := by rw [J.J_R_smul]
        _ = -(J.J_R (J.J_R (WithLp.snd u))) := by simp
    simp [doubleModularConjugation, to_doubled, h, J.involutive]

theorem doubleModularConjugation_preserves_kreinForm
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : RealModularConjugation E) (u v : DoubledSpace E) :
    kreinForm (E := E) (doubleModularConjugation E J u) (doubleModularConjugation E J v) =
      kreinForm (E := E) u v := by
  simp [doubleModularConjugation, kreinForm, spectral_epsilon, to_doubled, WithLp.prod_inner_apply, J.isometric,
    real_inner_comm, sub_eq_add_neg]

/-! ## 3. The doubled modular Hamiltonian -/

structure RealModularHamiltonian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  K_R : E → E
  K_R_add : ∀ x y : E, K_R (x + y) = K_R x + K_R y
  K_R_smul : ∀ (r : ℝ) (x : E), K_R (r • x) = r • K_R x
  cont : Continuous K_R

def doubleModularHamiltonian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : RealModularHamiltonian E) (u : DoubledSpace E) : DoubledSpace E :=
  to_doubled (-(K.K_R (WithLp.snd u))) (K.K_R (WithLp.fst u))

lemma doubleModularHamiltonian_sq_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : RealModularHamiltonian E) (u : DoubledSpace E) :
    doubleModularHamiltonian E K (doubleModularHamiltonian E K u) =
      to_doubled (-(K.K_R (K.K_R (WithLp.fst u)))) (-(K.K_R (K.K_R (WithLp.snd u)))) := by
  apply DoubledSpace.ext
  · simp [doubleModularHamiltonian, to_doubled, K.K_R_smul (-1 : ℝ)]
  · calc
      K.K_R (-(K.K_R (WithLp.snd u))) = K.K_R ((-1 : ℝ) • (K.K_R (WithLp.snd u))) := by simp
      _ = (-1 : ℝ) • K.K_R (K.K_R (WithLp.snd u)) := by rw [K.K_R_smul]
      _ = -(K.K_R (K.K_R (WithLp.snd u))) := by simp

/-! ## 4. Commutation: 𝐉 commutes with 𝐊² -/

theorem J_commutes_with_Ksq
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : RealModularConjugation E) (K : RealModularHamiltonian E)
    (comm_apply : ∀ x : E, J.J_R (K.K_R x) = K.K_R (J.J_R x))
    (u : DoubledSpace E) :
    doubleModularConjugation E J (doubleModularHamiltonian E K (doubleModularHamiltonian E K u)) =
    doubleModularHamiltonian E K (doubleModularHamiltonian E K (doubleModularConjugation E J u)) := by
  apply DoubledSpace.ext
  · calc
      WithLp.fst (doubleModularConjugation E J (doubleModularHamiltonian E K (doubleModularHamiltonian E K u)))
          = J.J_R (WithLp.fst (doubleModularHamiltonian E K (doubleModularHamiltonian E K u))) := rfl
      _ = J.J_R (-(K.K_R (K.K_R (WithLp.fst u)))) := by
        simp [doubleModularHamiltonian_sq_apply E K]
      _ = -(J.J_R (K.K_R (K.K_R (WithLp.fst u)))) := by
        calc
          J.J_R (-(K.K_R (K.K_R (WithLp.fst u)))) = J.J_R ((-1 : ℝ) • (K.K_R (K.K_R (WithLp.fst u)))) := by simp
          _ = (-1 : ℝ) • J.J_R (K.K_R (K.K_R (WithLp.fst u))) := by rw [J.J_R_smul]
          _ = -(J.J_R (K.K_R (K.K_R (WithLp.fst u)))) := by simp
      _ = -(K.K_R (K.K_R (J.J_R (WithLp.fst u)))) := by simp [comm_apply]
      _ = WithLp.fst (doubleModularHamiltonian E K (doubleModularHamiltonian E K (doubleModularConjugation E J u))) := by
        simp [doubleModularConjugation, doubleModularHamiltonian, to_doubled, doubleModularHamiltonian_sq_apply E K]
  · calc
      WithLp.snd (doubleModularConjugation E J (doubleModularHamiltonian E K (doubleModularHamiltonian E K u)))
          = -(J.J_R (WithLp.snd (doubleModularHamiltonian E K (doubleModularHamiltonian E K u)))) := rfl
      _ = -(J.J_R (-(K.K_R (K.K_R (WithLp.snd u))))) := by
        simp [doubleModularHamiltonian_sq_apply E K]
      _ = -( -(J.J_R (K.K_R (K.K_R (WithLp.snd u))))) := by
        calc
          -(J.J_R (-(K.K_R (K.K_R (WithLp.snd u))))) = -(J.J_R ((-1 : ℝ) • (K.K_R (K.K_R (WithLp.snd u))))) := by simp
          _ = -((-1 : ℝ) • J.J_R (K.K_R (K.K_R (WithLp.snd u)))) := by rw [J.J_R_smul]
          _ = -( -(J.J_R (K.K_R (K.K_R (WithLp.snd u))))) := by simp
      _ = J.J_R (K.K_R (K.K_R (WithLp.snd u))) := by simp
      _ = K.K_R (K.K_R (J.J_R (WithLp.snd u))) := by
        calc
          J.J_R (K.K_R (K.K_R (WithLp.snd u))) = J.J_R (K.K_R (K.K_R (WithLp.snd u))) := rfl
          _ = K.K_R (J.J_R (K.K_R (WithLp.snd u))) := by rw [comm_apply]
          _ = K.K_R (K.K_R (J.J_R (WithLp.snd u))) := by rw [comm_apply]
      _ = WithLp.snd (doubleModularHamiltonian E K (doubleModularHamiltonian E K (doubleModularConjugation E J u))) := by
        have h_sq : doubleModularHamiltonian E K (doubleModularHamiltonian E K (doubleModularConjugation E J u)) =
          to_doubled (-(K.K_R (K.K_R (J.J_R (WithLp.fst u))))) (-(K.K_R (K.K_R (-(J.J_R (WithLp.snd u)))))) := by
          simp [doubleModularHamiltonian_sq_apply E K, doubleModularConjugation, to_doubled]
        have h_kr_neg : ∀ x : E, K.K_R (-x) = -(K.K_R x) := fun x => by
          calc
            K.K_R (-x) = K.K_R ((-1 : ℝ) • x) := by simp
            _ = (-1 : ℝ) • K.K_R x := by rw [K.K_R_smul]
            _ = -(K.K_R x) := by simp
        have h_snd_eq : K.K_R (K.K_R (J.J_R (WithLp.snd u))) = -(K.K_R (K.K_R (-(J.J_R (WithLp.snd u))))) := by
          calc
            K.K_R (K.K_R (J.J_R (WithLp.snd u))) = -(-(K.K_R (K.K_R (J.J_R (WithLp.snd u))))) := by simp
            _ = -(K.K_R (-(K.K_R (J.J_R (WithLp.snd u))))) := by rw [h_kr_neg (K.K_R (J.J_R (WithLp.snd u)))]
            _ = -(K.K_R (K.K_R (-(J.J_R (WithLp.snd u))))) := by rw [h_kr_neg (J.J_R (WithLp.snd u))]
        simp [h_sq, h_snd_eq]

/-! ## 5. The Hodge 1-Laplacian connection -/

structure HodgeDifferentialData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  d₀ : DoubledSpace E → DoubledSpace E
  d₀Star : DoubledSpace E → DoubledSpace E

namespace HodgeDifferentialData

/-- The Hodge one-Laplacian is the composite `d₀ ∘ d₀Star`. -/
abbrev hodge_one_laplacian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : HodgeDifferentialData E) : DoubledSpace E → DoubledSpace E :=
  D.d₀ ∘ D.d₀Star

@[simp] theorem hodge_one_laplacian_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : HodgeDifferentialData E) :
    D.hodge_one_laplacian = D.d₀ ∘ D.d₀Star :=
  rfl

end HodgeDifferentialData

class HodgePositivityCondition (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : HodgeDifferentialData E) : Prop where
  laplacian_injective_on_negative :
    ∀ (ξ : E), D.hodge_one_laplacian (to_doubled (0 : E) ξ) = (0 : DoubledSpace E) → ξ = 0

theorem hodgeLaplacian_detects_Ksq_kernel
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : RealModularConjugation E) (K : RealModularHamiltonian E)
    (D : HodgeDifferentialData E) [HodgePositivityCondition E D]
    (comm_apply : ∀ x : E, J.J_R (K.K_R x) = K.K_R (J.J_R x))
    (d0_acts_as_Ksq : ∀ (x : E),
      D.hodge_one_laplacian (to_doubled (0 : E) x) = to_doubled (K.K_R (K.K_R (J.J_R x))) (0 : E))
    (ξ : E) (hΔ : D.hodge_one_laplacian (to_doubled (0 : E) ξ) = 0) :
    K.K_R (K.K_R ξ) = 0 := by
  have h_zero : to_doubled (K.K_R (K.K_R (J.J_R ξ))) (0 : E) = 0 := by
    rw [← d0_acts_as_Ksq, hΔ]
  have h_fst : K.K_R (K.K_R (J.J_R ξ)) = 0 := by
    have := congrArg (WithLp.fst (p := (2 : ENNReal))) h_zero
    simpa [to_doubled] using this
  calc
    K.K_R (K.K_R ξ) = J.J_R (J.J_R (K.K_R (K.K_R ξ))) := by
      simp [J.involutive]
    _ = J.J_R (K.K_R (K.K_R (J.J_R ξ))) := by
      simp [comm_apply]
    _ = J.J_R 0 := by rw [h_fst]
    _ = 0 := by
      calc
        J.J_R 0 = J.J_R ((0 : ℝ) • (0 : E)) := by simp
        _ = (0 : ℝ) • J.J_R (0 : E) := by rw [J.J_R_smul]
        _ = 0 := by simp

end InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge
