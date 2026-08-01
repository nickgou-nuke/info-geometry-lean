import Mathlib.Tactic

noncomputable section

namespace SarsGNSWeyl

open Complex

abbrev RPhaseSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def canonicalSigma {n : ℕ} (u v : RPhaseSpace n) : ℝ :=
  Finset.univ.sum (fun i => u.1 i * v.2 i - u.2 i * v.1 i)

def normSq {n : ℕ} (u : RPhaseSpace n) : ℝ :=
  Finset.univ.sum (fun i => u.1 i * u.1 i + u.2 i * u.2 i)

def weylPhase (σ : ℝ) : ℂ := Complex.exp (-(Complex.I / 2) * (σ : ℂ))

def fockState {n : ℕ} (u : RPhaseSpace n) : ℂ :=
  Complex.exp (-(normSq u : ℂ) / 4)

/-- Zero-padding from one mode to two modes. -/
def pad1to2 (u : RPhaseSpace 1) : RPhaseSpace 2 :=
  (fun i => if (i : Nat) = 0 then u.1 0 else 0,
   fun i => if (i : Nat) = 0 then u.2 0 else 0)

@[simp] theorem canonicalSigma_skew {n : ℕ} (u v : RPhaseSpace n) :
    canonicalSigma v u = -canonicalSigma u v := by
  unfold canonicalSigma
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem canonicalSigma_self {n : ℕ} (u : RPhaseSpace n) :
    canonicalSigma u u = 0 := by
  unfold canonicalSigma
  apply Finset.sum_eq_zero
  intro i _
  ring

@[simp] theorem pad1to2_sigma (u v : RPhaseSpace 1) :
    canonicalSigma (pad1to2 u) (pad1to2 v) = canonicalSigma u v := by
  simp [canonicalSigma, pad1to2]

@[simp] theorem pad1to2_normSq (u : RPhaseSpace 1) :
    normSq (pad1to2 u) = normSq u := by
  norm_num [normSq, pad1to2, Fin.sum_univ_two]

@[simp] theorem weylPhase_pad1to2 (u v : RPhaseSpace 1) :
    weylPhase (canonicalSigma (pad1to2 u) (pad1to2 v)) =
      weylPhase (canonicalSigma u v) := by
  rw [pad1to2_sigma]

@[simp] theorem fockState_zero_one {n : ℕ} :
    fockState (0 : RPhaseSpace n) = 1 := by
  have h : normSq (0 : RPhaseSpace n) = 0 := by
    unfold normSq
    apply Finset.sum_eq_zero
    intro i _
    simp
  unfold fockState
  rw [h]
  norm_num

@[simp] theorem fockState_pad1to2 (u : RPhaseSpace 1) :
    fockState (pad1to2 u) = fockState u := by
  unfold fockState
  rw [pad1to2_normSq]

structure WeylSystem (V A : Type*) [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A] where
  sigma : V → V → ℝ
  W : V → A
  W_zero : W 0 = 1
  W_neg : ∀ u : V, W (-u) = star (W u)
  W_mul : ∀ u v : V, W u * W v = weylPhase (sigma u v) • W (u + v)

structure GNSWeylState (V A H : Type*)
    [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (𝓦 : WeylSystem V A) where
  omega : A → ℂ
  pi : A → H →L[ℂ] H
  Omega : H
  vacuum_expectation :
    ∀ u : V, omega (𝓦.W u) = inner ℂ Omega (pi (𝓦.W u) Omega)
  cyclic :
    Submodule.span ℂ (Set.range fun a : A => pi a Omega) = ⊤

structure RegularWeylGNS (V A H : Type*)
    [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (𝓦 : WeylSystem V A) extends GNSWeylState V A H 𝓦 where
  R : V → H →L[ℂ] H
  exp_generator_matches_weyl :
    ∀ u : V, NormedSpace.exp (R u) = pi (𝓦.W u)

@[simp] theorem gns_vacuum_expectation
    {V A H : Type*}
    [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {𝓦 : WeylSystem V A} (G : GNSWeylState V A H 𝓦) (u : V) :
    G.omega (𝓦.W u) = inner ℂ G.Omega (G.pi (𝓦.W u) G.Omega) :=
  G.vacuum_expectation u

/-- The represented orbit of the GNS vector spans the Hilbert carrier. -/
theorem gns_cyclic_span
    {V A H : Type*}
    [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {𝓦 : WeylSystem V A} (G : GNSWeylState V A H 𝓦) :
    Submodule.span ℂ (Set.range fun a : A => G.pi a G.Omega) = ⊤ :=
  G.cyclic

/-- Regular Weyl generators exponentiate to the represented Weyl operators. -/
theorem regular_generator_exp
    {V A H : Type*}
    [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {𝓦 : WeylSystem V A} (G : RegularWeylGNS V A H 𝓦) (u : V) :
    NormedSpace.exp (G.R u) = G.pi (𝓦.W u) :=
  G.exp_generator_matches_weyl u

end SarsGNSWeyl

end noncomputable section
