import Mathlib.Tactic

noncomputable section

namespace SarsWeylColimit

open Complex

abbrev Phase := ℂ

def weylPhase (σ : ℝ) : ℂ := Complex.exp (-(Complex.I / 2) * (σ : ℂ))

structure SymplecticForm (V : Type*) [AddCommGroup V] where
  sigma : V → V → ℝ
  skew : ∀ u v : V, sigma v u = -sigma u v

structure SymplecticEmbedding
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    (S : SymplecticForm V) (T : SymplecticForm W) where
  f : V → W
  map_add : ∀ u v : V, f (u + v) = f u + f v
  preserves_sigma : ∀ u v : V, T.sigma (f u) (f v) = S.sigma u v

structure WeylSystem (V A : Type*) [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]
    (S : SymplecticForm V) where
  W : V → A
  W_zero : W 0 = 1
  W_neg : ∀ u : V, W (-u) = star (W u)
  W_mul : ∀ u v : V, W u * W v = weylPhase (S.sigma u v) • W (u + v)

structure CompatibleWeylEmbedding
    (V W A B : Type*)
    [AddCommGroup V] [AddCommGroup W]
    [One A] [Mul A] [Star A] [SMul ℂ A]
    [One B] [Mul B] [Star B] [SMul ℂ B]
    (S : SymplecticForm V) (T : SymplecticForm W)
    (WV : WeylSystem V A S) (WW : WeylSystem W B T) where
  emb : SymplecticEmbedding V W S T
  mapA : A → B
  preserves_W : ∀ u : V, mapA (WV.W u) = WW.W (emb.f u)

namespace CompatibleWeylEmbedding

variable {V W A B : Type*}
variable [AddCommGroup V] [AddCommGroup W]
variable [One A] [Mul A] [Star A] [SMul ℂ A]
variable [One B] [Mul B] [Star B] [SMul ℂ B]
variable {S : SymplecticForm V} {T : SymplecticForm W}
variable {WV : WeylSystem V A S} {WW : WeylSystem W B T}

 theorem target_weyl_relation (E : CompatibleWeylEmbedding V W A B S T WV WW) (u v : V) :
    WW.W (E.emb.f u) * WW.W (E.emb.f v) =
      weylPhase (S.sigma u v) • WW.W (E.emb.f (u + v)) := by
  rw [WW.W_mul]
  rw [E.emb.preserves_sigma]
  rw [E.emb.map_add]

end CompatibleWeylEmbedding

abbrev RPhaseSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def canonicalSigma {n : ℕ} (u v : RPhaseSpace n) : ℝ :=
  Finset.univ.sum (fun i => u.1 i * v.2 i - u.2 i * v.1 i)

theorem canonicalSigma_skew {n : ℕ} (u v : RPhaseSpace n) :
    canonicalSigma v u = -canonicalSigma u v := by
  unfold canonicalSigma
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def canonicalSymplectic (n : ℕ) : SymplecticForm (RPhaseSpace n) where
  sigma := canonicalSigma
  skew := canonicalSigma_skew

/-- Zero-padding from one mode to two modes. -/
def pad1to2 (u : RPhaseSpace 1) : RPhaseSpace 2 :=
  (fun i => if (i : Nat) = 0 then u.1 0 else 0,
   fun i => if (i : Nat) = 0 then u.2 0 else 0)

@[simp] theorem pad1to2_zero : pad1to2 0 = 0 := by
  ext i <;> fin_cases i <;> rfl

@[simp] theorem pad1to2_add (u v : RPhaseSpace 1) :
    pad1to2 (u + v) = pad1to2 u + pad1to2 v := by
  ext i <;> fin_cases i <;> simp [pad1to2]

@[simp] theorem pad1to2_preserves_sigma (u v : RPhaseSpace 1) :
    canonicalSigma (pad1to2 u) (pad1to2 v) = canonicalSigma u v := by
  simp [canonicalSigma, pad1to2]

def symplecticEmbedding1to2 :
    SymplecticEmbedding (RPhaseSpace 1) (RPhaseSpace 2)
      (canonicalSymplectic 1) (canonicalSymplectic 2) where
  f := pad1to2
  map_add := pad1to2_add
  preserves_sigma := pad1to2_preserves_sigma

/-- Finite CAR/UHF block dimension at stage `n`. -/
def BlockDim (n : ℕ) : ℕ := 32 ^ n

theorem block_dim_zero : BlockDim 0 = 1 := by
  simp [BlockDim]

theorem block_dim_succ (n : ℕ) : BlockDim (n + 1) = BlockDim n * 32 := by
  simp [BlockDim, pow_succ]

theorem block_dim_two : BlockDim 2 = 1024 := by
  norm_num [BlockDim]

theorem cl55_block_dim : 2 ^ 10 = BlockDim 2 := by
  norm_num [BlockDim]

/-- Algebraic summary: one-mode Weyl relations survive zero-padding into two modes,
and the finite CAR block tower has `M_32 ⊗ M_32 = M_1024`. -/
theorem weyl_colimit_finite_step_kernel :
    (∀ u v : RPhaseSpace 1,
      canonicalSigma (pad1to2 u) (pad1to2 v) = canonicalSigma u v) ∧
    BlockDim 0 = 1 ∧
    BlockDim 1 = 32 ∧
    BlockDim 2 = 1024 ∧
    2 ^ 10 = BlockDim 2 := by
  exact ⟨pad1to2_preserves_sigma, block_dim_zero, by norm_num [BlockDim],
    block_dim_two, cl55_block_dim⟩

end SarsWeylColimit

end noncomputable section
