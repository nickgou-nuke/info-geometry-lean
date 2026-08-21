import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section

open Matrix

namespace InfoGeometry.InformationGeometry.TrifoldKL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

/-- Total Trace of a Bipartite State: Tr(ρ) = Tr(ρ₊) + Tr(ρ₋). -/
def totalTrace (ρ : Matrix ι ι R × Matrix ι ι R) : R :=
  Matrix.trace ρ.1 + Matrix.trace ρ.2

/-- Supertrace of a Bipartite State (Chiral Polarization): STr(ρ) = Tr(ρ₊) - Tr(ρ₋). -/
def superTrace (ρ : Matrix ι ι R × Matrix ι ι R) : R :=
  Matrix.trace ρ.1 - Matrix.trace ρ.2

/-- 
  The Expected Relative Surprisal (Algebraic KL Divergence):
  D_KL(ρ, 𝒦) = Tr(ρ₊ * 𝒦₊) + Tr(ρ₋ * 𝒦₋)
-/
def klDivergence (ρ : Matrix ι ι R × Matrix ι ι R) (K : Matrix ι ι R × Matrix ι ι R) : R :=
  Matrix.trace (ρ.1 * K.1) + Matrix.trace (ρ.2 * K.2)

/-- The Common Volume Mode of the Surprisal: α = Tr(𝒦) / 2n. -/
def alpha (two_n_inv : R) (K : Matrix ι ι R × Matrix ι ι R) : R :=
  (Matrix.trace K.1 + Matrix.trace K.2) * two_n_inv

/-- The Chiral Mode of the Surprisal: β = STr(𝒦) / 2n. -/
def beta (two_n_inv : R) (K : Matrix ι ι R × Matrix ι ι R) : R :=
  (Matrix.trace K.1 - Matrix.trace K.2) * two_n_inv

/-- The Pure Traceless/Supertraceless Shape Surprisal 𝒦₀ = 𝒦 - α I - β Γ. -/
def K_zero (two_n_inv : R) (K : Matrix ι ι R × Matrix ι ι R) : Matrix ι ι R × Matrix ι ι R :=
  (K.1 - (alpha two_n_inv K + beta two_n_inv K) • (1 : Matrix ι ι R),
   K.2 - (alpha two_n_inv K - beta two_n_inv K) • (1 : Matrix ι ι R))

/-- The residual has zero total trace when `two_n_inv` is the inverse of `2 * n`. -/
theorem K_zero_trace
    (two_n_inv : R)
    (h_norm : (2 * (Fintype.card ι : R)) * two_n_inv = 1)
    (K : Matrix ι ι R × Matrix ι ι R) :
    Matrix.trace (K_zero two_n_inv K).1 + Matrix.trace (K_zero two_n_inv K).2 = 0 := by
  dsimp [K_zero, alpha, beta]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  calc
    _ = (Matrix.trace K.1 + Matrix.trace K.2) -
        (2 * (Fintype.card ι : R) * two_n_inv) *
          (Matrix.trace K.1 + Matrix.trace K.2) := by ring
    _ = 0 := by rw [h_norm]; ring

/-- The residual has zero supertrace under the same normalization. -/
theorem K_zero_superTrace
    (two_n_inv : R)
    (h_norm : (2 * (Fintype.card ι : R)) * two_n_inv = 1)
    (K : Matrix ι ι R × Matrix ι ι R) :
    Matrix.trace (K_zero two_n_inv K).1 - Matrix.trace (K_zero two_n_inv K).2 = 0 := by
  dsimp [K_zero, alpha, beta]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  calc
    _ = (Matrix.trace K.1 - Matrix.trace K.2) -
        (2 * (Fintype.card ι : R) * two_n_inv) *
          (Matrix.trace K.1 - Matrix.trace K.2) := by ring
    _ = 0 := by rw [h_norm]; ring

/-- 
  MASTER THEOREM: Exact Trifold Scalar Decomposition of Relative Entropy:
  D_KL(ρ, 𝒦) = α • Tr(ρ) + β • STr(ρ) + D_KL(ρ, 𝒦₀)
-/
theorem trifold_kl_decomposition
    (two_n_inv : R)
    (ρ : Matrix ι ι R × Matrix ι ι R)
    (K : Matrix ι ι R × Matrix ι ι R) :
    klDivergence ρ K =
      (alpha two_n_inv K) * (totalTrace ρ) +
      (beta two_n_inv K) * (superTrace ρ) +
      klDivergence ρ (K_zero two_n_inv K) := by
  dsimp [klDivergence, totalTrace, superTrace, K_zero]
  simp only [mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  ring

/-- 
  COROLLARY 1 (Chiral Blindness of Unpolarized States):
  If the state has zero chiral polarization (STr(ρ) = 0), the chiral term β
  drops out identically from the relative entropy:
    D_KL(ρ, 𝒦) = α • Tr(ρ) + D_KL(ρ, 𝒦₀)
-/
theorem symmetric_state_chiral_blind
    (two_n_inv : R)
    (ρ : Matrix ι ι R × Matrix ι ι R)
    (K : Matrix ι ι R × Matrix ι ι R)
    (h_unpolarized : superTrace ρ = 0) :
    klDivergence ρ K = (alpha two_n_inv K) * (totalTrace ρ) + klDivergence ρ (K_zero two_n_inv K) := by
  rw [trifold_kl_decomposition two_n_inv ρ K, h_unpolarized]
  simp only [mul_zero, add_zero]

/-- 
  COROLLARY 2 (Pure Shape Relative Entropy):
  If the modular surprisal is pure shape (Tr(𝒦) = 0 and STr(𝒦) = 0),
  the volume and chiral scalar channels vanish:
    D_KL(ρ, 𝒦) = D_KL(ρ, 𝒦₀)
-/
theorem pure_shape_kl_divergence
    (two_n_inv : R)
    (ρ : Matrix ι ι R × Matrix ι ι R)
    (K : Matrix ι ι R × Matrix ι ι R)
    (h_tr : Matrix.trace K.1 + Matrix.trace K.2 = 0)
    (h_str : Matrix.trace K.1 - Matrix.trace K.2 = 0) :
    klDivergence ρ K = klDivergence ρ (K_zero two_n_inv K) := by
  have ha : alpha two_n_inv K = 0 := by
    dsimp [alpha]; rw [h_tr, zero_mul]
  have hb : beta two_n_inv K = 0 := by
    dsimp [beta]; rw [h_str, zero_mul]
  rw [trifold_kl_decomposition two_n_inv ρ K, ha, hb]
  simp only [zero_mul, zero_add]

end InfoGeometry.InformationGeometry.TrifoldKL

end noncomputable section
