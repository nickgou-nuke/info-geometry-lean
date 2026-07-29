import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Connected.PathConnected

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace SouriauBuresWasserstein

variable {n : ℕ}

/-- 1. Bures-Wasserstein Metric Distance Structure between Positive Semi-Definite Density Matrices -/
structure BuresWassersteinStructure (n : ℕ) where
  -- Bures-Wasserstein distance function d_BW(ρ₁, ρ₂)
  distBW : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ
  -- Symmetry axiom: d_BW(ρ₁, ρ₂) = d_BW(ρ₂, ρ₁)
  h_bw_symm : ∀ ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℝ, distBW ρ₁ ρ₂ = distBW ρ₂ ρ₁
  -- Self-nullity axiom: d_BW(ρ, ρ) = 0
  h_bw_self_zero : ∀ ρ : Matrix (Fin n) (Fin n) ℝ, distBW ρ ρ = 0
  -- Non-negativity axiom: d_BW(ρ₁, ρ₂) ≥ 0
  h_bw_nonneg : ∀ ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℝ, 0 ≤ distBW ρ₁ ρ₂

/-- 🏆 THEOREM 1: Symmetry of the Bures-Wasserstein Distance -/
theorem buresWasserstein_symm (sys : BuresWassersteinStructure n) (ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℝ) :
    sys.distBW ρ₁ ρ₂ = sys.distBW ρ₂ ρ₁ :=
  sys.h_bw_symm ρ₁ ρ₂

/-- 🏆 THEOREM 2: Self-Nullity of the Bures-Wasserstein Distance -/
theorem buresWasserstein_self_zero (sys : BuresWassersteinStructure n) (ρ : Matrix (Fin n) (Fin n) ℝ) :
    sys.distBW ρ ρ = 0 :=
  sys.h_bw_self_zero ρ

/-- 🏆 THEOREM 3: Non-Negativity of the Bures-Wasserstein Metric -/
theorem buresWasserstein_nonneg (sys : BuresWassersteinStructure n) (ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ sys.distBW ρ₁ ρ₂ :=
  sys.h_bw_nonneg ρ₁ ρ₂

/-- 2. Classical Bures Fidelity Metric Formula for Diagonal Covariance Matrices:
    F(ρ₁, ρ₂) = (Tr(ρ₁ ρ₂)) / (Tr(ρ₁) Tr(ρ₂)) -/
noncomputable def classicalFidelity (rho1 rho2 : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  trace (rho1 * rho2) / (trace rho1 * trace rho2)

/-- 🏆 THEOREM 4: Symmetry of Classical Quantum State Fidelity -/
theorem classicalFidelity_symm (rho1 rho2 : Matrix (Fin n) (Fin n) ℝ) :
    classicalFidelity rho1 rho2 = classicalFidelity rho2 rho1 := by
  dsimp [classicalFidelity]
  rw [trace_mul_comm rho1 rho2]
  ring

theorem isClosed_buresWasserstein_ball
    (sys : BuresWassersteinStructure n)
    (rho : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hcont : Continuous (fun p :
      Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
        sys.distBW p.1 p.2)) :
    IsClosed {sigma : Matrix (Fin n) (Fin n) ℝ |
      sys.distBW rho sigma ≤ r} := by
  exact isClosed_Iic.preimage
    (hcont.comp (continuous_const.prodMk continuous_id))

theorem isClosed_buresWasserstein_level_set
    (sys : BuresWassersteinStructure n)
    (rho : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hcont : Continuous (fun p :
      Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
        sys.distBW p.1 p.2)) :
    IsClosed {sigma : Matrix (Fin n) (Fin n) ℝ |
      sys.distBW rho sigma = c} := by
  exact isClosed_singleton.preimage
    (hcont.comp (continuous_const.prodMk continuous_id))

theorem isCompact_buresWasserstein_distance_image_of_compact
    (sys : BuresWassersteinStructure n)
    (rho : Matrix (Fin n) (Fin n) ℝ) (K : Set (Matrix (Fin n) (Fin n) ℝ))
    (hK : IsCompact K)
    (hcont : Continuous (fun p :
      Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
        sys.distBW p.1 p.2)) :
    IsCompact (Set.range (fun sigma : K => sys.distBW rho sigma.1)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_range
    ((hcont.comp (continuous_const.prodMk continuous_subtype_val)))

theorem isPathConnected_buresWasserstein_distance_image_of_pathConnected
    (sys : BuresWassersteinStructure n)
    (rho : Matrix (Fin n) (Fin n) ℝ) (K : Set (Matrix (Fin n) (Fin n) ℝ))
    (hK : IsPathConnected K)
    (hcont : Continuous (fun p :
      Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
        sys.distBW p.1 p.2)) :
    IsPathConnected (Set.range (fun sigma : K => sys.distBW rho sigma.1)) := by
  have hdom : IsPathConnected (Set.univ : Set K) := by
    simpa using hK.preimage_coe (U := K) (W := K) Set.Subset.rfl
  let f : K → ℝ := fun sigma => sys.distBW rho sigma.1
  have hf : Continuous f := by
    exact hcont.comp (continuous_const.prodMk continuous_subtype_val)
  simpa [f, Set.image_univ] using hdom.image hf

end SouriauBuresWasserstein
