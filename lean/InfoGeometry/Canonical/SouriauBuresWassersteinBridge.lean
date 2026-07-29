import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Connected.PathConnected
import InfoGeometry.Thermo.BuresWassersteinKMSCost

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace SouriauBuresWasserstein

open InfoGeometry.Thermo.BuresWassersteinKMSCost

variable {n : ℕ}

/- 1. A finite matrix shadow of the genuine positive-state Bures datum.
   The distance laws are inherited from `BuresWassersteinDatum`; only symmetry
   is an additional property of the chosen metric implementation. -/
def matrixPositiveDomain (n : ℕ) :
    PositiveStateDomain (Matrix (Fin n) (Fin n) ℝ) :=
  ⟨Set.univ⟩

def matrixPositiveState (n : ℕ) (ρ : Matrix (Fin n) (Fin n) ℝ) :
    PositiveState (matrixPositiveDomain n) :=
  ⟨ρ, Set.mem_univ ρ⟩

structure BuresWassersteinStructure (n : ℕ) where
  BW : BuresWassersteinDatum
    (Matrix (Fin n) (Fin n) ℝ) (matrixPositiveDomain n)
  dist_symm : ∀ ρ σ : PositiveState (matrixPositiveDomain n),
    BW.dist ρ σ = BW.dist σ ρ

def BuresWassersteinStructure.distBW (sys : BuresWassersteinStructure n)
    (ρ σ : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sys.BW.dist (matrixPositiveState n ρ) (matrixPositiveState n σ)

/-- 🏆 THEOREM 1: Symmetry of the Bures-Wasserstein Distance -/
theorem buresWasserstein_symm (sys : BuresWassersteinStructure n) (ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℝ) :
    sys.distBW ρ₁ ρ₂ = sys.distBW ρ₂ ρ₁ :=
  sys.dist_symm _ _

/-- 🏆 THEOREM 2: Self-Nullity of the Bures-Wasserstein Distance -/
theorem buresWasserstein_self_zero (sys : BuresWassersteinStructure n) (ρ : Matrix (Fin n) (Fin n) ℝ) :
    sys.distBW ρ ρ = 0 :=
  sys.BW.dist_self _

/-- 🏆 THEOREM 3: Non-Negativity of the Bures-Wasserstein Metric -/
theorem buresWasserstein_nonneg (sys : BuresWassersteinStructure n) (ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ sys.distBW ρ₁ ρ₂ :=
  sys.BW.dist_nonneg _ _

/-- Normalized operator trace pairing.

This is defined for arbitrary finite matrix observables; no commutativity or
diagonalization hypothesis is part of the carrier.  It is a scalar readout of
the noncommutative product, not the quantum root fidelity.
-/
noncomputable def normalizedTracePairing (rho1 rho2 : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  trace (rho1 * rho2) / (trace rho1 * trace rho2)

/-- Compatibility name retained for downstream users of the old API. -/
noncomputable abbrev classicalFidelity {n : ℕ} :=
  normalizedTracePairing (n := n)

/-- Cyclic symmetry of the normalized trace pairing. -/
theorem normalizedTracePairing_symm (rho1 rho2 : Matrix (Fin n) (Fin n) ℝ) :
    normalizedTracePairing rho1 rho2 = normalizedTracePairing rho2 rho1 := by
  dsimp [normalizedTracePairing]
  rw [trace_mul_comm rho1 rho2]
  ring

/-- Compatibility theorem for the former API name. -/
theorem classicalFidelity_symm (rho1 rho2 : Matrix (Fin n) (Fin n) ℝ) :
    classicalFidelity rho1 rho2 = classicalFidelity rho2 rho1 :=
  normalizedTracePairing_symm rho1 rho2

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
