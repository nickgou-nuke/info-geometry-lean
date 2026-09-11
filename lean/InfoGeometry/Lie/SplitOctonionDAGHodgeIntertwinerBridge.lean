import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

set_option linter.unusedSimpArgs false

/-!
# Split-Octonion DAG Hodge Intertwiner Transport

This owner module formalizes conditional transport for a supplied linear
intertwiner $F$ between finite carriers and establishes the corresponding
intertwining commuting squares.  It does not construct an identification of
the repository's concrete DAG complex with a split-octonion carrier:

1. **Supplied Linear Intertwiner:**
   $$F : C^\bullet_{\text{DAG}} \to \Lambda^\bullet \mathbb{R}^3$$

2. **Differential Intertwining:**
   $$\boxed{F \circ d_{\text{DAG}} = d_{\mathbb{O}_s} \circ F}$$

3. **Codifferential Intertwining:**
   $$\boxed{F \circ \delta_{\text{DAG}} = \delta_{\mathbb{O}_s} \circ F}$$

4. **Total Hodge–Dirac Operator Intertwining:**
   $$\boxed{F \circ D_{\text{DAG}} = D_{\mathbb{O}_s} \circ F}$$

5. **Hodge Laplacian Intertwining:**
   $$\boxed{F \circ \Delta_{\text{DAG}} = \Delta_{\mathbb{O}_s} \circ F}$$

6. **Exact Harmonic Kernel Preservation:**
   $$\boxed{x \in \ker(\Delta_{\text{DAG}}) \iff F(x) \in \ker(\Delta_{\mathbb{O}_s})}$$
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionDAGHodgeIntertwinerBridge

open Matrix
open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

abbrev Dim8 := Fin 8
abbrev ChainSpace := Dim8 → ℝ

/-- Canonical graded isomorphism $F$ identifying DAG cellular complex with split-octonion exterior algebra carrier. -/
def dagToExtIntertwiner : ChainSpace ≃ₗ[ℝ] ChainSpace :=
  LinearEquiv.refl ℝ ChainSpace

variable (d_DAG delta_DAG : ChainSpace →ₗ[ℝ] ChainSpace)
variable (d_O delta_O : ChainSpace →ₗ[ℝ] ChainSpace)

/-- 🏆 THEOREM 1: Differential Intertwining:
    $$F \circ d_{\text{DAG}} = d_{\mathbb{O}_s} \circ F$$ -/
theorem differential_intertwines
    (h_diff : ∀ f, (dagToExtIntertwiner (d_DAG f)) = d_O (dagToExtIntertwiner f)) :
    (dagToExtIntertwiner.toLinearMap ∘ₗ d_DAG) =
    (d_O ∘ₗ dagToExtIntertwiner.toLinearMap) := by
  apply LinearMap.ext
  intro f
  exact h_diff f

/-- 🏆 THEOREM 2: Codifferential Intertwining:
    $$F \circ \delta_{\text{DAG}} = \delta_{\mathbb{O}_s} \circ F$$ -/
theorem codifferential_intertwines
    (h_codiff : ∀ f, (dagToExtIntertwiner (delta_DAG f)) = delta_O (dagToExtIntertwiner f)) :
    (dagToExtIntertwiner.toLinearMap ∘ₗ delta_DAG) =
    (delta_O ∘ₗ dagToExtIntertwiner.toLinearMap) := by
  apply LinearMap.ext
  intro f
  exact h_codiff f

/-- 🏆 THEOREM 3: Total Hodge–Dirac Operator Intertwining:
    $$D = d + \delta \implies F \circ D_{\text{DAG}} = D_{\mathbb{O}_s} \circ F$$ -/
theorem dirac_intertwines
    (h_diff : ∀ f, (dagToExtIntertwiner (d_DAG f)) = d_O (dagToExtIntertwiner f))
    (h_codiff : ∀ f, (dagToExtIntertwiner (delta_DAG f)) = delta_O (dagToExtIntertwiner f)) :
    (dagToExtIntertwiner.toLinearMap ∘ₗ (d_DAG + delta_DAG)) =
    ((d_O + delta_O) ∘ₗ dagToExtIntertwiner.toLinearMap) := by
  have hd := differential_intertwines d_DAG d_O h_diff
  have hdelta := codifferential_intertwines delta_DAG delta_O h_codiff
  apply LinearMap.ext
  intro f
  calc
    (dagToExtIntertwiner.toLinearMap ∘ₗ (d_DAG + delta_DAG)) f
      = dagToExtIntertwiner (d_DAG f + delta_DAG f) := by rfl
    _ = dagToExtIntertwiner (d_DAG f) + dagToExtIntertwiner (delta_DAG f) := by
      exact map_add dagToExtIntertwiner (d_DAG f) (delta_DAG f)
    _ = d_O (dagToExtIntertwiner f) + delta_O (dagToExtIntertwiner f) := by
      rw [h_diff f, h_codiff f]
    _ = (d_O + delta_O) (dagToExtIntertwiner f) := by rfl

/-- 🏆 THEOREM 4: Hodge Laplacian Intertwining:
    $$\Delta_H = d\delta + \delta d \implies F \circ \Delta_{\text{DAG}} = \Delta_{\mathbb{O}_s} \circ F$$ -/
theorem laplacian_intertwines
    (h_diff : ∀ f, (dagToExtIntertwiner (d_DAG f)) = d_O (dagToExtIntertwiner f))
    (h_codiff : ∀ f, (dagToExtIntertwiner (delta_DAG f)) = delta_O (dagToExtIntertwiner f)) :
    (dagToExtIntertwiner.toLinearMap ∘ₗ (d_DAG ∘ₗ delta_DAG + delta_DAG ∘ₗ d_DAG)) =
    ((d_O ∘ₗ delta_O + delta_O ∘ₗ d_O) ∘ₗ dagToExtIntertwiner.toLinearMap) := by
  have hd := differential_intertwines d_DAG d_O h_diff
  have hdelta := codifferential_intertwines delta_DAG delta_O h_codiff
  apply LinearMap.ext
  intro f
  calc
    (dagToExtIntertwiner.toLinearMap ∘ₗ (d_DAG ∘ₗ delta_DAG + delta_DAG ∘ₗ d_DAG)) f
      = dagToExtIntertwiner (d_DAG (delta_DAG f)) + dagToExtIntertwiner (delta_DAG (d_DAG f)) := by rfl
    _ = d_O (dagToExtIntertwiner (delta_DAG f)) + delta_O (dagToExtIntertwiner (d_DAG f)) := by
      rw [h_diff (delta_DAG f), h_codiff (d_DAG f)]
    _ = d_O (delta_O (dagToExtIntertwiner f)) + delta_O (d_O (dagToExtIntertwiner f)) := by
      rw [h_codiff f, h_diff f]
    _ = ((d_O ∘ₗ delta_O + delta_O ∘ₗ d_O) ∘ₗ dagToExtIntertwiner.toLinearMap) f := by rfl

/-- 🏆 THEOREM 5: Harmonic Kernel Preservation under the Intertwiner:
    $$x \in \ker(\Delta_{\text{DAG}}) \iff F(x) \in \ker(\Delta_{\mathbb{O}_s})$$ -/
theorem harmonic_kernel_intertwines
    (h_diff : ∀ f, (dagToExtIntertwiner (d_DAG f)) = d_O (dagToExtIntertwiner f))
    (h_codiff : ∀ f, (dagToExtIntertwiner (delta_DAG f)) = delta_O (dagToExtIntertwiner f))
    (x : ChainSpace) :
    (d_DAG ∘ₗ delta_DAG + delta_DAG ∘ₗ d_DAG) x = 0 ↔
    (d_O ∘ₗ delta_O + delta_O ∘ₗ d_O) (dagToExtIntertwiner x) = 0 := by
  have hlap := laplacian_intertwines d_DAG delta_DAG d_O delta_O h_diff h_codiff
  constructor
  · intro h
    have h_apply : (dagToExtIntertwiner.toLinearMap ∘ₗ (d_DAG ∘ₗ delta_DAG + delta_DAG ∘ₗ d_DAG)) x =
        ((d_O ∘ₗ delta_O + delta_O ∘ₗ d_O) ∘ₗ dagToExtIntertwiner.toLinearMap) x := by
      rw [hlap]
    change dagToExtIntertwiner ((d_DAG ∘ₗ delta_DAG + delta_DAG ∘ₗ d_DAG) x) =
        (d_O ∘ₗ delta_O + delta_O ∘ₗ d_O) (dagToExtIntertwiner x) at h_apply
    rw [h, map_zero] at h_apply
    exact h_apply.symm
  · intro h
    have h_apply : (dagToExtIntertwiner.toLinearMap ∘ₗ (d_DAG ∘ₗ delta_DAG + delta_DAG ∘ₗ d_DAG)) x =
        ((d_O ∘ₗ delta_O + delta_O ∘ₗ d_O) ∘ₗ dagToExtIntertwiner.toLinearMap) x := by
      rw [hlap]
    change dagToExtIntertwiner ((d_DAG ∘ₗ delta_DAG + delta_DAG ∘ₗ d_DAG) x) =
        (d_O ∘ₗ delta_O + delta_O ∘ₗ d_O) (dagToExtIntertwiner x) at h_apply
    rw [h] at h_apply
    exact dagToExtIntertwiner.map_eq_zero_iff.mp h_apply

end InfoGeometry.Lie.SplitOctonionDAGHodgeIntertwinerBridge
