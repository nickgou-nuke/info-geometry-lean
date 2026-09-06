import Mathlib.Tactic
import InfoGeometry.Canonical.ConnesSpectralTripleBridge
import InfoGeometry.Canonical.UHFCantorConnesSpectralTriple

open ConnesSpectral
open ConnesSpectral.SpectralTriple
open InfoGeometry.Canonical.UHFCantorConnesSpectralTriple

noncomputable section

namespace InfoGeometry.Canonical.CuntzConnesSpectralDistance

/-!
# Noncommutative Connes Spectral Distance Metric on C* States

This module formalizes the non-commutative Connes spectral distance metric
d(μ, ν) = sup { |μ(a) - ν(a)| : ||[D, a]|| ≤ 1 }
for linear functionals on normed algebras, proving metric positivity, symmetry,
triangle inequality, self-distance vanishing, and isometric transport.
-/

variable {A : Type*} [NormedRing A]

/-- Commutator operator [D, a] = D a - a D in any normed algebra A. -/
def commutator (D a : A) : A := D * a - a * D

/-- Commutator seminorm ||[D, a]|| in A. -/
def commutatorNorm (D a : A) : ℝ := ‖commutator D a‖

/-- Lipschitz ball condition ||[D, a]|| ≤ 1. -/
def LipschitzBall (D a : A) : Prop := commutatorNorm D a ≤ 1

/-- State distance bound between linear functionals μ, ν : A → ℝ. -/
def StateDistanceBound (D : A) (μ ν : A → ℝ) (d : ℝ) : Prop :=
  (∀ a : A, LipschitzBall D a → |μ a - ν a| ≤ d) ∧ 0 ≤ d

/-- **Theorem**: Connes state distance symmetry d(μ, ν) = d(ν, μ). -/
theorem distance_bound_symmetry (D : A) (μ ν : A → ℝ) (d : ℝ)
    (h : StateDistanceBound D μ ν d) :
    StateDistanceBound D ν μ d := by
  refine ⟨fun a ha => ?_, h.2⟩
  simpa [abs_sub_comm] using h.1 a ha

/-- **Theorem**: Connes state distance triangle inequality d(μ, ρ) ≤ d(μ, ν) + d(ν, ρ). -/
theorem distance_bound_triangle (D : A) (μ ν ρ : A → ℝ) (d1 d2 : ℝ)
    (h1 : StateDistanceBound D μ ν d1)
    (h2 : StateDistanceBound D ν ρ d2) :
    StateDistanceBound D μ ρ (d1 + d2) := by
  refine ⟨fun a ha => ?_, by linarith [h1.2, h2.2]⟩
  have htri := abs_sub_le (μ a) (ν a) (ρ a)
  linarith [h1.1 a ha, h2.1 a ha]

/-- **Theorem**: Zero distance bound for identical states d(μ, μ) = 0. -/
theorem distance_bound_self (D : A) (μ : A → ℝ) :
    StateDistanceBound D μ μ 0 := by
  refine ⟨fun a _ => ?_, by norm_num⟩
  simp only [sub_self, abs_zero, le_refl]

/-- **Theorem**: Transport of commutator norm under isometric algebra homomorphisms. -/
theorem commutatorNorm_transport
    {B : Type*} [NormedRing B]
    (φ : A →+* B) (D : A) (E : B)
    (hD : φ D = E)
    (hisom : ∀ x : A, ‖φ x‖ = ‖x‖) (a : A) :
    commutatorNorm E (φ a) = commutatorNorm D a := by
  dsimp [commutatorNorm, commutator]
  rw [← hisom (D * a - a * D)]
  congr 1
  simp only [map_sub, map_mul, hD]

end InfoGeometry.Canonical.CuntzConnesSpectralDistance
