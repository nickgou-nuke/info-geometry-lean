import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds

namespace InfoGeometry.Topology.NonOrientableEP

/-- Coordinates in the Brillouin Zone -/
structure Momentum where
  kx : ℝ
  ky : ℝ

/-- The action of glide symmetry on momentum space -/
noncomputable def glide (k : Momentum) : Momentum :=
  { kx := -k.kx, ky := k.ky + Real.pi }

/-- An abstract 2-band Hamiltonian -/
structure TwoBandHamiltonian where
  dx : Momentum → ℂ
  dy : Momentum → ℂ

/-- A Hamiltonian satisfies the Klein Brillouin Zone glide symmetry if it is invariant under the glide operation -/
def is_KBZ_symmetric (H : TwoBandHamiltonian) : Prop :=
  ∀ k, H.dx (glide k) = H.dx k ∧ H.dy (glide k) = H.dy k

/-- An Exceptional Point occurs when the eigenvalues coalesce (d_x^2 + d_y^2 = 0) without vanishing completely (H != 0) -/
def is_exceptional_point (H : TwoBandHamiltonian) (k : Momentum) : Prop :=
  (H.dx k)^2 + (H.dy k)^2 = 0 ∧ (H.dx k ≠ 0 ∨ H.dy k ≠ 0)

/-- The specific parameterization from the Drazin digest -/
noncomputable def dx_model (α : ℝ) (k : Momentum) : ℂ :=
  (Real.cos k.kx : ℂ) + (Complex.I * (α : ℂ))

noncomputable def dy_model (β γ : ℝ) (k : Momentum) : ℂ :=
  - (Real.sin k.kx : ℂ) * (((1 - γ) * Real.sin k.ky + γ * Real.cos k.ky) : ℂ) - (0.5 : ℂ) + (Complex.I * (β : ℂ))

noncomputable def H_model (α β γ : ℝ) : TwoBandHamiltonian :=
  { dx := dx_model α,
    dy := dy_model β γ }

/-- Theorem: The model Hamiltonian satisfies the Klein Brillouin Zone glide symmetry. -/
theorem model_is_KBZ_symmetric (α β γ : ℝ) : is_KBZ_symmetric (H_model α β γ) := by
  dsimp [is_KBZ_symmetric, H_model, glide, dx_model, dy_model]
  intro k
  have hdx : (Real.cos (-k.kx) : ℂ) + Complex.I * (α : ℂ) = (Real.cos k.kx : ℂ) + Complex.I * (α : ℂ) := by
    simp
  have hdy : (-(Real.sin (-k.kx) : ℂ) * (((1 - γ) * Real.sin (k.ky + Real.pi) + γ * Real.cos (k.ky + Real.pi)) : ℂ) - (0.5 : ℂ) + Complex.I * (β : ℂ)) =
      (-(Real.sin k.kx : ℂ) * (((1 - γ) * Real.sin k.ky + γ * Real.cos k.ky) : ℂ) - (0.5 : ℂ) + Complex.I * (β : ℂ)) := by
    simp [Real.sin_neg, Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi]
    ring
  exact And.intro hdx hdy

end InfoGeometry.Topology.NonOrientableEP
