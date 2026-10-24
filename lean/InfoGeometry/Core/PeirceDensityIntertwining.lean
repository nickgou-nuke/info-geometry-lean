/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceWeylUnits
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Division-free density and weighted-trace intertwining

The scalar weights are arbitrary. A tracial linear functional is not silently
assumed positive or normalized. The theorems are algebraic boundary identities,
not an analytic KMS condition or a construction of a modular automorphism group.
-/

namespace InfoGeometry.Core.PeirceDensityIntertwining

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable {R A : Type*} [CommRing R] [Ring A] [StarRing A] [Algebra R A]

/-- The source note's weight, generalized from squared to arbitrary scalars. -/
def density (d b : A) (u v : R) : A :=
  u • coexactSupport d b + v • exactSupport d b

/-- Weight an arbitrary linear functional on the left by the density. -/
def weightedTrace (τ : A →ₗ[R] R) (ρ x : A) : R := τ (ρ * x)

variable {d b : A}

/-- Four scalar eigen-relations; no division or invertibility is required. -/
theorem density_actions (h : IsMoorePenroseInverse d b) (hd : d * d = 0)
    (u v : R) :
    density d b u v * d = v • d ∧ d * density d b u v = u • d ∧
    density d b u v * b = u • b ∧ b * density d b u v = v • b := by
  rcases partial_matrix_unit_identities h hd with ⟨⟨hpd, hdq, hdp, hqd⟩,
    ⟨hqb, hbp, hbq, hpb⟩, _⟩
  simp only [density, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hpd, hdq, hdp, hqd, hqb, hbp, hbq, hpb, smul_zero, zero_add, add_zero,
    and_self]

/-- Cross-multiplication avoids division and remains valid at zero weights. -/
theorem density_intertwining (h : IsMoorePenroseInverse d b) (hd : d * d = 0)
    (u v : R) :
    u • (density d b u v * d) = v • (d * density d b u v) ∧
    v • (density d b u v * b) = u • (b * density d b u v) := by
  rcases density_actions h hd u v with ⟨h₁, h₂, h₃, h₄⟩
  rw [h₁, h₂, h₃, h₄]
  simp only [smul_smul, mul_comm u v, and_self]

/-- The source's two squared-parameter identities, without a new pair predicate. -/
theorem squared_density_intertwining
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) (u v : R) :
    (u * u) • (density d b (u * u) (v * v) * d) =
      (v * v) • (d * density d b (u * u) (v * v)) ∧
    (v * v) • (density d b (u * u) (v * v) * b) =
      (u * u) • (b * density d b (u * u) (v * v)) :=
  density_intertwining h hd (u * u) (v * v)

/-- Pass an algebraic cross-intertwining law through an actually tracial map. -/
theorem weighted_trace_of_intertwining
    (τ : A →ₗ[R] R) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    {ρ x : A} {u v : R} (h : u • (ρ * x) = v • (x * ρ)) (y : A) :
    u * weightedTrace τ ρ (x * y) = v * weightedTrace τ ρ (y * x) := by
  have ht := congrArg τ (congrArg (fun z : A => z * y) h)
  simp only [smul_mul_assoc, map_smul, smul_eq_mul] at ht
  unfold weightedTrace
  calc
    u * τ (ρ * (x * y)) = u * τ ((ρ * x) * y) := by rw [mul_assoc]
    _ = v * τ ((x * ρ) * y) := ht
    _ = v * τ (ρ * (y * x)) := by rw [mul_assoc, hτ x (ρ * y), mul_assoc]

/-- Both directed weighted-trace boundary laws in the same convention. -/
theorem density_trace_boundary
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0)
    (τ : A →ₗ[R] R) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    (u v : R) (y : A) :
    u * weightedTrace τ (density d b u v) (d * y) =
      v * weightedTrace τ (density d b u v) (y * d) ∧
    v * weightedTrace τ (density d b u v) (b * y) =
      u * weightedTrace τ (density d b u v) (y * b) := by
  exact ⟨weighted_trace_of_intertwining τ hτ (density_intertwining h hd u v).1 y,
    weighted_trace_of_intertwining τ hτ (density_intertwining h hd u v).2 y⟩

/-- Merely squaring arbitrary ring scalars does not establish order positivity. -/
theorem density_harmonic_annihilation
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) (u v : R) :
    density d b u v * harmonicSupport d b = 0 ∧
    harmonicSupport d b * density d b u v = 0 := by
  constructor
  · simp only [density, add_mul, smul_mul_assoc,
      h.coexactSupport_mul_harmonicSupport hd, h.exactSupport_mul_harmonicSupport hd,
      smul_zero, add_zero]
  · simp only [density, mul_add, mul_smul_comm,
      h.harmonicSupport_mul_coexactSupport hd, h.harmonicSupport_mul_exactSupport hd,
      smul_zero, add_zero]

end InfoGeometry.Core.PeirceDensityIntertwining
