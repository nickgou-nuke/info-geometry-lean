import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.LocalToHodgeBridge

Minimal conditional bridge from local square-zero operators to global
Hodge-style operator identities.

This file is theorem-only:
- no wrapper structures
- no certificates
- explicit hypotheses only
-/

namespace LocalToHodgeBridge

/--
If `d` is square-zero, restate it as a theorem-level fact.
-/
@[rep_depth thermo]
theorem d_sq_zero
    {R V : Type*}
    [Ring R] [AddCommGroup V] [Module R V]
    (d : Module.End R V)
    (hd2 : d * d = 0) :
    d * d = 0 := hd2

/--
If `δ` is square-zero, restate it as a theorem-level fact.
-/
@[rep_depth thermo]
theorem delta_sq_zero
    {R V : Type*}
    [Ring R] [AddCommGroup V] [Module R V]
    (δ : Module.End R V)
    (hδ2 : δ * δ = 0) :
    δ * δ = 0 := hδ2

/--
Laplacian definition in operator form:

`Δ = d*δ + δ*d`.
-/
@[rep_depth thermo]
theorem laplacian_def
    {R V : Type*}
    [Ring R] [AddCommGroup V] [Module R V]
    (d δ Δ : Module.End R V)
    (hΔ : Δ = d * δ + δ * d) :
    Δ = d * δ + δ * d := hΔ

/--
From `d^2 = 0` and `Δ = d*δ + δ*d`, `d` commutes with `Δ`:

`d*Δ = Δ*d`.
-/
@[rep_depth thermo]
theorem comm_d_laplacian
    {R V : Type*}
    [Ring R] [AddCommGroup V] [Module R V]
    (d δ Δ : Module.End R V)
    (hd2 : d * d = 0)
    (hΔ : Δ = d * δ + δ * d) :
    d * Δ = Δ * d := by
  have hleft : d * Δ = d * δ * d := by
    calc
      d * Δ = d * (d * δ + δ * d) := by simpa [hΔ]
      _ = d * (d * δ) + d * (δ * d) := by rw [mul_add]
      _ = ((d * d) * δ) + d * (δ * d) := by rw [mul_assoc]
      _ = d * (δ * d) := by rw [hd2, zero_mul, zero_add]
      _ = d * δ * d := by rw [mul_assoc]
  have hright : Δ * d = d * δ * d := by
    calc
      Δ * d = (d * δ + δ * d) * d := by simpa [hΔ]
      _ = (d * δ) * d + (δ * d) * d := by rw [add_mul]
      _ = (d * δ) * d + δ * (d * d) := by rw [mul_assoc δ d d]
      _ = (d * δ) * d + δ * 0 := by rw [hd2]
      _ = (d * δ) * d := by rw [mul_zero, add_zero]
      _ = d * δ * d := by rw [mul_assoc]
  exact hleft.trans hright.symm

/--
From `δ^2 = 0` and `Δ = d*δ + δ*d`, `δ` commutes with `Δ`:

`δ*Δ = Δ*δ`.
-/
@[rep_depth thermo]
theorem comm_delta_laplacian
    {R V : Type*}
    [Ring R] [AddCommGroup V] [Module R V]
    (d δ Δ : Module.End R V)
    (hδ2 : δ * δ = 0)
    (hΔ : Δ = d * δ + δ * d) :
    δ * Δ = Δ * δ := by
  have hleft : δ * Δ = δ * d * δ := by
    calc
      δ * Δ = δ * (d * δ + δ * d) := by simpa [hΔ]
      _ = δ * (d * δ) + δ * (δ * d) := by rw [mul_add]
      _ = δ * (d * δ) + (δ * δ) * d := by rw [mul_assoc]
      _ = δ * (d * δ) := by rw [hδ2, zero_mul, add_zero]
      _ = δ * d * δ := by rw [mul_assoc]
  have hright : Δ * δ = δ * d * δ := by
    calc
      Δ * δ = (d * δ + δ * d) * δ := by simpa [hΔ]
      _ = (d * δ) * δ + (δ * d) * δ := by rw [add_mul]
      _ = d * (δ * δ) + (δ * d) * δ := by rw [mul_assoc]
      _ = d * 0 + (δ * d) * δ := by rw [hδ2]
      _ = (δ * d) * δ := by rw [mul_zero, zero_add]
      _ = δ * d * δ := by rw [mul_assoc]
  exact hleft.trans hright.symm

end LocalToHodgeBridge
