import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic

/-!
# `osp(1|2)` logarithmic-weight transport

This file proves the finite linear-algebra lemma behind transport of a
rank-two `L₀` Jordan pair by an odd operator of weight `1/2`.

No continuum limit, super-Virasoro representation, spin-chain integrability,
or existence of a nonzero fermionic partner is assumed.
-/

noncomputable section

namespace InfoGeometry.Algebra.OSp12LogarithmicTransport

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/--
If `[L₀,G] = (1/2)G`, then `G` sends an `L₀` eigenvector of weight `h` to an
eigenvector of weight `h + 1/2`.
-/
theorem map_eigenvector
    (L₀ G : Module.End ℂ V) (h : ℂ)
    (hcomm :
      L₀.comp G - G.comp L₀ = (1 / 2 : ℂ) • G)
    {φ : V} (hφ : L₀ φ = h • φ) :
    L₀ (G φ) = (h + 1 / 2) • G φ := by
  have hcommφ :
      L₀ (G φ) - G (L₀ φ) = (1 / 2 : ℂ) • G φ := by
    simpa using LinearMap.congr_fun hcomm φ
  rw [hφ, LinearMap.map_smul] at hcommφ
  have hsolve :
      L₀ (G φ) = (1 / 2 : ℂ) • G φ + h • G φ :=
    sub_eq_iff_eq_add.mp hcommφ
  calc
    L₀ (G φ) = (1 / 2 : ℂ) • G φ + h • G φ := hsolve
    _ = h • G φ + (1 / 2 : ℂ) • G φ := add_comm _ _
    _ = (h + 1 / 2) • G φ := (add_smul h (1 / 2 : ℂ) (G φ)).symm

/--
Under the same commutator law, `G` transports a rank-two generalized
eigenvector equation to the shifted fermionic sector.
-/
theorem map_jordan_partner
    (L₀ G : Module.End ℂ V) (h : ℂ)
    (hcomm :
      L₀.comp G - G.comp L₀ = (1 / 2 : ℂ) • G)
    {φ ψ : V}
    (hψ : L₀ ψ = h • ψ + φ) :
    L₀ (G ψ) = (h + 1 / 2) • G ψ + G φ := by
  have hcommψ :
      L₀ (G ψ) - G (L₀ ψ) = (1 / 2 : ℂ) • G ψ := by
    simpa using LinearMap.congr_fun hcomm ψ
  rw [hψ, LinearMap.map_add, LinearMap.map_smul] at hcommψ
  have hsolve :
      L₀ (G ψ) = (1 / 2 : ℂ) • G ψ + (h • G ψ + G φ) :=
    sub_eq_iff_eq_add.mp hcommψ
  calc
    L₀ (G ψ) = (1 / 2 : ℂ) • G ψ + (h • G ψ + G φ) := hsolve
    _ = (h • G ψ + (1 / 2 : ℂ) • G ψ) + G φ := by abel
    _ = (h + 1 / 2) • G ψ + G φ := by
      rw [add_smul]

/--
Combined finite logarithmic-supermultiplet transport.  The first component is
the shifted eigenvector equation and the second is its Jordan-partner equation.
-/
theorem map_jordan_pair
    (L₀ G : Module.End ℂ V) (h : ℂ)
    (hcomm :
      L₀.comp G - G.comp L₀ = (1 / 2 : ℂ) • G)
    {φ ψ : V}
    (hφ : L₀ φ = h • φ)
    (hψ : L₀ ψ = h • ψ + φ) :
    L₀ (G φ) = (h + 1 / 2) • G φ ∧
      L₀ (G ψ) = (h + 1 / 2) • G ψ + G φ :=
  ⟨map_eigenvector L₀ G h hcomm hφ,
    map_jordan_partner L₀ G h hcomm hψ⟩

end InfoGeometry.Algebra.OSp12LogarithmicTransport
