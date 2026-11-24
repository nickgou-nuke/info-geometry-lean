/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.JordanAssociatorRing
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Data.Real.Basic

/-!
# Pairing identities from represented Clifford anticommutators

An explicitly supplied scalar anticommutator relation lets us reflect two
associative-algebra identities back to a real-valued pairing. Ordinary unit
conjugation preserves that pairing when it intertwines a supplied vector map;
an inner commutator is skew for the pairing when it intertwines a supplied
vector map.

The pairing is kept as `V → V → ℝ`: the proofs use only its displayed
anticommutator relation, so a native bilinear form can be supplied by coercion.
The two pairing results do not require injectivity of the vector lift or
linearity of the supplied vector maps. Separate constructions derive their
linearity when the lift is injective. No group action, bijectivity, smooth
vector field, or trajectory conservation is asserted.

The commutator calculation reuses `commutator_symm_leibniz` from the existing
ring-level Jordan owner. All products remain in the arbitrary associative
real algebra `B`.
-/

namespace InfoGeometry.Clifford.AnticommutatorSymmetry

variable {V B : Type*} [AddCommGroup V] [Module ℝ V] [Ring B] [Algebra ℝ B]

section Pairing

variable [Nontrivial B]

/-- Ordinary unit conjugation preserves a scalar Clifford pairing under the
explicit intertwining equation. The vector map is allowed to be a function. -/
theorem pairing_eq_of_unit_conjugation_intertwining
    (ι : V →ₗ[ℝ] B) (η : V → V → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hCl : ∀ u v : V, ι u * ι v + ι v * ι u = (c * η u v) • (1 : B))
    (g : Bˣ) (Λ : V → V)
    (hΛ : ∀ u : V, (g : B) * ι u * (↑(g⁻¹) : B) = ι (Λ u))
    (u v : V) : η (Λ u) (Λ v) = η u v := by
  have hscalar : (c * η (Λ u) (Λ v)) • (1 : B) =
      (c * η u v) • (1 : B) := by
    calc
      (c * η (Λ u) (Λ v)) • (1 : B) =
          ι (Λ u) * ι (Λ v) + ι (Λ v) * ι (Λ u) := (hCl _ _).symm
      _ = ((g : B) * ι u * (↑(g⁻¹) : B)) *
            ((g : B) * ι v * (↑(g⁻¹) : B)) +
          ((g : B) * ι v * (↑(g⁻¹) : B)) *
            ((g : B) * ι u * (↑(g⁻¹) : B)) := by rw [hΛ u, hΛ v]
      _ = (g : B) * (ι u * ι v + ι v * ι u) * (↑(g⁻¹) : B) := by
        simp only [mul_add, add_mul, mul_assoc, Units.inv_mul_cancel_left]
      _ = (g : B) * ((c * η u v) • (1 : B)) * (↑(g⁻¹) : B) := by
        rw [hCl u v]
      _ = (c * η u v) • (1 : B) := by
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
          mul_one, Units.mul_inv]
  exact mul_left_cancel₀ hc
    (smul_left_injective ℝ (one_ne_zero : (1 : B) ≠ 0) hscalar)

/-- Intertwining an inner commutator makes the supplied vector map skew for
the scalar Clifford pairing. This is an algebraic identity for two vectors. -/
theorem pairing_skew_of_commutator_intertwining
    (ι : V →ₗ[ℝ] B) (η : V → V → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hCl : ∀ u v : V, ι u * ι v + ι v * ι u = (c * η u v) • (1 : B))
    (K : B) (ξ : V → V)
    (hξ : ∀ u : V, K * ι u - ι u * K = ι (ξ u))
    (u v : V) : η (ξ u) v + η u (ξ v) = 0 := by
  have hzero : (c * (η (ξ u) v + η u (ξ v))) • (1 : B) = 0 := by
    calc
      (c * (η (ξ u) v + η u (ξ v))) • (1 : B) =
          (c * η (ξ u) v) • (1 : B) +
            (c * η u (ξ v)) • (1 : B) := by rw [mul_add, add_smul]
      _ = (ι (ξ u) * ι v + ι v * ι (ξ u)) +
          (ι u * ι (ξ v) + ι (ξ v) * ι u) := by
        rw [hCl (ξ u) v, hCl u (ξ v)]
      _ = ((K * ι u - ι u * K) * ι v + ι v * (K * ι u - ι u * K)) +
          (ι u * (K * ι v - ι v * K) + (K * ι v - ι v * K) * ι u) := by
        rw [hξ u, hξ v]
      _ = K * (ι u * ι v + ι v * ι u) - (ι u * ι v + ι v * ι u) * K :=
        (InfoGeometry.Core.JordanAssociator.commutator_symm_leibniz
          K (ι u) (ι v)).symm
      _ = K * ((c * η u v) • (1 : B)) -
          ((c * η u v) • (1 : B)) * K := by rw [hCl u v]
      _ = 0 := by
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
          mul_one, one_mul, sub_self]
  have hscalar : c * (η (ξ u) v + η u (ξ v)) = 0 :=
    (smul_eq_zero.mp hzero).resolve_right one_ne_zero
  exact (mul_eq_zero.mp hscalar).resolve_left hc

end Pairing

/-- A function intertwined by an injective lift with ordinary unit
conjugation is linear. The closure equation alone need not make it surjective. -/
def linearMapOfUnitConjugationIntertwining
    (ι : V →ₗ[ℝ] B) (hι : Function.Injective ι)
    (g : Bˣ) (Λ : V → V)
    (hΛ : ∀ u : V, (g : B) * ι u * (↑(g⁻¹) : B) = ι (Λ u)) :
    Module.End ℝ V where
  toFun := Λ
  map_add' u v := by
    apply hι
    calc
      ι (Λ (u + v)) = (g : B) * ι (u + v) * (↑(g⁻¹) : B) := (hΛ _).symm
      _ = (g : B) * ι u * (↑(g⁻¹) : B) +
          (g : B) * ι v * (↑(g⁻¹) : B) := by rw [map_add, mul_add, add_mul]
      _ = ι (Λ u + Λ v) := by rw [hΛ u, hΛ v, map_add]
  map_smul' r u := by
    apply hι
    change ι (Λ (r • u)) = ι (r • Λ u)
    calc
      ι (Λ (r • u)) = (g : B) * ι (r • u) * (↑(g⁻¹) : B) := (hΛ _).symm
      _ = r • ((g : B) * ι u * (↑(g⁻¹) : B)) := by
        rw [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      _ = ι (r • Λ u) := by rw [hΛ u, map_smul]

/-- A function intertwined by an injective lift with an inner commutator
is linear, with both linearity laws derived from the intertwining equation. -/
def linearMapOfCommutatorIntertwining
    (ι : V →ₗ[ℝ] B) (hι : Function.Injective ι)
    (K : B) (ξ : V → V)
    (hξ : ∀ u : V, K * ι u - ι u * K = ι (ξ u)) :
    Module.End ℝ V where
  toFun := ξ
  map_add' u v := by
    apply hι
    calc
      ι (ξ (u + v)) = K * ι (u + v) - ι (u + v) * K := (hξ _).symm
      _ = (K * ι u - ι u * K) + (K * ι v - ι v * K) := by
        rw [map_add]
        noncomm_ring
      _ = ι (ξ u + ξ v) := by rw [hξ u, hξ v, map_add]
  map_smul' r u := by
    apply hι
    change ι (ξ (r • u)) = ι (r • ξ u)
    calc
      ι (ξ (r • u)) = K * ι (r • u) - ι (r • u) * K := (hξ _).symm
      _ = r • (K * ι u - ι u * K) := by
        rw [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
      _ = ι (r • ξ u) := by rw [hξ u, map_smul]

end InfoGeometry.Clifford.AnticommutatorSymmetry
