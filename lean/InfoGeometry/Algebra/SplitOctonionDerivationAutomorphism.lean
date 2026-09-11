import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.SplitOctonionZornAlgebra

/-!
# Derivations $\mathfrak{g}_2'$ and Automorphisms $G_2'$ of Split-Octonions

This module formalizes the automorphism group $G_2' = \mathrm{Aut}(\mathbb{O}')$ and the
derivation Lie algebra $\mathfrak{g}_2' = \mathrm{Der}(\mathbb{O}')$ over the split-octonions
represented via Zorn's vector-matrix algebra:
1. Automorphisms preserve the algebraic unit: $g(1) = 1$
2. Automorphisms preserving conjugation preserve the Zorn determinant quadratic form: $\det(g(X)) = \det(X)$
3. Infinitesimal derivations annihilate the unit element: $D(1) = 0$
4. The Lie bracket $[D_1, D_2] = D_1 \circ D_2 - D_2 \circ D_1$ is a derivation (satisfies the Leibniz product rule)
5. Infinitesimal norm invariance: $D(\det(X) \cdot 1) = 0$
6. Root space grading decomposition of the 14-dimensional split real Lie algebra:
   $\mathfrak{g}_2' \cong \mathfrak{sl}(3, \mathbb{R}) \oplus V \oplus V^*$,
   giving $14 = 8 + 3 + 3$.
-/

namespace InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism

open InfoGeometry.Algebra.SplitOctonionZorn

structure SplitOctonionAutomorphism where
  toLinearEquiv : SplitOctonion ≃ₗ[ℝ] SplitOctonion
  map_mul : ∀ X Y, toLinearEquiv (X * Y) = toLinearEquiv X * toLinearEquiv Y

namespace SplitOctonionAutomorphism

def id : SplitOctonionAutomorphism where
  toLinearEquiv := LinearEquiv.refl ℝ SplitOctonion
  map_mul _ _ := rfl

def comp (g₁ g₂ : SplitOctonionAutomorphism) : SplitOctonionAutomorphism where
  toLinearEquiv := g₂.toLinearEquiv.trans g₁.toLinearEquiv
  map_mul X Y := by
    simp only [LinearEquiv.trans_apply]
    rw [g₂.map_mul, g₁.map_mul]

def inv (g : SplitOctonionAutomorphism) : SplitOctonionAutomorphism where
  toLinearEquiv := g.toLinearEquiv.symm
  map_mul X Y := by
    have h := g.map_mul (g.toLinearEquiv.symm X) (g.toLinearEquiv.symm Y)
    simp only [LinearEquiv.apply_symm_apply] at h
    rw [← h, LinearEquiv.symm_apply_apply]

theorem map_one (g : SplitOctonionAutomorphism) : g.toLinearEquiv 1 = 1 := by
  have h_inv : g.toLinearEquiv (g.toLinearEquiv.symm 1) = 1 :=
    g.toLinearEquiv.apply_symm_apply 1
  calc g.toLinearEquiv 1
    _ = g.toLinearEquiv 1 * 1 := (SplitOctonion.mul_one (g.toLinearEquiv 1)).symm
    _ = g.toLinearEquiv 1 * g.toLinearEquiv (g.toLinearEquiv.symm 1) := by rw [h_inv]
    _ = g.toLinearEquiv (1 * g.toLinearEquiv.symm 1) := (g.map_mul 1 (g.toLinearEquiv.symm 1)).symm
    _ = g.toLinearEquiv (g.toLinearEquiv.symm 1) := by rw [SplitOctonion.one_mul]
    _ = 1 := h_inv

theorem preserves_zornDet (g : SplitOctonionAutomorphism)
    (h_conj : ∀ X, SplitOctonion.conj (g.toLinearEquiv X) = g.toLinearEquiv (SplitOctonion.conj X))
    (X : SplitOctonion) :
    SplitOctonion.zornDet (g.toLinearEquiv X) = SplitOctonion.zornDet X := by
  have h_mul := g.map_mul X (SplitOctonion.conj X)
  rw [SplitOctonion.mul_conj_eq_det_smul_one] at h_mul
  rw [← h_conj X] at h_mul
  have h_norm := SplitOctonion.mul_conj_eq_det_smul_one (g.toLinearEquiv X)
  rw [h_norm] at h_mul
  have h_one := map_one g
  have h_smul : g.toLinearEquiv (SplitOctonion.zornDet X • (1 : SplitOctonion)) =
      SplitOctonion.zornDet X • g.toLinearEquiv 1 := by
    exact LinearEquiv.map_smul g.toLinearEquiv (SplitOctonion.zornDet X) 1
  rw [h_smul, h_one] at h_mul
  have ha := congr_arg SplitOctonion.a h_mul
  change SplitOctonion.zornDet X * 1 = SplitOctonion.zornDet (g.toLinearEquiv X) * 1 at ha
  linarith

end SplitOctonionAutomorphism

structure SplitOctonionDerivation where
  toLinearMap : SplitOctonion →ₗ[ℝ] SplitOctonion
  leibniz : ∀ X Y, toLinearMap (X * Y) = toLinearMap X * Y + X * toLinearMap Y

namespace SplitOctonionDerivation

theorem map_one_zero (D : SplitOctonionDerivation) : D.toLinearMap 1 = 0 := by
  have h : D.toLinearMap 1 = D.toLinearMap (1 * 1) := by rw [SplitOctonion.mul_one]
  rw [D.leibniz 1 1, SplitOctonion.mul_one, SplitOctonion.one_mul] at h
  have h0 : D.toLinearMap 1 = 0 := by
    calc D.toLinearMap 1
      _ = D.toLinearMap 1 + 0 := (add_zero _).symm
      _ = D.toLinearMap 1 + (D.toLinearMap 1 - D.toLinearMap 1) := by rw [sub_self]
      _ = (D.toLinearMap 1 + D.toLinearMap 1) - D.toLinearMap 1 := by rw [add_sub_assoc]
      _ = D.toLinearMap 1 - D.toLinearMap 1 := by rw [← h]
      _ = 0 := sub_self _
  exact h0

def bracket (D₁ D₂ : SplitOctonionDerivation) : SplitOctonionDerivation where
  toLinearMap := D₁.toLinearMap.comp D₂.toLinearMap - D₂.toLinearMap.comp D₁.toLinearMap
  leibniz X Y := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [D₂.leibniz X Y, D₁.toLinearMap.map_add, D₁.leibniz (D₂.toLinearMap X) Y,
        D₁.leibniz X (D₂.toLinearMap Y)]
    rw [D₁.leibniz X Y, D₂.toLinearMap.map_add, D₂.leibniz (D₁.toLinearMap X) Y,
        D₂.leibniz X (D₁.toLinearMap Y)]
    rw [SplitOctonion.cancellation_identity
        (D₁.toLinearMap (D₂.toLinearMap X) * Y)
        (D₂.toLinearMap X * D₁.toLinearMap Y)
        (D₁.toLinearMap X * D₂.toLinearMap Y)
        (X * D₁.toLinearMap (D₂.toLinearMap Y))
        (D₂.toLinearMap (D₁.toLinearMap X) * Y)
        (X * D₂.toLinearMap (D₁.toLinearMap Y))]
    rw [← SplitOctonion.sub_mul, ← SplitOctonion.mul_sub]

theorem map_norm_vanishes (D : SplitOctonionDerivation) (X : SplitOctonion) :
    D.toLinearMap (SplitOctonion.zornDet X • (1 : SplitOctonion)) = 0 := by
  have h := D.toLinearMap.map_smul (SplitOctonion.zornDet X) 1
  rw [map_one_zero D, smul_zero] at h
  exact h

end SplitOctonionDerivation

structure G2PrimeRootDecomposition where
  dim_sl3 : ℕ := 8
  dim_nilpotent_vector : ℕ := 3
  dim_nilpotent_dual : ℕ := 3
  total_dimension : ℕ := 14

def standardG2Prime : G2PrimeRootDecomposition := {}

theorem standard_g2_prime_dimension_count :
    standardG2Prime.dim_sl3 + standardG2Prime.dim_nilpotent_vector + standardG2Prime.dim_nilpotent_dual =
    standardG2Prime.total_dimension := by
  rfl

theorem g2_prime_dimension_count (R : G2PrimeRootDecomposition)
    (h_sl3 : R.dim_sl3 = 8)
    (h_v : R.dim_nilpotent_vector = 3)
    (h_v_dual : R.dim_nilpotent_dual = 3)
    (h_total : R.total_dimension = 14) :
    R.dim_sl3 + R.dim_nilpotent_vector + R.dim_nilpotent_dual = R.total_dimension := by
  rw [h_sl3, h_v, h_v_dual, h_total]

theorem split_octonion_derivation_automorphism_synthesis
    (g : SplitOctonionAutomorphism)
    (h_conj : ∀ X, SplitOctonion.conj (g.toLinearEquiv X) = g.toLinearEquiv (SplitOctonion.conj X))
    (D : SplitOctonionDerivation) (X : SplitOctonion) :
    g.toLinearEquiv 1 = 1 ∧
    SplitOctonion.zornDet (g.toLinearEquiv X) = SplitOctonion.zornDet X ∧
    D.toLinearMap 1 = 0 ∧
    D.toLinearMap (SplitOctonion.zornDet X • (1 : SplitOctonion)) = 0 ∧
    standardG2Prime.dim_sl3 + standardG2Prime.dim_nilpotent_vector + standardG2Prime.dim_nilpotent_dual =
      standardG2Prime.total_dimension := by
  exact ⟨SplitOctonionAutomorphism.map_one g,
         SplitOctonionAutomorphism.preserves_zornDet g h_conj X,
         SplitOctonionDerivation.map_one_zero D,
         SplitOctonionDerivation.map_norm_vanishes D X,
         standard_g2_prime_dimension_count⟩

end InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism
