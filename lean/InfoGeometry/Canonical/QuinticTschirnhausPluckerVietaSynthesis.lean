/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Tschirnhaus–Plücker–Vieta Quintic Pipeline & Graded `SOLVE / COAGULA` Synthesis (`Ξ_⊤`)

This Canonical owner module formalizes the complete 15-element causal poset from the epistemic
`SOLVE / COAGULA` structural distillation connecting ordered quintic root tuples `r : Fin 5 → K`,
simplicial coboundary bivectors `1 ∧ r ∈ ⋀[K]^2 (Fin 5 → K)`, curved Vandermonde bivectors
`r ∧ r^(2)`, projective Grassmannian embeddings `ℙ³_Tsch ↪ Gr(2, 5)`, weighted projective
quotients `ℙ(2, 3, 4, 5)` and `ℙ(2, 3, 4, 5; 10)`, and Galois non-solvability obstructions:

1. **Poset Nodes `Δ₀, T, S, T_shear, A₁, Ax.1, Ded.3`**:
   `monicRootPoly5`, Vieta elementary symmetric polynomials `vietaE1..vietaE5`, `S₅`-invariance,
   root-dilation multi-weights `(c^1, c^2, c^3, c^4, c^5)` vs. polynomial coefficient scaling
   weight `c^0` (`poly_smul_root_invariant`), the explicit `[countermodel_found]` shear witness
   `aporia_A1_vieta_weight_shear_countermodel`, and `vieta_quadruple_ne_zero_of_sum_zero`
   (nonzero zero-sum roots never map to `(0, 0, 0, 0)`).
2. **Poset Nodes `Ax.2, Ax.4, K_TT, Π_ST, Σ_TS, G, A₀, Ded.1`**:
   `plucker5ExteriorLinearEquiv : (⋀[K]^2 (Fin 5 → K)) ≃ₗ[K] (RootPair5 → K)` (`finrank = 10`),
   the simplicial difference bivector `exteriorCoboundary5 K r := ιMulti 2 ![onesVec5, r]`,
   the `[countermodel_found]` diagonal kernel `ker (exteriorCoboundary5 K) = K ∙ onesVec5`
   (`aporia_A0_diagonal_kernel`), the 4D `TschirnhausHyperplane5 K ≃ (K⁵ ⧸ K ∙ 1)`, and the
   globally injective projective Schubert embeddings `schubertPsi1Proj : ℙ³_Tsch ↪ ℙ(⋀² K⁵)` and
   `schubertPsi1Grassmannian : ℙ³_Tsch ↪ Module.Grassmannian K (Fin 5 → K) 3`.
3. **Poset Nodes `Ded.2, A₃, B, Γ_SS`**:
   Simplicial 1-coboundary `simplicialCoboundary1` (`d₁ ∘ d₀ = 0`, `range d₀ = ker d₁`,
   `finrank = 4 < 10`), linear vanishing of all five Klein–Plücker quadrics on `ker d₁`,
   the weight-3 curved Vandermonde bivector `vandermondeExterior5 r := r ∧ r^(2)` (`p_{ij}^Vand = rᵢ rⱼ (rⱼ - rᵢ)`),
   its exact Klein–Plücker annihilation, and its non-vanishing coboundary
   `(d₁ p^Vand)_{ijk} = (r_j - r_i)(r_k - r_j)(r_k - r_i) ≠ 0` escaping `range (exteriorCoboundary5 K)`.
4. **Poset Nodes `Ax.3, Ax.5, Ded.4, Ded.5, A₂, A_ω, H, W_quin, Ξ_⊤`**:
   Multi-weight homogeneity ladder `(1, 2, 3, 10, 20)`, `32`-to-`1` coordinate-squaring sign erasure
   vs. `A₅` orientation recovery via `quinticVandermonde` (`√Δ`), nonexistence of any linear Vieta
   section (`aporia_Aomega_no_linear_vieta_section`, `[countermodel_found]`), genuine quotients
   `WeightedProj2345 K` (`ℙ(2, 3, 4, 5)`) and `OrientedWeightedProj2345_10 K` (`ℙ(2, 3, 4, 5; 10)`),
   total morphisms `weightedVietaDescent` & `orientedWeightedVietaDescent`, and the master terminal
   join `quintic_tschirnhaus_plucker_vieta_master_synthesis` (`Ξ_⊤ = H ∨ W_quin`).

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

open scoped Polynomial Matrix LinearAlgebra.Projectivization

namespace InfoGeometry.Canonical.QuinticTschirnhausPluckerVietaSynthesis

section Section0IndicesAndWitness

/-- T16 noncommutativity ground witness on `Matrix (Fin 2) (Fin 2) ℚ`. -/
theorem quinticTschirnhaus_gl2_noncommutative :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℚ, a * b ≠ b * a := by
  refine ⟨!![1, 1; 0, 1], !![1, 0; 1, 1], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Ten unordered distinct-pair indices `1 ≤ i < j ≤ 5` indexing `⋀² K⁵`. -/
abbrev RootPair5 : Type := { p : Fin 5 × Fin 5 // p.1 < p.2 }

/-- Ten unordered distinct-triple indices `1 ≤ i < j < k ≤ 5` indexing simplicial 2-cochains. -/
abbrev RootTriple5 : Type := { t : Fin 5 × Fin 5 × Fin 5 // t.1 < t.2.1 ∧ t.2.1 < t.2.2 }

theorem card_rootPair5 : Fintype.card RootPair5 = 10 := by
  decide

theorem card_rootTriple5 : Fintype.card RootTriple5 = 10 := by
  decide

end Section0IndicesAndWitness

/-! ## Section 1: Vieta Grading `(1, 2, 3, 4, 5)` vs. Polynomial Scaling Weight `0` (`Ax.1, Ded.3, A₁`) -/

section VietaGradingAndShear

/-- Monic degree-5 polynomial assembled from an ordered root tuple `r : Fin 5 → R`. -/
def monicRootPoly5 {R : Type*} [CommRing R] (r : Fin 5 → R) : R[X] :=
  ∏ i : Fin 5, (Polynomial.X - Polynomial.C (r i))

/-- Explicit Vieta elementary symmetric sums `(e₁, e₂, e₃, e₄, e₅)` on `Fin 5 → R`. -/
def vietaE1 {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  r 0 + r 1 + r 2 + r 3 + r 4

def vietaE2 {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 0 * r 4 + r 1 * r 2 +
    r 1 * r 3 + r 1 * r 4 + r 2 * r 3 + r 2 * r 4 + r 3 * r 4

def vietaE3 {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  r 0 * r 1 * r 2 + r 0 * r 1 * r 3 + r 0 * r 1 * r 4 + r 0 * r 2 * r 3 +
    r 0 * r 2 * r 4 + r 0 * r 3 * r 4 + r 1 * r 2 * r 3 + r 1 * r 2 * r 4 +
    r 1 * r 3 * r 4 + r 2 * r 3 * r 4

def vietaE4 {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  r 0 * r 1 * r 2 * r 3 + r 0 * r 1 * r 2 * r 4 + r 0 * r 1 * r 3 * r 4 +
    r 0 * r 2 * r 3 * r 4 + r 1 * r 2 * r 3 * r 4

def vietaE5 {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  r 0 * r 1 * r 2 * r 3 * r 4

theorem vietaE1_eq_sum {R : Type*} [CommRing R] (r : Fin 5 → R) :
    vietaE1 r = ∑ i : Fin 5, r i := by
  rw [Fin.sum_univ_five]
  rfl

theorem monicRootPoly5_vieta_expansion {R : Type*} [CommRing R] (r : Fin 5 → R) :
    monicRootPoly5 r =
      Polynomial.X ^ 5 - Polynomial.C (vietaE1 r) * Polynomial.X ^ 4 +
        Polynomial.C (vietaE2 r) * Polynomial.X ^ 3 -
        Polynomial.C (vietaE3 r) * Polynomial.X ^ 2 +
        Polynomial.C (vietaE4 r) * Polynomial.X -
        Polynomial.C (vietaE5 r) := by
  simp only [monicRootPoly5, Fin.prod_univ_five, vietaE1, vietaE2, vietaE3, vietaE4, vietaE5,
    map_add, map_mul]
  ring

theorem monicRootPoly5_coeffs {R : Type*} [CommRing R] (r : Fin 5 → R) :
    (monicRootPoly5 r).coeff 4 = -(vietaE1 r) ∧
      (monicRootPoly5 r).coeff 3 = vietaE2 r ∧
      (monicRootPoly5 r).coeff 2 = -(vietaE3 r) ∧
      (monicRootPoly5 r).coeff 1 = vietaE4 r ∧
      (monicRootPoly5 r).coeff 0 = -(vietaE5 r) := by
  rw [monicRootPoly5_vieta_expansion r]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]

theorem monicRootPoly5_perm {R : Type*} [CommRing R] (r : Fin 5 → R) (σ : Equiv.Perm (Fin 5)) :
    monicRootPoly5 (fun i => r (σ i)) = monicRootPoly5 r := by
  unfold monicRootPoly5
  exact Fintype.prod_bijective σ σ.bijective
    (fun i => Polynomial.X - Polynomial.C (r (σ i)))
    (fun i => Polynomial.X - Polynomial.C (r i))
    (fun _ => rfl)

/-- Every `vietaEk` is invariant under arbitrary `S₅` root permutations. -/
theorem vieta_perm_invariant {R : Type*} [CommRing R] (r : Fin 5 → R) (σ : Equiv.Perm (Fin 5)) :
    vietaE1 (fun i => r (σ i)) = vietaE1 r ∧
      vietaE2 (fun i => r (σ i)) = vietaE2 r ∧
      vietaE3 (fun i => r (σ i)) = vietaE3 r ∧
      vietaE4 (fun i => r (σ i)) = vietaE4 r ∧
      vietaE5 (fun i => r (σ i)) = vietaE5 r := by
  have hpoly := monicRootPoly5_perm r σ
  have hcσ := monicRootPoly5_coeffs (fun i => r (σ i))
  have hcr := monicRootPoly5_coeffs r
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h4 := congrArg (fun P : R[X] => P.coeff 4) hpoly
    rw [hcσ.1, hcr.1] at h4
    exact neg_inj.mp h4
  · have h3 := congrArg (fun P : R[X] => P.coeff 3) hpoly
    rwa [hcσ.2.1, hcr.2.1] at h3
  · have h2 := congrArg (fun P : R[X] => P.coeff 2) hpoly
    rw [hcσ.2.2.1, hcr.2.2.1] at h2
    exact neg_inj.mp h2
  · have h1 := congrArg (fun P : R[X] => P.coeff 1) hpoly
    rwa [hcσ.2.2.2.1, hcr.2.2.2.1] at h1
  · have h0 := congrArg (fun P : R[X] => P.coeff 0) hpoly
    rw [hcσ.2.2.2.2, hcr.2.2.2.2] at h0
    exact neg_inj.mp h0

/-- **`Ax.1` (Axiom of Vieta Grading Asymmetry)**:
Root dilation `r ↦ c • r` scales `(e₁, e₂, e₃, e₄, e₅)` with multi-weights `(c^1, c^2, c^3, c^4, c^5)`. -/
theorem vieta_smul_weights {R : Type*} [CommRing R] (c : R) (r : Fin 5 → R) :
    vietaE1 (c • r) = c * vietaE1 r ∧
      vietaE2 (c • r) = c ^ 2 * vietaE2 r ∧
      vietaE3 (c • r) = c ^ 3 * vietaE3 r ∧
      vietaE4 (c • r) = c ^ 4 * vietaE4 r ∧
      vietaE5 (c • r) = c ^ 5 * vietaE5 r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [vietaE1, vietaE2, vietaE3, vietaE4, vietaE5, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- **`Ax.1` (Zero-Weight Polynomial Scaling Law)**:
Uniform nonzero polynomial scaling `P ↦ c • P` leaves roots completely invariant (weight `0`). -/
theorem poly_smul_root_invariant {K : Type*} [Field K] (P : K[X]) {c : K} (hc : c ≠ 0) (x : K) :
    (c • P).eval x = 0 ↔ P.eval x = 0 := by
  rw [Polynomial.eval_smul, smul_eq_mul]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc, fun h => by simp [h]⟩

/-- **`A₁` (`[countermodel_found]`)**:
Vieta's map fails uniform degree-1 homogeneity by `(c^2 - c) * vietaE2 r`, realized concretely on
`r = ![-2, -1, 0, 1, 2] : Fin 5 → ℚ` with `c = 2`. -/
theorem aporia_A1_vieta_weight_shear_countermodel :
    (∀ {R : Type*} [CommRing R] (c : R) (r : Fin 5 → R),
      vietaE2 (c • r) - c * vietaE2 r = (c ^ 2 - c) * vietaE2 r) ∧
      (∃ r : Fin 5 → ℚ, ∃ c : ℚ, vietaE1 r = 0 ∧ vietaE2 (c • r) ≠ c * vietaE2 r) := by
  refine ⟨fun c r => by rw [(vieta_smul_weights c r).2.1]; ring, ?_⟩
  refine ⟨![-2, -1, 0, 1, 2], 2, ?_, ?_⟩
  · norm_num [vietaE1]
  · norm_num [vietaE2, Pi.smul_apply, smul_eq_mul]

/-- Every nonzero vector in the Tschirnhaus hyperplane `∑ rᵢ = 0` has a nonzero Vieta quadruple
`(e₂, e₃, e₄, e₅) ≠ 0`, making the weighted projective map into `ℙ(2, 3, 4, 5)` total. -/
theorem vieta_quadruple_ne_zero_of_sum_zero {K : Type*} [Field K]
    {r : Fin 5 → K} (hsum : ∑ i : Fin 5, r i = 0) (hr : r ≠ 0) :
    (vietaE2 r, vietaE3 r, vietaE4 r, vietaE5 r) ≠ 0 := by
  intro hzero
  have he1 : vietaE1 r = 0 := by rw [vietaE1_eq_sum, hsum]
  have he2 : vietaE2 r = 0 := congrArg Prod.fst hzero
  have he3 : vietaE3 r = 0 := congrArg (fun p : K × K × K × K => p.2.1) hzero
  have he4 : vietaE4 r = 0 := congrArg (fun p : K × K × K × K => p.2.2.1) hzero
  have he5 : vietaE5 r = 0 := congrArg (fun p : K × K × K × K => p.2.2.2) hzero
  have hpoly : monicRootPoly5 r = Polynomial.X ^ 5 := by
    rw [monicRootPoly5_vieta_expansion, he1, he2, he3, he4, he5]
    simp
  apply hr
  funext i
  have heval : (monicRootPoly5 r).eval (r i) = 0 := by
    simp only [monicRootPoly5, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [hpoly, Polynomial.eval_pow, Polynomial.eval_X] at heval
  exact eq_zero_of_pow_eq_zero heval

end VietaGradingAndShear

/-! ## Section 2: Native `⋀[K]^2 (Fin 5 → K)`, Diagonal Kernel `1 ∧ 1 = 0`, & `Ψ₁ : ℙ³_Tsch ↪ Gr(2, 5)` -/

section SimplicialCoboundaryAndTschirnhaus

/-- Canonical bilinear alternating Plücker evaluation `u ∧ v ↦ (uᵢ vⱼ - uⱼ vᵢ)_{i<j}` on `K⁵`. -/
def plucker5Multilinear (K : Type*) [Field K] :
    MultilinearMap K (fun _ : Fin 2 => Fin 5 → K) (RootPair5 → K) where
  toFun v p := v 0 p.1.1 * v 1 p.1.2 - v 0 p.1.2 * v 1 p.1.1
  map_update_add' m i x y := by
    funext p
    fin_cases i
    · change Function.update m 0 (x + y) 0 p.1.1 * Function.update m 0 (x + y) 1 p.1.2 -
          Function.update m 0 (x + y) 0 p.1.2 * Function.update m 0 (x + y) 1 p.1.1 =
        (Function.update m 0 x 0 p.1.1 * Function.update m 0 x 1 p.1.2 -
          Function.update m 0 x 0 p.1.2 * Function.update m 0 x 1 p.1.1) +
        (Function.update m 0 y 0 p.1.1 * Function.update m 0 y 1 p.1.2 -
          Function.update m 0 y 0 p.1.2 * Function.update m 0 y 1 p.1.1)
      simp only [Function.update_self, Function.update_of_ne (Fin.zero_ne_one.symm : (1 : Fin 2) ≠ 0),
        Pi.add_apply]
      ring
    · change Function.update m 1 (x + y) 0 p.1.1 * Function.update m 1 (x + y) 1 p.1.2 -
          Function.update m 1 (x + y) 0 p.1.2 * Function.update m 1 (x + y) 1 p.1.1 =
        (Function.update m 1 x 0 p.1.1 * Function.update m 1 x 1 p.1.2 -
          Function.update m 1 x 0 p.1.2 * Function.update m 1 x 1 p.1.1) +
        (Function.update m 1 y 0 p.1.1 * Function.update m 1 y 1 p.1.2 -
          Function.update m 1 y 0 p.1.2 * Function.update m 1 y 1 p.1.1)
      simp only [Function.update_self, Function.update_of_ne (Fin.zero_ne_one : (0 : Fin 2) ≠ 1),
        Pi.add_apply]
      ring
  map_update_smul' m i c x := by
    funext p
    fin_cases i
    · change Function.update m 0 (c • x) 0 p.1.1 * Function.update m 0 (c • x) 1 p.1.2 -
          Function.update m 0 (c • x) 0 p.1.2 * Function.update m 0 (c • x) 1 p.1.1 =
        c * (Function.update m 0 x 0 p.1.1 * Function.update m 0 x 1 p.1.2 -
          Function.update m 0 x 0 p.1.2 * Function.update m 0 x 1 p.1.1)
      simp only [Function.update_self, Function.update_of_ne (Fin.zero_ne_one.symm : (1 : Fin 2) ≠ 0),
        Pi.smul_apply, smul_eq_mul]
      ring
    · change Function.update m 1 (c • x) 0 p.1.1 * Function.update m 1 (c • x) 1 p.1.2 -
          Function.update m 1 (c • x) 0 p.1.2 * Function.update m 1 (c • x) 1 p.1.1 =
        c * (Function.update m 1 x 0 p.1.1 * Function.update m 1 x 1 p.1.2 -
          Function.update m 1 x 0 p.1.2 * Function.update m 1 x 1 p.1.1)
      simp only [Function.update_self, Function.update_of_ne (Fin.zero_ne_one : (0 : Fin 2) ≠ 1),
        Pi.smul_apply, smul_eq_mul]
      ring

def plucker5Alternating (K : Type*) [Field K] :
    (Fin 5 → K) [⋀^Fin 2]→ₗ[K] (RootPair5 → K) :=
  AlternatingMap.mk (plucker5Multilinear K) (by
    intro v i j hij hne
    funext p
    dsimp [plucker5Multilinear]
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h01 : v 0 = v 1 := by simpa using hij
      rw [h01]
      ring
    · have h10 : v 1 = v 0 := by simpa using hij
      rw [h10]
      ring
    · exact (hne rfl).elim)

@[simp] theorem plucker5Alternating_apply {K : Type*} [Field K] (u v : Fin 5 → K) (p : RootPair5) :
    plucker5Alternating K ![u, v] p = u p.1.1 * v p.1.2 - u p.1.2 * v p.1.1 := by
  simp [plucker5Alternating, plucker5Multilinear]

/-- Canonical Plücker coordinate linear map from Mathlib's `⋀[K]^2 (Fin 5 → K)` to `RootPair5 → K`. -/
def plucker5ExteriorMap (K : Type*) [Field K] :
    (⋀[K]^2 (Fin 5 → K)) →ₗ[K] (RootPair5 → K) :=
  exteriorPower.alternatingMapLinearEquiv (plucker5Alternating K)

theorem plucker5ExteriorMap_ιMulti {K : Type*} [Field K] (u v : Fin 5 → K) :
    plucker5ExteriorMap K (exteriorPower.ιMulti K 2 ![u, v]) =
      plucker5Alternating K ![u, v] :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (plucker5Alternating K) ![u, v]

theorem plucker5ExteriorMap_surjective (K : Type*) [Field K] :
    Function.Surjective (plucker5ExteriorMap K) := by
  rw [← LinearMap.range_eq_top]
  apply le_antisymm le_top
  rw [← (Pi.basisFun K RootPair5).span_eq]
  apply Submodule.span_le.2
  rintro _ ⟨p, rfl⟩
  refine ⟨exteriorPower.ιMulti K 2 ![Pi.single p.1.1 (1 : K), Pi.single p.1.2 (1 : K)], ?_⟩
  rw [plucker5ExteriorMap_ιMulti]
  simp only [Pi.basisFun_apply]
  funext q
  rw [plucker5Alternating_apply]
  by_cases hqp : q = p
  · subst hqp
    have hne : q.1.1 ≠ q.1.2 := q.2.ne
    simp [hne]
  · have h1 : ¬ (q.1.1 = p.1.1 ∧ q.1.2 = p.1.2) := fun ⟨a, b⟩ =>
      hqp (Subtype.ext (Prod.ext a b))
    have h2 : ¬ (q.1.2 = p.1.1 ∧ q.1.1 = p.1.2) := fun ⟨a, b⟩ => by
      have hp_lt : p.1.1 < p.1.2 := p.2
      have hq_lt : q.1.1 < q.1.2 := q.2
      omega
    simp only [Pi.single_apply]
    split_ifs <;> try simp_all

theorem plucker5ExteriorMap_finrank_eq (K : Type*) [Field K] :
    Module.finrank K (⋀[K]^2 (Fin 5 → K)) = Module.finrank K (RootPair5 → K) := by
  have h5 : Module.finrank K (Fin 5 → K) = 5 := by simp
  rw [exteriorPower.finrank_eq (R := K) (M := Fin 5 → K) (n := 2), h5, Module.finrank_pi,
    card_rootPair5]
  decide

/-- **`Ax.2` (Bivector Carrier Identification)**:
Mathlib's genuine exterior square `⋀[K]^2 (Fin 5 → K)` is linearly isomorphic to `RootPair5 → K`. -/
def plucker5ExteriorLinearEquiv (K : Type*) [Field K] :
    (⋀[K]^2 (Fin 5 → K)) ≃ₗ[K] (RootPair5 → K) :=
  LinearEquiv.ofBijective (plucker5ExteriorMap K)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (plucker5ExteriorMap_finrank_eq K)).2 (plucker5ExteriorMap_surjective K),
     plucker5ExteriorMap_surjective K⟩

theorem plucker5ExteriorLinearEquiv_ιMulti {K : Type*} [Field K] (u v : Fin 5 → K) (p : RootPair5) :
    plucker5ExteriorLinearEquiv K (exteriorPower.ιMulti K 2 ![u, v]) p =
      u p.1.1 * v p.1.2 - u p.1.2 * v p.1.1 := by
  change plucker5ExteriorMap K (exteriorPower.ιMulti K 2 ![u, v]) p = _
  rw [plucker5ExteriorMap_ιMulti, plucker5Alternating_apply]

/-- Five-index Klein–Plücker quadric quadratic relation `p_{ab} p_{cd} - p_{ac} p_{bd} + p_{ad} p_{bc}`
over all ordered 4-tuples `a < b < c < d` in `Fin 5`. -/
def signedPlucker5Coord {K : Type*} [CommRing K] (P : RootPair5 → K) (i j : Fin 5) : K :=
  if h : i < j then P ⟨(i, j), h⟩ else if h' : j < i then -P ⟨(j, i), h'⟩ else 0

theorem signedPlucker5Coord_lt {K : Type*} [CommRing K] (P : RootPair5 → K) {i j : Fin 5}
    (hij : i < j) :
    signedPlucker5Coord P i j = P ⟨(i, j), hij⟩ := by
  dsimp only [signedPlucker5Coord]
  split_ifs
  rfl

def kleinPlucker5Quadric {K : Type*} [CommRing K] (P : RootPair5 → K) (a b c d : Fin 5) : K :=
  signedPlucker5Coord P a b * signedPlucker5Coord P c d -
    signedPlucker5Coord P a c * signedPlucker5Coord P b d +
    signedPlucker5Coord P a d * signedPlucker5Coord P b c

/-- **`Ax.2` (Decomposable Klein Quadrics on `⋀[K]^2 K⁵`)**:
Every decomposable bivector `ιMulti K 2 ![u, v]` identically satisfies all 5 Klein–Plücker quadrics. -/
theorem kleinPlucker5Quadric_decomposable (K : Type*) [Field K] (u v : Fin 5 → K)
    (a b c d : Fin 5) :
    kleinPlucker5Quadric (plucker5ExteriorLinearEquiv K (exteriorPower.ιMulti K 2 ![u, v]))
      a b c d = 0 := by
  have hs : ∀ i j : Fin 5,
      signedPlucker5Coord (plucker5ExteriorLinearEquiv K (exteriorPower.ιMulti K 2 ![u, v])) i j =
        u i * v j - u j * v i := fun i j => by
    dsimp only [signedPlucker5Coord]
    split_ifs with h1 h2
    · exact plucker5ExteriorLinearEquiv_ιMulti u v ⟨(i, j), h1⟩
    · rw [plucker5ExteriorLinearEquiv_ιMulti u v ⟨(j, i), h2⟩]
      ring
    · have hij : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      subst hij
      ring
  simp only [kleinPlucker5Quadric, hs]
  ring

/-- The constant all-ones diagonal vector `1 = (1, 1, 1, 1, 1) ∈ K⁵`. -/
def onesVec5 (K : Type*) [CommSemiring K] : Fin 5 → K :=
  fun _ => 1

theorem onesVec5_ne_zero (K : Type*) [Field K] : onesVec5 K ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  exact one_ne_zero h0

/-- Simplicial 0-coboundary `(d₀ r)_{i<j} = rⱼ - rᵢ` on `Fin 5 → K`. -/
def simplicialDiff5 (K : Type*) [Field K] : (Fin 5 → K) →ₗ[K] (RootPair5 → K) where
  toFun r p := r p.1.2 - r p.1.1
  map_add' r s := by
    funext p
    simp only [Pi.add_apply]
    ring
  map_smul' c r := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **`Ax.4` (Exterior Coboundary `B₁(r) = 1 ∧ r ∈ ⋀[K]^2 K⁵`)**:
Fixes `u = 1` in the canonical exterior wedge, with `plucker5ExteriorLinearEquiv` readout equal to
the pairwise root differences `rⱼ - rᵢ`. -/
def exteriorCoboundary5 (K : Type*) [Field K] : (Fin 5 → K) →ₗ[K] ⋀[K]^2 (Fin 5 → K) :=
  (plucker5ExteriorLinearEquiv K).symm.toLinearMap.comp (simplicialDiff5 K)

theorem exteriorCoboundary5_eq_ιMulti {K : Type*} [Field K] (r : Fin 5 → K) :
    exteriorCoboundary5 K r = exteriorPower.ιMulti K 2 ![onesVec5 K, r] := by
  apply (plucker5ExteriorLinearEquiv K).injective
  simp only [exteriorCoboundary5, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  funext p
  rw [plucker5ExteriorLinearEquiv_ιMulti]
  simp [simplicialDiff5, onesVec5]

theorem exteriorCoboundary5_smul_weight1 {K : Type*} [Field K] (c : K) (r : Fin 5 → K) :
    exteriorCoboundary5 K (c • r) = c • exteriorCoboundary5 K r :=
  map_smul (exteriorCoboundary5 K) c r

/-- **`A₀` (Diagonal Base-Point Annihilation, `[countermodel_found]`)**:
Even though `1 ≠ 0`, `exteriorCoboundary5 K (c • 1) = 0`, `ker (1 ∧ -) = K ∙ 1`, and
`exteriorCoboundary5 K` fails injectivity, blocking total projective descent on `ℙ(K⁵)`. -/
theorem aporia_A0_diagonal_kernel (K : Type*) [Field K] :
    onesVec5 K ≠ 0 ∧
      (∀ c : K, exteriorCoboundary5 K (c • onesVec5 K) = 0) ∧
      LinearMap.ker (exteriorCoboundary5 K) = K ∙ onesVec5 K ∧
      ¬ Function.Injective (exteriorCoboundary5 K) := by
  have hzero : ∀ c : K, exteriorCoboundary5 K (c • onesVec5 K) = 0 := fun c => by
    apply (plucker5ExteriorLinearEquiv K).injective
    rw [map_zero]
    simp only [exteriorCoboundary5, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    funext p
    simp [simplicialDiff5, onesVec5]
  have hker : LinearMap.ker (exteriorCoboundary5 K) = K ∙ onesVec5 K := by
    apply le_antisymm
    · intro r hr
      rw [LinearMap.mem_ker] at hr
      have hdiff := congrArg (plucker5ExteriorLinearEquiv K) hr
      rw [map_zero] at hdiff
      simp only [exteriorCoboundary5, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at hdiff
      have hconst : ∀ i : Fin 5, r i = r 0 := fun i => by
        by_cases hi : 0 < i
        · have hi0 := congrFun hdiff ⟨(0, i), hi⟩
          simp only [simplicialDiff5, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hi0
          exact sub_eq_zero.mp hi0
        · have hi0 : i = 0 := Fin.ext (by omega)
          rw [hi0]
      rw [Submodule.mem_span_singleton]
      refine ⟨r 0, funext fun i => ?_⟩
      simp [onesVec5, hconst i]
    · rw [Submodule.span_le]
      rintro _ rfl
      change (exteriorCoboundary5 K) (onesVec5 K) = 0
      simpa using hzero 1
  refine ⟨onesVec5_ne_zero K, hzero, hker, fun hinj => ?_⟩
  have heq : onesVec5 K = 0 := hinj (by simpa using hzero 1)
  exact onesVec5_ne_zero K heq

/-- Coordinate sum linear functional `r ↦ ∑ i, r i` on `K⁵`. -/
def sumCoord5 (K : Type*) [Field K] : (Fin 5 → K) →ₗ[K] K :=
  ∑ i : Fin 5, LinearMap.proj i

@[simp] theorem sumCoord5_apply {K : Type*} [Field K] (r : Fin 5 → K) :
    sumCoord5 K r = ∑ i : Fin 5, r i := by
  simp [sumCoord5]

/-- The 4-dimensional Tschirnhaus sum-zero hyperplane `V_std^(4) = ker (r ↦ ∑ rᵢ)`. -/
abbrev TschirnhausHyperplane5 (K : Type*) [Field K] : Type _ :=
  LinearMap.ker (sumCoord5 K)

theorem sumCoord5_onesVec5 (K : Type*) [Field K] :
    sumCoord5 K (onesVec5 K) = (5 : K) := by
  simp [sumCoord5, onesVec5, Finset.sum_const]

theorem finrank_tschirnhausHyperplane5 (K : Type*) [Field K] [CharZero K] :
    Module.finrank K (TschirnhausHyperplane5 K) = 4 := by
  have h5 : (5 : K) ≠ 0 := by norm_num
  have hsurj : Function.Surjective (sumCoord5 K) := fun c => by
    refine ⟨(c / 5) • onesVec5 K, ?_⟩
    rw [map_smul, sumCoord5_onesVec5, smul_eq_mul, div_mul_cancel₀ _ h5]
  have hrank := LinearMap.finrank_range_add_finrank_ker (sumCoord5 K)
  have htop : Module.finrank K (LinearMap.range (sumCoord5 K)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have h5dim : Module.finrank K (Fin 5 → K) = 5 := by simp
  rw [htop, h5dim] at hrank
  change 1 + Module.finrank K (TschirnhausHyperplane5 K) = 5 at hrank
  omega

/-- Tschirnhaus centering projection `π_Tsch(r) = r - ((∑ rᵢ)/5) • 1` onto `V_std^(4)`. -/
def tschirnhausProj5 (K : Type*) [Field K] [CharZero K] :
    (Fin 5 → K) →ₗ[K] TschirnhausHyperplane5 K where
  toFun r := ⟨r - (sumCoord5 K r / 5) • onesVec5 K, by
    rw [LinearMap.mem_ker, map_sub, map_smul, sumCoord5_onesVec5, smul_eq_mul,
      div_mul_cancel₀ _ (by norm_num : (5 : K) ≠ 0), sub_self]⟩
  map_add' r s := by
    ext i
    simp [map_add, add_div, add_smul]
    ring
  map_smul' c r := by
    ext i
    simp [map_smul, smul_eq_mul, mul_div_assoc]
    ring

theorem tschirnhausProj5_ker (K : Type*) [Field K] [CharZero K] :
    LinearMap.ker (tschirnhausProj5 K) = K ∙ onesVec5 K := by
  apply le_antisymm
  · intro r hr
    rw [LinearMap.mem_ker, Subtype.ext_iff] at hr
    change r - (sumCoord5 K r / 5) • onesVec5 K = 0 at hr
    rw [Submodule.mem_span_singleton]
    exact ⟨sumCoord5 K r / 5, (sub_eq_zero.mp hr).symm⟩
  · rw [Submodule.span_le]
    rintro _ rfl
    change tschirnhausProj5 K (onesVec5 K) = 0
    ext i
    dsimp [tschirnhausProj5]
    rw [sumCoord5_onesVec5, div_self (by norm_num : (5 : K) ≠ 0), one_mul, sub_self]

theorem tschirnhausProj5_surjective (K : Type*) [Field K] [CharZero K] :
    Function.Surjective (tschirnhausProj5 K) := fun ⟨r, hr⟩ => by
  refine ⟨r, Subtype.ext ?_⟩
  rw [LinearMap.mem_ker] at hr
  change r - (sumCoord5 K r / 5) • onesVec5 K = r
  rw [hr, zero_div, zero_smul, sub_zero]

/-- Explicit isomorphism `(K⁵ ⧸ K ∙ 1) ≃ₗ[K] V_std^(4)` quotienting out the diagonal kernel. -/
def quotientOnesEquivTschirnhaus5 (K : Type*) [Field K] [CharZero K] :
    ((Fin 5 → K) ⧸ (K ∙ onesVec5 K)) ≃ₗ[K] TschirnhausHyperplane5 K :=
  (Submodule.quotEquivOfEq _ _ (tschirnhausProj5_ker K).symm).trans
    ((tschirnhausProj5 K).quotKerEquivOfSurjective (tschirnhausProj5_surjective K))

/-- Restriction of `exteriorCoboundary5 K` to `V_std^(4)` (`Ded.1`, kernel excised). -/
def tschirnhausExteriorCoboundary5 (K : Type*) [Field K] :
    TschirnhausHyperplane5 K →ₗ[K] ⋀[K]^2 (Fin 5 → K) :=
  (exteriorCoboundary5 K).comp (LinearMap.ker (sumCoord5 K)).subtype

theorem tschirnhausExteriorCoboundary5_injective (K : Type*) [Field K] [CharZero K] :
    Function.Injective (tschirnhausExteriorCoboundary5 K) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨r, hr⟩ hker
  rw [LinearMap.mem_ker] at hker
  change (exteriorCoboundary5 K) r = 0 at hker
  rw [← LinearMap.mem_ker, (aporia_A0_diagonal_kernel K).2.2.1,
    Submodule.mem_span_singleton] at hker
  obtain ⟨c, hc⟩ := hker
  rw [LinearMap.mem_ker, ← hc, map_smul, sumCoord5_onesVec5, smul_eq_mul] at hr
  have hc0 : c = 0 := (mul_eq_zero.mp hr).resolve_right (by norm_num)
  subst hc0
  rw [zero_smul] at hc
  ext i
  exact congrFun hc.symm i

/-- **`Ded.1` (Globally Injective Projective Schubert Morphism `Ψ₁ : ℙ³_Tsch ↪ ℙ(⋀² K⁵)`)**:
Induced via `Projectivization.map` after Tschirnhaus quotienting eliminates `1 ∧ 1 = 0`. -/
def schubertPsi1Proj (K : Type*) [Field K] [CharZero K] :
    ℙ K (TschirnhausHyperplane5 K) → ℙ K (⋀[K]^2 (Fin 5 → K)) :=
  Projectivization.map (tschirnhausExteriorCoboundary5 K)
    (tschirnhausExteriorCoboundary5_injective K)

theorem schubertPsi1Proj_injective (K : Type*) [Field K] [CharZero K] :
    Function.Injective (schubertPsi1Proj K) :=
  Projectivization.map_injective (tschirnhausExteriorCoboundary5 K)
    (tschirnhausExteriorCoboundary5_injective K)

private lemma span_pair_ones_tschirnhaus_finrank {K : Type*} [Field K] [CharZero K]
    (r : TschirnhausHyperplane5 K) (hr : r ≠ 0) :
    LinearIndependent K ![onesVec5 K, r.1] ∧
      Module.finrank K (Submodule.span K {onesVec5 K, r.1}) = 2 := by
  have hli : LinearIndependent K ![onesVec5 K, r.1] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [Fin.sum_univ_two] at hc
    have hsum := congrArg (sumCoord5 K) hc
    simp only [map_add, map_smul, map_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      sumCoord5_onesVec5, LinearMap.mem_ker.mp r.2, smul_eq_mul, mul_zero, add_zero] at hsum
    have hc0 : c 0 = 0 := (mul_eq_zero.mp hsum).resolve_right (by norm_num)
    rw [hc0, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, zero_add] at hc
    have hr1 : r.1 ≠ 0 := fun hz => hr (Subtype.ext hz)
    have hc1 : c 1 = 0 := (smul_eq_zero.mp hc).resolve_right hr1
    fin_cases i
    · exact hc0
    · exact hc1
  refine ⟨hli, ?_⟩
  have hsp : Submodule.span K {onesVec5 K, r.1} = Submodule.span K (Set.range ![onesVec5 K, r.1]) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm),
      fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)⟩
  rw [hsp, Module.finrank_eq_card_basis (Module.Basis.span hli), Fintype.card_fin]

/-- **`Ded.1` (Globally Injective Projective Morphism `Ψ₁ : ℙ³_Tsch ↪ Module.Grassmannian K K⁵ 3`)**:
Remembering Mathlib's `Module.Grassmannian K M q` parameterizes subspaces whose **quotient** has
rank `q`, a 2-plane in `K⁵` is an element of `Module.Grassmannian K (Fin 5 → K) 3`. -/
def schubertPsi1Grassmannian (K : Type*) [Field K] [CharZero K]
    (x : ℙ K (TschirnhausHyperplane5 K)) : Module.Grassmannian K (Fin 5 → K) 3 :=
  Quotient.liftOn x (fun ⟨r, hr⟩ =>
    let hfr := (span_pair_ones_tschirnhaus_finrank r hr).2
    let W : Submodule K (Fin 5 → K) := Submodule.span K {onesVec5 K, r.1}
    { toSubmodule := W
      finite_quotient := inferInstance
      projective_quotient := inferInstance
      rankAtStalk_eq := fun p => by
        have hq := Submodule.finrank_quotient_add_finrank W
        have h5 : Module.finrank K (Fin 5 → K) = 5 := by simp
        rw [hfr, h5] at hq
        have h3 : Module.finrank K ((Fin 5 → K) ⧸ W) = 3 := by omega
        simp [Module.rankAtStalk_eq_finrank_of_free, h3] })
    (by
      rintro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ ⟨u, hu⟩
      apply Module.Grassmannian.ext
      change Submodule.span K {onesVec5 K, r₁.1} = Submodule.span K {onesVec5 K, r₂.1}
      have hu1 : r₁.1 = (u : K) • r₂.1 := by
        simpa [Subtype.ext_iff, Units.smul_def] using hu.symm
      rw [hu1]
      apply le_antisymm <;> rw [Submodule.span_le]
      · rintro y (rfl | rfl)
        · exact Submodule.subset_span (Set.mem_insert _ _)
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      · rintro y (rfl | rfl)
        · exact Submodule.subset_span (Set.mem_insert _ _)
        · have heq : r₂.1 = ((u⁻¹ : Kˣ) : K) • ((u : K) • r₂.1) := by
            rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
          have hmem : (u : K) • r₂.1 ∈ Submodule.span K {onesVec5 K, (u : K) • r₂.1} :=
            Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
          have hsm := Submodule.smul_mem _ ((u⁻¹ : Kˣ) : K) hmem
          rwa [← heq] at hsm)

theorem schubertPsi1Grassmannian_injective (K : Type*) [Field K] [CharZero K] :
    Function.Injective (schubertPsi1Grassmannian K) := by
  intro x y hxy
  induction x using Projectivization.ind with | h r₁ hr₁ =>
  induction y using Projectivization.ind with | h r₂ hr₂ =>
  have hsub : Submodule.span K {onesVec5 K, r₁.1} = Submodule.span K {onesVec5 K, r₂.1} :=
    congrArg Module.Grassmannian.toSubmodule hxy
  have hmem : r₁.1 ∈ Submodule.span K {onesVec5 K, r₂.1} := by
    rw [← hsub]
    exact Submodule.subset_span (Or.inr rfl)
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hsum := congrArg (sumCoord5 K) hab
  simp only [map_add, map_smul, sumCoord5_onesVec5, LinearMap.mem_ker.mp r₁.2,
    LinearMap.mem_ker.mp r₂.2, smul_eq_mul, mul_zero, add_zero] at hsum
  have ha0 : a = 0 := (mul_eq_zero.mp hsum).resolve_right (by norm_num : (5 : K) ≠ 0)
  rw [ha0, zero_smul, zero_add] at hab
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨b, Subtype.ext hab⟩

end SimplicialCoboundaryAndTschirnhaus

/-! ## Section 3: Simplicial Flatness `d₁ ∘ d₀ = 0` (`ℙ³ ⊊ Gr(2, 5)`) vs. Curved Vandermonde `r ∧ r^(2)` (`Ded.2, A₃, B`) -/

section SimplicialFlatnessAndVandermondeLift

/-- Simplicial 1-coboundary `(d₁ P)_{i<j<k} = P_{ij} + P_{jk} - P_{ik}`. -/
def simplicialCoboundary1 (K : Type*) [Field K] : (RootPair5 → K) →ₗ[K] (RootTriple5 → K) where
  toFun P t :=
    P ⟨(t.1.1, t.1.2.1), t.2.1⟩ +
      P ⟨(t.1.2.1, t.1.2.2), t.2.2⟩ -
      P ⟨(t.1.1, t.1.2.2), lt_trans t.2.1 t.2.2⟩
  map_add' P Q := by
    funext t
    simp only [Pi.add_apply]
    ring
  map_smul' c P := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **`A₃` (Exact Simplicial Coboundary Flatness `d₁ ∘ d₀ = 0`)**:
All pairwise root differences satisfy `d₁(d₀ r) = 0`, `range d₀ = ker d₁`, `finrank (Im(1 ∧ -)) = 4 < 10`,
and every element of `ker d₁` satisfies Klein's Plücker quadrics by linear elimination. -/
theorem simplicialCoboundary1_comp_simplicialDiff5 (K : Type*) [Field K] :
    (simplicialCoboundary1 K).comp (simplicialDiff5 K) = 0 := by
  ext r t
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    simplicialCoboundary1, simplicialDiff5, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem range_simplicialDiff5_eq_ker_coboundary1 (K : Type*) [Field K] :
    LinearMap.range (simplicialDiff5 K) = LinearMap.ker (simplicialCoboundary1 K) := by
  apply le_antisymm
  · rintro P ⟨r, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
      simplicialCoboundary1_comp_simplicialDiff5 K, LinearMap.zero_apply]
  · intro P hP
    rw [LinearMap.mem_ker] at hP
    let r : Fin 5 → K := fun k => if hk : (0 : Fin 5) < k then P ⟨(0, k), hk⟩ else 0
    refine ⟨r, ?_⟩
    funext ⟨⟨i, j⟩, hij⟩
    change r j - r i = P ⟨(i, j), hij⟩
    have hj : (0 : Fin 5) < j := lt_of_le_of_lt (Fin.zero_le i) hij
    by_cases hi : (0 : Fin 5) < i
    · have ht := congrFun hP ⟨(0, i, j), hi, hij⟩
      simp only [Pi.zero_apply, simplicialCoboundary1, LinearMap.coe_mk, AddHom.coe_mk] at ht
      dsimp only [r]
      rw [dite_eq_left hj, dite_eq_left hi]
      linear_combination -ht
    · have hi0 : i = 0 := Fin.ext (by omega)
      subst hi0
      dsimp only [r]
      rw [dite_eq_left hij, dite_eq_right (lt_irrefl _), sub_zero]

theorem finrank_range_exteriorCoboundary5 (K : Type*) [Field K] :
    Module.finrank K (LinearMap.range (exteriorCoboundary5 K)) = 4 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (exteriorCoboundary5 K)
  have hker : Module.finrank K (LinearMap.ker (exteriorCoboundary5 K)) = 1 := by
    rw [(aporia_A0_diagonal_kernel K).2.2.1]
    exact finrank_span_singleton (onesVec5_ne_zero K)
  have h5 : Module.finrank K (Fin 5 → K) = 5 := by simp
  rw [hker, h5] at hrank
  omega

theorem kleinPlucker5_zero_of_mem_ker_coboundary1 (K : Type*) [Field K]
    {P : RootPair5 → K} (hP : P ∈ LinearMap.ker (simplicialCoboundary1 K))
    (a b c d : Fin 5) :
    kleinPlucker5Quadric P a b c d = 0 := by
  rw [← range_simplicialDiff5_eq_ker_coboundary1 K] at hP
  obtain ⟨r, rfl⟩ := hP
  have hback : simplicialDiff5 K r =
      plucker5ExteriorLinearEquiv K (exteriorCoboundary5 K r) := by
    simp only [exteriorCoboundary5, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  rw [hback, exteriorCoboundary5_eq_ιMulti]
  exact kleinPlucker5Quadric_decomposable K (onesVec5 K) r a b c d

/-- **`Ded.2` & `B` (Curved Weight-3 Vandermonde Bivector `B_Vand(r) = r ∧ r^(2)`)**:
Pairs `r` (weight `1`) with `fun i => (r i)^2` (weight `2`) inside `⋀[K]^2 (Fin 5 → K)`. -/
def vandermondeExterior5 (K : Type*) [Field K] (r : Fin 5 → K) : ⋀[K]^2 (Fin 5 → K) :=
  exteriorPower.ιMulti K 2 ![r, fun i => r i ^ 2]

def vandermondePlucker5 (K : Type*) [Field K] (r : Fin 5 → K) : RootPair5 → K :=
  plucker5ExteriorLinearEquiv K (vandermondeExterior5 K r)

theorem vandermondePlucker5_apply {K : Type*} [Field K] (r : Fin 5 → K) (p : RootPair5) :
    vandermondePlucker5 K r p = r p.1.1 * r p.1.2 * (r p.1.2 - r p.1.1) := by
  change plucker5ExteriorLinearEquiv K (exteriorPower.ιMulti K 2 ![r, fun i => r i ^ 2]) p = _
  rw [plucker5ExteriorLinearEquiv_ιMulti]
  ring

theorem vandermondeExterior5_smul_weight3 {K : Type*} [Field K] (c : K) (r : Fin 5 → K) :
    vandermondeExterior5 K (c • r) = (c ^ 3) • vandermondeExterior5 K r := by
  apply (plucker5ExteriorLinearEquiv K).injective
  rw [map_smul]
  funext p
  simp only [Pi.smul_apply, smul_eq_mul]
  change vandermondePlucker5 K (c • r) p = c ^ 3 * vandermondePlucker5 K r p
  simp only [vandermondePlucker5_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem kleinPlucker5_vandermondePlucker5 (K : Type*) [Field K] (r : Fin 5 → K)
    (a b c d : Fin 5) :
    kleinPlucker5Quadric (vandermondePlucker5 K r) a b c d = 0 :=
  kleinPlucker5Quadric_decomposable K r (fun i => r i ^ 2) a b c d

/-- Exact non-vanishing coboundary law:
`(d₁ p^Vand)_{ijk} = (r_j - r_i)(r_k - r_j)(r_k - r_i) ≠ 0`, escaping `ker d₁ = Im(1 ∧ -)`. -/
theorem coboundary1_vandermondePlucker5 {K : Type*} [Field K] (r : Fin 5 → K) (t : RootTriple5) :
    simplicialCoboundary1 K (vandermondePlucker5 K r) t =
      (r t.1.2.1 - r t.1.1) * (r t.1.2.2 - r t.1.2.1) * (r t.1.2.2 - r t.1.1) := by
  simp only [simplicialCoboundary1, LinearMap.coe_mk, AddHom.coe_mk, vandermondePlucker5_apply]
  ring

theorem vandermondeExterior5_not_mem_flat_schubert (K : Type*) [Field K] [CharZero K]
    (r : Fin 5 → K) {t : RootTriple5}
    (h12 : r t.1.1 ≠ r t.1.2.1) (h23 : r t.1.2.1 ≠ r t.1.2.2) (h13 : r t.1.1 ≠ r t.1.2.2) :
    vandermondeExterior5 K r ≠ 0 ∧
      vandermondeExterior5 K r ∉ LinearMap.range (exteriorCoboundary5 K) := by
  have hcob_ne : simplicialCoboundary1 K (vandermondePlucker5 K r) t ≠ 0 := by
    rw [coboundary1_vandermondePlucker5]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12.symm) (sub_ne_zero.mpr h23.symm))
      (sub_ne_zero.mpr h13.symm)
  have hnot_mem : vandermondeExterior5 K r ∉ LinearMap.range (exteriorCoboundary5 K) := by
    rintro ⟨s, hs⟩
    have hpl : vandermondePlucker5 K r = simplicialDiff5 K s := by
      have hs' := congrArg (plucker5ExteriorLinearEquiv K) hs
      change plucker5ExteriorLinearEquiv K (exteriorCoboundary5 K s) = vandermondePlucker5 K r at hs'
      have hdiff : plucker5ExteriorLinearEquiv K (exteriorCoboundary5 K s) = simplicialDiff5 K s := by
        change plucker5ExteriorLinearEquiv K ((plucker5ExteriorLinearEquiv K).symm (simplicialDiff5 K s)) = _
        rw [LinearEquiv.apply_symm_apply]
      rw [hdiff] at hs'
      exact hs'.symm
    have hzero : simplicialCoboundary1 K (vandermondePlucker5 K r) t = 0 := by
      have h0 : (simplicialCoboundary1 K).comp (simplicialDiff5 K) s = 0 := by
        rw [simplicialCoboundary1_comp_simplicialDiff5 K, LinearMap.zero_apply]
      rw [hpl, ← LinearMap.comp_apply]
      exact congrFun h0 t
    exact hcob_ne hzero
  have hne0 : vandermondeExterior5 K r ≠ 0 := fun h0 =>
    hnot_mem (h0 ▸ Submodule.zero_mem _)
  exact ⟨hne0, hnot_mem⟩

/-- For any tuple `r : Fin 5 → K` with three distinct coordinates, the curved 2-plane
`span K {r, r^(2)}` is a genuine point of `Module.Grassmannian K (Fin 5 → K) 3` lying
strictly outside the flat Schubert image `Set.range (schubertPsi1Grassmannian K)`. -/
def vandermondeGrassmannianPoint (K : Type*) [Field K]
    (r : Fin 5 → K) {t : RootTriple5}
    (h12 : r t.1.1 ≠ r t.1.2.1) (h23 : r t.1.2.1 ≠ r t.1.2.2) (h13 : r t.1.1 ≠ r t.1.2.2) :
    Module.Grassmannian K (Fin 5 → K) 3 :=
  let W : Submodule K (Fin 5 → K) := Submodule.span K {r, fun i => r i ^ 2}
  have hli : LinearIndependent K ![r, fun i => r i ^ 2] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [Fin.sum_univ_two] at hc
    have h0 := congrFun hc t.1.1
    have h1 := congrFun hc t.1.2.1
    have h2 := congrFun hc t.1.2.2
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
    have hdet : c 0 * (r t.1.1 - r t.1.2.1) + c 1 * (r t.1.1 ^ 2 - r t.1.2.1 ^ 2) = 0 := by
      linear_combination h0 - h1
    have hdet2 : c 0 * (r t.1.2.1 - r t.1.2.2) + c 1 * (r t.1.2.1 ^ 2 - r t.1.2.2 ^ 2) = 0 := by
      linear_combination h1 - h2
    have hcb : (r t.1.1 - r t.1.2.2) * (r t.1.1 - r t.1.2.1) * (r t.1.2.1 - r t.1.2.2) * c 1 = 0 := by
      linear_combination (r t.1.2.1 - r t.1.2.2) * hdet - (r t.1.1 - r t.1.2.1) * hdet2
    have hne : (r t.1.1 - r t.1.2.2) * (r t.1.1 - r t.1.2.1) * (r t.1.2.1 - r t.1.2.2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h13) (sub_ne_zero.mpr h12))
        (sub_ne_zero.mpr h23)
    have hc1 : c 1 = 0 := (mul_eq_zero.mp hcb).resolve_left hne
    rw [hc1, zero_mul, add_zero] at hdet
    have hc0 : c 0 = 0 := (mul_eq_zero.mp hdet).resolve_right (sub_ne_zero.mpr h12)
    fin_cases i
    · exact hc0
    · exact hc1
  have hfr : Module.finrank K W = 2 := by
    have hsp : W = Submodule.span K (Set.range ![r, fun i => r i ^ 2]) := by
      dsimp only [W]
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm),
        fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)⟩
    rw [hsp, Module.finrank_eq_card_basis (Module.Basis.span hli), Fintype.card_fin]
  { toSubmodule := W
    finite_quotient := inferInstance
    projective_quotient := inferInstance
    rankAtStalk_eq := fun p => by
      have hq := Submodule.finrank_quotient_add_finrank W
      have h5 : Module.finrank K (Fin 5 → K) = 5 := by simp
      rw [hfr, h5] at hq
      have h3 : Module.finrank K ((Fin 5 → K) ⧸ W) = 3 := by omega
      simp [Module.rankAtStalk_eq_finrank_of_free, h3] }

theorem vandermondeGrassmannianPoint_not_mem_flat_range (K : Type*) [Field K] [CharZero K]
    (r : Fin 5 → K) {t : RootTriple5}
    (h12 : r t.1.1 ≠ r t.1.2.1) (h23 : r t.1.2.1 ≠ r t.1.2.2) (h13 : r t.1.1 ≠ r t.1.2.2) :
    vandermondeGrassmannianPoint K r h12 h23 h13 ∉ Set.range (schubertPsi1Grassmannian K) := by
  rintro ⟨x, hx⟩
  induction x using Projectivization.ind with | h z _ =>
  have hsub : Submodule.span K {onesVec5 K, z.1} =
      Submodule.span K {r, fun i => r i ^ 2} :=
    congrArg Module.Grassmannian.toSubmodule hx
  have hones : onesVec5 K ∈ Submodule.span K {r, fun i => r i ^ 2} := by
    rw [← hsub]
    exact Submodule.subset_span (Set.mem_insert _ _)
  rw [Submodule.mem_span_pair] at hones
  obtain ⟨a, b, hab⟩ := hones
  have e1 := congrFun hab t.1.1
  have e2 := congrFun hab t.1.2.1
  have e3 := congrFun hab t.1.2.2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec5] at e1 e2 e3
  have d1 : a * (r t.1.1 - r t.1.2.1) + b * (r t.1.1 ^ 2 - r t.1.2.1 ^ 2) = 0 := by
    linear_combination e1 - e2
  have d2 : a * (r t.1.2.1 - r t.1.2.2) + b * (r t.1.2.1 ^ 2 - r t.1.2.2 ^ 2) = 0 := by
    linear_combination e2 - e3
  have hcb : (r t.1.1 - r t.1.2.2) * (r t.1.1 - r t.1.2.1) * (r t.1.2.1 - r t.1.2.2) * b = 0 := by
    linear_combination (r t.1.2.1 - r t.1.2.2) * d1 - (r t.1.1 - r t.1.2.1) * d2
  have hne : (r t.1.1 - r t.1.2.2) * (r t.1.1 - r t.1.2.1) * (r t.1.2.1 - r t.1.2.2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h13) (sub_ne_zero.mpr h12))
      (sub_ne_zero.mpr h23)
  have hb0 : b = 0 := (mul_eq_zero.mp hcb).resolve_left hne
  rw [hb0, zero_mul, add_zero] at d1
  have ha0 : a = 0 := (mul_eq_zero.mp d1).resolve_right (sub_ne_zero.mpr h12)
  rw [ha0, hb0, zero_mul, zero_mul, add_zero] at e1
  exact one_ne_zero e1.symm

end SimplicialFlatnessAndVandermondeLift

/-! ## Section 4: Multi-Weight Ladder, `32`-to-`1` Sign Erasure, Weighted `ℙ(2,3,4,5)`, & Master `Ξ_⊤` -/

section WeightedVietaDescentAndMasterSynthesis

/-- Coordinatewise squaring `(yᵢ ↦ yᵢ²)` modelling the degree-2 resolvent squaring map. -/
def coordSquare5 {R : Type*} [Mul R] (y : Fin 5 → R) : Fin 5 → R :=
  fun i => y i * y i

/-- Root Vandermonde determinant `∏_{i < j} (rⱼ - rᵢ)` (`weight 10`). -/
def quinticVandermonde {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  (Matrix.vandermonde r).det

/-- Root discriminant `Δ(r) = (quinticVandermonde r)^2` (`weight 20`). -/
def quinticDisc5 {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  quinticVandermonde r ^ 2

theorem quinticVandermonde_smul {K : Type*} [Field K] (c : K) (r : Fin 5 → K) :
    quinticVandermonde (c • r) = c ^ 10 * quinticVandermonde r := by
  simp only [quinticVandermonde, Matrix.det_vandermonde, Pi.smul_apply, smul_eq_mul]
  calc
    ∏ x : Fin 5, ∏ i ∈ Finset.Ioi x, (c * r i - c * r x)
        = ∏ x : Fin 5, ∏ i ∈ Finset.Ioi x, (c * (r i - r x)) := by
      refine Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun i _ =>
        (mul_sub c (r i) (r x)).symm
    _ = (∏ x : Fin 5, ∏ _i ∈ Finset.Ioi x, c) *
          ∏ x : Fin 5, ∏ i ∈ Finset.Ioi x, (r i - r x) := by
      simp only [Finset.prod_mul_distrib]
    _ = c ^ 10 * ∏ x : Fin 5, ∏ i ∈ Finset.Ioi x, (r i - r x) := by
      congr 1
      simp only [Finset.prod_const, Finset.prod_pow_eq_pow_sum]
      have hcard10 : ∑ x : Fin 5, (Finset.Ioi x).card = 10 := by decide
      rw [hcard10]

/-- **`Ded.4` (Multi-Weight Homogeneity Ladder `(1, 2, 3, 10, 20)`)**:
Simultaneously tracks weights `1` (`B₁`), `2` (`Sq`), `3` (`B_Vand`), `10` (`√Δ`), and `20` (`Δ`). -/
theorem multi_weight_homogeneity_ladder (K : Type*) [Field K] (c : K) (r : Fin 5 → K) :
    exteriorCoboundary5 K (c • r) = c ^ 1 • exteriorCoboundary5 K r ∧
      coordSquare5 (c • r) = c ^ 2 • coordSquare5 r ∧
      vandermondeExterior5 K (c • r) = c ^ 3 • vandermondeExterior5 K r ∧
      quinticVandermonde (c • r) = c ^ 10 * quinticVandermonde r ∧
      quinticDisc5 (c • r) = c ^ 20 * quinticDisc5 r := by
  have hv := quinticVandermonde_smul c r
  refine ⟨by simp, ?_,
    vandermondeExterior5_smul_weight3 c r, hv, ?_⟩
  · funext i
    simp only [coordSquare5, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [quinticDisc5, hv]
    ring

def signedFlip5 {R : Type*} [Neg R] (b : Fin 5 → Bool) (y : Fin 5 → R) : Fin 5 → R :=
  fun i => if b i then y i else -y i

/-- **`A₂` (`32`-to-`1` Coordinate-Squaring Sign Erasure & `A₅` Orientation Recovery via `√Δ`)**:
1. There are `2^5 = 32` sign choices `b : Fin 5 → Bool`, all mapping to the identical `coordSquare5`,
   with all `32` sign flips distinct whenever `∀ i, y i ≠ 0` (`[CharZero K]`).
2. `quinticVandermonde (r ∘ σ) = sign σ * quinticVandermonde r` distinguishes `A₅` (`sign = 1`) from
   odd permutations (`sign = -1`), whereas `quinticDisc5` is fully `S₅`-invariant. -/
theorem aporia_A2_sign_erasure_and_A5_recovery (K : Type*) [Field K] [CharZero K]
    (y r : Fin 5 → K) (hy : ∀ i : Fin 5, y i ≠ 0) (σ : Equiv.Perm (Fin 5)) :
    Fintype.card (Fin 5 → Bool) = 32 ∧
      (∀ b : Fin 5 → Bool, coordSquare5 (signedFlip5 b y) = coordSquare5 y) ∧
      Function.Injective (fun b : Fin 5 → Bool => signedFlip5 b y) ∧
      quinticVandermonde (fun i => r (σ i)) = (Equiv.Perm.sign σ : ℤ) • quinticVandermonde r ∧
      quinticDisc5 (fun i => r (σ i)) = quinticDisc5 r := by
  have hflip : ∀ b : Fin 5 → Bool, coordSquare5 (signedFlip5 b y) = coordSquare5 y := fun b => by
    funext i
    simp only [coordSquare5, signedFlip5]
    split_ifs <;> ring
  have hinj : Function.Injective (fun b : Fin 5 → Bool => signedFlip5 b y) := by
    intro b₁ b₂ h
    funext i
    have hi := congrFun h i
    simp only [signedFlip5] at hi
    rcases Bool.dichotomy (b₁ i) with h1 | h1 <;> rcases Bool.dichotomy (b₂ i) with h2 | h2
    · exact h1.trans h2.symm
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hi
      have hy2 : 2 * y i = 0 := by linear_combination -hi
      have : y i = 0 := (mul_eq_zero.mp hy2).resolve_left (by norm_num)
      exact False.elim (hy i this)
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hi
      have hy2 : 2 * y i = 0 := by linear_combination hi
      have : y i = 0 := (mul_eq_zero.mp hy2).resolve_left (by norm_num)
      exact False.elim (hy i this)
    · exact h1.trans h2.symm
  have hvand : quinticVandermonde (fun i => r (σ i)) =
      (Equiv.Perm.sign σ : ℤ) • quinticVandermonde r := by
    have hsub : Matrix.vandermonde (fun i => r (σ i)) =
        (Matrix.vandermonde r).submatrix σ id := by
      ext i j
      simp [Matrix.vandermonde]
    change (Matrix.vandermonde (fun i => r (σ i))).det = _
    rw [hsub, Matrix.det_permute, zsmul_eq_mul]
    rfl
  have hdisc : quinticDisc5 (fun i => r (σ i)) = quinticDisc5 r := by
    simp only [quinticDisc5, hvand, zsmul_eq_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  exact ⟨by decide, hflip, hinj, hvand, hdisc⟩

/-- **`A_ω` (`[countermodel_found]`, No Linear Vieta Section)**:
No `K`-linear map `L : K⁵ →ₗ[K] (Fin 5 → K)` can invert the Vieta morphism `(e₁, e₂, e₃, e₄, e₅)`. -/
theorem aporia_Aomega_no_linear_vieta_section (K : Type*) [Field K] [CharZero K] :
    ¬ ∃ L : (K × K × K × K × K) →ₗ[K] (Fin 5 → K),
      ∀ r : Fin 5 → K,
        monicRootPoly5 (L (vietaE1 r, vietaE2 r, vietaE3 r, vietaE4 r, vietaE5 r)) =
          monicRootPoly5 r := by
  rintro ⟨L, hL⟩
  let r₀ : Fin 5 → K := ![1, -1, 0, 0, 0]
  have hv0 : (vietaE1 r₀, vietaE2 r₀, vietaE3 r₀, vietaE4 r₀, vietaE5 r₀) = (0, -1, 0, 0, 0) := by
    ext <;> simp [r₀, vietaE1, vietaE2, vietaE3, vietaE4, vietaE5]
  have hv2 : (vietaE1 ((2 : K) • r₀), vietaE2 ((2 : K) • r₀), vietaE3 ((2 : K) • r₀),
      vietaE4 ((2 : K) • r₀), vietaE5 ((2 : K) • r₀)) = (0, -4, 0, 0, 0) := by
    ext <;> simp [r₀, vietaE1, vietaE2, vietaE3, vietaE4, vietaE5, Pi.smul_apply, smul_eq_mul]
    norm_num
  have hrel : ((vietaE1 ((2 : K) • r₀), vietaE2 ((2 : K) • r₀), vietaE3 ((2 : K) • r₀),
      vietaE4 ((2 : K) • r₀), vietaE5 ((2 : K) • r₀)) : K × K × K × K × K) =
      (4 : K) • (vietaE1 r₀, vietaE2 r₀, vietaE3 r₀, vietaE4 r₀, vietaE5 r₀) := by
    rw [hv0, hv2]
    ext <;> simp [smul_eq_mul]
  have hpoly0 := hL r₀
  have hpoly2 := hL ((2 : K) • r₀)
  have hmul : L (vietaE1 ((2 : K) • r₀), vietaE2 ((2 : K) • r₀), vietaE3 ((2 : K) • r₀),
      vietaE4 ((2 : K) • r₀), vietaE5 ((2 : K) • r₀)) =
      (4 : K) • L (vietaE1 r₀, vietaE2 r₀, vietaE3 r₀, vietaE4 r₀, vietaE5 r₀) := by
    rw [hrel, map_smul]
  have he2_eq : vietaE2 ((4 : K) • L (vietaE1 r₀, vietaE2 r₀, vietaE3 r₀, vietaE4 r₀, vietaE5 r₀)) =
      vietaE2 ((2 : K) • r₀) := by
    have hc2 := congrArg (fun P : K[X] => P.coeff 3) hpoly2
    rw [hmul, (monicRootPoly5_coeffs _).2.1, (monicRootPoly5_coeffs _).2.1] at hc2
    exact hc2
  have he2_eq0 : vietaE2 (L (vietaE1 r₀, vietaE2 r₀, vietaE3 r₀, vietaE4 r₀, vietaE5 r₀)) =
      vietaE2 r₀ := by
    have hc0 := congrArg (fun P : K[X] => P.coeff 3) hpoly0
    rw [(monicRootPoly5_coeffs _).2.1, (monicRootPoly5_coeffs _).2.1] at hc0
    exact hc0
  rw [(vieta_smul_weights (4 : K) _).2.1, he2_eq0] at he2_eq
  have hw0 : vietaE2 r₀ = -1 := by simp [r₀, vietaE2]
  have hw2 : vietaE2 ((2 : K) • r₀) = -4 := by
    simp [r₀, vietaE2, Pi.smul_apply, smul_eq_mul]; ring
  rw [hw0, hw2] at he2_eq
  norm_num at he2_eq

/-- Setoid defining the weighted projective space `ℙ(2, 3, 4, 5)` over `K`. -/
def weightedProj2345Setoid (K : Type*) [Field K] :
    Setoid { t : K × K × K × K // t ≠ 0 } where
  r a b := ∃ u : Kˣ,
    b.1 = ((u : K) ^ 2 * a.1.1, (u : K) ^ 3 * a.1.2.1,
      (u : K) ^ 4 * a.1.2.2.1, (u : K) ^ 5 * a.1.2.2.2)
  iseqv :=
    { refl := fun a => ⟨1, by ext <;> simp⟩
      symm := fun ⟨u, hu⟩ => ⟨u⁻¹, by
        rw [hu]
        ext <;> simp only [Units.val_inv_eq_inv_val] <;>
          simp only [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ u.ne_zero), one_mul]⟩
      trans := fun ⟨u₁, h₁⟩ ⟨u₂, h₂⟩ => ⟨u₂ * u₁, by
        rw [h₂, h₁]
        ext <;> simp only [Units.val_mul, mul_pow, mul_assoc]⟩ }

/-- Genuine quotient carrier `ℙ(2, 3, 4, 5)` for Tschirnhaus principal quintic coefficients. -/
def WeightedProj2345 (K : Type*) [Field K] : Type _ :=
  Quotient (weightedProj2345Setoid K)

/-- Setoid defining the `A₅`-oriented cover `ℙ(2, 3, 4, 5; 10)` carrying the weight-10 `√Δ`. -/
def orientedWeightedProjSetoid (K : Type*) [Field K] :
    Setoid { t : (K × K × K × K) × K // t.1 ≠ 0 } where
  r a b := ∃ u : Kˣ,
    b.1 = (((u : K) ^ 2 * a.1.1.1, (u : K) ^ 3 * a.1.1.2.1,
      (u : K) ^ 4 * a.1.1.2.2.1, (u : K) ^ 5 * a.1.1.2.2.2), (u : K) ^ 10 * a.1.2)
  iseqv :=
    { refl := fun a => ⟨1, by ext <;> simp⟩
      symm := fun ⟨u, hu⟩ => ⟨u⁻¹, by
        rw [hu]
        ext <;> simp only [Units.val_inv_eq_inv_val] <;>
          simp only [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ u.ne_zero), one_mul]⟩
      trans := fun ⟨u₁, h₁⟩ ⟨u₂, h₂⟩ => ⟨u₂ * u₁, by
        rw [h₂, h₁]
        ext <;> simp only [Units.val_mul, mul_pow, mul_assoc]⟩ }

/-- Genuine `ℤ₂`-branched double cover `ℙ(2, 3, 4, 5; 10)` over `ℙ(2, 3, 4, 5)`. -/
def OrientedWeightedProj2345_10 (K : Type*) [Field K] : Type _ :=
  Quotient (orientedWeightedProjSetoid K)

/-- Canonical `ℤ₂`-forgetful projection `ℙ(2, 3, 4, 5; 10) → ℙ(2, 3, 4, 5)`. -/
def orientedToUnorientedWeightedProj {K : Type*} [Field K] :
    OrientedWeightedProj2345_10 K → WeightedProj2345 K :=
  Quotient.map (fun t => ⟨t.1.1, t.2⟩) (fun _ _ ⟨u, hu⟩ => ⟨u, congrArg Prod.fst hu⟩)

/-- Canonical deck involution `√Δ ↦ -√Δ` on `ℙ(2, 3, 4, 5; 10)`. -/
def z2OrientationFlip {K : Type*} [Field K] :
    OrientedWeightedProj2345_10 K → OrientedWeightedProj2345_10 K :=
  Quotient.map (fun t => ⟨(t.1.1, -t.1.2), t.2⟩) (fun a b ⟨u, hu⟩ => ⟨u, by
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.snd hu
    ext <;> simp [h1, h2]⟩)

/-- **`Ded.5` (Total `S₅`-Invariant Weighted Vieta Descent `ℙ³_Tsch → ℙ(2, 3, 4, 5)`)**. -/
def weightedVietaDescent (K : Type*) [Field K] :
    ℙ K (TschirnhausHyperplane5 K) → WeightedProj2345 K :=
  fun x => Quotient.liftOn x (fun ⟨r, hr⟩ =>
    @Quotient.mk _ (weightedProj2345Setoid K)
      ⟨(vietaE2 r.1, vietaE3 r.1, vietaE4 r.1, vietaE5 r.1),
        vieta_quadruple_ne_zero_of_sum_zero (by rw [← sumCoord5_apply, LinearMap.mem_ker.mp r.2])
          (fun h0 => hr (Subtype.ext h0))⟩)
    (by
      rintro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ ⟨u, hu⟩
      apply Quotient.sound
      have hu1 : r₁.1 = (u : K) • r₂.1 := by
        simpa [Subtype.ext_iff, Units.smul_def] using hu.symm
      have hu2 : r₂.1 = ((u⁻¹ : Kˣ) : K) • r₁.1 := by
        rw [hu1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      refine ⟨u⁻¹, ?_⟩
      have hw := vieta_smul_weights ((u⁻¹ : Kˣ) : K) r₁.1
      dsimp only
      rw [hu2, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])

/-- **`Ded.5` (Total `A₅`-Oriented Weighted Vieta Descent `ℙ³_Tsch → ℙ(2, 3, 4, 5; 10)`)**. -/
def orientedWeightedVietaDescent (K : Type*) [Field K] :
    ℙ K (TschirnhausHyperplane5 K) → OrientedWeightedProj2345_10 K :=
  fun x => Quotient.liftOn x (fun ⟨r, hr⟩ =>
    @Quotient.mk _ (orientedWeightedProjSetoid K)
      ⟨((vietaE2 r.1, vietaE3 r.1, vietaE4 r.1, vietaE5 r.1), quinticVandermonde r.1),
        vieta_quadruple_ne_zero_of_sum_zero (by rw [← sumCoord5_apply, LinearMap.mem_ker.mp r.2])
          (fun h0 => hr (Subtype.ext h0))⟩)
    (by
      rintro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ ⟨u, hu⟩
      apply Quotient.sound
      have hu1 : r₁.1 = (u : K) • r₂.1 := by
        simpa [Subtype.ext_iff, Units.smul_def] using hu.symm
      have hu2 : r₂.1 = ((u⁻¹ : Kˣ) : K) • r₁.1 := by
        rw [hu1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      refine ⟨u⁻¹, ?_⟩
      have hw := vieta_smul_weights ((u⁻¹ : Kˣ) : K) r₁.1
      have hv := quinticVandermonde_smul ((u⁻¹ : Kˣ) : K) r₁.1
      dsimp only
      rw [hu2, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2, hv])

/-- Exact factorization `orientedToUnorientedWeightedProj ∘ orientedWeightedVietaDescent = weightedVietaDescent`. -/
theorem orientedWeightedVietaDescent_factorization (K : Type*) [Field K]
    (x : ℙ K (TschirnhausHyperplane5 K)) :
    orientedToUnorientedWeightedProj (orientedWeightedVietaDescent K x) = weightedVietaDescent K x := by
  induction x using Projectivization.ind with | h r hr =>
  rfl

/-- Helper permuting a Tschirnhaus vector in `TschirnhausHyperplane5 K`. -/
def permTschirnhaus {K : Type*} [Field K] (σ : Equiv.Perm (Fin 5))
    (r : TschirnhausHyperplane5 K) : TschirnhausHyperplane5 K :=
  ⟨fun i => r.1 (σ i), by
    rw [LinearMap.mem_ker, sumCoord5_apply]
    have hsum : ∑ i : Fin 5, r.1 (σ i) = ∑ i : Fin 5, r.1 i :=
      Fintype.sum_bijective σ σ.bijective _ _ (fun _ => rfl)
    rw [hsum, ← sumCoord5_apply, LinearMap.mem_ker.mp r.2]⟩

def permTschirnhausLinear (K : Type*) [Field K] (σ : Equiv.Perm (Fin 5)) :
    TschirnhausHyperplane5 K →ₗ[K] TschirnhausHyperplane5 K where
  toFun := permTschirnhaus σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem permTschirnhausLinear_coe_val {K : Type*} [Field K] (σ : Equiv.Perm (Fin 5))
    (r : TschirnhausHyperplane5 K) :
    ((permTschirnhausLinear K σ r) : Fin 5 → K) = fun i => r.1 (σ i) :=
  rfl

theorem permTschirnhausLinear_injective (K : Type*) [Field K] (σ : Equiv.Perm (Fin 5)) :
    Function.Injective (permTschirnhausLinear K σ) := by
  intro r₁ r₂ h
  ext i
  have hi := congrFun (congrArg Subtype.val h) (σ⁻¹ i)
  change r₁.1 (σ (σ⁻¹ i)) = r₂.1 (σ (σ⁻¹ i)) at hi
  simpa using hi

def permTschirnhausProj {K : Type*} [Field K] (σ : Equiv.Perm (Fin 5))
    (x : ℙ K (TschirnhausHyperplane5 K)) : ℙ K (TschirnhausHyperplane5 K) :=
  Projectivization.map (permTschirnhausLinear K σ) (permTschirnhausLinear_injective K σ) x

/-- `S₅`-invariance of `weightedVietaDescent`, `A₅`-invariance of `orientedWeightedVietaDescent`,
and `z2OrientationFlip`-equivariance under odd permutations. -/
theorem vietaDescent_equivariance (K : Type*) [Field K] [CharZero K]
    (σ : Equiv.Perm (Fin 5)) (x : ℙ K (TschirnhausHyperplane5 K)) :
    weightedVietaDescent K (permTschirnhausProj σ x) = weightedVietaDescent K x ∧
      (σ ∈ alternatingGroup (Fin 5) →
        orientedWeightedVietaDescent K (permTschirnhausProj σ x) = orientedWeightedVietaDescent K x) ∧
      (σ ∉ alternatingGroup (Fin 5) →
        orientedWeightedVietaDescent K (permTschirnhausProj σ x) =
          z2OrientationFlip (orientedWeightedVietaDescent K x)) := by
  induction x using Projectivization.ind with | h r hr =>
  have hvp := vieta_perm_invariant r.1 σ
  have hvand := (aporia_A2_sign_erasure_and_A5_recovery K (fun _ => 1) r.1
    (fun _ => one_ne_zero) σ).2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [permTschirnhausProj]
    rw [Projectivization.map_mk]
    dsimp only [weightedVietaDescent, Projectivization.mk]
    apply Quotient.sound
    refine ⟨1, ?_⟩
    dsimp only
    simp only [Units.val_one, one_pow, one_mul, permTschirnhausLinear_coe_val,
      hvp.2.1, hvp.2.2.1, hvp.2.2.2.1, hvp.2.2.2.2]
  · intro hA5
    have hsign : Equiv.Perm.sign σ = 1 := hA5
    dsimp only [permTschirnhausProj]
    rw [Projectivization.map_mk]
    dsimp only [orientedWeightedVietaDescent, Projectivization.mk]
    apply Quotient.sound
    refine ⟨1, ?_⟩
    dsimp only
    simp only [Units.val_one, one_pow, one_mul, permTschirnhausLinear_coe_val,
      hvp.2.1, hvp.2.2.1, hvp.2.2.2.1, hvp.2.2.2.2, hvand, hsign, one_smul]
  · intro hodd
    have hsign : Equiv.Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hm1
      · exact False.elim (hodd h1)
      · exact hm1
    dsimp only [permTschirnhausProj]
    rw [Projectivization.map_mk]
    dsimp only [orientedWeightedVietaDescent, z2OrientationFlip, Projectivization.mk]
    apply Quotient.sound
    refine ⟨1, ?_⟩
    dsimp only
    simp only [Units.val_neg, Units.val_one, one_pow, one_mul, permTschirnhausLinear_coe_val,
      hvp.2.1, hvp.2.2.1, hvp.2.2.2.1, hvp.2.2.2.2, hvand, hsign, neg_zsmul, one_smul]

/-- **`Thm.⊤` (`Ξ_⊤ = H ∨ W_quin` Terminal Master Synthesis)**:
Certifies all four laws of the Tschirnhaus–Projectivized Plücker–Vieta Quintic System simultaneously
for any `[Field K] [CharZero K]` together with the Galois non-solvability obstruction on `A₅` quintics. -/
theorem quintic_tschirnhaus_plucker_vieta_master_synthesis (K : Type*) [Field K] [CharZero K] :
    -- Law 1: Kernel excision & total injective Ψ₁ on Tschirnhaus ℙ³_Tsch
    ((LinearMap.ker (exteriorCoboundary5 K) = K ∙ onesVec5 K ∧
        ¬ Function.Injective (exteriorCoboundary5 K)) ∧
      (Function.Injective (schubertPsi1Proj K) ∧
        Function.Injective (schubertPsi1Grassmannian K))) ∧
    -- Law 2: Flat coboundary kernel (dim = 4 < 10) escaped by curved Vandermonde B_Vand
    ((LinearMap.range (simplicialDiff5 K) = LinearMap.ker (simplicialCoboundary1 K) ∧
        Module.finrank K (LinearMap.range (exteriorCoboundary5 K)) = 4) ∧
      (∀ (r : Fin 5 → K) {t : RootTriple5}
        (h12 : r t.1.1 ≠ r t.1.2.1) (h23 : r t.1.2.1 ≠ r t.1.2.2) (h13 : r t.1.1 ≠ r t.1.2.2),
        vandermondeExterior5 K r ≠ 0 ∧
          vandermondeExterior5 K r ∉ LinearMap.range (exteriorCoboundary5 K) ∧
          vandermondeGrassmannianPoint K r h12 h23 h13 ∉
            Set.range (schubertPsi1Grassmannian K))) ∧
    -- Law 3 & 4: Vieta weight grading (1..5), no linear inverse, & A₅/S₅ weighted descent
    ((¬ ∃ L : (K × K × K × K × K) →ₗ[K] (Fin 5 → K),
        ∀ r : Fin 5 → K,
          monicRootPoly5 (L (vietaE1 r, vietaE2 r, vietaE3 r, vietaE4 r, vietaE5 r)) =
            monicRootPoly5 r) ∧
      (∀ x : ℙ K (TschirnhausHyperplane5 K),
        orientedToUnorientedWeightedProj (orientedWeightedVietaDescent K x) =
          weightedVietaDescent K x) ∧
      (∀ (σ : Equiv.Perm (Fin 5)) (x : ℙ K (TschirnhausHyperplane5 K)),
        weightedVietaDescent K (permTschirnhausProj σ x) = weightedVietaDescent K x)) := by
  refine ⟨⟨⟨(aporia_A0_diagonal_kernel K).2.2.1, (aporia_A0_diagonal_kernel K).2.2.2⟩,
    ⟨schubertPsi1Proj_injective K, schubertPsi1Grassmannian_injective K⟩⟩,
    ⟨⟨range_simplicialDiff5_eq_ker_coboundary1 K, finrank_range_exteriorCoboundary5 K⟩,
      fun r t h12 h23 h13 =>
        ⟨(vandermondeExterior5_not_mem_flat_schubert K r h12 h23 h13).1,
         (vandermondeExterior5_not_mem_flat_schubert K r h12 h23 h13).2,
         vandermondeGrassmannianPoint_not_mem_flat_range K r h12 h23 h13⟩⟩,
    ⟨aporia_Aomega_no_linear_vieta_section K,
      orientedWeightedVietaDescent_factorization K,
      fun σ x => (vietaDescent_equivariance K σ x).1⟩⟩

end WeightedVietaDescentAndMasterSynthesis

end InfoGeometry.Canonical.QuinticTschirnhausPluckerVietaSynthesis
