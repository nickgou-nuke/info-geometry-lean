/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Grassmann Product Structures, Quotients, Regressive Factorization, Shadows & Complete Poset Atlas

Wave III / Complete Extraction formalization of Hermann Grassmann's *Extension Theory* (*Die
Ausdehnungslehre*, 1862) and all remaining editorial/supplementary notes in `hmath019-endmatter.pdf`:

1. **`GA₁₇` (`Editorial Note 11, pp. 333–334`, `Nos. 48–51`, Seligman `pp. 393, 396`)**:
   Engel's 3-factor linear product classification contrasting Type 1 scalar-associative products
   with Type 2 skew/Lie/Jacobi products (`engel_note11_commutator_lie_identities`), plus the explicit
   3D vector cross-product `[countermodel_found]` (`engel_note11_crossProduct3_nonassociative_lie`)
   proving Lie/Jacobi identities without `(u × v) × w = a • (u × (v × w))`.
2. **`GA₁₈` (`Editorial Note 13, p. 334`, `Nos. 377, 384, 441`, Seligman `pp. 396–398`)**:
   Quotient transformation top exterior power equals determinant (`quotient_top_power_eq_det_smul_volume`),
   Hankel–Grassmann determinant multiplicativity via `ExteriorAlgebra.map_comp_map`
   (`grassmann_hankel_note13_det_mul`), and Jacobian functional determinant top-power identity
   for `fderiv ℝ f x` (`grassmann_no441_fderiv_top_power`).
3. **`GA₁₉` (`Editorial Note 21, pp. 336–337`, `No. 143`)**:
   Polar hyperplane reciprocity of Grassmann's supplement:
   `y ∈ bladeSupport (hodge b (ι K x)) ↔ ∑ i, b.repr x i * b.repr y i = 0`.
4. **`GA₂₀` (`Editorial Notes 34–35, pp. 343–345`, `Nos. 112–113`)**:
   Every independent `m`-blade factors as an iterated regressive product of `(n - m)` hyperplane
   `(n - 1)`-blades (`note34_blade_as_iterated_regressive_hyperplanes`), and `regressive b A (ιMulti K m w)`
   lies in `(ExteriorAlgebra.map W.subtype).range` (`note35_regressive_mem_blade_subalgebra`).
5. **`GA₂₁` (`Seligman Ch. 3 Nos. 127–130, p. 395`, `Editorial Notes 39–42`)**:
   Grassmann's exterior shadow / oblique projection theorem along complementary subspaces
   `IsCompl U W`: `regressive b (ιMulti u) (ι x * ιMulti w) = volCoord b (ιMulti u * ιMulti w) • ι (U.projection W hCompl x)`.
6. **`GA₂₂` (`Editorial Notes 68–69, pp. 357–358`, `Nos. 195–198`, & `Note 111 / No. 505, pp. 374–375, 398`)**:
   Left exterior multiplication adjointness to interior dual contraction (`extInner_ι_mul_left`),
   Binet–Cauchy & Lagrange bivector norm identities (`note69_binet_cauchy_two_blades`,
   `note69_lagrange_bivector_norm_sq`), Euclidean positive-definiteness & Cauchy–Schwarz
   (`note68_extInner_cauchy_schwarz`), and multilinear alternatization / determinant theorem
   (`note111_multilinear_alternatization`).
7. **`GA₂₃`: Unified 23-Node Ausdehnungslehre Causal Poset (`GrassmannCompleteArchetype`) & Complete Master Synthesis**.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrassmannProductQuotientAndMasterAtlas

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.ExteriorBladeIncidence
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra
open InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms

/-! ## 1. Engel Note 11: 3-Factor Linear Product Classification & Lie/Jacobi Dichotomy -/

section EngelNote11ThreeFactorClassification

/-- Associative-algebra commutator `[x, y] = x * y - y * x` modeling Grassmann–Engel Type 2
linear alternating/Lie multiplication (`Editorial Note 11, pp. 333–334`). -/
def commutatorProduct (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]
    (x y : A) : A :=
  x * y - y * x

/-- **Engel Note 11, Eqs. `(2a)`, `(2b)`, `(3)`**: the commutator satisfies square-vanishing
`[x, x] = 0`, antisymmetry `[x, y] = (-1) • [y, x]`, and the Jacobi identity. -/
theorem engel_note11_commutator_lie_identities (R : Type*) [CommRing R] {A : Type*} [Ring A]
    [Algebra R A] (x y z : A) :
    commutatorProduct R x x = 0 ∧
      commutatorProduct R x y = (-1 : R) • commutatorProduct R y x ∧
      commutatorProduct R (commutatorProduct R x y) z +
        commutatorProduct R (commutatorProduct R y z) x +
        commutatorProduct R (commutatorProduct R z x) y = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [commutatorProduct]
    exact sub_self _
  · dsimp [commutatorProduct]
    rw [neg_smul, one_smul, neg_sub]
  · dsimp [commutatorProduct]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel

/-- Canonical 3D cross product `(u × v)` on `Fin 3 → K`. -/
def crossProduct3 (K : Type*) [CommRing K] (u v : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- **`[countermodel_found]` — Engel Editorial Note 11 (`pp. 333–334`)**:
`crossProduct3` satisfies all three Type 2 Lie identities (`x × x = 0`, `x × y = -(y × x)`, and
Jacobi) yet fails EVERY Type 1 scalar-associativity law `(u × v) × w = a • (u × (v × w))`. -/
theorem engel_note11_crossProduct3_nonassociative_lie (K : Type*) [Field K] :
    (∀ u : Fin 3 → K, crossProduct3 K u u = 0) ∧
      (∀ u v : Fin 3 → K, crossProduct3 K u v = -crossProduct3 K v u) ∧
      (∀ u v w : Fin 3 → K,
        crossProduct3 K (crossProduct3 K u v) w +
          crossProduct3 K (crossProduct3 K v w) u +
          crossProduct3 K (crossProduct3 K w u) v = 0) ∧
      ¬ ∃ a : K, ∀ u v w : Fin 3 → K,
        crossProduct3 K (crossProduct3 K u v) w = a • crossProduct3 K u (crossProduct3 K v w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    ext i
    fin_cases i <;> simp [crossProduct3] <;> ring
  · intro u v
    ext i
    fin_cases i <;> simp [crossProduct3] <;> ring
  · intro u v w
    ext i
    fin_cases i <;> simp [crossProduct3] <;> ring
  · rintro ⟨a, ha⟩
    have h0 := congrFun (ha ![1, 0, 0] ![0, 1, 0] ![0, 1, 0]) 0
    simp [crossProduct3] at h0

end EngelNote11ThreeFactorClassification

/-! ## 2. Note 13, Hankel Determinant Multiplicativity, & Jacobian Top-Power (`Nos. 377, 384, 441`) -/

section QuotientHankelJacobian

/-- **Grassmann No. 384 / Note 13 (`p. 334`)**: over ANY `[CommRing R]`, pushing forward the top
basis blade under `Q : M →ₗ[R] M` multiplies it by `LinearMap.det Q`. -/
theorem quotient_top_power_eq_det_smul_volume {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) (Q : M →ₗ[R] M) :
    (ExteriorAlgebra.map Q) (b.ExteriorAlgebra Finset.univ) =
      (LinearMap.det Q) • b.ExteriorAlgebra Finset.univ := by
  have hb_top : b.ExteriorAlgebra Finset.univ = ExteriorAlgebra.ιMulti R n b := by
    have h := ιMulti_eq_det_smul_volume b b
    rw [b.det_self, one_smul] at h
    exact h.symm
  calc
    (ExteriorAlgebra.map Q) (b.ExteriorAlgebra Finset.univ)
        = (ExteriorAlgebra.map Q) (ExteriorAlgebra.ιMulti R n b) := by rw [hb_top]
    _ = ExteriorAlgebra.ιMulti R n (Q ∘ b) := ExteriorAlgebra.map_apply_ιMulti Q b
    _ = (b.det (Q ∘ b)) • b.ExteriorAlgebra Finset.univ := ιMulti_eq_det_smul_volume b (Q ∘ b)
    _ = (LinearMap.det Q) • b.ExteriorAlgebra Finset.univ := by
      rw [b.det_comp Q b, b.det_self, mul_one]

/-- **Editorial Note 13 / Hankel (1861) Determinant Multiplicativity**:
deriving `det (P ∘ₗ Q) = det P * det Q` directly from functoriality of `ExteriorAlgebra.map`
and the top-blade coordinate functional `b.ExteriorAlgebra.coord Finset.univ`. -/
theorem grassmann_hankel_note13_det_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M) (P Q : M →ₗ[R] M) :
    (b.ExteriorAlgebra.coord Finset.univ) ((ExteriorAlgebra.map Q) (b.ExteriorAlgebra Finset.univ)) =
        LinearMap.det Q ∧
      (b.ExteriorAlgebra.coord Finset.univ)
          ((ExteriorAlgebra.map (P.comp Q)) (b.ExteriorAlgebra Finset.univ)) =
        LinearMap.det P * LinearMap.det Q ∧
      LinearMap.det (P.comp Q) = LinearMap.det P * LinearMap.det Q := by
  have hQ : (b.ExteriorAlgebra.coord Finset.univ)
      ((ExteriorAlgebra.map Q) (b.ExteriorAlgebra Finset.univ)) = LinearMap.det Q := by
    rw [quotient_top_power_eq_det_smul_volume b Q, LinearMap.map_smul, b.ExteriorAlgebra.coord_apply,
      b.ExteriorAlgebra.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have hPQ_ext : (ExteriorAlgebra.map (P.comp Q)) (b.ExteriorAlgebra Finset.univ) =
      (LinearMap.det P * LinearMap.det Q) • b.ExteriorAlgebra Finset.univ := by
    rw [← ExteriorAlgebra.map_comp_map Q P, AlgHom.comp_apply,
      quotient_top_power_eq_det_smul_volume b Q, map_smul,
      quotient_top_power_eq_det_smul_volume b P, smul_smul, mul_comm]
  have hPQ_coord : (b.ExteriorAlgebra.coord Finset.univ)
      ((ExteriorAlgebra.map (P.comp Q)) (b.ExteriorAlgebra Finset.univ)) =
      LinearMap.det P * LinearMap.det Q := by
    rw [hPQ_ext, LinearMap.map_smul, b.ExteriorAlgebra.coord_apply, b.ExteriorAlgebra.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  refine ⟨hQ, hPQ_coord, ?_⟩
  rw [← hPQ_coord, quotient_top_power_eq_det_smul_volume b (P.comp Q), LinearMap.map_smul,
    b.ExteriorAlgebra.coord_apply, b.ExteriorAlgebra.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

/-- **Grassmann No. 441 (`Seligman p. 398`) — Functional Jacobian Determinant**:
for any `f : (Fin n → ℝ) → (Fin n → ℝ)` and `x : Fin n → ℝ`, the pushforward of `volume b` under
the differential `(fderiv ℝ f x).toLinearMap` equals the Jacobian determinant times `volume b`. -/
theorem grassmann_no441_fderiv_top_power {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) :
    let b := Pi.basisFun ℝ (Fin n)
    (ExteriorAlgebra.map (fderiv ℝ f x).toLinearMap) (volume b) =
        LinearMap.det (fderiv ℝ f x).toLinearMap • volume b ∧
      volCoord b ((ExteriorAlgebra.map (fderiv ℝ f x).toLinearMap) (volume b)) =
        (LinearMap.toMatrix b b (fderiv ℝ f x).toLinearMap).det := by
  intro b
  have hq : (ExteriorAlgebra.map (fderiv ℝ f x).toLinearMap) (volume b) =
      LinearMap.det (fderiv ℝ f x).toLinearMap • volume b :=
    quotient_top_power_eq_det_smul_volume b _
  refine ⟨hq, ?_⟩
  rw [hq, LinearMap.map_smul, volCoord_volume b, smul_eq_mul, mul_one, LinearMap.det_toMatrix]

end QuotientHankelJacobian

/-! ## 3. Editorial Note 21: Polar Hyperplane Reciprocity of the Supplement (`No. 143`) -/

section Note21PolarHyperplane

/-- Basis singleton `b.ExteriorAlgebra {i}` equals `ExteriorAlgebra.ι K (b i)`. -/
private theorem basis_singleton_eq_ι {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M) (i : Fin n) :
    b.ExteriorAlgebra ({i} : Finset (Fin n)) = ExteriorAlgebra.ι R (b i) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  let g := Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofCard (Finset.card_singleton i))
  have hg0 : g 0 = i := Finset.mem_singleton.mp
    ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g 0)).1 ⟨0, rfl⟩)
  change ExteriorAlgebra.ιMulti R 1 (fun k => b (g k)) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]

/-- **Editorial Note 21 (`pp. 336–337`, `No. 143`) — Polar Hyperplane Reciprocity**:
in any `[Field K]` vector space with basis `b : Fin n → V`, a vector `y` annihilates the supplement
`hodge b (ι K x)` (so `ι K y * ★(ι K x) = 0`) iff `x` and `y` are `b`-orthogonal. -/
theorem note21_polar_hyperplane_supplement {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : V) :
    y ∈ bladeSupport (hodge b (ExteriorAlgebra.ι K x)) ↔
      ∑ i : Fin n, b.repr x i * b.repr y i = 0 := by
  cases n with
  | zero =>
    have hy0 : y = 0 := by simpa using (b.sum_repr y).symm
    rw [mem_bladeSupport, hy0, map_zero, zero_mul]
    simp
  | succ m =>
    have hdeg : ExteriorAlgebra.ι K y * hodge b (ExteriorAlgebra.ι K x) ∈ ⋀[K]^(m + 1) V := by
      have hy_mem : ExteriorAlgebra.ι K y ∈ ⋀[K]^1 V := by
        rw [ExteriorAlgebra.exteriorPower, pow_one]
        exact LinearMap.mem_range_self _ y
      have hx_mem : ExteriorAlgebra.ι K x ∈ ⋀[K]^1 V := by
        rw [ExteriorAlgebra.exteriorPower, pow_one]
        exact LinearMap.mem_range_self _ x
      have hh_mem : hodge b (ExteriorAlgebra.ι K x) ∈ ⋀[K]^m V := by
        simpa using hodge_mem_exteriorPower b hx_mem
      have hprod : ExteriorAlgebra.ι K y * hodge b (ExteriorAlgebra.ι K x) ∈ ⋀[K]^(1 + m) V := by
        rw [ExteriorAlgebra.exteriorPower, pow_add]
        exact Submodule.mul_mem_mul hy_mem hh_mem
      rwa [add_comm 1 m] at hprod
    have hvol_iff : ExteriorAlgebra.ι K y * hodge b (ExteriorAlgebra.ι K x) = 0 ↔
        volCoord b (ExteriorAlgebra.ι K y * hodge b (ExteriorAlgebra.ι K x)) = 0 := by
      constructor
      · intro hz
        rw [hz, map_zero]
      · intro hvc
        have hsm := eq_volCoord_smul_volume b hdeg
        rwa [hvc, zero_smul] at hsm
    have hinner : extInner b (ExteriorAlgebra.ι K y) (ExteriorAlgebra.ι K x) =
        ∑ i : Fin (m + 1), b.repr x i * b.repr y i := by
      have hx : x = ∑ i : Fin (m + 1), b.repr x i • b i := (b.sum_repr x).symm
      have hy : y = ∑ j : Fin (m + 1), b.repr y j • b j := (b.sum_repr y).symm
      have hιx : ExteriorAlgebra.ι K x =
          ∑ i : Fin (m + 1), b.repr x i • b.ExteriorAlgebra {i} := by
        conv_lhs => rw [hx, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, basis_singleton_eq_ι]
      have hιy : ExteriorAlgebra.ι K y =
          ∑ j : Fin (m + 1), b.repr y j • b.ExteriorAlgebra {j} := by
        conv_lhs => rw [hy, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, basis_singleton_eq_ι]
      rw [hιy, hιx]
      simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right,
        extInner_basis]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp [mul_comm]
      · intro j _ hji
        simp [hji.symm]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    rw [mem_bladeSupport, hvol_iff, ← extInner_apply, hinner]

end Note21PolarHyperplane

/-! ## 4. Editorial Notes 34 & 35: Hyperplane Regressive Factorization & Blade Subalgebra (`Nos. 112–113`) -/

section Notes34_35HyperplaneMeetAndSubalgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem hodge_foldr_regressive {n : ℕ} (b : Module.Basis (Fin n) K V)
    (L : List (ExteriorAlgebra K V)) :
    hodge b (L.foldr (regressive b) (volume b)) = (L.map (hodge b)).prod := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, hodge_regressive, ih]

private theorem foldr_regressive_change_basis {n : ℕ} (b b' : Module.Basis (Fin n) K V)
    (L : List (ExteriorAlgebra K V)) :
    ∃ u : Kˣ, L.foldr (regressive b') (volume b') = (u : K) • L.foldr (regressive b) (volume b) := by
  induction L with
  | nil =>
    refine ⟨(b.isUnit_det b').unit, ?_⟩
    exact volume_change_basis b b'
  | cons a as ih =>
    obtain ⟨u, hu⟩ := ih
    let dU : Kˣ := (b.isUnit_det b').unit
    have hreg : regressive b' a (as.foldr (regressive b) (volume b)) =
        (dU⁻¹ : Kˣ) • regressive b a (as.foldr (regressive b) (volume b)) := by
      have hd := det_smul_regressive_change_basis b b' a (as.foldr (regressive b) (volume b))
      have hd' : (dU : K) • regressive b' a (as.foldr (regressive b) (volume b)) =
          regressive b a (as.foldr (regressive b) (volume b)) := hd
      have h := congrArg ((dU⁻¹ : Kˣ) • ·) hd'
      simpa only [Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_smul] using h
    refine ⟨u * dU⁻¹, ?_⟩
    simp only [List.foldr_cons]
    rw [hu, regressive_smul, hreg, Units.smul_def, smul_smul, Units.val_mul]

private theorem list_prod_units_smul_ι {k : ℕ} (u : Fin k → Kˣ) (x : Fin k → V) :
    ∃ U : Kˣ,
      (List.ofFn fun j : Fin k => (u j : K) • ExteriorAlgebra.ι K (x j)).prod =
        (U : K) • ExteriorAlgebra.ιMulti K k x := by
  induction k with
  | zero =>
    exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨U', hU'⟩ := ih (u ∘ Fin.succ) (x ∘ Fin.succ)
    refine ⟨u 0 * U', ?_⟩
    rw [List.ofFn_succ, List.prod_cons]
    have hrest :
        (List.ofFn fun i : Fin k => ((u i.succ : K) • ExteriorAlgebra.ι K (x i.succ))).prod =
          (U' : K) • ExteriorAlgebra.ιMulti K k (x ∘ Fin.succ) := hU'
    rw [hrest, smul_mul_assoc, mul_smul_comm, smul_smul, Units.val_mul,
      ExteriorAlgebra.ιMulti_succ_apply]
    rfl

/-- **Editorial Note 34 (`pp. 343–344`, `No. 112`) — Dual Hyperplane Regressive Factorization**:
in dimension `n ≥ 1`, any linearly independent `m`-blade (`m ≤ n`) equals a nonzero scalar unit times
an iterated regressive product of `(n - m)` hyperplane `(n - 1)`-blades. -/
theorem note34_blade_as_iterated_regressive_hyperplanes {n m : ℕ} (b : Module.Basis (Fin n) K V)
    (hm : m ≤ n) (v : Fin m → V) (hv : LinearIndependent K v) :
    ∃ (c : Kˣ) (w : Fin (n - m) → Fin (n - 1) → V),
      (∀ j : Fin (n - m), LinearIndependent K (w j)) ∧
        ExteriorAlgebra.ιMulti K m v =
          (c : K) •
            (List.ofFn fun j : Fin (n - m) =>
              ExteriorAlgebra.ιMulti K (n - 1) (w j)).foldr (regressive b) (volume b) := by
  let U := Submodule.span K (Set.range v)
  have : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨U', hU'⟩ := U.exists_isCompl
  have hfinV : Module.finrank K V = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hfinU : Module.finrank K U = m := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hadd := Submodule.finrank_add_eq_of_isCompl hU'
  have hfinU' : Module.finrank K U' = n - m := by omega
  let bU' := Module.finBasisOfFinrankEq K U' hfinU'
  let u' : Fin (n - m) → V := fun j => (bU' j : V)
  have hu'_li : LinearIndependent K u' :=
    bU'.linearIndependent.map' U'.subtype (Submodule.ker_subtype U')
  have hspan_u' : Submodule.span K (Set.range u') = U' := by
    have hrng : Set.range u' = U'.subtype '' Set.range bU' := Set.range_comp U'.subtype bU'
    rw [hrng, ← Submodule.map_span, bU'.span_eq, Submodule.map_subtype_top]
  have happ_li : LinearIndependent K (Fin.append v u') := by
    rw [linearIndependent_append_iff_disjoint v u' hv hu'_li, hspan_u']
    exact hU'.disjoint
  have happ_span : Submodule.span K (Set.range (Fin.append v u')) = ⊤ := by
    rw [range_fin_append, Submodule.span_union, hspan_u']
    exact hU'.sup_eq_top
  have hmn : m + (n - m) = n := Nat.add_sub_of_le hm
  let e := finCongr hmn
  let bFam : Fin n → V := (Fin.append v u') ∘ e.symm
  have hb_li : LinearIndependent K bFam := happ_li.comp e.symm e.symm.injective
  have hb_span : ⊤ ≤ Submodule.span K (Set.range bFam) := by
    have hrng : Set.range bFam = Set.range (Fin.append v u') := by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    rw [hrng, happ_span]
  let b' : Module.Basis (Fin n) K V := Module.Basis.mk hb_li hb_span
  have hb'_val : ∀ i : Fin n, b' i = Fin.append v u' (e.symm i) := fun i => by
    simp [b', Module.Basis.mk_apply, bFam]
  by_cases hn0 : n = 0
  · subst hn0
    have hm0 : m = 0 := by omega
    subst hm0
    refine ⟨1, fun j => j.elim0, fun j => j.elim0, ?_⟩
    have hv0 : ExteriorAlgebra.ιMulti K 0 v = 1 := ExteriorAlgebra.ιMulti_zero_apply _
    have hvol0 : volume b = 1 := by
      have huniv : (Finset.univ : Finset (Fin 0)) = ∅ := rfl
      change b.ExteriorAlgebra Finset.univ = 1
      rw [huniv, basis_empty]
    simp [hv0, hvol0]
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
  let sHyp : Fin (n - m) → Finset (Fin n) := fun j =>
    (Finset.univ : Finset (Fin n)).erase (e (Fin.natAdd m j))
  have hsHyp_card : ∀ j : Fin (n - m), (sHyp j).card = n - 1 := fun j => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  let w : Fin (n - m) → Fin (n - 1) → V := fun j k =>
    b' (Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (s := sHyp j) (hsHyp_card j)) k)
  have hw_li : ∀ j : Fin (n - m), LinearIndependent K (w j) := fun j =>
    b'.linearIndependent.comp _
      (Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard (s := sHyp j) (hsHyp_card j))).injective
  have hw_eq : ∀ j : Fin (n - m), ExteriorAlgebra.ιMulti K (n - 1) (w j) =
      b'.ExteriorAlgebra (sHyp j) := fun j => by
    rw [ExteriorAlgebra.basis_apply_ofCard b' (hsHyp_card j)]
    rfl
  have hsHyp_compl : ∀ j : Fin (n - m), (sHyp j)ᶜ = {e (Fin.natAdd m j)} := fun j => by
    ext x
    simp [sHyp]
  have hhodge_hyp : ∀ j : Fin (n - m),
      hodge b' (ExteriorAlgebra.ιMulti K (n - 1) (w j)) =
        (orientationUnit (K := K) (sHyp j) : K) • ExteriorAlgebra.ι K (u' j) := fun j => by
    rw [hw_eq j, hodge_basis b' (sHyp j), hsHyp_compl j, basis_singleton_eq_ι, hb'_val,
      Equiv.symm_apply_apply, Fin.append_right]
  let L := List.ofFn fun j : Fin (n - m) => ExteriorAlgebra.ιMulti K (n - 1) (w j)
  have hL_hodge : hodge b' (L.foldr (regressive b') (volume b')) =
      (List.ofFn fun j : Fin (n - m) =>
        (orientationUnit (K := K) (sHyp j) : K) • ExteriorAlgebra.ι K (u' j)).prod := by
    rw [hodge_foldr_regressive b' L]
    dsimp [L]
    rw [List.map_ofFn]
    exact congrArg List.prod (congrArg List.ofFn (funext hhodge_hyp))
  obtain ⟨U1, hU1⟩ := list_prod_units_smul_ι
    (fun j => orientationUnit (K := K) (sHyp j)) u'
  rw [hU1] at hL_hodge
  let embV : Fin m ↪ Fin n :=
    ⟨fun i => ⟨i.val, by omega⟩, fun i j h => by ext; simpa using congrArg Fin.val h⟩
  let sV : Finset (Fin n) := Finset.univ.map embV
  have hsV_card : sV.card = m := by simp [sV]
  let embU' : Fin (n - m) ↪ Fin n :=
    ⟨fun j => ⟨m + j.val, by omega⟩, fun i j h => by
      ext
      have hv' := congrArg Fin.val h
      dsimp at hv'
      omega⟩
  let sU' : Finset (Fin n) := Finset.univ.map embU'
  have hsU'_card : sU'.card = n - m := by simp [sU']
  have hsV_compl : sVᶜ = sU' := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_compl] at hx
      have hge : m ≤ x.val := by
        by_contra hlt
        apply hx
        refine Finset.mem_map.mpr ⟨⟨x.val, by omega⟩, Finset.mem_univ _, ?_⟩
        ext
        rfl
      refine Finset.mem_map.mpr ⟨⟨x.val - m, by omega⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext (by change m + (x.val - m) = x.val; omega)
    · rw [Finset.card_compl, Fintype.card_fin, hsV_card, hsU'_card]
  let gV := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := sV) hsV_card)
  let gU' := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := sU') hsU'_card)
  have hbV_eq : b'.ExteriorAlgebra sV = ExteriorAlgebra.ιMulti K m (fun i => b' (gV i)) := by
    rw [ExteriorAlgebra.basis_apply_ofCard b' hsV_card]
    rfl
  have hbU'_eq : b'.ExteriorAlgebra sU' = ExteriorAlgebra.ιMulti K (n - m) (fun j => b' (gU' j)) := by
    rw [ExteriorAlgebra.basis_apply_ofCard b' hsU'_card]
    rfl
  have hspan_gV : Submodule.span K (Set.range (fun i => b' (gV i))) = Submodule.span K (Set.range v) := by
    have hrng : Set.range (fun i => b' (gV i)) = Set.range v := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        have hmem : gV i ∈ sV :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
            (Set.powersetCard.ofCard (s := sV) hsV_card) (gV i)).1 ⟨i, rfl⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hmem
        refine ⟨j, ?_⟩
        dsimp only
        rw [← hj, hb'_val]
        have heinv : e.symm (embV j) = Fin.castAdd (n - m) j := by
          ext; rfl
        rw [heinv, Fin.append_left]
      · rintro ⟨j, rfl⟩
        have hmem : embV j ∈ sV := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
        obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := sV) hsV_card) (embV j)).2 hmem
        refine ⟨i, ?_⟩
        dsimp only
        rw [hi, hb'_val]
        have heinv : e.symm (embV j) = Fin.castAdd (n - m) j := by ext; rfl
        rw [heinv, Fin.append_left]
    rw [hrng]
  have hspan_gU' : Submodule.span K (Set.range (fun j => b' (gU' j))) =
      Submodule.span K (Set.range u') := by
    have hrng : Set.range (fun j => b' (gU' j)) = Set.range u' := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        have hmem : gU' j ∈ sU' :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
            (Set.powersetCard.ofCard (s := sU') hsU'_card) (gU' j)).1 ⟨j, rfl⟩
        obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hmem
        refine ⟨k, ?_⟩
        dsimp only
        rw [← hk, hb'_val]
        have heinv : e.symm (embU' k) = Fin.natAdd m k := by ext; rfl
        rw [heinv, Fin.append_right]
      · rintro ⟨k, rfl⟩
        have hmem : embU' k ∈ sU' := Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩
        obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := sU') hsU'_card) (embU' k)).2 hmem
        refine ⟨j, ?_⟩
        dsimp only
        rw [hj, hb'_val]
        have heinv : e.symm (embU' k) = Fin.natAdd m k := by ext; rfl
        rw [heinv, Fin.append_right]
    rw [hrng]
  have hgV_li : LinearIndependent K (fun i => b' (gV i)) := b'.linearIndependent.comp _ gV.injective
  have hgU'_li : LinearIndependent K (fun j => b' (gU' j)) := b'.linearIndependent.comp _ gU'.injective
  obtain ⟨cV, hcV⟩ := (plucker_span_eq_iff_proportional v (fun i => b' (gV i)) hv hgV_li).mp
    hspan_gV.symm
  obtain ⟨cU', hcU'⟩ := (plucker_span_eq_iff_proportional u' (fun j => b' (gU' j)) hu'_li hgU'_li).mp
    hspan_gU'.symm
  have hL_foldr_b' : ∃ C : Kˣ, ExteriorAlgebra.ιMulti K m v =
      (C : K) • (hodge b').symm ((hodge b') (L.foldr (regressive b') (volume b'))) := by
    have hh_sV : hodge b' (b'.ExteriorAlgebra sV) =
        (orientationUnit (K := K) sV : K) • ExteriorAlgebra.ιMulti K (n - m) (fun j => b' (gU' j)) := by
      rw [hodge_basis b' sV, hsV_compl, hbU'_eq]
    have hL_eval : hodge b' (L.foldr (regressive b') (volume b')) =
        ((U1 * cU' * (orientationUnit (K := K) sV)⁻¹ * cV⁻¹ : Kˣ) : K) •
          hodge b' (ExteriorAlgebra.ιMulti K m v) := by
      rw [hL_hodge, hcU', ← hbU'_eq]
      have hb_inv : b'.ExteriorAlgebra sU' =
          (((orientationUnit (K := K) sV)⁻¹ : Kˣ) : K) • hodge b' (b'.ExteriorAlgebra sV) := by
        rw [hodge_basis b' sV, hsV_compl, smul_smul, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_smul]
      rw [hb_inv, hbV_eq]
      have hιv : ExteriorAlgebra.ιMulti K m (fun i => b' (gV i)) =
          ((cV⁻¹ : Kˣ) : K) • ExteriorAlgebra.ιMulti K m v := by
        rw [hcV, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      rw [hιv, map_smul, smul_smul, smul_smul, smul_smul]
      simp only [Units.val_mul]
    let Ck : Kˣ := U1 * cU' * (orientationUnit (K := K) sV)⁻¹ * cV⁻¹
    refine ⟨Ck⁻¹, ?_⟩
    apply (hodge b').injective
    rw [map_smul, LinearEquiv.apply_symm_apply, hL_eval, smul_smul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  obtain ⟨C, hC⟩ := hL_foldr_b'
  rw [LinearEquiv.symm_apply_apply] at hC
  obtain ⟨uFold, huFold⟩ := foldr_regressive_change_basis b b' L
  refine ⟨C * uFold, w, hw_li, ?_⟩
  rw [hC, huFold, smul_smul]
  rfl

/-- **Editorial Note 35 (`pp. 344–345`, `No. 113`) — Blade Subalgebra Containment**:
for ANY multivector `A : ExteriorAlgebra K V` and ANY family `w : Fin m → V`, the regressive product
`regressive b A (ιMulti K m w)` belongs to the subalgebra generated by `span K (Set.range w)`. -/
theorem note35_regressive_mem_blade_subalgebra {n m : ℕ} (b : Module.Basis (Fin n) K V)
    (A : ExteriorAlgebra K V) (w : Fin m → V) :
    regressive b A (ExteriorAlgebra.ιMulti K m w) ∈
      (ExteriorAlgebra.map (Submodule.span K (Set.range w)).subtype).range := by
  let W := Submodule.span K (Set.range w)
  let algW : Subalgebra K (ExteriorAlgebra K V) := (ExteriorAlgebra.map W.subtype).range
  change regressive b A (ExteriorAlgebra.ιMulti K m w) ∈ algW
  by_cases hw : LinearIndependent K w
  · have : Module.Finite K V := Module.Finite.of_basis b
    obtain ⟨W', hW'⟩ := W.exists_isCompl
    have hfinV : Module.finrank K V = n := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    have hfinW : Module.finrank K W = m := by
      rw [finrank_span_eq_card hw, Fintype.card_fin]
    have hadd := Submodule.finrank_add_eq_of_isCompl hW'
    have hfinW' : Module.finrank K W' = n - m := by omega
    have hmn : m ≤ n := by omega
    let bW' := Module.finBasisOfFinrankEq K W' hfinW'
    let w' : Fin (n - m) → V := fun j => (bW' j : V)
    have hw'_li : LinearIndependent K w' :=
      bW'.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
    have hspan_w' : Submodule.span K (Set.range w') = W' := by
      have hrng : Set.range w' = W'.subtype '' Set.range bW' := Set.range_comp W'.subtype bW'
      rw [hrng, ← Submodule.map_span, bW'.span_eq, Submodule.map_subtype_top]
    have happ_li : LinearIndependent K (Fin.append w w') := by
      rw [linearIndependent_append_iff_disjoint w w' hw hw'_li, hspan_w']
      exact hW'.disjoint
    have happ_span : Submodule.span K (Set.range (Fin.append w w')) = ⊤ := by
      rw [range_fin_append, Submodule.span_union, hspan_w']
      exact hW'.sup_eq_top
    let e := finCongr (Nat.add_sub_of_le hmn)
    let bFam : Fin n → V := (Fin.append w w') ∘ e.symm
    have hb_li : LinearIndependent K bFam := happ_li.comp e.symm e.symm.injective
    have hb_span : ⊤ ≤ Submodule.span K (Set.range bFam) := by
      have hrng : Set.range bFam = Set.range (Fin.append w w') := by
        rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
      rw [hrng, happ_span]
    let b' : Module.Basis (Fin n) K V := Module.Basis.mk hb_li hb_span
    have hb'_val : ∀ i : Fin n, b' i = Fin.append w w' (e.symm i) := fun i => by
      simp [b', Module.Basis.mk_apply, bFam]
    let embW : Fin m ↪ Fin n :=
      ⟨fun i => ⟨i.val, by omega⟩, fun i j h => by ext; simpa using congrArg Fin.val h⟩
    let sW : Finset (Fin n) := Finset.univ.map embW
    have hsW_card : sW.card = m := by simp [sW]
    have hb'_mem_W : ∀ i ∈ sW, b' i ∈ W := fun i hi => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      rw [hb'_val]
      have heinv : e.symm (embW j) = Fin.castAdd (n - m) j := by ext; rfl
      rw [heinv, Fin.append_left]
      exact Submodule.subset_span (Set.mem_range_self j)
    let gW := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := sW) hsW_card)
    have hspan_gW : Submodule.span K (Set.range (fun i => b' (gW i))) = W := by
      have hrng : Set.range (fun i => b' (gW i)) = Set.range w := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          have hmem : gW i ∈ sW :=
            (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
              (Set.powersetCard.ofCard (s := sW) hsW_card) (gW i)).1 ⟨i, rfl⟩
          obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hmem
          refine ⟨j, ?_⟩
          dsimp only
          rw [← hj, hb'_val]
          have heinv : e.symm (embW j) = Fin.castAdd (n - m) j := by ext; rfl
          rw [heinv, Fin.append_left]
        · rintro ⟨j, rfl⟩
          have hmem : embW j ∈ sW := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
          obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
            (Set.powersetCard.ofCard (s := sW) hsW_card) (embW j)).2 hmem
          refine ⟨i, ?_⟩
          dsimp only
          rw [hi, hb'_val]
          have heinv : e.symm (embW j) = Fin.castAdd (n - m) j := by ext; rfl
          rw [heinv, Fin.append_left]
      rw [hrng]
    have hgW_li : LinearIndependent K (fun i => b' (gW i)) := b'.linearIndependent.comp _ gW.injective
    obtain ⟨cW, hcW⟩ := (plucker_span_eq_iff_proportional w (fun i => b' (gW i)) hw hgW_li).mp
      hspan_gW.symm
    have hbW_eq : ExteriorAlgebra.ιMulti K m (fun i => b' (gW i)) = b'.ExteriorAlgebra sW := by
      rw [ExteriorAlgebra.basis_apply_ofCard b' hsW_card]
      rfl
    rw [hcW, hbW_eq, ← det_smul_regressive_change_basis b b', regressive_smul]
    refine Subalgebra.smul_mem algW (Subalgebra.smul_mem algW ?_ _) _
    have hA : A = ∑ s : Finset (Fin n), b'.ExteriorAlgebra.repr A s • b'.ExteriorAlgebra s :=
      (b'.ExteriorAlgebra.sum_repr A).symm
    have hsum_reg : regressive b' A (b'.ExteriorAlgebra sW) =
        ∑ s : Finset (Fin n), b'.ExteriorAlgebra.repr A s •
          regressive b' (b'.ExteriorAlgebra s) (b'.ExteriorAlgebra sW) := by
      conv_lhs => rw [hA]
      clear hA
      dsimp only [regressive]
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
    rw [hsum_reg]
    refine Subalgebra.sum_mem algW fun s _ => Subalgebra.smul_mem algW ?_ _
    by_cases hdisj : Disjoint sᶜ sWᶜ
    · let t := sᶜ.disjUnion sWᶜ hdisj
      have ht_compl : tᶜ = s ∩ sW := by
        ext x
        simp [t]
      let sc' : Set.powersetCard (Fin n) sᶜ.card := Set.powersetCard.ofCard rfl
      let sWc' : Set.powersetCard (Fin n) sWᶜ.card := Set.powersetCard.ofCard rfl
      have hdisj' : Disjoint (sc' : Finset (Fin n)) (sWc' : Finset (Fin n)) := hdisj
      let ε : ℤˣ := (Set.powersetCard.permOfDisjoint hdisj').sign
      have hmul : b'.ExteriorAlgebra sᶜ * b'.ExteriorAlgebra sWᶜ =
          ((ε : ℤ) : K) • b'.ExteriorAlgebra t := by
        have hm := ExteriorAlgebra.basis_mul_of_disjoint b' sc' sWc' hdisj'
        rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K] at hm
        exact hm
      have hsymm_t : (hodge b').symm (b'.ExteriorAlgebra t) =
          (orientationUnit (K := K) tᶜ : K) • b'.ExteriorAlgebra tᶜ := by
        apply (hodge b').injective
        rw [LinearEquiv.apply_symm_apply, map_smul, hodge_basis b' tᶜ, compl_compl, smul_smul,
          orientationUnit_mul_self, one_smul]
      have hbas : regressive b' (b'.ExteriorAlgebra s) (b'.ExteriorAlgebra sW) =
          ((orientationUnit (K := K) s : K) * (orientationUnit (K := K) sW : K) *
            ((ε : ℤ) : K) * (orientationUnit (K := K) tᶜ : K)) •
              b'.ExteriorAlgebra (s ∩ sW) := by
        dsimp [regressive]
        rw [hodge_basis b' s, hodge_basis b' sW, smul_mul_assoc, mul_smul_comm, hmul, map_smul,
          map_smul, map_smul, hsymm_t, ht_compl, smul_smul, smul_smul, smul_smul]
      rw [hbas]
      refine Subalgebra.smul_mem algW ?_ _
      rw [ExteriorAlgebra.basis_apply b' (s ∩ sW)]
      let gI := Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.prodEquiv.symm (s ∩ sW)).2
      let yI : Fin (s ∩ sW).card → W := fun i => by
        refine ⟨b' (gI i), hb'_mem_W (gI i) ?_⟩
        have hmem : gI i ∈ s ∩ sW :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (gI i)).1 ⟨i, rfl⟩
        exact (Finset.mem_inter.mp hmem).2
      refine ⟨ExteriorAlgebra.ιMulti K (s ∩ sW).card yI, ?_⟩
      change ExteriorAlgebra.map W.subtype (ExteriorAlgebra.ιMulti K (s ∩ sW).card yI) =
        ExteriorAlgebra.ιMulti K (s ∩ sW).card (fun i => b' (gI i))
      rw [ExteriorAlgebra.map_apply_ιMulti]
      rfl
    · have hmul0 : b'.ExteriorAlgebra sᶜ * b'.ExteriorAlgebra sWᶜ = 0 := by
        simpa only [Set.powersetCard.val_ofCard] using
          (ExteriorAlgebra.basis_mul_of_not_disjoint b'
            (Set.powersetCard.ofCard (s := sᶜ) rfl)
            (Set.powersetCard.ofCard (s := sWᶜ) rfl) hdisj)
      have hbas0 : regressive b' (b'.ExteriorAlgebra s) (b'.ExteriorAlgebra sW) = 0 := by
        apply (hodge b').injective
        rw [hodge_regressive b', hodge_basis b' s, hodge_basis b' sW, smul_mul_assoc,
          mul_smul_comm, hmul0, smul_zero, smul_zero, map_zero]
      rw [hbas0]
      exact Subalgebra.zero_mem algW
  · rw [(ιMulti_eq_zero_iff w).mpr hw, regressive_zero]
    exact Subalgebra.zero_mem algW

end Notes34_35HyperplaneMeetAndSubalgebra

/-! ## 5. Seligman Nos. 127–130 / Notes 39–42: Grassmann's Exterior Shadow Projection -/

section ExteriorShadowProjection

private theorem ιMulti_finCongr {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m n : ℕ} (h : n = m) (f : Fin m → V) :
    ExteriorAlgebra.ιMulti K n (f ∘ finCongr h) = ExteriorAlgebra.ιMulti K m f := by
  subst h
  rfl

/-- **Seligman Ch. 3 Nos. 127–130 (`p. 395`), Notes 39–42 — Exterior Shadow / Oblique Projection**:
for complementary subspaces `U = span u` and `W = span w` (`IsCompl U W`), the top product
`ιMulti u * ιMulti w` has nonzero volume coordinate and for every `x : V`,
`regressive b (ιMulti u) (ι x * ιMulti w) = volCoord b (ιMulti u * ιMulti w) • ι (U.projection W hCompl x)`. -/
theorem grassmann_no129_exterior_projection {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n r s : ℕ} (b : Module.Basis (Fin n) K V) (u : Fin r → V) (w : Fin s → V)
    (hu : LinearIndependent K u) (hw : LinearIndependent K w)
    (hCompl : IsCompl (Submodule.span K (Set.range u)) (Submodule.span K (Set.range w))) :
    r + s = n ∧
      volCoord b (ExteriorAlgebra.ιMulti K r u * ExteriorAlgebra.ιMulti K s w) ≠ 0 ∧
      ∀ x : V,
        regressive b (ExteriorAlgebra.ιMulti K r u)
            (ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K s w) =
          volCoord b (ExteriorAlgebra.ιMulti K r u * ExteriorAlgebra.ιMulti K s w) •
            ExteriorAlgebra.ι K
              ((Submodule.span K (Set.range u)).projection
                (Submodule.span K (Set.range w)) hCompl x) := by
  let U := Submodule.span K (Set.range u)
  let W := Submodule.span K (Set.range w)
  have huw_li : LinearIndependent K (Fin.append u w) := by
    rw [linearIndependent_append_iff_disjoint u w hu hw]
    exact hCompl.disjoint
  have huw_span : Submodule.span K (Set.range (Fin.append u w)) = ⊤ := by
    rw [range_fin_append, Submodule.span_union]
    exact hCompl.sup_eq_top
  have hrs : r + s = n := by
    have h1 := finrank_span_eq_card huw_li
    have h2 : Module.finrank K V = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    rw [huw_span, finrank_top, Fintype.card_fin] at h1
    omega
  have hprod_ne : ExteriorAlgebra.ιMulti K r u * ExteriorAlgebra.ιMulti K s w ≠ 0 := by
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
    exact ιMulti_ne_zero_of_linearIndependent _ huw_li
  have hprod_mem : ExteriorAlgebra.ιMulti K r u * ExteriorAlgebra.ιMulti K s w ∈ ⋀[K]^n V := by
    have hmem : ExteriorAlgebra.ιMulti K r u * ExteriorAlgebra.ιMulti K s w ∈ ⋀[K]^(r + s) V := by
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
      exact ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩
    simpa [hrs] using hmem
  have hvol_ne : volCoord b (ExteriorAlgebra.ιMulti K r u * ExteriorAlgebra.ιMulti K s w) ≠ 0 := by
    intro h0
    apply hprod_ne
    have hsm := eq_volCoord_smul_volume b hprod_mem
    rwa [h0, zero_smul] at hsm
  refine ⟨hrs, hvol_ne, fun x => ?_⟩
  let u₀ : V := U.projection W hCompl x
  let w₀ : V := W.projection U hCompl.symm x
  have hx_split : x = u₀ + w₀ := (Submodule.projection_add_projection_eq_self hCompl x).symm
  have hw₀_mem : w₀ ∈ W := Submodule.projection_apply_mem hCompl.symm x
  have hu₀_mem : u₀ ∈ U := Submodule.projection_apply_mem hCompl x
  have hw_ann : ExteriorAlgebra.ι K w₀ * ExteriorAlgebra.ιMulti K s w = 0 :=
    (ι_mul_ιMulti_eq_zero_iff w hw w₀).mpr hw₀_mem
  have hx_wedge : ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K s w =
      ExteriorAlgebra.ι K u₀ * ExteriorAlgebra.ιMulti K s w := by
    rw [hx_split, map_add, add_mul, hw_ann, add_zero]
  change regressive b (ExteriorAlgebra.ιMulti K r u)
      (ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K s w) =
    volCoord b (ExteriorAlgebra.ιMulti K r u * ExteriorAlgebra.ιMulti K s w) •
      ExteriorAlgebra.ι K u₀
  rw [hx_wedge]
  by_cases hu0 : u₀ = 0
  · simp [hu0]
  · have : Module.Finite K U := Module.Finite.span_of_finite K (Set.finite_range u)
    let u₀U : U := ⟨u₀, hu₀_mem⟩
    have hu₀U_ne : u₀U ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
    let L : Submodule K U := K ∙ u₀U
    obtain ⟨L', hL'⟩ := L.exists_isCompl
    have hfinU : Module.finrank K U = r := by rw [finrank_span_eq_card hu, Fintype.card_fin]
    have hfinL : Module.finrank K L = 1 := finrank_span_singleton hu₀U_ne
    have haddL := Submodule.finrank_add_eq_of_isCompl hL'
    have hr1 : 1 ≤ r := by omega
    have hfinL' : Module.finrank K L' = r - 1 := by omega
    let bL' := Module.finBasisOfFinrankEq K L' hfinL'
    let u_tailU : Fin (r - 1) → U := fun j => (bL' j : U)
    have htailU_li : LinearIndependent K u_tailU :=
      bL'.linearIndependent.map' L'.subtype (Submodule.ker_subtype L')
    have hspan_tailU : Submodule.span K (Set.range u_tailU) = L' := by
      have hrng : Set.range u_tailU = L'.subtype '' Set.range bL' := Set.range_comp L'.subtype bL'
      rw [hrng, ← Submodule.map_span, bL'.span_eq, Submodule.map_subtype_top]
    have hu0U_notMem : u₀U ∉ Submodule.span K (Set.range u_tailU) := by
      rw [hspan_tailU]
      intro hmem
      have huL : u₀U ∈ L := Submodule.mem_span_singleton_self u₀U
      have hbot := hL'.disjoint.le_bot ⟨huL, hmem⟩
      exact hu₀U_ne ((Submodule.mem_bot K).mp hbot)
    have hconsU_li : LinearIndependent K (Fin.cons u₀U u_tailU) :=
      linearIndependent_finCons.2 ⟨htailU_li, hu0U_notMem⟩
    let u_tail : Fin (r - 1) → V := fun j => (u_tailU j : V)
    have hcons_eq : Fin.cons u₀ u_tail = U.subtype ∘ Fin.cons u₀U u_tailU := by
      ext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> rfl
    have hcons_li : LinearIndependent K (Fin.cons u₀ u_tail) := by
      rw [hcons_eq]
      exact hconsU_li.map' U.subtype (Submodule.ker_subtype U)
    have hspan_consU : Submodule.span K (Set.range (Fin.cons u₀U u_tailU)) = ⊤ := by
      have hrng : Set.range (Fin.cons u₀U u_tailU) = {u₀U} ∪ Set.range u_tailU := by
        ext z
        simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨i, rfl⟩
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨j, rfl⟩
        · rintro (rfl | ⟨j, rfl⟩)
          · exact ⟨0, rfl⟩
          · exact ⟨j.succ, rfl⟩
      rw [hrng, Submodule.span_union, hspan_tailU]
      exact hL'.sup_eq_top
    have hspan_cons : Submodule.span K (Set.range (Fin.cons u₀ u_tail)) = U := by
      rw [hcons_eq, Set.range_comp, ← Submodule.map_span, hspan_consU, Submodule.map_subtype_top]
    have hkr : r - 1 + 1 = r := Nat.sub_add_cancel hr1
    let fam : Fin r → V := (Fin.cons u₀ u_tail) ∘ (finCongr hkr).symm
    have hfam_li : LinearIndependent K fam := hcons_li.comp _ (finCongr hkr).symm.injective
    have hspan_fam : Submodule.span K (Set.range fam) = U := by
      have hrng : Set.range fam = Set.range (Fin.cons u₀ u_tail) := by
        rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
      rw [hrng, hspan_cons]
    obtain ⟨c, hc⟩ := (plucker_span_eq_iff_proportional u fam hu hfam_li).mp hspan_fam.symm
    have hfam_ι : ExteriorAlgebra.ιMulti K r fam =
        ExteriorAlgebra.ι K u₀ * ExteriorAlgebra.ιMulti K (r - 1) u_tail := by
      dsimp [fam]
      rw [ιMulti_finCongr hkr.symm, ExteriorAlgebra.ιMulti_succ_apply]
      rfl
    have hu_eq : ExteriorAlgebra.ιMulti K r u =
        (c : K) • (ExteriorAlgebra.ι K u₀ * ExteriorAlgebra.ιMulti K (r - 1) u_tail) := by
      rw [hc, hfam_ι]
    have h1_eq : ExteriorAlgebra.ιMulti K 1 ![u₀] = ExteriorAlgebra.ι K u₀ := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      rfl
    have h103 := grassmann_no103_blade b (by omega : 1 + (r - 1) + s = n) ![u₀]
      (ExteriorAlgebra.ιMulti_range K (r - 1) ⟨u_tail, rfl⟩)
      (ExteriorAlgebra.ιMulti_range K s ⟨w, rfl⟩)
    rw [h1_eq] at h103
    rw [hu_eq, smul_regressive, h103, smul_smul, smul_mul_assoc, LinearMap.map_smul, smul_eq_mul]

end ExteriorShadowProjection

/-! ## 6. Notes 68–69 & Note 111 / No. 505: Adjointness, Binet–Cauchy, Cauchy–Schwarz, Alternatization -/

section BinetCauchyCauchySchwarzAlternatization

/-- Genuine non-commutativity witness for the exterior/Clifford product (`e₀ ∧ e₁ ≠ e₁ ∧ e₀`
on `ℝ²`). -/
theorem exterior_clifford_noncommutative_witness :
    ¬ Commute
      (ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 0))
      (ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 1)) := by
  intro h
  let b := Pi.basisFun ℝ (Fin 2)
  have hsum : ExteriorAlgebra.ι ℝ (b 0) * ExteriorAlgebra.ι ℝ (b 1) +
      ExteriorAlgebra.ι ℝ (b 1) * ExteriorAlgebra.ι ℝ (b 0) = 0 := by
    have hsq := ExteriorAlgebra.ι_sq_zero (R := ℝ) (b 0 + b 1)
    rw [map_add, add_mul, mul_add, mul_add, ExteriorAlgebra.ι_sq_zero,
      ExteriorAlgebra.ι_sq_zero, zero_add, add_zero] at hsq
    exact hsq
  change ExteriorAlgebra.ι ℝ (b 0) * ExteriorAlgebra.ι ℝ (b 1) =
    ExteriorAlgebra.ι ℝ (b 1) * ExteriorAlgebra.ι ℝ (b 0) at h
  rw [← h, ← two_smul ℝ] at hsum
  have hprod0 : ExteriorAlgebra.ι ℝ (b 0) * ExteriorAlgebra.ι ℝ (b 1) = 0 :=
    (smul_eq_zero.mp hsum).resolve_left two_ne_zero
  have hli : ExteriorAlgebra.ιMulti ℝ 2 b ≠ 0 :=
    ιMulti_ne_zero_of_linearIndependent b b.linearIndependent
  have h2 : ExteriorAlgebra.ιMulti ℝ 2 b =
      ExteriorAlgebra.ι ℝ (b 0) * ExteriorAlgebra.ι ℝ (b 1) := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  exact hli (h2.trans hprod0)

/-- Dual basis contraction of basis element with index absent vanishes (`contractLeft`). -/
private theorem contractLeft_dualBasis_notMem {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V) (i : Fin n) (s : Finset (Fin n))
    (his : i ∉ s) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i)
        (b.ExteriorAlgebra s) = 0 := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl]
  let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl)
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i)
      (ExteriorAlgebra.ιMulti K s.card (fun k => b (g k))) = 0
  have hzero : ∀ {m : ℕ} (v : Fin m → V), (∀ k, b.dualBasis i (v k) = 0) →
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i)
        (ExteriorAlgebra.ιMulti K m v) = 0 := by
    intro m
    induction m with
    | zero => intro _ _; simp [CliffordAlgebra.contractLeft_one]
    | succ m ih =>
      intro v hv
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      have hι0 : CliffordAlgebra.ι (0 : QuadraticForm K V) (v 0) = ExteriorAlgebra.ι K (v 0) := rfl
      have hcm := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm K V))
        (b.dualBasis i) (v 0) (ExteriorAlgebra.ιMulti K m (Matrix.vecTail v))
      rw [hι0] at hcm
      rw [hcm, hv 0, zero_smul, zero_sub, ih (Matrix.vecTail v) (fun k => hv k.succ),
        mul_zero, neg_zero]
  refine hzero (fun k => b (g k)) fun k => ?_
  have hmem : g k ∈ s :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g k)).1 ⟨k, rfl⟩
  have hne : g k ≠ i := fun h => his (h ▸ hmem)
  rw [b.dualBasis_apply_self, ite_eq_right hne]

private theorem ι_mul_basis_notMem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (i : Fin n) (s : Finset (Fin n)) (his : i ∉ s) :
    ∃ ε : ℤˣ, ExteriorAlgebra.ι K (b i) * b.ExteriorAlgebra s =
      ((ε : ℤ) : K) • b.ExteriorAlgebra (insert i s) := by
  have hd : Disjoint ({i} : Finset (Fin n)) s := Finset.disjoint_singleton_left.mpr his
  let s0 : Set.powersetCard (Fin n) 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  let ss : Set.powersetCard (Fin n) s.card := Set.powersetCard.ofCard rfl
  have hd' : Disjoint (s0 : Finset (Fin n)) (ss : Finset (Fin n)) := hd
  have hunion : ({i} : Finset (Fin n)).disjUnion s hd = insert i s := by
    ext x
    simp
  have hsu : b.ExteriorAlgebra (Set.powersetCard.disjUnion hd') =
      b.ExteriorAlgebra (insert i s) := congrArg b.ExteriorAlgebra hunion
  refine ⟨(Set.powersetCard.permOfDisjoint hd').sign, ?_⟩
  have hm := ExteriorAlgebra.basis_mul_of_disjoint b s0 ss hd'
  have hs0 : b.ExteriorAlgebra s0 = ExteriorAlgebra.ι K (b i) := basis_singleton_eq_ι b i
  have hse : b.ExteriorAlgebra ss = b.ExteriorAlgebra s := rfl
  rw [hs0, hse, hsu, Units.smul_def, ← Int.cast_smul_eq_zsmul K] at hm
  exact hm

private theorem contractLeft_dualBasis_basis_mem {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V) (i : Fin n) (s : Finset (Fin n))
    (his : i ∈ s) :
    ∃ ε : ℤˣ,
      ExteriorAlgebra.ι K (b i) * b.ExteriorAlgebra (s.erase i) =
          ((ε : ℤ) : K) • b.ExteriorAlgebra s ∧
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i)
            (b.ExteriorAlgebra s) =
          ((ε : ℤ) : K) • b.ExteriorAlgebra (s.erase i) := by
  obtain ⟨ε, hmul⟩ := ι_mul_basis_notMem b i (s.erase i) (Finset.notMem_erase i s)
  rw [Finset.insert_erase his] at hmul
  refine ⟨ε, hmul, ?_⟩
  have hinv : b.ExteriorAlgebra s =
      ((ε : ℤ) : K) • (ExteriorAlgebra.ι K (b i) * b.ExteriorAlgebra (s.erase i)) := by
    have hsq0 : ((ε : ℤ) * (ε : ℤ)) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self ε, Units.val_one]
    have hsq : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rw [← Int.cast_mul, hsq0, Int.cast_one]
    rw [hmul, smul_smul, hsq, one_smul]
  rw [hinv, LinearMap.map_smul]
  congr 1
  have hι0 : CliffordAlgebra.ι (0 : QuadraticForm K V) (b i) = ExteriorAlgebra.ι K (b i) := rfl
  have hcm := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm K V)) (b.dualBasis i)
    (b i) (b.ExteriorAlgebra (s.erase i))
  rw [hι0] at hcm
  rw [hcm, b.dualBasis_apply_self, ite_eq_left rfl, one_smul,
    contractLeft_dualBasis_notMem b i (s.erase i) (Finset.notMem_erase i s), mul_zero, sub_zero]

/-- **Editorial Note 68 / Interior-Exterior Adjointness**:
for every basis `b`, left exterior multiplication by `ι K u` is adjoint to left interior contraction
by `b.toDualEquiv u` with respect to `extInner b` across ALL multivector grades. -/
theorem extInner_ι_mul_left {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (u : V) (X Y : ExteriorAlgebra K V) :
    extInner b (ExteriorAlgebra.ι K u * X) Y =
      extInner b X
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.toDualEquiv u) Y) := by
  have hbas : ∀ (i : Fin n) (s t : Finset (Fin n)),
      extInner b (ExteriorAlgebra.ι K (b i) * b.ExteriorAlgebra s) (b.ExteriorAlgebra t) =
        extInner b (b.ExteriorAlgebra s)
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i)
            (b.ExteriorAlgebra t)) := fun i s t => by
    by_cases his : i ∈ s
    · have hd : ¬ Disjoint ({i} : Finset (Fin n)) s :=
        fun hd => Finset.disjoint_singleton_left.mp hd his
      have hmul0 : ExteriorAlgebra.ι K (b i) * b.ExteriorAlgebra s = 0 := by
        rw [← basis_singleton_eq_ι b i]
        simpa only [Set.powersetCard.val_ofCard] using
          (ExteriorAlgebra.basis_mul_of_not_disjoint b
            (Set.powersetCard.ofCard (Finset.card_singleton i))
            (Set.powersetCard.ofCard (s := s) rfl) hd)
      rw [hmul0, LinearMap.map_zero, LinearMap.zero_apply]
      by_cases hit : i ∈ t
      · obtain ⟨ε, _, hcon⟩ := contractLeft_dualBasis_basis_mem b i t hit
        have hne : s ≠ t.erase i := fun h => by
          have : i ∈ t.erase i := h ▸ his
          exact Finset.notMem_erase i t this
        rw [hcon, extInner_smul_right, extInner_basis, ite_eq_right hne, mul_zero]
      · rw [contractLeft_dualBasis_notMem b i t hit, LinearMap.map_zero]
    · by_cases hit : i ∈ t
      · obtain ⟨ε, hmul, hcon⟩ := contractLeft_dualBasis_basis_mem b i t hit
        by_cases hst : s = t.erase i
        · subst hst
          rw [hmul, hcon, extInner_smul_left, extInner_smul_right, extInner_basis, extInner_basis,
            ite_eq_left rfl, ite_eq_left rfl]
        · have hinsert : insert i s ≠ t := fun h => hst (by
            have : s = (insert i s).erase i := (Finset.erase_insert his).symm
            rw [h] at this
            exact this)
          obtain ⟨ε', hmul'⟩ := ι_mul_basis_notMem b i s his
          rw [hmul', hcon, extInner_smul_left, extInner_smul_right, extInner_basis, extInner_basis,
            ite_eq_right hinsert, ite_eq_right hst, mul_zero, mul_zero]
      · obtain ⟨ε', hmul'⟩ := ι_mul_basis_notMem b i s his
        have hne : insert i s ≠ t := fun h => hit (h ▸ Finset.mem_insert_self i s)
        rw [hmul', contractLeft_dualBasis_notMem b i t hit, extInner_smul_left, extInner_basis,
          ite_eq_right hne, mul_zero, LinearMap.map_zero]
  have hu : u = ∑ i : Fin n, b.repr u i • b i := (b.sum_repr u).symm
  have hX : X = ∑ s : Finset (Fin n), b.ExteriorAlgebra.repr X s • b.ExteriorAlgebra s :=
    (b.ExteriorAlgebra.sum_repr X).symm
  have hY : Y = ∑ t : Finset (Fin n), b.ExteriorAlgebra.repr Y t • b.ExteriorAlgebra t :=
    (b.ExteriorAlgebra.sum_repr Y).symm
  rw [hu]
  simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc,
    LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [hX]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [hY]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have hdual : b.toDualEquiv (b i) = b.dualBasis i := by
    change b.toDualEquiv (b i) = b.map b.toDualEquiv i
    rw [Module.Basis.map_apply]
  rw [hdual]
  exact hbas i s t

private theorem toDualEquiv_eq_extInner {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (u v : V) :
    (b.toDualEquiv u) v = extInner b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K v) := by
  have h1_eval : extInner b 1 (1 : ExteriorAlgebra K V) = 1 := by
    rw [← basis_empty b]
    exact extInner_basis b ∅ ∅
  have h := extInner_ι_mul_left b u 1 (ExteriorAlgebra.ι K v)
  rw [mul_one, CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one,
    extInner_smul_right, h1_eval, mul_one] at h
  exact h.symm

/-- **Editorial Note 69 (`No. 198`) — Binet–Cauchy Inner Product for Two-Blades**:
`[u ∧ v | w ∧ z] = [u | w] [v | z] - [u | z] [v | w]` over any `[Field K]`. -/
theorem note69_binet_cauchy_two_blades {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (u v w z : V) :
    extInner b (ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v)
        (ExteriorAlgebra.ι K w * ExteriorAlgebra.ι K z) =
      extInner b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K w) *
          extInner b (ExteriorAlgebra.ι K v) (ExteriorAlgebra.ι K z) -
        extInner b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K z) *
          extInner b (ExteriorAlgebra.ι K v) (ExteriorAlgebra.ι K w) := by
  rw [extInner_ι_mul_left]
  have hιw : CliffordAlgebra.ι (0 : QuadraticForm K V) w = ExteriorAlgebra.ι K w := rfl
  have hιz : CliffordAlgebra.ι (0 : QuadraticForm K V) z = ExteriorAlgebra.ι K z := rfl
  have hcl : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.toDualEquiv u)
      (ExteriorAlgebra.ι K w * ExteriorAlgebra.ι K z) =
      (b.toDualEquiv u w) • ExteriorAlgebra.ι K z -
        (b.toDualEquiv u z) • ExteriorAlgebra.ι K w := by
    rw [← hιw, CliffordAlgebra.contractLeft_ι_mul, hιw, CliffordAlgebra.contractLeft_ι,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rw [hcl, map_sub, extInner_smul_right, extInner_smul_right,
    toDualEquiv_eq_extInner b u w, toDualEquiv_eq_extInner b u z]

/-- **Lagrange's Identity (`No. 197`)**: squared exterior norm of a bivector `u ∧ v`. -/
theorem note69_lagrange_bivector_norm_sq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (u v : V) :
    extInner b (ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v)
        (ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) =
      extInner b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K u) *
          extInner b (ExteriorAlgebra.ι K v) (ExteriorAlgebra.ι K v) -
        (extInner b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K v)) ^ 2 := by
  rw [note69_binet_cauchy_two_blades, sq, extInner_symm b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K v)]

/-- **Editorial Note 68 — Euclidean Positive-Definiteness & Cauchy–Schwarz** over `ℝ`:
`0 ≤ [X | X]`, `[X | X] = 0 ↔ X = 0`, and `[X | Y]^2 ≤ [X | X] [Y | Y]`. -/
theorem note68_extInner_cauchy_schwarz {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (X Y : ExteriorAlgebra ℝ V) :
    0 ≤ extInner b X X ∧
      (extInner b X X = 0 ↔ X = 0) ∧
      (extInner b X Y) ^ 2 ≤ extInner b X X * extInner b Y Y := by
  have hnonneg : ∀ Z : ExteriorAlgebra ℝ V, 0 ≤ extInner b Z Z := fun Z => by
    rw [extInner_eq_sum_repr]
    exact Finset.sum_nonneg fun s _ => mul_self_nonneg _
  have hdef : ∀ Z : ExteriorAlgebra ℝ V, extInner b Z Z = 0 ↔ Z = 0 := fun Z => by
    constructor
    · intro h0
      rw [extInner_eq_sum_repr] at h0
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_self_nonneg _)] at h0
      apply b.ExteriorAlgebra.repr.injective
      ext s
      simpa using mul_self_eq_zero.mp (h0 s (Finset.mem_univ s))
    · intro h0
      subst h0
      simp
  refine ⟨hnonneg X, hdef X, ?_⟩
  by_cases hY : extInner b Y Y = 0
  · have hY0 : Y = 0 := (hdef Y).mp hY
    subst hY0
    simp
  · have hY_pos : 0 < extInner b Y Y := lt_of_le_of_ne (hnonneg Y) (Ne.symm hY)
    let t : ℝ := extInner b X Y / extInner b Y Y
    have hq := hnonneg (X - t • Y)
    have hexp : extInner b (X - t • Y) (X - t • Y) =
        extInner b X X - (extInner b X Y) ^ 2 / extInner b Y Y := by
      rw [LinearMap.map_sub₂, map_sub, map_sub, extInner_smul_left, extInner_smul_right,
        extInner_smul_left, extInner_smul_right, extInner_symm b Y X]
      dsimp [t]
      field_simp [hY]
      ring
    rw [hexp, sub_nonneg, div_le_iff₀ hY_pos] at hq
    exact hq

/-- **Editorial Note 111 / Grassmann No. 505 (`pp. 374–375, 398`) — Multilinear Alternatization**:
1. Every alternatized `n`-multilinear functional `L` over `[CommRing R]` scales by `b.det v`.
2. Alternatizing the product of `n` linear functionals `φ : Fin n → Dual R M` produces the matrix
   determinant `(Matrix.of fun i j => φ i (v j)).det`. -/
theorem note111_multilinear_alternatization {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M)
    (L : MultilinearMap R (fun _ : Fin n => M) R) (φ : Fin n → Module.Dual R M)
    (v : Fin n → M) :
    MultilinearMap.alternatization L v = (MultilinearMap.alternatization L b) * b.det v ∧
      MultilinearMap.alternatization ((MultilinearMap.mkPiRing R (Fin n) (1 : R)).compLinearMap φ) v =
        (Matrix.of fun i j => φ i (v j)).det := by
  refine ⟨?_, ?_⟩
  · have h := alternatingMap_apply_eq_det_smul b (MultilinearMap.alternatization L) v
    rw [smul_eq_mul, mul_comm] at h
    exact h
  · rw [MultilinearMap.alternatization_apply, ← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    simp [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]

end BinetCauchyCauchySchwarzAlternatization

/-! ## 7. Complete 23-Node Ausdehnungslehre Causal Poset & Master Synthesis (`GA₁`–`GA₂₃`) -/

section CompletePosetAndMasterAtlas

/-- Unified 23-node non-linear acyclic causal poset covering ALL extracted archetypes across
`hmath019-endmatter.pdf`:
- `GA1`–`GA8` (Wave I): Foundations, Poincaré contraction, codim-1 vs 4D bivector, No. 103 & Note 31,
  normal shadow & inertia, No. 511 Pfaff jet vanishing, No. 518 Darboux chain, Cayley bordered Pfaffian-5.
- `GA9`–`GA16` (Wave II): Plücker subspace equivalence, No. 87 meet dichotomy, exterior Cramer,
  circle space & Note 97, No. 512 syzygy, Note 114 Pfaffian systems, Lie No. 503 symplectic bound,
  Darboux odd/even normal-form dichotomy.
- `GA17`–`GA22` (Wave III): Note 11 3-factor Lie classification, Note 13 / Hankel / Jacobian det,
  Note 21 polar hyperplane, Notes 34–35 hyperplane meet & blade subalgebra, No. 129 exterior projection,
  Notes 68–69 & 111 Binet–Cauchy / Cauchy–Schwarz / alternatization.
- `GA23`: Unified Ausdehnungslehre Endmatter Master Synthesis. -/
inductive GrassmannCompleteArchetype : Type
  | GA1_GradedCommutativityHodgeSquare
  | GA2_PoincareContractionBasisCovariance
  | GA3_CodimOneVsDim4CompoundBivector
  | GA4_No103ShuffleAndNote31Countermodel
  | GA5_NormalShadowReciprocityAndPolarization
  | GA6_No511PfaffJetVanishing
  | GA7_No518ExteriorDivisionDarbouxChain
  | GA8_CayleyBorderedPfaffian5
  | GA9_PluckerSubspaceEquivalence
  | GA10_RegressiveSubspaceMeetDichotomy
  | GA11_ExteriorCramerRule
  | GA12_CircleSpaceMullerAndSyncyclic
  | GA13_No512ContractionSyzygyReduction
  | GA14_Note114PfaffianSystems
  | GA15_No503LieSymplecticIsotropicBound
  | GA16_Nos522_527DarbouxClassDichotomy
  | GA17_Note11ThreeFactorLieDichotomy
  | GA18_Note13HankelQuotientJacobianDet
  | GA19_Note21PolarHyperplaneSupplement
  | GA20_Notes34_35HyperplaneMeetSubalgebra
  | GA21_No129ExteriorShadowProjection
  | GA22_Notes68_69BinetCauchyAlternatization
  | GA23_CompleteAusdehnungslehreSynthesis
  deriving DecidableEq, Repr

open GrassmannCompleteArchetype

/-- Downward-closed ancestor bitmask in `Fin 23` giving a fast, verified partial order. -/
def gaCompleteAncMask (x : GrassmannCompleteArchetype) : Nat :=
  let m0 := 1 <<< 0
  let m1 := m0 ||| (1 <<< 1)
  let m2 := m1 ||| (1 <<< 2)
  let m3 := m1 ||| (1 <<< 3)
  let m4 := m3 ||| (1 <<< 4)
  let m5 := m0 ||| (1 <<< 5)
  let m6 := m5 ||| (1 <<< 6)
  let m7 := m6 ||| (1 <<< 7)
  let m8 := m0 ||| (1 <<< 8)
  let m9 := m3 ||| m8 ||| (1 <<< 9)
  let m10 := m8 ||| (1 <<< 10)
  let m11 := m4 ||| m8 ||| (1 <<< 11)
  let m12 := m5 ||| (1 <<< 12)
  let m13 := m12 ||| (1 <<< 13)
  let m14 := m0 ||| (1 <<< 14)
  let m15 := m6 ||| m12 ||| m14 ||| (1 <<< 15)
  let m16 := m0 ||| (1 <<< 16)
  let m17 := m8 ||| (1 <<< 17)
  let m18 := m4 ||| (1 <<< 18)
  let m19 := m2 ||| m8 ||| (1 <<< 19)
  let m20 := m9 ||| (1 <<< 20)
  let m21 := m4 ||| m8 ||| (1 <<< 21)
  let m22 := (1 <<< 23) - 1
  match x with
  | GA1_GradedCommutativityHodgeSquare => m0
  | GA2_PoincareContractionBasisCovariance => m1
  | GA3_CodimOneVsDim4CompoundBivector => m2
  | GA4_No103ShuffleAndNote31Countermodel => m3
  | GA5_NormalShadowReciprocityAndPolarization => m4
  | GA6_No511PfaffJetVanishing => m5
  | GA7_No518ExteriorDivisionDarbouxChain => m6
  | GA8_CayleyBorderedPfaffian5 => m7
  | GA9_PluckerSubspaceEquivalence => m8
  | GA10_RegressiveSubspaceMeetDichotomy => m9
  | GA11_ExteriorCramerRule => m10
  | GA12_CircleSpaceMullerAndSyncyclic => m11
  | GA13_No512ContractionSyzygyReduction => m12
  | GA14_Note114PfaffianSystems => m13
  | GA15_No503LieSymplecticIsotropicBound => m14
  | GA16_Nos522_527DarbouxClassDichotomy => m15
  | GA17_Note11ThreeFactorLieDichotomy => m16
  | GA18_Note13HankelQuotientJacobianDet => m17
  | GA19_Note21PolarHyperplaneSupplement => m18
  | GA20_Notes34_35HyperplaneMeetSubalgebra => m19
  | GA21_No129ExteriorShadowProjection => m20
  | GA22_Notes68_69BinetCauchyAlternatization => m21
  | GA23_CompleteAusdehnungslehreSynthesis => m22

private def gaCompleteOfIdx : Nat → GrassmannCompleteArchetype
  | 0 => GA1_GradedCommutativityHodgeSquare
  | 1 => GA2_PoincareContractionBasisCovariance
  | 2 => GA3_CodimOneVsDim4CompoundBivector
  | 3 => GA4_No103ShuffleAndNote31Countermodel
  | 4 => GA5_NormalShadowReciprocityAndPolarization
  | 5 => GA6_No511PfaffJetVanishing
  | 6 => GA7_No518ExteriorDivisionDarbouxChain
  | 7 => GA8_CayleyBorderedPfaffian5
  | 8 => GA9_PluckerSubspaceEquivalence
  | 9 => GA10_RegressiveSubspaceMeetDichotomy
  | 10 => GA11_ExteriorCramerRule
  | 11 => GA12_CircleSpaceMullerAndSyncyclic
  | 12 => GA13_No512ContractionSyzygyReduction
  | 13 => GA14_Note114PfaffianSystems
  | 14 => GA15_No503LieSymplecticIsotropicBound
  | 15 => GA16_Nos522_527DarbouxClassDichotomy
  | 16 => GA17_Note11ThreeFactorLieDichotomy
  | 17 => GA18_Note13HankelQuotientJacobianDet
  | 18 => GA19_Note21PolarHyperplaneSupplement
  | 19 => GA20_Notes34_35HyperplaneMeetSubalgebra
  | 20 => GA21_No129ExteriorShadowProjection
  | 21 => GA22_Notes68_69BinetCauchyAlternatization
  | _ => GA23_CompleteAusdehnungslehreSynthesis

private theorem gaCompleteAncMask_injective {a b : GrassmannCompleteArchetype}
    (h : gaCompleteAncMask a = gaCompleteAncMask b) : a = b := by
  have hlog : ∀ x : GrassmannCompleteArchetype,
      gaCompleteOfIdx (Nat.log2 (gaCompleteAncMask x)) = x := fun x => by
    cases x <;> decide
  rw [← hlog a, ← hlog b, h]

def gaCompleteLe (a b : GrassmannCompleteArchetype) : Prop :=
  (gaCompleteAncMask a &&& gaCompleteAncMask b) = gaCompleteAncMask a

instance : DecidableRel gaCompleteLe := fun a b =>
  inferInstanceAs (Decidable ((gaCompleteAncMask a &&& gaCompleteAncMask b) = gaCompleteAncMask a))

instance : PartialOrder GrassmannCompleteArchetype where
  le := gaCompleteLe
  le_refl a := by
    dsimp [gaCompleteLe]
    exact Nat.and_self (gaCompleteAncMask a)
  le_trans a b c hab hbc := by
    dsimp [gaCompleteLe] at hab hbc ⊢
    rw [← hab, Nat.and_assoc, hbc]
  le_antisymm a b hab hba := by
    dsimp [gaCompleteLe] at hab hba
    have hmask : gaCompleteAncMask a = gaCompleteAncMask b := by
      rw [← hab, Nat.and_comm, hba]
    exact gaCompleteAncMask_injective hmask

instance : DecidableLE GrassmannCompleteArchetype := fun a b =>
  inferInstanceAs (Decidable (gaCompleteLe a b))

instance : DecidableLT GrassmannCompleteArchetype := fun a b => by
  change Decidable (gaCompleteLe a b ∧ ¬ gaCompleteLe b a)
  infer_instance

/-- Explicit non-linear branching witnesses across all 4 lanes of the 23-node causal poset. -/
theorem grassmann_complete_poset_branching :
    ¬ (GA17_Note11ThreeFactorLieDichotomy ≤ GA18_Note13HankelQuotientJacobianDet) ∧
      ¬ (GA18_Note13HankelQuotientJacobianDet ≤ GA17_Note11ThreeFactorLieDichotomy) ∧
      ¬ (GA20_Notes34_35HyperplaneMeetSubalgebra ≤ GA21_No129ExteriorShadowProjection) ∧
      ¬ (GA21_No129ExteriorShadowProjection ≤ GA20_Notes34_35HyperplaneMeetSubalgebra) ∧
      ¬ (GA12_CircleSpaceMullerAndSyncyclic ≤ GA16_Nos522_527DarbouxClassDichotomy) ∧
      ¬ (GA16_Nos522_527DarbouxClassDichotomy ≤ GA12_CircleSpaceMullerAndSyncyclic) ∧
      GA1_GradedCommutativityHodgeSquare < GA2_PoincareContractionBasisCovariance ∧
      GA2_PoincareContractionBasisCovariance < GA4_No103ShuffleAndNote31Countermodel ∧
      GA4_No103ShuffleAndNote31Countermodel < GA10_RegressiveSubspaceMeetDichotomy ∧
      GA10_RegressiveSubspaceMeetDichotomy < GA21_No129ExteriorShadowProjection ∧
      GA21_No129ExteriorShadowProjection < GA23_CompleteAusdehnungslehreSynthesis ∧
      GA1_GradedCommutativityHodgeSquare < GA17_Note11ThreeFactorLieDichotomy ∧
      GA17_Note11ThreeFactorLieDichotomy < GA23_CompleteAusdehnungslehreSynthesis := by
  decide

/-- Complete unified master synthesis uniting Waves I, II, and III (`GA₁`–`GA₂₃`) of
`hmath019-endmatter.pdf` in a single kernel-checked proposition. -/
theorem grassmann_complete_endmatter_master_synthesis :
    -- Wave I & Wave II master syntheses
    (let b5 := Pi.basisFun ℝ (Fin 5)
     let A := ExteriorAlgebra.ι ℝ (b5 0) * ExteriorAlgebra.ι ℝ (b5 1)
     let B := ExteriorAlgebra.ι ℝ (b5 0) * ExteriorAlgebra.ι ℝ (b5 2)
     let C := ExteriorAlgebra.ι ℝ (b5 3) * ExteriorAlgebra.ι ℝ (b5 4)
     regressive b5 (A * C) (B * C) ≠ C * regressive b5 (A * B) C) ∧
      (sigPos circleBilin.toQuadraticMap = 1 ∧ sigNeg circleBilin.toQuadraticMap = 3) ∧
      -- GA17: 3D cross product Jacobi identity & non-associativity countermodel
      (¬ ∃ a : ℝ, ∀ u v w : Fin 3 → ℝ,
        crossProduct3 ℝ (crossProduct3 ℝ u v) w = a • crossProduct3 ℝ u (crossProduct3 ℝ v w)) ∧
      -- GA18: Top exterior power of differential = Jacobian determinant
      (∀ (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ),
        let b := Pi.basisFun ℝ (Fin 3)
        (ExteriorAlgebra.map (fderiv ℝ f x).toLinearMap) (volume b) =
          LinearMap.det (fderiv ℝ f x).toLinearMap • volume b) ∧
      -- GA19: Polar hyperplane reciprocity
      (∀ (x y : Fin 4 → ℝ),
        let b := Pi.basisFun ℝ (Fin 4)
        y ∈ bladeSupport (hodge b (ExteriorAlgebra.ι ℝ x)) ↔
          ∑ i : Fin 4, b.repr x i * b.repr y i = 0) ∧
      -- GA20: Regressive meet belongs to blade subalgebra
      (∀ (A : ExteriorAlgebra ℝ (Fin 4 → ℝ)) (w : Fin 2 → (Fin 4 → ℝ)),
        regressive (Pi.basisFun ℝ (Fin 4)) A (ExteriorAlgebra.ιMulti ℝ 2 w) ∈
          (ExteriorAlgebra.map (Submodule.span ℝ (Set.range w)).subtype).range) ∧
      -- GA21: Grassmann exterior shadow projection
      (∀ (u w : Fin 2 → (Fin 4 → ℝ)), LinearIndependent ℝ u → LinearIndependent ℝ w →
          ∀ (hCompl : IsCompl (Submodule.span ℝ (Set.range u)) (Submodule.span ℝ (Set.range w)))
            (x : Fin 4 → ℝ),
        let b := Pi.basisFun ℝ (Fin 4)
        regressive b (ExteriorAlgebra.ιMulti ℝ 2 u)
            (ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ιMulti ℝ 2 w) =
          volCoord b (ExteriorAlgebra.ιMulti ℝ 2 u * ExteriorAlgebra.ιMulti ℝ 2 w) •
            ExteriorAlgebra.ι ℝ
              ((Submodule.span ℝ (Set.range u)).projection
                (Submodule.span ℝ (Set.range w)) hCompl x)) ∧
      -- GA22: Lagrange bivector norm & Cauchy–Schwarz & Multilinear alternatization
      (∀ (u v : Fin 3 → ℝ),
        let b := Pi.basisFun ℝ (Fin 3)
        extInner b (ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v)
            (ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v) =
          extInner b (ExteriorAlgebra.ι ℝ u) (ExteriorAlgebra.ι ℝ u) *
              extInner b (ExteriorAlgebra.ι ℝ v) (ExteriorAlgebra.ι ℝ v) -
            (extInner b (ExteriorAlgebra.ι ℝ u) (ExteriorAlgebra.ι ℝ v)) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact grassmann_endmatter_master_synthesis.2.2.2.1
  · exact ⟨circleBilin_signature.1, circleBilin_signature.2⟩
  · exact (engel_note11_crossProduct3_nonassociative_lie ℝ).2.2.2
  · intro f x b
    exact (grassmann_no441_fderiv_top_power f x).1
  · intro x y b
    exact note21_polar_hyperplane_supplement b x y
  · intro A w
    exact note35_regressive_mem_blade_subalgebra (Pi.basisFun ℝ (Fin 4)) A w
  · intro u w hu hw hCompl x b
    exact (grassmann_no129_exterior_projection b u w hu hw hCompl).2.2 x
  · intro u v b
    exact note69_lagrange_bivector_norm_sq b u v

end CompletePosetAndMasterAtlas

end InfoGeometry.Canonical.GrassmannProductQuotientAndMasterAtlas
