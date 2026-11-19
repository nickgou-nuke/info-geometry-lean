/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
import InfoGeometry.Projective.DahmPluckerKleinCollineation
import InfoGeometry.Projective.PluckerMatrixAction
import InfoGeometry.Projective.PluckerRayAxisAndDyname
import InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Erlangen Program (§§4–5): Transfer Principle, Veronese Conic, Hesse Transference, & Bodies

This module formalizes Archetypes `EK₃` and `EK₄` of Felix Klein's 1872 *Erlangen Program*
(`0807.3161v1 (1).pdf`, pp. 6–9) together with **Grassmann–Plücker–Klein Bridge I**:

1. **Transfer Principle by Representation (`Abbildung`, `§4`, p. 6)**:
   * Transporting a `G`-action along a bijection `e : A ≃ A'` yields an explicit equivalence
     (`klein_transfer_invariant_equiv`) preserving `IsGeometricInvariant` lattices.
2. **Binary Forms ↔ Conic & Stereographic Quadric Representation (`§4`, pp. 6–7)**:
   * Veronese map `veroneseConic u v = ![u², u v, v²]` on `conicQuadric x = x₀ x₂ - x₁² = 0`,
     multiplicative symmetric-square representation `symSq2 : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 3) (Fin 3) R`
     satisfying `det (symSq2 M) = (det M)³` and `conicQuadric (symSq2 M *ᵥ x) = (det M)² * conicQuadric x`.
   * Quadric stereographic chart `quadricStereo z w = ![1, z, w, z w]` onto `x₀ x₃ - x₁ x₂ = 0`.
3. **Hesse's Principle of Transference & Grassmann–Plücker–Klein Bridge I (`§5`, pp. 7–8)**:
   * Point-pairs / binary quadratic forms `c₀ u² + 2 c₁ u v + c₂ v²` correspond to dual conic lines
     `![c₀, 2 c₁, c₂] ⬝ᵥ veroneseConic u v` whose discriminant scales by `(det M)²` under `symSq2 M`.
   * Constructive Mathlib alternating map `grassmannBladeToPlucker : (Fin 4 → R) [⋀^Fin 2]→ₗ[R] (Fin 6 → R)`
     connecting Grassmann's extensive `2`-blades, Plücker's `15`-minor ray–axis duality
     (`ray_axis_minors_eq_of_four_incidences`), `PluckerMatrixAction.secondCompound` `GL₄`-covariance,
     and Klein's `O(3,3)` split senary quadratic form (`DahmPluckerKleinCollineation.kleinQ_splitKleinMap`).
4. **Klein's *Körper* / Bodies & `[countermodel_found]` Footnote 23 (`§5`, pp. 8–9)**:
   * Decomposition of every `G`-invariant configuration set into Klein bodies (`MulAction.orbit`).
   * Proof that any normal subgroup `N` fixing one point of a body fixes every point of that body
     (`klein_footnote23_normal_subgroup_fixes_entire_body`), realized concretely by `Equiv.Perm (Fin 4)`
     acting unfaithfully via `V₄` on its `3`-element double-pair partition body.
-/

namespace InfoGeometry.Erlangen.ErlangenProgramTransferHesseAndBodies

open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
open InfoGeometry.Projective
open Matrix

/-! ## 1. Representation Transfer Principle (`Abbildung`, §4) -/

section RepresentationTransfer

/-- Transported scalar multiplication on `A'` induced by a bijection `e : A ≃ A'`. -/
def transportedSmul {G A A' : Type*} [SMul G A] (e : A ≃ A') (g : G) (a' : A') : A' :=
  e (g • e.symm a')

/-- **Klein's Transfer Theorem (`§4`, p. 6)**:
Any bijection `e : A ≃ A'` bijectively transports `G`-invariant predicates on `A` to
predicates invariant under the conjugated `G`-action on `A'`, preserving logical entailment. -/
def klein_transfer_invariant_equiv (G : Type*) [Group G] {A A' : Type*} [MulAction G A]
    (e : A ≃ A') :
    {P : A → Prop // IsGeometricInvariant G A P} ≃
      {P' : A' → Prop // ∀ (g : G) (a' : A'), P' (transportedSmul e g a') ↔ P' a'} where
  toFun P :=
    ⟨fun a' => P.1 (e.symm a'), fun g a' => by
      dsimp [transportedSmul]
      rw [e.symm_apply_apply]
      exact P.2 g (e.symm a')⟩
  invFun P' :=
    ⟨fun a => P'.1 (e a), fun g a => by
      have h := P'.2 g (e a)
      simpa [transportedSmul, e.symm_apply_apply] using h⟩
  left_inv P := by
    apply Subtype.ext
    funext a
    simp [e.symm_apply_apply]
  right_inv P' := by
    apply Subtype.ext
    funext a'
    simp [e.apply_symm_apply]

end RepresentationTransfer

/-! ## 2. Veronese Conic Representation & Quadric Stereographic Projection (§4) -/

section VeroneseAndQuadric

/-- Non-commutativity witness for `Matrix (Fin 2) (Fin 2) R`. -/
theorem matrix2_noncomm {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Non-commutativity witness for `Matrix (Fin 3) (Fin 3) R` over general `[Ring R]`. -/
theorem matrix3_noncomm_ring {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Non-commutativity witness for `Matrix (Fin 4) (Fin 4) R` over general `[Ring R]`. -/
theorem matrix4_noncomm_ring {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 4) (Fin 4) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Non-commutativity witness for `Matrix (Fin 6) (Fin 6) R` over general `[Ring R]`. -/
theorem matrix6_noncomm_ring {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 6) (Fin 6) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Veronese rational parameterization `(u, v) ↦ [u² : u v : v²]` mapping `P¹` onto a plane conic. -/
def veroneseConic {R : Type*} [CommRing R] (u v : R) : Fin 3 → R :=
  ![u ^ 2, u * v, v ^ 2]

/-- Canonical plane conic quadratic form `x₀ x₂ - x₁²`. -/
def conicQuadric {R : Type*} [CommRing R] (x : Fin 3 → R) : R :=
  x 0 * x 2 - x 1 ^ 2

theorem conicQuadric_veroneseConic {R : Type*} [CommRing R] (u v : R) :
    conicQuadric (veroneseConic u v) = 0 := by
  dsimp [conicQuadric, veroneseConic]
  ring

/-- Second symmetric power representation `GL₂(R) → GL₃(R)` induced on `[u² : uv : v²]` (`§4`). -/
def symSq2 {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  ![ ![M 0 0 ^ 2,           2 * M 0 0 * M 0 1,                 M 0 1 ^ 2],
     ![M 0 0 * M 1 0,       M 0 0 * M 1 1 + M 0 1 * M 1 0,     M 0 1 * M 1 1],
     ![M 1 0 ^ 2,           2 * M 1 0 * M 1 1,                 M 1 1 ^ 2] ]

/-- Equivariance of the Veronese conic under binary linear substitutions (`§4`, p. 6). -/
theorem symSq2_equivariant {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (u v : R) :
    symSq2 M *ᵥ veroneseConic u v =
      veroneseConic (M 0 0 * u + M 0 1 * v) (M 1 0 * u + M 1 1 * v) := by
  ext i
  fin_cases i <;>
    (simp [symSq2, veroneseConic, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring)

theorem symSq2_one {R : Type*} [CommRing R] :
    symSq2 (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symSq2]

theorem symSq2_mul {R : Type*} [CommRing R] (M N : Matrix (Fin 2) (Fin 2) R) :
    symSq2 (M * N) = symSq2 M * symSq2 N := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    (simp [symSq2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]; ring)

/-- `symSq2` is a monoid homomorphism `Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 3) (Fin 3) R`. -/
def symSq2Hom (R : Type*) [CommRing R] :
    Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 3) (Fin 3) R where
  toFun := symSq2
  map_one' := symSq2_one
  map_mul' := symSq2_mul

/-- Determinant of the second symmetric power: `det (symSq2 M) = (det M)³`. -/
theorem symSq2_det {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (symSq2 M).det = M.det ^ 3 := by
  have h00 : symSq2 M 0 0 = M 0 0 ^ 2 := rfl
  have h01 : symSq2 M 0 1 = 2 * M 0 0 * M 0 1 := rfl
  have h02 : symSq2 M 0 2 = M 0 1 ^ 2 := rfl
  have h10 : symSq2 M 1 0 = M 0 0 * M 1 0 := rfl
  have h11 : symSq2 M 1 1 = M 0 0 * M 1 1 + M 0 1 * M 1 0 := rfl
  have h12 : symSq2 M 1 2 = M 0 1 * M 1 1 := rfl
  have h20 : symSq2 M 2 0 = M 1 0 ^ 2 := rfl
  have h21 : symSq2 M 2 1 = 2 * M 1 0 * M 1 1 := rfl
  have h22 : symSq2 M 2 2 = M 1 1 ^ 2 := rfl
  rw [Matrix.det_fin_three, Matrix.det_fin_two,
    h00, h01, h02, h10, h11, h12, h20, h21, h22]
  ring

/-- `symSq2 M` preserves the conic quadratic form up to `(det M)²` across all `x : Fin 3 → R` (`§4`). -/
theorem conicQuadric_symSq2 {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (x : Fin 3 → R) :
    conicQuadric (symSq2 M *ᵥ x) = M.det ^ 2 * conicQuadric x := by
  dsimp [conicQuadric]
  simp [symSq2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [Matrix.det_fin_two]
  ring

/-- Canonical doubly ruled quadric `x₀ x₃ - x₁ x₂ = 0` (`§4`, pp. 6–7). -/
def ruledQuadric4 {R : Type*} [Ring R] (x : Fin 4 → R) : R :=
  x 0 * x 3 - x 1 * x 2

/-- Stereographic Segre/quadric parameterization `(z, w) ↦ [1 : z : w : z w]` (`§4`, pp. 6–7). -/
def quadricStereo {R : Type*} [Ring R] (z w : R) : Fin 4 → R :=
  ![1, z, w, z * w]

theorem ruledQuadric4_stereo {R : Type*} [CommRing R] (z w : R) :
    ruledQuadric4 (quadricStereo z w) = 0 := by
  dsimp [ruledQuadric4, quadricStereo]
  ring

/-- Away from the two fundamental generators (`x₀ ≠ 0`), stereographic projection is birational (`§4`). -/
theorem quadricStereo_left_inv {K : Type*} [Field K] {x : Fin 4 → K}
    (hx0 : x 0 ≠ 0) (hq : ruledQuadric4 x = 0) :
    quadricStereo (x 1 / x 0) (x 2 / x 0) = (x 0)⁻¹ • x := by
  ext i
  fin_cases i
  · simp [quadricStereo, hx0]
  · simp [quadricStereo, div_eq_inv_mul]
  · simp [quadricStereo, div_eq_inv_mul]
  · dsimp [ruledQuadric4] at hq
    have hmul : x 0 * x 3 = x 1 * x 2 := sub_eq_zero.mp hq
    have hquad3 : quadricStereo (x 1 / x 0) (x 2 / x 0) 3 = (x 1 / x 0) * (x 2 / x 0) := rfl
    change quadricStereo (x 1 / x 0) (x 2 / x 0) 3 = (x 0)⁻¹ * x 3
    rw [hquad3]
    field_simp [hx0]
    linear_combination hmul.symm

end VeroneseAndQuadric

/-! ## 3. Hesse's Principle of Transference & Grassmann–Plücker–Klein Bridge I (§5) -/

section HesseAndGrassmannPluckerKleinBridge

/-- Homogeneous binary quadratic form `c₀ u² + 2 c₁ u v + c₂ v²` representing an unordered
point-pair on `P¹` (`§5`, p. 7). -/
def binaryQuadForm {R : Type*} [CommRing R] (c : Fin 3 → R) (u v : R) : R :=
  c 0 * u ^ 2 + 2 * c 1 * u * v + c 2 * v ^ 2

/-- **Hesse's Principle of Transference (`§5`, p. 7)**:
A binary quadratic form `(u, v)` vanishes precisely when the plane line `![c₀, 2 c₁, c₂]` is
incident to the Veronese conic point `veroneseConic u v` (secant point-pair ↔ line in the plane). -/
theorem hesse_pointPair_eq_planeLine_pairing {R : Type*} [CommRing R]
    (c : Fin 3 → R) (u v : R) :
    binaryQuadForm c u v = ![c 0, 2 * c 1, c 2] ⬝ᵥ veroneseConic u v := by
  simp [binaryQuadForm, veroneseConic, dotProduct, Fin.sum_univ_three]
  ring

/-- The contragredient transformation `(symSq2 M)ᵀ` on dual line coordinates `![c₀, 2 c₁, c₂]`
scales the binary quadratic discriminant `4 c₀ c₂ - (2 c₁)²` uniformly by `(det M)²` (`§5`, p. 7). -/
theorem hesse_dual_discriminant_scale {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (c : Fin 3 → R) :
    let ct := (symSq2 M)ᵀ *ᵥ ![c 0, 2 * c 1, c 2]
    4 * (ct 0 * ct 2) - ct 1 ^ 2 = M.det ^ 2 * (4 * (c 0 * c 2) - (2 * c 1) ^ 2) := by
  dsimp only
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
  have hc0 : (![c 0, 2 * c 1, c 2] : Fin 3 → R) 0 = c 0 := rfl
  have hc1 : (![c 0, 2 * c 1, c 2] : Fin 3 → R) 1 = 2 * c 1 := rfl
  have hc2 : (![c 0, 2 * c 1, c 2] : Fin 3 → R) 2 = c 2 := rfl
  have h00 : symSq2 M 0 0 = M 0 0 ^ 2 := rfl
  have h01 : symSq2 M 0 1 = 2 * M 0 0 * M 0 1 := rfl
  have h02 : symSq2 M 0 2 = M 0 1 ^ 2 := rfl
  have h10 : symSq2 M 1 0 = M 0 0 * M 1 0 := rfl
  have h11 : symSq2 M 1 1 = M 0 0 * M 1 1 + M 0 1 * M 1 0 := rfl
  have h12 : symSq2 M 1 2 = M 0 1 * M 1 1 := rfl
  have h20 : symSq2 M 2 0 = M 1 0 ^ 2 := rfl
  have h21 : symSq2 M 2 1 = 2 * M 1 0 * M 1 1 := rfl
  have h22 : symSq2 M 2 2 = M 1 1 ^ 2 := rfl
  rw [Matrix.det_fin_two, hc0, hc1, hc2, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  ring

private lemma rayPlucker_update_add {R : Type*} [CommRing R]
    (v : Fin 2 → Fin 4 → R) (i : Fin 2) (x y : Fin 4 → R) :
    PluckerMatrixAction.coordinates
        (PluckerRayAxisAndDyname.rayPlucker
          (Function.update v i (x + y) 0) (Function.update v i (x + y) 1)) =
      PluckerMatrixAction.coordinates
          (PluckerRayAxisAndDyname.rayPlucker (Function.update v i x 0) (Function.update v i x 1)) +
        PluckerMatrixAction.coordinates
          (PluckerRayAxisAndDyname.rayPlucker (Function.update v i y 0) (Function.update v i y 1)) := by
  ext k
  fin_cases i <;> fin_cases k <;>
    (simp [Function.update, PluckerMatrixAction.coordinates, PluckerRayAxisAndDyname.rayPlucker];
     ring)

private lemma rayPlucker_update_smul {R : Type*} [CommRing R]
    (v : Fin 2 → Fin 4 → R) (i : Fin 2) (c : R) (x : Fin 4 → R) :
    PluckerMatrixAction.coordinates
        (PluckerRayAxisAndDyname.rayPlucker
          (Function.update v i (c • x) 0) (Function.update v i (c • x) 1)) =
      c • PluckerMatrixAction.coordinates
          (PluckerRayAxisAndDyname.rayPlucker (Function.update v i x 0) (Function.update v i x 1)) := by
  ext k
  fin_cases i <;> fin_cases k <;>
    (simp [Function.update, PluckerMatrixAction.coordinates, PluckerRayAxisAndDyname.rayPlucker];
     ring)

private lemma rayPlucker_eq_zero_of_eq {R : Type*} [CommRing R]
    (v : Fin 2 → Fin 4 → R) {i j : Fin 2} (heq : v i = v j) (hne : i ≠ j) :
    PluckerMatrixAction.coordinates (PluckerRayAxisAndDyname.rayPlucker (v 0) (v 1)) = 0 := by
  ext k
  have h01 : v 0 = v 1 := by
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hne | exact heq | exact heq.symm
  rw [h01]
  fin_cases k <;>
    (simp [PluckerMatrixAction.coordinates, PluckerRayAxisAndDyname.rayPlucker]; ring)

/-- **Grassmann–Plücker–Klein Bridge I (`§5`, p. 8)**:
Alternating `R`-bilinear Grassmann map `(Fin 4 → R) [⋀^Fin 2]→ₗ[R] (Fin 6 → R)` sending a
`2`-frame `![x, y]` to its Plücker ray `coordinates (rayPlucker x y)` in `Λ²(R⁴) ≅ R⁶`. -/
def grassmannBladeToPlucker (R : Type*) [CommRing R] :
    (Fin 4 → R) [⋀^Fin 2]→ₗ[R] (Fin 6 → R) where
  toFun v := PluckerMatrixAction.coordinates (PluckerRayAxisAndDyname.rayPlucker (v 0) (v 1))
  map_update_add' := by
    intro d v i x y
    rw [Subsingleton.elim d (instDecidableEqFin 2)]
    exact rayPlucker_update_add v i x y
  map_update_smul' := by
    intro d v i c x
    rw [Subsingleton.elim d (instDecidableEqFin 2)]
    exact rayPlucker_update_smul v i c x
  map_eq_zero_of_eq' := fun v i j heq hne => rayPlucker_eq_zero_of_eq v heq hne

theorem grassmannBladeToPlucker_apply {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    grassmannBladeToPlucker R ![x, y] =
      PluckerMatrixAction.coordinates (PluckerRayAxisAndDyname.rayPlucker x y) := by
  dsimp [grassmannBladeToPlucker]

/-- Applying any linear transformation `A : Matrix (Fin 4) (Fin 4) R` to the two generating points
is covariant with multiplying by `secondCompound A` on the Grassmann–Plücker `6`-vector (`§5`, p. 8). -/
theorem grassmannBladeToPlucker_linear_equivariance {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (x y : Fin 4 → R) :
    grassmannBladeToPlucker R ![A *ᵥ x, A *ᵥ y] =
      PluckerMatrixAction.secondCompound A *ᵥ grassmannBladeToPlucker R ![x, y] := by
  ext k
  fin_cases k <;>
    (simp [grassmannBladeToPlucker_apply, PluckerMatrixAction.coordinates,
      PluckerRayAxisAndDyname.rayPlucker, PluckerMatrixAction.secondCompound,
      PluckerMatrixAction.coordinatePair, Matrix.mulVec, dotProduct,
      Fin.sum_univ_six, Fin.sum_univ_four];
     ring)

/-- Every decomposable Grassmann `2`-blade image lies identically on the Klein quadric (`§5`, p. 8). -/
theorem grassmannBladeToPlucker_on_kleinQuadric {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    (PluckerMatrixAction.coordinates.symm (grassmannBladeToPlucker R ![x, y])).IsKlein := by
  rw [grassmannBladeToPlucker_apply, Equiv.symm_apply_apply]
  exact PluckerRayAxisAndDyname.rayPlucker_kleinQ x y

/-- **Unified Grassmann–Plücker–Klein Senary Theorem (`§5`, p. 8)**:
Combines (1) Plücker's `15`-minor ray–axis coincidence under four point–plane incidences,
(2) Grassmann `2`-blade `secondCompound` covariance and Klein-quadric annihilation, and
(3) Klein's `det A` relative invariance of `Plucker6.kleinQ` together with Dahm's noncommutative
`SO(3,3)` split-senary defect law. -/
theorem grassmann_plucker_senary_unification {R : Type*} [CommRing R] :
    (∀ (x y u v : Fin 4 → R),
      (∑ k, u k * x k = 0) → (∑ k, u k * y k = 0) →
      (∑ k, v k * x k = 0) → (∑ k, v k * y k = 0) →
      ∀ i j, grassmannBladeToPlucker R ![x, y] i *
          PluckerMatrixAction.coordinates (PluckerRayAxisAndDyname.axisAsRayPlucker u v) j =
        grassmannBladeToPlucker R ![x, y] j *
          PluckerMatrixAction.coordinates (PluckerRayAxisAndDyname.axisAsRayPlucker u v) i) ∧
      (∀ (A : Matrix (Fin 4) (Fin 4) R) (P : KleinQuadric.Plucker6 R),
        (PluckerMatrixAction.transform A P).kleinQ = A.det * P.kleinQ) ∧
      (∀ (B : Type*) [Ring B] (x₁ x₂ x₃ x₄ x₅ x₆ : B),
        KleinQuadric.Plucker6.kleinQ (DahmPluckerKleinCollineation.splitKleinMap x₁ x₂ x₃ x₄ x₅ x₆) =
          (x₁ * x₁ - x₂ * x₂) + (x₃ * x₃ - x₄ * x₄) + (x₅ * x₅ - x₆ * x₆) -
            DahmPluckerKleinCollineation.senaryDefect x₁ x₂ x₃ x₄ x₅ x₆) :=
  ⟨fun x y u v h1 h2 h3 h4 i j => by
      rw [grassmannBladeToPlucker_apply]
      exact PluckerRayAxisAndDyname.ray_axis_minors_eq_of_four_incidences x y u v h1 h2 h3 h4 i j,
   fun A P => PluckerMatrixAction.kleinQ_transform A P,
   fun _ _ x₁ x₂ x₃ x₄ x₅ x₆ => DahmPluckerKleinCollineation.kleinQ_splitKleinMap x₁ x₂ x₃ x₄ x₅ x₆⟩

end HesseAndGrassmannPluckerKleinBridge

/-! ## 4. Klein's *Körper* (Bodies) & `[countermodel_found]` Footnote 23 (§5, pp. 8–9) -/

section KleinBodiesAndFootnote23

/-- A Klein body (*Körper*) with respect to a group action is a single `G`-orbit (`§5`, pp. 8–9). -/
def IsKleinBody (G : Type*) {X : Type*} [Group G] [MulAction G X] (B : Set X) : Prop :=
  ∃ x : X, B = MulAction.orbit G x

/-- Every `G`-invariant configuration set decomposes cleanly as the union of its Klein bodies (`§5`). -/
theorem invariantSet_eq_sUnion_bodies (G : Type*) {X : Type*} [Group G] [MulAction G X]
    {S : Set X} (hS : ∀ (g : G) {x : X}, x ∈ S → g • x ∈ S) :
    S = ⋃₀ {B : Set X | IsKleinBody G B ∧ B ⊆ S} := by
  apply Set.Subset.antisymm
  · intro x hx
    refine Set.mem_sUnion.mpr ⟨MulAction.orbit G x, ⟨⟨x, rfl⟩, ?_⟩, MulAction.mem_orbit_self x⟩
    rintro y ⟨g, rfl⟩
    exact hS g hx
  · rintro y ⟨B, ⟨_, hsub⟩, hy⟩
    exact hsub hy

/-- **`[countermodel_found]` Klein's Footnote 23 (`§5`, p. 9)**:
If a normal subgroup `N` of `G` stabilizes a single point `x₀` of a Klein body `orbit G x₀`, then
`N` fixes **every** member of that body pointwise. -/
theorem klein_footnote23_normal_subgroup_fixes_entire_body
    {G X : Type*} [Group G] [MulAction G X] (N : Subgroup G) (hN : N.Normal) (x₀ : X)
    (hfix : ∀ n ∈ N, n • x₀ = x₀) :
    ∀ y ∈ MulAction.orbit G x₀, ∀ n ∈ N, n • y = y := by
  rintro y ⟨g, rfl⟩ n hn
  have hconj : g⁻¹ * n * g ∈ N := by
    have hconj1 := hN.conj_mem n hn g⁻¹
    simpa [mul_assoc] using hconj1
  calc
    n • (g • x₀) = (n * g) • x₀ := (mul_smul n g x₀).symm
    _ = (g * (g⁻¹ * n * g)) • x₀ := by group
    _ = g • ((g⁻¹ * n * g) • x₀) := mul_smul g (g⁻¹ * n * g) x₀
    _ = g • x₀ := by rw [hfix (g⁻¹ * n * g) hconj]

/-- Explicit action of `Equiv.Perm (Fin 4)` on unordered double-pair partitions `Finset (Finset (Fin 4))`. -/
def permPartAct (σ : Equiv.Perm (Fin 4)) (P : Finset (Finset (Fin 4))) :
    Finset (Finset (Fin 4)) :=
  P.image (Finset.image σ)

instance : MulAction (Equiv.Perm (Fin 4)) (Finset (Finset (Fin 4))) where
  smul := permPartAct
  one_smul P := by
    change permPartAct 1 P = P
    ext s
    simp [permPartAct]
  mul_smul σ τ P := by
    change permPartAct (σ * τ) P = permPartAct σ (permPartAct τ P)
    simp [permPartAct, Finset.image_image, Function.comp_def]

/-- Canonical `2 + 2` double-pair partition `{{0, 1}, {2, 3}}` in `Fin 4`. -/
def doublePair0 : Finset (Finset (Fin 4)) := {{0, 1}, {2, 3}}

/-- Explicit non-identity `V₄` permutation `(0 1)(2 3) ∈ S₄` stabilizing `doublePair0` and its orbit. -/
def s4V4Witness : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

private lemma s4V4Witness_fixes_any_pair (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    s4V4Witness • ({{a, b}, {c, d}} : Finset (Finset (Fin 4))) = {{a, b}, {c, d}} := by
  change permPartAct s4V4Witness {{a, b}, {c, d}} = {{a, b}, {c, d}}
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
      | exact absurd rfl hab
      | exact absurd rfl hac
      | exact absurd rfl had
      | exact absurd rfl hbc
      | exact absurd rfl hbd
      | exact absurd rfl hcd
      | decide

/-- Pointwise kernel of the action of `G` on the orbit of `x₀` (always a normal subgroup of `G`). -/
def orbitActionKernel (G : Type*) {X : Type*} [Group G] [MulAction G X] (x₀ : X) : Subgroup G where
  carrier := {n : G | ∀ y ∈ MulAction.orbit G x₀, n • y = y}
  one_mem' y _ := one_smul G y
  mul_mem' {a b} ha hb y hy := by rw [mul_smul, hb y hy, ha y hy]
  inv_mem' {a} ha y hy := by
    have hinv := congrArg (fun z => a⁻¹ • z) (ha y hy)
    simpa [inv_smul_smul] using hinv.symm

theorem orbitActionKernel_normal (G : Type*) {X : Type*} [Group G] [MulAction G X] (x₀ : X) :
    (orbitActionKernel G x₀).Normal where
  conj_mem n hn g y hy := by
    obtain ⟨k, rfl⟩ := hy
    have hk : g⁻¹ • (k • x₀) ∈ MulAction.orbit G x₀ := ⟨g⁻¹ * k, mul_smul g⁻¹ k x₀⟩
    have hfix := hn (g⁻¹ • (k • x₀)) hk
    calc
      (g * n * g⁻¹) • (k • x₀) = g • (n • (g⁻¹ • (k • x₀))) := by
        rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • (k • x₀)) := by rw [hfix]
      _ = k • x₀ := smul_inv_smul g (k • x₀)

/-- **`[countermodel_found]` Footnote 23 Concrete Witness (`S₄` on the `3`-partition body)**:
`orbitActionKernel (Equiv.Perm (Fin 4)) doublePair0` is a normal subgroup containing `s4V4Witness ≠ 1`
(`V₄ ≤ S₄`) that fixes every element of the Klein body `MulAction.orbit (Equiv.Perm (Fin 4)) doublePair0`,
so the `S₄`-body is unfaithful and cannot recover `S₄` operations faithfully. -/
theorem klein_footnote23_s4_v4_countermodel :
    let N := orbitActionKernel (Equiv.Perm (Fin 4)) doublePair0
    N.Normal ∧ s4V4Witness ∈ N ∧ s4V4Witness ≠ 1 ∧
      ∀ y ∈ MulAction.orbit (Equiv.Perm (Fin 4)) doublePair0, s4V4Witness • y = y := by
  intro N
  have hmem : s4V4Witness ∈ N := by
    rintro y ⟨g, rfl⟩
    have hinj := g.injective
    have hact : (fun m : Equiv.Perm (Fin 4) => m • doublePair0) g =
        ({{g 0, g 1}, {g 2, g 3}} : Finset (Finset (Fin 4))) := by
      change permPartAct g doublePair0 = {{g 0, g 1}, {g 2, g 3}}
      simp [permPartAct, doublePair0]
    rw [hact]
    exact s4V4Witness_fixes_any_pair (g 0) (g 1) (g 2) (g 3)
      (fun h => by have := hinj h; exact (by decide : (0 : Fin 4) ≠ 1) this)
      (fun h => by have := hinj h; exact (by decide : (0 : Fin 4) ≠ 2) this)
      (fun h => by have := hinj h; exact (by decide : (0 : Fin 4) ≠ 3) this)
      (fun h => by have := hinj h; exact (by decide : (1 : Fin 4) ≠ 2) this)
      (fun h => by have := hinj h; exact (by decide : (1 : Fin 4) ≠ 3) this)
      (fun h => by have := hinj h; exact (by decide : (2 : Fin 4) ≠ 3) this)
  have hne : s4V4Witness ≠ 1 := by
    intro h
    have h0 : s4V4Witness 0 = (1 : Equiv.Perm (Fin 4)) 0 := congrArg (fun σ => σ 0) h
    have hval : s4V4Witness 0 = 1 := by decide
    rw [hval] at h0
    have hbad : (1 : Fin 4) = 0 := h0.trans (Equiv.Perm.one_apply 0)
    revert hbad
    decide
  exact ⟨orbitActionKernel_normal _ _, hmem, hne, fun y hy => hmem y hy⟩

end KleinBodiesAndFootnote23

end InfoGeometry.Erlangen.ErlangenProgramTransferHesseAndBodies
