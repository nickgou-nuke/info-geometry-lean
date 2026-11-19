/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
import InfoGeometry.Projective.PluckerLinearComplexGeometry
import InfoGeometry.Projective.PluckerRayAxisAndDyname
import InfoGeometry.Canonical.PluckerGrassmannKleinUnifiedSynthesis
import InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Grassmann & Plücker Primary-Source Archetypes (`S2-01`..`S2-04`)

This module formalizes the foundational primary-source archetypes of Hermann Grassmann
(*Die lineale Ausdehnungslehre*, 1844; *Die Ausdehnungslehre*, 1862) and Julius Plücker
(*Phil. Trans. R. Soc.* 155, 1865; *Neue Geometrie des Raumes*, 1868–1869), preserving
`ORIGINAL_REQUEST.md § R3.2`:

1. **`S2-01` & `S2-02` (Grassmann 1844 / 1862 / 1877)**:
   - Coordinate-free, metric-free dual contraction (`CliffordAlgebra.contractLeft (Q := 0)`)
     functoriality under `ExteriorAlgebra.map g` for any `g : M ≃ₗ[R] M`.
   - `MetricFreeVolumeDatum`: basis-free volume blade + Poincaré contraction isomorphism
     defining `dualContractionRegressive` without any Euclidean metric or Hodge-star
     prerequisite, proven compatible with `ExteriorRegressive.regressive b`.
   - Exact `(det g)⁻¹` covariance under `GeneralLinearGroup K V` and strict invariance under
     `SpecialLinearGroup K V`.
   - Non-spanning zero-meet edge cases (`span v ⊔ span w ≠ ⊤`) and Engel/Müller Note 31 &
     Note 97 (`GL(4)` `IsSyncyclic4` vs. `OCircleBilin` tangency separation).
2. **`S2-03` (Plücker 1865)**:
   - Canonical linear equivalence `(Fin 6 → R) ≃ₗ[R] ⋀[R]^2 (Fin 4 → R)` embedding `Plucker6`.
   - Arbitrary-field (`[Field K]`, `(2 : K) ≠ 0`) and coordinate-free 4D exterior-square
     decomposability `ω * ω = 0 ↔ ∃ u v, ω = ι u * ι v`, plus the all-characteristic
     Klein quadric equivalence `P.kleinQ = 0 ↔ decomposable`.
   - Explicit non-decomposable bivector counterexample `e₀ ∧ e₁ + e₂ ∧ e₃`.
3. **`S2-04` (Plücker 1868–1869)**:
   - Exterior wedge and regressive characterization of linear complexes `C.Incident P`.
   - Arbitrary-field `(0, 2, 4)` kernel-rank trichotomy of `complexForm C` (general,
     nonzero special directrix plane, zero).
   - Poinsot/Plücker dyname central-axis and pitch reduction uniting
     `PluckerAffineScrew.axisFoot`, `pitch`, `affineTranslateDirMom`, and
     `canonicalCentralComplex_slope`.
-/

noncomputable section

namespace InfoGeometry.Projective.GrassmannPrimarySources

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.ExteriorBladeIncidence
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerLinearComplex
open InfoGeometry.Projective.PluckerLinearComplexGeometry
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open InfoGeometry.Canonical.PluckerGrassmannKleinUnifiedSynthesis
open InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges
open scoped Matrix

/-! ## Part I: Grassmann (1844, 1862) — Metric-Free Dual-Contraction Regressive Structure (`S2-01`, `S2-02`) -/

section GrassmannDualContraction

/-- **Grassmann (`S2-01` Part II Ch. 3; `S2-02` Part 1 Nos. 63, 87; `R3.2`)**:
naturality of `CliffordAlgebra.contractLeft (Q := 0)` under `ExteriorAlgebra.map g.toLinearMap`
for any module automorphism `g : M ≃ₗ[R] M`. -/
theorem contractLeft_map_linearEquiv {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (g : M ≃ₗ[R] M) (d : Module.Dual R M) (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d
        (ExteriorAlgebra.map g.toLinearMap x) =
      ExteriorAlgebra.map g.toLinearMap
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
          (g.toLinearMap.dualMap d) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    have h1 : ExteriorAlgebra.map g.toLinearMap (algebraMap R (ExteriorAlgebra R M) r) =
        algebraMap R (ExteriorAlgebra R M) r := AlgHom.commutes _ r
    rw [h1, CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.contractLeft_algebraMap,
      map_zero]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul y v hy =>
    have hι : CliffordAlgebra.ι (0 : QuadraticForm R M) v = ExteriorAlgebra.ι R v := rfl
    have hmap_ι : ExteriorAlgebra.map g.toLinearMap (ExteriorAlgebra.ι R v) =
        ExteriorAlgebra.ι R (g v) := ExteriorAlgebra.map_apply_ι g.toLinearMap v
    rw [hι, map_mul, hmap_ι]
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d
        (CliffordAlgebra.ι 0 (g v) * ExteriorAlgebra.map g.toLinearMap y) =
      ExteriorAlgebra.map g.toLinearMap
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
          (g.toLinearMap.dualMap d) (CliffordAlgebra.ι 0 v * y))
    rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul, map_sub,
      map_smul, map_mul, ← hι, hmap_ι, hy]
    rfl

/-- **Grassmann (`S2-01` Part II Ch. 3 §§125–148; `S2-02` Part 1 Nos. 63, 87; `R3.2`)**:
pushforward form of `CliffordAlgebra.contractLeft (Q := 0)` equivariance under `g : M ≃ₗ[R] M`,
intertwining `d` with `g.symm.toLinearMap.dualMap d`. -/
theorem map_contractLeft_linearEquiv {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (g : M ≃ₗ[R] M) (d : Module.Dual R M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map g.toLinearMap
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
        (g.symm.toLinearMap.dualMap d) (ExteriorAlgebra.map g.toLinearMap x) := by
  have hdual : g.toLinearMap.dualMap (g.symm.toLinearMap.dualMap d) = d := by
    ext v
    change d (g.symm (g v)) = d v
    rw [g.symm_apply_apply]
  have h := contractLeft_map_linearEquiv g (g.symm.toLinearMap.dualMap d) x
  rw [hdual] at h
  exact h.symm

/-- **Grassmann (`S2-02` Part 1 Nos. 63, 87, 103; `R3.2`)**:
equivariance of the opposite-algebra dual contraction action `dualContractionAlgHom` under
`g : M ≃ₗ[R] M` on both `Λ(M^*)` and `Λ(M)`. -/
theorem map_dualContractionAlgHom_linearEquiv {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (g : M ≃ₗ[R] M)
    (α : ExteriorAlgebra R (Module.Dual R M)) (z : ExteriorAlgebra R M) :
    ExteriorAlgebra.map g.toLinearMap ((dualContractionAlgHom α).unop z) =
      (dualContractionAlgHom (ExteriorAlgebra.map g.symm.toLinearMap.dualMap α)).unop
        (ExteriorAlgebra.map g.toLinearMap z) := by
  induction α using ExteriorAlgebra.induction generalizing z with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    simp only [MulOpposite.unop_smul, MulOpposite.unop_one, LinearMap.smul_apply]
    rw [map_smul]
    rfl
  | ι d =>
    rw [ExteriorAlgebra.map_apply_ι, dualContractionAlgHom_ι, dualContractionAlgHom_ι]
    exact map_contractLeft_linearEquiv g d z
  | mul α β hα hβ =>
    rw [dualContractionAlgHom_mul, hβ, hα, ← dualContractionAlgHom_mul, ← map_mul]
  | add α β hα hβ =>
    simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, hα, hβ]

/-- **Grassmann (`S2-01` Part II §§125–148; `S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
metric-free, basis-free volume datum consisting of a top-domain blade `volumeBlade` and the
Poincaré contraction linear equivalence `Λ(V^*) ≃ₗ[K] Λ(V)` realized purely by
`dualContractionAlgHom`. -/
structure MetricFreeVolumeDatum (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  volumeBlade : ExteriorAlgebra K V
  poincareEquiv : ExteriorAlgebra K (Module.Dual K V) ≃ₗ[K] ExteriorAlgebra K V
  poincareEquiv_eq : ∀ α : ExteriorAlgebra K (Module.Dual K V),
    poincareEquiv α = (dualContractionAlgHom α).unop volumeBlade

/-- **Grassmann (`S2-01` Part II Ch. 3 §§125–148; `S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
construct a `MetricFreeVolumeDatum` from any basis `b : Module.Basis (Fin n) K V` via
`ExteriorRegressive.volume b` and `GrassmannAusdehnungslehreRegressiveShadow.poincareEquiv b`. -/
def metricFreeVolumeDatumOfBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) : MetricFreeVolumeDatum K V where
  volumeBlade := ExteriorRegressive.volume b
  poincareEquiv := GrassmannAusdehnungslehreRegressiveShadow.poincareEquiv b
  poincareEquiv_eq := poincareEquiv_apply b

/-- **Grassmann (`S2-01` Part II Ch. 3 §§125–148; `S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
canonical finite-dimensional inhabitant for `MetricFreeVolumeDatum K V` constructed from
`Module.finBasis K V`. -/
noncomputable def canonicalMetricFreeVolumeDatum (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : MetricFreeVolumeDatum K V :=
  metricFreeVolumeDatumOfBasis (Module.finBasis K V)

/-- **Grassmann (`S2-01` Part II Ch. 3 §§125–148; `S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
`Inhabited` witness for `MetricFreeVolumeDatum K V` on finite-dimensional vector spaces. -/
noncomputable instance instInhabitedMetricFreeVolumeDatum (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : Inhabited (MetricFreeVolumeDatum K V) :=
  ⟨canonicalMetricFreeVolumeDatum K V⟩

/-- **Grassmann (`S2-01` Part II Ch. 3 §§125–148; `S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
concrete `ℝ⁴` inhabitant of `MetricFreeVolumeDatum ℝ (Fin 4 → ℝ)`. -/
noncomputable def real4MetricFreeVolumeDatum : MetricFreeVolumeDatum ℝ (Fin 4 → ℝ) :=
  metricFreeVolumeDatumOfBasis (Pi.basisFun ℝ (Fin 4))

/-- **Grassmann (`S2-01` Part II §§125–148; `S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
metric-free regressive product defined strictly by dual contraction relative to a
`MetricFreeVolumeDatum`, without any Euclidean metric or Hodge star. -/
def dualContractionRegressive {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (vol : MetricFreeVolumeDatum K V) (x y : ExteriorAlgebra K V) :
    ExteriorAlgebra K V :=
  vol.poincareEquiv (vol.poincareEquiv.symm x * vol.poincareEquiv.symm y)

/-- **Grassmann (`S2-01` §130; `S2-02`; `R3.2`)**:
associativity of the metric-free dual-contraction regressive product. -/
theorem dualContractionRegressive_assoc {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (vol : MetricFreeVolumeDatum K V) (x y z : ExteriorAlgebra K V) :
    dualContractionRegressive vol (dualContractionRegressive vol x y) z =
      dualContractionRegressive vol x (dualContractionRegressive vol y z) := by
  dsimp [dualContractionRegressive]
  rw [vol.poincareEquiv.symm_apply_apply, vol.poincareEquiv.symm_apply_apply, mul_assoc]

/-- **Grassmann (`S2-01` Part II Ch. 3 §134; `S2-02` Part 1 No. 87; `R3.2`)**:
Poincaré contraction maps the unit `1 ∈ Λ(V^*)` to `vol.volumeBlade`. -/
theorem poincareEquiv_one_eq_volumeBlade {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (vol : MetricFreeVolumeDatum K V) :
    vol.poincareEquiv 1 = vol.volumeBlade := by
  rw [vol.poincareEquiv_eq 1, map_one, MulOpposite.unop_one]
  rfl

/-- **Grassmann (`S2-01` §134; `R3.2`)**:
`vol.volumeBlade` is a left identity for `dualContractionRegressive vol`. -/
theorem dualContractionRegressive_volumeBlade_left {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (vol : MetricFreeVolumeDatum K V) (x : ExteriorAlgebra K V) :
    dualContractionRegressive vol vol.volumeBlade x = x := by
  dsimp [dualContractionRegressive]
  have h1 : vol.poincareEquiv.symm vol.volumeBlade = 1 := by
    apply vol.poincareEquiv.injective
    rw [vol.poincareEquiv.apply_symm_apply, poincareEquiv_one_eq_volumeBlade]
  rw [h1, one_mul, vol.poincareEquiv.apply_symm_apply]

/-- **Grassmann (`S2-01` §134; `R3.2`)**:
`vol.volumeBlade` is a right identity for `dualContractionRegressive vol`. -/
theorem dualContractionRegressive_volumeBlade_right {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (vol : MetricFreeVolumeDatum K V) (x : ExteriorAlgebra K V) :
    dualContractionRegressive vol x vol.volumeBlade = x := by
  dsimp [dualContractionRegressive]
  have h1 : vol.poincareEquiv.symm vol.volumeBlade = 1 := by
    apply vol.poincareEquiv.injective
    rw [vol.poincareEquiv.apply_symm_apply, poincareEquiv_one_eq_volumeBlade]
  rw [h1, mul_one, vol.poincareEquiv.apply_symm_apply]

/-- **Grassmann (`S2-01` Part II Ch. 3 §§125–148; `S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
when instantiated with `metricFreeVolumeDatumOfBasis b`, `dualContractionRegressive` agrees
identically with `ExteriorRegressive.regressive b`. -/
theorem dualContractionRegressive_ofBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : ExteriorAlgebra K V) :
    dualContractionRegressive (metricFreeVolumeDatumOfBasis b) x y =
      ExteriorRegressive.regressive b x y :=
  (regressive_eq_poincareEquiv b x y).symm

private theorem fin_orderEmb_eq_id {n : ℕ} (σ : Fin n ↪o Fin n) (j : Fin n) : σ j = j := by
  have hle : j ≤ σ j := σ.strictMono.id_le j
  have hle_set : Finset.image σ (Finset.Ici j) ≤ Finset.Ici (σ j) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
    exact Finset.mem_Ici.mpr (σ.monotone (Finset.mem_Ici.mp hk))
  have hcard := Finset.card_le_card hle_set
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Ici, Fin.card_Ici] at hcard
  have hj_lt : j.val < n := j.isLt
  have hσ_lt : (σ j).val < n := (σ j).isLt
  have hle_val : j.val ≤ (σ j).val := hle
  exact Fin.ext (by omega)

/-- **Grassmann (`S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
any endomorphism `g : V →ₗ[K] V` acts on the top exterior power `⋀[K]^(finrank K V) V`
by multiplication by `LinearMap.det g`. -/
theorem map_top_exteriorPower_eq_det_smul {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (g : V →ₗ[K] V) {ω : ExteriorAlgebra K V}
    (hω : ω ∈ ⋀[K]^(Module.finrank K V) V) :
    ExteriorAlgebra.map g ω = LinearMap.det g • ω := by
  let b := Module.finBasis K V
  have hvol_eq : ExteriorRegressive.volume b =
      ExteriorAlgebra.ιMulti K (Module.finrank K V) b := by
    change b.ExteriorAlgebra Finset.univ = _
    rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin (Module.finrank K V))]
    let e := Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_fin (Module.finrank K V)))
    have he_fun : (fun i : Fin (Module.finrank K V) => b (e i)) = b := by
      funext i
      rw [fin_orderEmb_eq_id e i]
    change ExteriorAlgebra.ιMulti K (Module.finrank K V) (fun i => b (e i)) = _
    rw [he_fun]
  have hω_coord : ω = volCoord b ω • ExteriorRegressive.volume b :=
    eq_volCoord_smul_volume b hω
  have hdet : b.det (g ∘ b) = LinearMap.det g := by
    rw [← LinearMap.det_toMatrix b g, Module.Basis.det_apply]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  calc
    ExteriorAlgebra.map g ω
        = ExteriorAlgebra.map g (volCoord b ω • ExteriorRegressive.volume b) := by
          conv_lhs => rw [hω_coord]
    _ = volCoord b ω • ExteriorAlgebra.map g (ExteriorAlgebra.ιMulti K (Module.finrank K V) b) := by
          rw [map_smul, hvol_eq]
    _ = volCoord b ω • ExteriorAlgebra.ιMulti K (Module.finrank K V) (g ∘ b) := by
          rw [ExteriorAlgebra.map_apply_ιMulti]
    _ = volCoord b ω • (b.det (g ∘ b) • ExteriorRegressive.volume b) := by
          rw [ιMulti_eq_det_smul_volume b (g ∘ b)]
          rfl
    _ = LinearMap.det g • (volCoord b ω • ExteriorRegressive.volume b) := by
          rw [hdet, smul_smul, smul_smul, mul_comm]
    _ = LinearMap.det g • ω := by
          rw [← hω_coord]

/-- **Grassmann (`S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
for any `g ∈ GL(V)`, `ExteriorAlgebra.map g` intertwines the metric-free regressive product
with scaling by `(LinearMap.det g)⁻¹`. -/
theorem dualContractionRegressive_map_gl {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (vol : MetricFreeVolumeDatum K V)
    (hvol : vol.volumeBlade ∈ ⋀[K]^(Module.finrank K V) V)
    (g : LinearMap.GeneralLinearGroup K V) (x y : ExteriorAlgebra K V) :
    ExteriorAlgebra.map (g : V →ₗ[K] V) (dualContractionRegressive vol x y) =
      (LinearMap.det (g : V →ₗ[K] V))⁻¹ •
        dualContractionRegressive vol
          (ExteriorAlgebra.map (g : V →ₗ[K] V) x)
          (ExteriorAlgebra.map (g : V →ₗ[K] V) y) := by
  let gE : V ≃ₗ[K] V := g.toLinearEquiv
  have hgE : gE.toLinearMap = (g : V →ₗ[K] V) := rfl
  let d : K := LinearMap.det (g : V →ₗ[K] V)
  have hd_ne : d ≠ 0 := by
    have hunit : IsUnit (LinearMap.det (g : V →ₗ[K] V)) := by
      rw [← hgE, ← LinearEquiv.coe_det]
      exact Units.isUnit gE.det
    exact hunit.ne_zero
  have hpoinc : ∀ α : ExteriorAlgebra K (Module.Dual K V),
      ExteriorAlgebra.map (g : V →ₗ[K] V) (vol.poincareEquiv α) =
        d • vol.poincareEquiv (ExteriorAlgebra.map gE.symm.toLinearMap.dualMap α) := by
    intro α
    rw [vol.poincareEquiv_eq, vol.poincareEquiv_eq, ← hgE, map_dualContractionAlgHom_linearEquiv gE,
      hgE, show ExteriorAlgebra.map (g : V →ₗ[K] V) vol.volumeBlade = d • vol.volumeBlade from
        map_top_exteriorPower_eq_det_smul (g : V →ₗ[K] V) hvol,
      map_smul]
  have hsymm : ∀ z : ExteriorAlgebra K V,
      vol.poincareEquiv.symm (ExteriorAlgebra.map (g : V →ₗ[K] V) z) =
        d • ExteriorAlgebra.map gE.symm.toLinearMap.dualMap (vol.poincareEquiv.symm z) := by
    intro z
    apply vol.poincareEquiv.injective
    rw [vol.poincareEquiv.apply_symm_apply, map_smul, ← hpoinc,
      vol.poincareEquiv.apply_symm_apply]
  dsimp [dualContractionRegressive]
  rw [hpoinc, hsymm x, hsymm y, smul_mul_assoc, mul_smul_comm, map_smul, map_smul,
    ← map_mul (ExteriorAlgebra.map gE.symm.toLinearMap.dualMap),
    smul_smul, smul_smul]
  congr 1
  dsimp only [d]
  field_simp [hd_ne]

/-- **Grassmann (`S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
strict `SL(V)` covariance of the metric-free dual-contraction regressive product. -/
theorem dualContractionRegressive_map_sl {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (vol : MetricFreeVolumeDatum K V)
    (hvol : vol.volumeBlade ∈ ⋀[K]^(Module.finrank K V) V)
    (g : SpecialLinearGroup K V) (x y : ExteriorAlgebra K V) :
    ExteriorAlgebra.map (g : V →ₗ[K] V) (dualContractionRegressive vol x y) =
      dualContractionRegressive vol
        (ExteriorAlgebra.map (g : V →ₗ[K] V) x)
        (ExteriorAlgebra.map (g : V →ₗ[K] V) y) := by
  have hgl := dualContractionRegressive_map_gl vol hvol g.toGeneralLinearGroup x y
  have hcoe : (g.toGeneralLinearGroup : V →ₗ[K] V) = (g : V →ₗ[K] V) := rfl
  have hdet : LinearMap.det (g : V →ₗ[K] V) = 1 := SpecialLinearGroup.det_eq_one g
  rw [hcoe, hdet, inv_one, one_smul] at hgl
  exact hgl

/-- **Grassmann (`S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
compatibility of `ExteriorRegressive.regressive b` with `GeneralLinearGroup K V` `(det g)⁻¹`
covariance. -/
theorem regressive_map_gl_inv_det {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (g : LinearMap.GeneralLinearGroup K V)
    (x y : ExteriorAlgebra K V) :
    ExteriorAlgebra.map (g : V →ₗ[K] V) (ExteriorRegressive.regressive b x y) =
      (LinearMap.det (g : V →ₗ[K] V))⁻¹ •
        ExteriorRegressive.regressive b
          (ExteriorAlgebra.map (g : V →ₗ[K] V) x)
          (ExteriorAlgebra.map (g : V →ₗ[K] V) y) := by
  let gE : V ≃ₗ[K] V := g.toLinearEquiv
  have hgE : gE.toLinearMap = (g : V →ₗ[K] V) := rfl
  have hdet_ne : LinearMap.det (g : V →ₗ[K] V) ≠ 0 := by
    rw [← hgE, ← LinearEquiv.coe_det]
    exact Units.ne_zero gE.det
  have hreg := InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges.regressive_map_linearEquiv b gE x y
  rw [hgE] at hreg
  have hscaled := congrArg (fun z => (LinearMap.det (g : V →ₗ[K] V))⁻¹ • z) hreg
  rwa [smul_smul, inv_mul_cancel₀ hdet_ne, one_smul] at hscaled

/-- **Grassmann (`S2-02` Part 1 Nos. 87, 103; `R3.2`)**:
strict `SpecialLinearGroup K V` invariance of `ExteriorRegressive.regressive b`. -/
theorem regressive_map_specialLinearGroup {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V) (g : SpecialLinearGroup K V)
    (x y : ExteriorAlgebra K V) :
    ExteriorAlgebra.map (g : V →ₗ[K] V) (ExteriorRegressive.regressive b x y) =
      ExteriorRegressive.regressive b
        (ExteriorAlgebra.map (g : V →ₗ[K] V) x)
        (ExteriorAlgebra.map (g : V →ₗ[K] V) y) :=
  InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges.regressive_map_sl b g.toLinearEquiv
    (SpecialLinearGroup.det_eq_one g) x y

/-- **Grassmann (`S2-01` Part II Ch. 3; `S2-02` No. 87; `R3.2`)**:
non-spanning zero-meet edge case for `dualContractionRegressive`: whenever
`span v ⊔ span w ≠ ⊤`, the dual-contraction regressive meet vanishes even when
`span v ⊓ span w ≠ ⊥`. -/
theorem dualContractionRegressive_eq_zero_of_sup_ne_top {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (vol : MetricFreeVolumeDatum K V) (hvol : vol.volumeBlade ∈ ⋀[K]^(Module.finrank K V) V)
    {r s : ℕ} (v : Fin r → V) (w : Fin s → V)
    (hsup : Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) ≠ ⊤) :
    dualContractionRegressive vol
        (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w) = 0 := by
  let b := Module.finBasis K V
  let c : K := volCoord b vol.volumeBlade
  have hblade : vol.volumeBlade = c • ExteriorRegressive.volume b :=
    eq_volCoord_smul_volume b hvol
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hbv : vol.volumeBlade = 0 := by
      rw [hblade, hc0, zero_smul]
    have h0 : vol.poincareEquiv 1 = 0 := by
      rw [poincareEquiv_one_eq_volumeBlade, hbv]
    have h10 : (1 : ExteriorAlgebra K (Module.Dual K V)) = 0 :=
      vol.poincareEquiv.injective (h0.trans (map_zero _).symm)
    exact one_ne_zero h10
  have hpoinc : ∀ α, vol.poincareEquiv α =
      c • GrassmannAusdehnungslehreRegressiveShadow.poincareEquiv b α := fun α => by
    rw [vol.poincareEquiv_eq, poincareEquiv_apply, hblade]
    rw [map_smul]
    rfl
  have hsymm : ∀ z, vol.poincareEquiv.symm z =
      c⁻¹ • (GrassmannAusdehnungslehreRegressiveShadow.poincareEquiv b).symm z := fun z => by
    apply vol.poincareEquiv.injective
    rw [vol.poincareEquiv.apply_symm_apply, map_smul, hpoinc, smul_smul,
      inv_mul_cancel₀ hc_ne, one_smul, LinearEquiv.apply_symm_apply]
  have hreg : dualContractionRegressive vol
      (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w) =
      c⁻¹ • ExteriorRegressive.regressive b
        (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w) := by
    dsimp [dualContractionRegressive]
    rw [hsymm, hsymm, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, hpoinc,
      ← regressive_eq_poincareEquiv b, smul_smul, smul_smul]
    congr 1
    field_simp [hc_ne]
  rw [hreg, regressive_ιMulti_eq_zero_of_sup_ne_top b v w hsup, smul_zero]

/-- **Grassmann (`S2-01`, `S2-02` Engel/Müller Note 31, p. 341; `R3.2`)**:
summary of regressive meet intersection (`U ⊔ W = ⊤`), non-spanning zero-meet edge case,
and Engel/Müller Note 31 left common-factor law vs. 5D countermodel. -/
theorem grassmann_regressive_meet_and_note31_summary (K : Type*) [Field K] :
    (let b := Pi.basisFun K (Fin 4)
     let A := ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)
     let B := ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)
     bladeSupport A ⊓ bladeSupport B ≠ ⊥ ∧ ExteriorRegressive.regressive b A B = 0) ∧
    (∀ {V : Type*} [AddCommGroup V] [Module K V] {n r s : ℕ} (b : Module.Basis (Fin n) K V)
      (v : Fin r → V) (w : Fin s → V),
      LinearIndependent K v → LinearIndependent K w →
      Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) = ⊤ →
      ExteriorRegressive.regressive b (ExteriorAlgebra.ιMulti K r v)
        (ExteriorAlgebra.ιMulti K s w) ≠ 0 ∧
        bladeSupport (ExteriorRegressive.regressive b (ExteriorAlgebra.ιMulti K r v)
          (ExteriorAlgebra.ιMulti K s w)) =
          Submodule.span K (Set.range v) ⊓ Submodule.span K (Set.range w)) ∧
    (∀ {α : ℕ} (v : Fin α → Fin 5 → K) (B C : ExteriorAlgebra K (Fin 5 → K)),
      ExteriorRegressive.regressive (Pi.basisFun K (Fin 5))
          (ExteriorAlgebra.ιMulti K α v * B) (ExteriorAlgebra.ιMulti K α v * C) =
        ExteriorAlgebra.ιMulti K α v *
          ExteriorRegressive.regressive (Pi.basisFun K (Fin 5))
            (ExteriorAlgebra.ιMulti K α v * B) C) ∧
    (let b := Pi.basisFun K (Fin 5)
     let A := ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)
     let B := ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)
     let C := ExteriorAlgebra.ι K (b 3) * ExteriorAlgebra.ι K (b 4)
     A * B = 0 ∧
       C * ExteriorRegressive.regressive b (A * B) C = 0 ∧
       ExteriorRegressive.regressive b C (ExteriorRegressive.regressive b (A * B) C) = 0 ∧
       ExteriorRegressive.regressive b (A * C) (B * C) ≠ 0 ∧
       ExteriorRegressive.regressive b (A * C) (B * C) ≠
         C * ExteriorRegressive.regressive b (A * B) C) := by
  refine ⟨regressive_non_spanning_counterexample_dim4 K, ?_, ?_, note31_counterexample_dim5 K⟩
  · intro V _ _ n r s b v w hv hw hsup
    exact regressive_blade_intersection_of_sup_eq_top b v w hv hw hsup
  · intro α v B C
    exact note31_valid_left_common_factor (Pi.basisFun K (Fin 5)) v B C

private noncomputable def note97ShiftLinearEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun u := ![u 0, u 1, u 2, u 3 - 3 * u 0]
  invFun w := ![w 0, w 1, w 2, w 3 + 3 * w 0]
  map_add' u v := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' c u := by ext i; fin_cases i <;> (simp; try ring)
  left_inv u := by ext i; fin_cases i <;> (simp; try ring)
  right_inv w := by ext i; fin_cases i <;> (simp; try ring)

/-- **Grassmann (`S2-02` Part 1 Nos. 396, 405–409; Engel/Müller Note 97, pp. 369–370; `R3.2`)**:
every `GL(4, ℝ)` automorphism preserves `IsSyncyclic4` and every `OCircleBilin ∈ O(1, 3)`
isometry preserves `IsCircleTangent`, while the explicit `GL(4, ℝ)` shear
`note97ShiftLinearEquiv` maps two tangent circles `(0,0; r=1)` and `(2,0; r=1)` to
non-tangent circles `(0,0; r=2)` and `(2,0; r=2)`. -/
theorem grassmann_note97_gl4_syncyclic_vs_orthogonal_tangency :
    (∀ (g : LinearMap.GeneralLinearGroup ℝ (Fin 4 → ℝ)) (C₁ C₂ C₃ C₄ : Fin 4 → ℝ),
      IsSyncyclic4 (g.toLinearEquiv C₁) (g.toLinearEquiv C₂)
        (g.toLinearEquiv C₃) (g.toLinearEquiv C₄) ↔ IsSyncyclic4 C₁ C₂ C₃ C₄) ∧
    (∀ (T : OCircleBilin) (u v : Fin 4 → ℝ),
      IsCircleTangent u v → IsCircleTangent (T u) (T v)) ∧
    (∃ (g : LinearMap.GeneralLinearGroup ℝ (Fin 4 → ℝ)) (u v : Fin 4 → ℝ),
      IsCircleTangent u v ∧ ¬ IsCircleTangent (g.toLinearEquiv u) (g.toLinearEquiv v)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g C₁ C₂ C₃ C₄
    exact note97_syncyclic_vs_moebius_tangency.1 g.toLinearEquiv C₁ C₂ C₃ C₄
  · intro T u v huv
    have hbilin : ∀ a b : Fin 4 → ℝ, circleBilin (T a) (T b) = circleBilin a b :=
      (bilin_preserves_iff_quadratic circleBilin circleBilin_symm T.toLinearMap).mpr T.map_app
    exact note97_syncyclic_vs_moebius_tangency.2.1 T.toLinearMap hbilin u v huv
  · refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv note97ShiftLinearEquiv,
      circleVec 0 0 1, circleVec 2 0 1, ?_, ?_⟩
    · dsimp [IsCircleTangent]
      rw [(grassmann_no396_double_distance 0 0 0 0 1 0 0 1 2 0 1).2.1,
        (grassmann_no396_double_distance 0 0 2 0 1 0 0 1 2 0 1).2.1,
        (grassmann_no396_double_distance 0 0 0 0 1 0 0 1 2 0 1).2.2]
      norm_num
    · have hu : (LinearMap.GeneralLinearGroup.ofLinearEquiv note97ShiftLinearEquiv).toLinearEquiv
          (circleVec 0 0 1) = circleVec 0 0 2 := by
        ext i; fin_cases i <;> (simp [note97ShiftLinearEquiv, circleVec]; try norm_num)
      have hv : (LinearMap.GeneralLinearGroup.ofLinearEquiv note97ShiftLinearEquiv).toLinearEquiv
          (circleVec 2 0 1) = circleVec 2 0 2 := by
        ext i; fin_cases i <;> (simp [note97ShiftLinearEquiv, circleVec]; try norm_num)
      rw [hu, hv]
      dsimp [IsCircleTangent]
      rw [(grassmann_no396_double_distance 0 0 0 0 2 0 0 2 2 0 2).2.1,
        (grassmann_no396_double_distance 0 0 2 0 2 0 0 2 2 0 2).2.1,
        (grassmann_no396_double_distance 0 0 0 0 2 0 0 2 2 0 2).2.2]
      norm_num

end GrassmannDualContraction

/-! ## Part II: Plücker (1865) — 6 Line Coordinates in `⋀^2 V` & Klein Quadric (`S2-03`) -/

section PluckerKleinQuadric

private theorem e4Pair_mem_exteriorPower_two {R : Type*} [CommRing R] (i j : Fin 4) :
    e4Pair (R := R) i j ∈ ⋀[R]^2 (Fin 4 → R) := by
  have heq : e4Pair (R := R) i j = ExteriorAlgebra.ιMulti R 2 ![e4 i, e4 j] := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  rw [heq]
  exact ExteriorAlgebra.ιMulti_range R 2 ⟨![e4 i, e4 j], rfl⟩

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
for any commutative ring `R`, `pluckerToExterior2 P` lies in the homogeneous second exterior
power `⋀[R]^2 (Fin 4 → R)`. -/
theorem pluckerToExterior2_mem_exteriorPower_two {R : Type*} [CommRing R] (P : Plucker6 R) :
    pluckerToExterior2 P ∈ ⋀[R]^2 (Fin 4 → R) := by
  dsimp [pluckerToExterior2]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (e4Pair_mem_exteriorPower_two _ _)

private theorem basisFun4_apply_eq_e4 {R : Type*} [CommRing R] (k : Fin 4) :
    Pi.basisFun R (Fin 4) k = e4 k := by
  ext j
  simp [Pi.basisFun_apply, e4, Pi.single_apply, eq_comm]

private theorem basisFun4_exteriorPower_two_pair {R : Type*} [CommRing R]
    {i j : Fin 4} (hij : i < j) :
    ((Pi.basisFun R (Fin 4)).exteriorPower 2
        (Set.powersetCard.ofCard (Finset.card_pair hij.ne)) : ExteriorAlgebra R (Fin 4 → R)) =
      e4Pair (R := R) i j := by
  let b := Pi.basisFun R (Fin 4)
  let s : Finset (Fin 4) := {i, j}
  have hcard : s.card = 2 := Finset.card_pair hij.ne
  change ((b.exteriorPower 2 (Set.powersetCard.ofCard (s := s) hcard) : ⋀[R]^2 (Fin 4 → R)) :
    ExteriorAlgebra R (Fin 4 → R)) = e4Pair i j
  rw [← ExteriorAlgebra.basis_eq_coe_basis b
    (Set.powersetCard.ofCard (s := s) hcard)]
  change b.ExteriorAlgebra s = e4Pair i j
  rw [ExteriorAlgebra.basis_apply_ofCard b hcard]
  let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard)
  have hg_mem : ∀ k : Fin 2, g k ∈ s := fun k =>
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g k)).1 ⟨k, rfl⟩
  have hg_lt : g 0 < g 1 := g.strictMono (by decide)
  have hm0 : g 0 = i ∨ g 0 = j := by simpa [s] using hg_mem 0
  have hm1 : g 1 = i ∨ g 1 = j := by simpa [s] using hg_mem 1
  have hg0 : g 0 = i := by
    rcases hm0 with h | h <;> rcases hm1 with h' | h' <;> omega
  have hg1 : g 1 = j := by
    rcases hm0 with h | h <;> rcases hm1 with h' | h' <;> omega
  change ExteriorAlgebra.ιMulti R 2 (fun k => b (g k)) = e4Pair i j
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have hsucc : (Fin.succ 0 : Fin 2) = 1 := rfl
  simp only [Matrix.vecTail, Function.comp_apply, hsucc, hg0, hg1, e4Pair]
  rw [basisFun4_apply_eq_e4, basisFun4_apply_eq_e4]

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
canonical linear isomorphism between 6 homogeneous Plücker coordinates `Fin 6 → R` and
`⋀[R]^2 (Fin 4 → R)` over any commutative ring `R`. -/
def pluckerExterior2LinearEquiv (R : Type*) [CommRing R] :
    (Fin 6 → R) ≃ₗ[R] ⋀[R]^2 (Fin 4 → R) :=
  let b := Pi.basisFun R (Fin 4)
  let B2 := b.exteriorPower 2
  let s01 : Set.powersetCard (Fin 4) 2 := Set.powersetCard.ofCard (Finset.card_pair (by decide : (0 : Fin 4) ≠ 1))
  let s02 : Set.powersetCard (Fin 4) 2 := Set.powersetCard.ofCard (Finset.card_pair (by decide : (0 : Fin 4) ≠ 2))
  let s03 : Set.powersetCard (Fin 4) 2 := Set.powersetCard.ofCard (Finset.card_pair (by decide : (0 : Fin 4) ≠ 3))
  let s12 : Set.powersetCard (Fin 4) 2 := Set.powersetCard.ofCard (Finset.card_pair (by decide : (1 : Fin 4) ≠ 2))
  let s13 : Set.powersetCard (Fin 4) 2 := Set.powersetCard.ofCard (Finset.card_pair (by decide : (1 : Fin 4) ≠ 3))
  let s23 : Set.powersetCard (Fin 4) 2 := Set.powersetCard.ofCard (Finset.card_pair (by decide : (2 : Fin 4) ≠ 3))
  have hs_all : ∀ s : Set.powersetCard (Fin 4) 2,
      s = s01 ∨ s = s02 ∨ s = s03 ∨ s = s12 ∨ s = s13 ∨ s = s23 := by
    intro ⟨t, ht⟩
    have h01 : s01.1 = ({0, 1} : Finset (Fin 4)) := rfl
    have h02 : s02.1 = ({0, 2} : Finset (Fin 4)) := rfl
    have h03 : s03.1 = ({0, 3} : Finset (Fin 4)) := rfl
    have h12 : s12.1 = ({1, 2} : Finset (Fin 4)) := rfl
    have h13 : s13.1 = ({1, 3} : Finset (Fin 4)) := rfl
    have h23 : s23.1 = ({2, 3} : Finset (Fin 4)) := rfl
    have hcard_sum : 2 =
        (if (0 : Fin 4) ∈ t then 1 else 0) + (if (1 : Fin 4) ∈ t then 1 else 0) +
        (if (2 : Fin 4) ∈ t then 1 else 0) + (if (3 : Fin 4) ∈ t then 1 else 0) := by
      have hsum : t.card = ∑ i : Fin 4, if i ∈ t then 1 else 0 := by
        rw [← Finset.card_filter]
        congr 1
        ext i; simp
      rw [Fin.sum_univ_four] at hsum
      exact (show t.card = 2 from ht).symm.trans hsum
    by_cases m0 : (0 : Fin 4) ∈ t <;> by_cases m1 : (1 : Fin 4) ∈ t <;>
      by_cases m2 : (2 : Fin 4) ∈ t <;> by_cases m3 : (3 : Fin 4) ∈ t
    · simp [m0, m1, m2, m3] at hcard_sum
    · simp [m0, m1, m2, m3] at hcard_sum
    · simp [m0, m1, m2, m3] at hcard_sum
    · left; apply Subtype.ext; rw [h01]; ext i; fin_cases i <;> simp [m0, m1, m2, m3]
    · simp [m0, m1, m2, m3] at hcard_sum
    · right; left; apply Subtype.ext; rw [h02]; ext i; fin_cases i <;> simp [m0, m1, m2, m3]
    · right; right; left; apply Subtype.ext; rw [h03]; ext i; fin_cases i <;> simp [m0, m1, m2, m3]
    · simp [m0, m1, m2, m3] at hcard_sum
    · simp [m0, m1, m2, m3] at hcard_sum
    · right; right; right; left; apply Subtype.ext; rw [h12]; ext i; fin_cases i <;> simp [m0, m1, m2, m3]
    · right; right; right; right; left; apply Subtype.ext; rw [h13]; ext i; fin_cases i <;> simp [m0, m1, m2, m3]
    · simp [m0, m1, m2, m3] at hcard_sum
    · right; right; right; right; right; apply Subtype.ext; rw [h23]; ext i; fin_cases i <;> simp [m0, m1, m2, m3]
    · simp [m0, m1, m2, m3] at hcard_sum
    · simp [m0, m1, m2, m3] at hcard_sum
    · simp [m0, m1, m2, m3] at hcard_sum
  have hpairs_ne :
      s01 ≠ s02 ∧ s01 ≠ s03 ∧ s01 ≠ s12 ∧ s01 ≠ s13 ∧ s01 ≠ s23 ∧
      s02 ≠ s03 ∧ s02 ≠ s12 ∧ s02 ≠ s13 ∧ s02 ≠ s23 ∧
      s03 ≠ s12 ∧ s03 ≠ s13 ∧ s03 ≠ s23 ∧
      s12 ≠ s13 ∧ s12 ≠ s23 ∧ s13 ≠ s23 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro h <;> have h1 := congrArg Subtype.val h <;> revert h1 <;> decide
  have hfwd : ∀ c : Fin 6 → R,
      (pluckerToExterior2 (coordinates.symm c) : ExteriorAlgebra R (Fin 4 → R)) =
        ((c 0 • B2 s01 + c 1 • B2 s02 + c 2 • B2 s03 +
          c 3 • B2 s12 + c 4 • B2 s13 + c 5 • B2 s23 : ⋀[R]^2 (Fin 4 → R)) :
          ExteriorAlgebra R (Fin 4 → R)) := by
    intro c
    simp only [pluckerToExterior2, coordinates, Equiv.coe_fn_symm_mk, Submodule.coe_add,
      Submodule.coe_smul]
    rw [basisFun4_exteriorPower_two_pair (by decide : (0 : Fin 4) < 1),
      basisFun4_exteriorPower_two_pair (by decide : (0 : Fin 4) < 2),
      basisFun4_exteriorPower_two_pair (by decide : (0 : Fin 4) < 3),
      basisFun4_exteriorPower_two_pair (by decide : (1 : Fin 4) < 2),
      basisFun4_exteriorPower_two_pair (by decide : (1 : Fin 4) < 3),
      basisFun4_exteriorPower_two_pair (by decide : (2 : Fin 4) < 3)]
  { toFun := fun c => ⟨pluckerToExterior2 (coordinates.symm c),
      pluckerToExterior2_mem_exteriorPower_two _⟩
    invFun := fun ω => ![B2.coord s01 ω, B2.coord s02 ω, B2.coord s03 ω,
      B2.coord s12 ω, B2.coord s13 ω, B2.coord s23 ω]
    map_add' := fun c d => by
      apply Subtype.ext
      change pluckerToExterior2 (coordinates.symm (c + d)) =
        pluckerToExterior2 (coordinates.symm c) + pluckerToExterior2 (coordinates.symm d)
      simp only [pluckerToExterior2, coordinates, Equiv.coe_fn_symm_mk, Pi.add_apply, add_smul]
      module
    map_smul' := fun r c => by
      apply Subtype.ext
      change pluckerToExterior2 (coordinates.symm (r • c)) =
        r • pluckerToExterior2 (coordinates.symm c)
      simp only [pluckerToExterior2, coordinates, Equiv.coe_fn_symm_mk, Pi.smul_apply,
        smul_eq_mul, smul_add, smul_smul]
    left_inv := fun c => by
      have hsub : (⟨pluckerToExterior2 (coordinates.symm c),
          pluckerToExterior2_mem_exteriorPower_two _⟩ : ⋀[R]^2 (Fin 4 → R)) =
          c 0 • B2 s01 + c 1 • B2 s02 + c 2 • B2 s03 +
            c 3 • B2 s12 + c 4 • B2 s13 + c 5 • B2 s23 :=
        Subtype.ext (hfwd c)
      ext i
      dsimp only
      rw [hsub]
      rcases hpairs_ne with ⟨h012, h013, h014, h015, h016, h023, h024, h025, h026,
        h034, h035, h036, h124, h125, h135⟩
      fin_cases i <;>
        simp [B2.coord_apply, h012, h013, h014, h015, h016, h023, h024, h025, h026,
          h034, h035, h036, h124, h125, h135,
          h012.symm, h013.symm, h014.symm, h015.symm, h016.symm, h023.symm, h024.symm,
          h025.symm, h026.symm, h034.symm, h035.symm, h036.symm, h124.symm, h125.symm, h135.symm]
    right_inv := fun ω => by
      apply Subtype.ext
      dsimp only
      rw [hfwd]
      congr 1
      have hsum : ω = ∑ s : Set.powersetCard (Fin 4) 2, B2.coord s ω • B2 s :=
        (B2.sum_repr ω).symm
      let U : Finset (Set.powersetCard (Fin 4) 2) := {s01, s02, s03, s12, s13, s23}
      have hU : U = Finset.univ := by
        ext s
        simp only [U, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
        exact hs_all s
      rw [← hU] at hsum
      rcases hpairs_ne with ⟨h012, h013, h014, h015, h016, h023, h024, h025, h026,
        h034, h035, h036, h124, h125, h135⟩
      rw [Finset.sum_insert (by simp [h012, h013, h014, h015, h016]),
        Finset.sum_insert (by simp [h023, h024, h025, h026]),
        Finset.sum_insert (by simp [h034, h035, h036]),
        Finset.sum_insert (by simp [h124, h125]),
        Finset.sum_insert (by simp [h135]),
        Finset.sum_singleton] at hsum
      conv_rhs => rw [hsum]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp only [add_assoc] }

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
evaluation formula for the linear isomorphism `pluckerExterior2LinearEquiv`. -/
@[simp] theorem pluckerExterior2LinearEquiv_apply {R : Type*} [CommRing R] (P : Plucker6 R) :
    (pluckerExterior2LinearEquiv R (coordinates P) : ExteriorAlgebra R (Fin 4 → R)) =
      pluckerToExterior2 P := by
  change pluckerToExterior2 (coordinates.symm (coordinates P)) = pluckerToExterior2 P
  rw [coordinates.symm_apply_apply]

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
the embedding `pluckerToExterior2 : Plucker6 R →ₗ[R] ⋀[R] (Fin 4 → R)` is injective. -/
theorem pluckerToExterior2_injective {R : Type*} [CommRing R] :
    Function.Injective (pluckerToExterior2 (R := R)) := by
  intro P Q hPQ
  have h1 : pluckerExterior2LinearEquiv R (coordinates P) =
      pluckerExterior2LinearEquiv R (coordinates Q) := by
    apply Subtype.ext
    simpa [pluckerExterior2LinearEquiv_apply] using hPQ
  exact coordinates.injective ((pluckerExterior2LinearEquiv R).injective h1)

/-- **Plücker & Grassmann (`S2-03` §§1–40; `S2-01`; `R3.2`)**:
the canonical 4-volume blade `extVol4` in `⋀^4 K^4` is nonzero over any field `K`. -/
theorem extVol4_ne_zero {K : Type*} [Field K] : (extVol4 (R := K)) ≠ 0 := by
  rw [extVol4_eq_ιMulti_basisFun]
  exact ιMulti_ne_zero_of_linearIndependent (Pi.basisFun K (Fin 4))
    (Pi.basisFun K (Fin 4)).linearIndependent

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
for any field `K` with `(2 : K) ≠ 0`, `pluckerToExterior2 P * pluckerToExterior2 P = 0` iff
the Klein quadric invariant `P.kleinQ = 0`. -/
theorem pluckerToExterior2_sq_eq_zero_iff_kleinQ {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (P : Plucker6 K) :
    pluckerToExterior2 P * pluckerToExterior2 P = 0 ↔ P.kleinQ = 0 := by
  rw [pluckerToExterior2_mul_pluckerToExterior2 P P, Plucker6.polar_self]
  constructor
  · intro h
    by_contra hq
    have hmul : (2 * P.kleinQ) ≠ 0 := mul_ne_zero h2 hq
    exact extVol4_ne_zero (smul_eq_zero.mp h |>.resolve_left hmul)
  · intro hq
    rw [hq, mul_zero, zero_smul]

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
over ANY field `K` (including characteristic 2), a Plücker 6-vector satisfies the Klein
relation `P.kleinQ = 0` iff `pluckerToExterior2 P` is a decomposable bivector `ι u * ι v`. -/
theorem plucker_kleinQ_eq_zero_iff_decomposable {K : Type*} [Field K] (P : Plucker6 K) :
    P.kleinQ = 0 ↔
      ∃ u v : Fin 4 → K, pluckerToExterior2 P = ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v := by
  constructor
  · intro hQ
    have hq_exp : P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 := hQ
    have ofVec : ∀ u v : Vec4 K,
        ExteriorAlgebra.ι K (vec4ToFin4 u) * ExteriorAlgebra.ι K (vec4ToFin4 v) =
          pluckerToExterior2 (Vec4.wedge u v) := ι_vec4_mul_ι_vec4
    by_cases h01 : P.p01 ≠ 0
    · let u : Vec4 K := ⟨1, 0, -P.p12 / P.p01, -P.p13 / P.p01⟩
      let v : Vec4 K := ⟨0, P.p01, P.p02, P.p03⟩
      refine ⟨vec4ToFin4 u, vec4ToFin4 v, ?_⟩
      rw [ofVec u v]
      congr 1
      apply Plucker6.ext
      · simp [u, v, Vec4.wedge]
      · simp [u, v, Vec4.wedge]
      · simp [u, v, Vec4.wedge]
      · simp [u, v, Vec4.wedge]; field_simp [h01]
      · simp [u, v, Vec4.wedge]; field_simp [h01]
      · simp [u, v, Vec4.wedge]; field_simp [h01]; linear_combination hq_exp
    · have hp01 : P.p01 = 0 := not_ne_iff.mp h01
      by_cases h02 : P.p02 ≠ 0
      · let u : Vec4 K := ⟨1, P.p12 / P.p02, 0, -P.p23 / P.p02⟩
        let v : Vec4 K := ⟨0, 0, P.p02, P.p03⟩
        refine ⟨vec4ToFin4 u, vec4ToFin4 v, ?_⟩
        rw [ofVec u v]
        congr 1
        apply Plucker6.ext
        · simp [u, v, Vec4.wedge, hp01]
        · simp [u, v, Vec4.wedge]
        · simp [u, v, Vec4.wedge]
        · simp [u, v, Vec4.wedge]; field_simp [h02]
        · simp [u, v, Vec4.wedge]; field_simp [h02]; linear_combination -hq_exp + P.p23 * hp01
        · simp [u, v, Vec4.wedge]; field_simp [h02]
      · have hp02 : P.p02 = 0 := not_ne_iff.mp h02
        by_cases h03 : P.p03 ≠ 0
        · have hp12 : P.p12 = 0 := by
            have h0 : P.p03 * P.p12 = 0 := by linear_combination hq_exp - P.p23 * hp01 + P.p13 * hp02
            exact (mul_eq_zero.mp h0).resolve_left h03
          let u : Vec4 K := ⟨1, P.p13 / P.p03, P.p23 / P.p03, 0⟩
          let v : Vec4 K := ⟨0, 0, 0, P.p03⟩
          refine ⟨vec4ToFin4 u, vec4ToFin4 v, ?_⟩
          rw [ofVec u v]
          congr 1
          apply Plucker6.ext
          · simp [u, v, Vec4.wedge, hp01]
          · simp [u, v, Vec4.wedge, hp02]
          · simp [u, v, Vec4.wedge]
          · simp [u, v, Vec4.wedge, hp12]
          · simp [u, v, Vec4.wedge]; field_simp [h03]
          · simp [u, v, Vec4.wedge]; field_simp [h03]
        · have hp03 : P.p03 = 0 := not_ne_iff.mp h03
          by_cases h12 : P.p12 ≠ 0
          · let u : Vec4 K := ⟨0, 1, 0, -P.p23 / P.p12⟩
            let v : Vec4 K := ⟨0, 0, P.p12, P.p13⟩
            refine ⟨vec4ToFin4 u, vec4ToFin4 v, ?_⟩
            rw [ofVec u v]
            congr 1
            apply Plucker6.ext
            · simp [u, v, Vec4.wedge, hp01]
            · simp [u, v, Vec4.wedge, hp02]
            · simp [u, v, Vec4.wedge, hp03]
            · simp [u, v, Vec4.wedge]
            · simp [u, v, Vec4.wedge]
            · simp [u, v, Vec4.wedge]; field_simp [h12]
          · have hp12 : P.p12 = 0 := not_ne_iff.mp h12
            by_cases h13 : P.p13 ≠ 0
            · let u : Vec4 K := ⟨0, 1, P.p23 / P.p13, 0⟩
              let v : Vec4 K := ⟨0, 0, 0, P.p13⟩
              refine ⟨vec4ToFin4 u, vec4ToFin4 v, ?_⟩
              rw [ofVec u v]
              congr 1
              apply Plucker6.ext
              · simp [u, v, Vec4.wedge, hp01]
              · simp [u, v, Vec4.wedge, hp02]
              · simp [u, v, Vec4.wedge, hp03]
              · simp [u, v, Vec4.wedge, hp12]
              · simp [u, v, Vec4.wedge]
              · simp [u, v, Vec4.wedge]; field_simp [h13]
            · have hp13 : P.p13 = 0 := not_ne_iff.mp h13
              let u : Vec4 K := ⟨0, 0, 1, 0⟩
              let v : Vec4 K := ⟨0, 0, 0, P.p23⟩
              refine ⟨vec4ToFin4 u, vec4ToFin4 v, ?_⟩
              rw [ofVec u v]
              congr 1
              apply Plucker6.ext <;> simp [u, v, Vec4.wedge, hp01, hp02, hp03, hp12, hp13]
  · rintro ⟨u, v, huv⟩
    let u' : Vec4 K := ⟨u 0, u 1, u 2, u 3⟩
    let v' : Vec4 K := ⟨v 0, v 1, v 2, v 3⟩
    have hu' : vec4ToFin4 u' = u := by ext i; fin_cases i <;> rfl
    have hv' : vec4ToFin4 v' = v := by ext i; fin_cases i <;> rfl
    rw [← hu', ← hv', ι_vec4_mul_ι_vec4] at huv
    have hP : P = Vec4.wedge u' v' := pluckerToExterior2_injective huv
    rw [hP]
    exact Vec4.wedge_isKlein u' v'

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
exterior-algebra decomposability characterization on `⋀[K]^2 (Fin 4 → K)` over any field `K`
with `(2 : K) ≠ 0`: `ω * ω = 0 ↔ ∃ u v, ω = ι u * ι v`. -/
theorem exteriorPower_two_sq_eq_zero_iff_decomposable_fin4 {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (ω : ⋀[K]^2 (Fin 4 → K)) :
    (ω : ExteriorAlgebra K (Fin 4 → K)) * (ω : ExteriorAlgebra K (Fin 4 → K)) = 0 ↔
      ∃ u v : Fin 4 → K, (ω : ExteriorAlgebra K (Fin 4 → K)) =
        ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v := by
  let P : Plucker6 K := coordinates.symm ((pluckerExterior2LinearEquiv K).symm ω)
  have hω : (ω : ExteriorAlgebra K (Fin 4 → K)) = pluckerToExterior2 P := by
    have h1 : ω = pluckerExterior2LinearEquiv K (coordinates P) := by
      dsimp [P]
      rw [coordinates.apply_symm_apply, LinearEquiv.apply_symm_apply]
    conv_lhs => rw [h1]
    exact pluckerExterior2LinearEquiv_apply P
  rw [hω, pluckerToExterior2_sq_eq_zero_iff_kleinQ h2 P,
    plucker_kleinQ_eq_zero_iff_decomposable P]

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
coordinate-free 4-dimensional exterior-square decomposability over any field `K` with
`(2 : K) ≠ 0`: for any `V` with `Module.finrank K V = 4` and `ω ∈ ⋀[K]^2 V`,
`ω * ω = 0 ↔ ∃ u v : V, ω = ι u * ι v`. -/
theorem exteriorPower_two_sq_eq_zero_iff_decomposable {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (h2 : (2 : K) ≠ 0) (hdim : Module.finrank K V = 4)
    (ω : ⋀[K]^2 V) :
    (ω : ExteriorAlgebra K V) * (ω : ExteriorAlgebra K V) = 0 ↔
      ∃ u v : V, (ω : ExteriorAlgebra K V) = ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v := by
  have : Module.Finite K V := Module.finite_of_finrank_eq_succ hdim
  let b := Module.finBasisOfFinrankEq K V hdim
  let e : V ≃ₗ[K] (Fin 4 → K) := b.equivFun
  let Φ : ExteriorAlgebra K V ≃ₐ[K] ExteriorAlgebra K (Fin 4 → K) :=
    AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap) (ExteriorAlgebra.map e.symm.toLinearMap)
      (by
        rw [ExteriorAlgebra.map_comp_map]
        have hc : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext v; simp
        rw [hc, ExteriorAlgebra.map_id])
      (by
        rw [ExteriorAlgebra.map_comp_map]
        have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext v; simp
        rw [hc, ExteriorAlgebra.map_id])
  let ω' : ⋀[K]^2 (Fin 4 → K) :=
    ⟨Φ (ω : ExteriorAlgebra K V), map_mem_exteriorPower e.toLinearMap ω.property⟩
  have hsq : ((ω : ExteriorAlgebra K V) * (ω : ExteriorAlgebra K V) = 0) ↔
      ((ω' : ExteriorAlgebra K (Fin 4 → K)) * (ω' : ExteriorAlgebra K (Fin 4 → K)) = 0) := by
    change _ ↔ Φ (ω : ExteriorAlgebra K V) * Φ (ω : ExteriorAlgebra K V) = 0
    rw [← map_mul Φ, map_eq_zero_iff Φ Φ.injective]
  rw [hsq, exteriorPower_two_sq_eq_zero_iff_decomposable_fin4 h2 ω']
  have hΦ : ∀ z : ExteriorAlgebra K V, Φ z = ExteriorAlgebra.map e.toLinearMap z := fun _ => rfl
  constructor
  · rintro ⟨u', v', huv'⟩
    refine ⟨e.symm u', e.symm v', ?_⟩
    apply Φ.injective
    rw [hΦ, hΦ, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
    simpa [ω', hΦ] using huv'
  · rintro ⟨u, v, huv⟩
    refine ⟨e u, e v, ?_⟩
    change Φ (ω : ExteriorAlgebra K V) = _
    rw [huv, hΦ, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
    rfl

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
explicit compound bivector `e₀ ∧ e₁ + e₂ ∧ e₃` encoded in `Plucker6 R`. -/
def nonDecomposablePlucker (R : Type*) [CommRing R] : Plucker6 R :=
  ⟨1, 0, 0, 0, 0, 1⟩

/-- **Plücker (`S2-03` §§1–40; `R3.2`)**:
the compound bivector `e₀ ∧ e₁ + e₂ ∧ e₃` has `kleinQ = 1`, is never decomposable over any
field `K`, and has nonzero square in `ExteriorAlgebra K (Fin 4 → K)` whenever `(2 : K) ≠ 0`. -/
theorem nonDecomposablePlucker_not_decomposable (K : Type*) [Field K] :
    (nonDecomposablePlucker K).kleinQ = 1 ∧
      pluckerToExterior2 (nonDecomposablePlucker K) = e4Pair 0 1 + e4Pair 2 3 ∧
      (¬ ∃ u v : Fin 4 → K,
        pluckerToExterior2 (nonDecomposablePlucker K) =
          ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) ∧
      ((2 : K) ≠ 0 →
        pluckerToExterior2 (nonDecomposablePlucker K) *
          pluckerToExterior2 (nonDecomposablePlucker K) ≠ 0) := by
  have hq : (nonDecomposablePlucker K).kleinQ = 1 := by
    simp [nonDecomposablePlucker, Plucker6.kleinQ]
  have hext : pluckerToExterior2 (nonDecomposablePlucker K) = e4Pair 0 1 + e4Pair 2 3 := by
    simp [pluckerToExterior2, nonDecomposablePlucker]
  refine ⟨hq, hext, ?_, ?_⟩
  · intro hdec
    have h0 := (plucker_kleinQ_eq_zero_iff_decomposable (nonDecomposablePlucker K)).mpr hdec
    rw [hq] at h0
    exact one_ne_zero h0
  · intro h2 hsq
    have h0 := (pluckerToExterior2_sq_eq_zero_iff_kleinQ h2 (nonDecomposablePlucker K)).mp hsq
    rw [hq] at h0
    exact one_ne_zero h0

end PluckerKleinQuadric

/-! ## Part III: Plücker (1868–1869) — Linear Complexes, Rank-Drop, & Dyname Reduction (`S2-04`) -/

section PluckerComplexAndDyname

/-- **Plücker (`S2-04` Part I §§1–3, Nos. 26–148; `R3.2`)**:
linear complex membership `C.Incident P` is equivalent to vanishing of the exterior wedge
`pluckerToExterior2 C * pluckerToExterior2 P = 0` over any field `K`. -/
theorem linearComplex_iff_exterior_wedge_eq_zero {K : Type*} [Field K]
    (C P : Plucker6 K) :
    C.Incident P ↔ pluckerToExterior2 C * pluckerToExterior2 P = 0 := by
  rw [Plucker6.Incident, pluckerToExterior2_mul_pluckerToExterior2]
  constructor
  · intro h
    rw [h, zero_smul]
  · intro h
    exact (smul_eq_zero.mp h).resolve_right extVol4_ne_zero

/-- **Plücker (`S2-04` Part I Nos. 26–36; `R3.2`)**:
the skew-symmetric bilinear form `complexForm C` evaluates on two points `x, y : Vec4 R`
to the Plücker polar `C.polar (Vec4.wedge x y)`. -/
theorem complexForm_eq_polar_wedge {R : Type*} [CommRing R]
    (C : Plucker6 R) (x y : KleinQuadric.Vec4 R) :
    complexForm C (vec4ToFin4 x) (vec4ToFin4 y) = C.polar (Vec4.wedge x y) := by
  simp [complexForm, complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4,
    vec4ToFin4, Matrix.toBilin'_apply, Fin.sum_univ_four, Plucker6.polar_formula, Vec4.wedge]
  ring

/-- **Plücker (`S2-04` Part I Nos. 26–36; `R3.2`)**:
linear complex incidence `C.Incident P` equals vanishing of the Grassmann regressive meet
`ExteriorRegressive.regressive (Pi.basisFun K (Fin 4)) (pluckerToExterior2 C) (pluckerToExterior2 P)`. -/
theorem linearComplex_iff_regressive_eq_zero {K : Type*} [Field K]
    (C P : Plucker6 K) :
    C.Incident P ↔
      ExteriorRegressive.regressive (Pi.basisFun K (Fin 4))
        (pluckerToExterior2 C) (pluckerToExterior2 P) = 0 := by
  rw [Plucker6.Incident, regressive_pluckerToExterior2]
  constructor
  · intro h
    rw [h, zero_smul]
  · intro h
    exact (smul_eq_zero.mp h).resolve_right one_ne_zero

private theorem complexForm_eq_volCoord_wedge {K : Type*} [Field K]
    (C : Plucker6 K) (x y : Fin 4 → K) :
    complexForm C x y =
      volCoord (Pi.basisFun K (Fin 4))
        (pluckerToExterior2 C * ExteriorAlgebra.ι K x * ExteriorAlgebra.ι K y) := by
  let x' : Vec4 K := ⟨x 0, x 1, x 2, x 3⟩
  let y' : Vec4 K := ⟨y 0, y 1, y 2, y 3⟩
  have hx : vec4ToFin4 x' = x := by ext i; fin_cases i <;> rfl
  have hy : vec4ToFin4 y' = y := by ext i; fin_cases i <;> rfl
  rw [← hx, ← hy, complexForm_eq_polar_wedge, mul_assoc, ι_vec4_mul_ι_vec4,
    pluckerToExterior2_mul_pluckerToExterior2, map_smul, extVol4_eq_ιMulti_basisFun]
  have hvol : ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4)) =
      ExteriorRegressive.volume (Pi.basisFun K (Fin 4)) := by
    let b := Pi.basisFun K (Fin 4)
    let g := Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_fin 4))
    have hfun : (fun i : Fin 4 => b (g i)) = b := by
      funext i
      rw [fin_orderEmb_eq_id g i]
    change ExteriorAlgebra.ιMulti K 4 b = b.ExteriorAlgebra Finset.univ
    rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin 4)]
    change ExteriorAlgebra.ιMulti K 4 b = ExteriorAlgebra.ιMulti K 4 (fun i => b (g i))
    rw [hfun]
  rw [hvol, volCoord_volume, smul_eq_mul, mul_one]

/-- **Plücker (`S2-04` Part I Nos. 30–36; `R3.2`)**:
over any field `K`, every nonzero special linear complex (`C ≠ ⟨0, 0, 0, 0, 0, 0⟩`, `C.kleinQ = 0`)
is decomposable as `ι u * ι v` for linearly independent `u, v` whose span is exactly the
2-dimensional kernel (directrix) of `complexForm C`. -/
theorem complexForm_ker_eq_span_of_special {K : Type*} [Field K]
    (C : Plucker6 K) (hC : C ≠ ⟨0, 0, 0, 0, 0, 0⟩) (hQ : C.kleinQ = 0) :
    ∃ u v : Fin 4 → K, LinearIndependent K ![u, v] ∧
      pluckerToExterior2 C = ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v ∧
      LinearMap.ker (complexForm C) = Submodule.span K {u, v} ∧
      Module.finrank K (LinearMap.ker (complexForm C)) = 2 := by
  obtain ⟨u, v, huv⟩ := (plucker_kleinQ_eq_zero_iff_decomposable C).mp hQ
  have hli : LinearIndependent K ![u, v] := by
    by_contra hdep
    have hι0 : ExteriorAlgebra.ιMulti K 2 ![u, v] = 0 := (ιMulti_eq_zero_iff ![u, v]).mpr hdep
    have hι_eq : ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v =
        ExteriorAlgebra.ιMulti K 2 ![u, v] := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      rfl
    rw [hι_eq, hι0] at huv
    have h0 : pluckerToExterior2 (⟨0, 0, 0, 0, 0, 0⟩ : Plucker6 K) = 0 := by
      simp [pluckerToExterior2]
    have hC0 : C = ⟨0, 0, 0, 0, 0, 0⟩ := pluckerToExterior2_injective (huv.trans h0.symm)
    exact hC hC0
  have hker : LinearMap.ker (complexForm C) = Submodule.span K {u, v} := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      by_contra hx_not
      have hli3 : LinearIndependent K ![u, v, x] := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hc2 : c 2 = 0 := by
          by_contra hc2_ne
          apply hx_not
          have hx_eq : x = (-(c 2)⁻¹ * c 0) • u + (-(c 2)⁻¹ * c 1) • v := by
            have hsum : c 0 • u + c 1 • v + c 2 • x = 0 := by
              simpa [Fin.sum_univ_three, add_assoc] using hc
            have hcx : c 2 • x = -(c 0 • u + c 1 • v) := eq_neg_of_add_eq_zero_right hsum
            have hinv := congrArg (fun z : Fin 4 → K => (c 2)⁻¹ • z) hcx
            rw [smul_smul, inv_mul_cancel₀ hc2_ne, one_smul, smul_neg, smul_add, smul_smul,
              smul_smul] at hinv
            rw [hinv]
            module
          rw [hx_eq]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have hsum2 : c 0 • u + c 1 • v = 0 := by
          simpa [Fin.sum_univ_three, hc2] using hc
        have hlin2 := (Fintype.linearIndependent_iff.mp hli) ![c 0, c 1]
          (by simpa [Fin.sum_univ_two] using hsum2)
        intro i
        fin_cases i
        · exact hlin2 0
        · exact hlin2 1
        · exact hc2
      have hspan_ne_top : Submodule.span K {u, v, x} ≠ ⊤ := by
        intro htop
        have hfin : Module.finrank K (Submodule.span K (Set.range ![u, v, x])) = 3 := by
          rw [finrank_span_eq_card hli3, Fintype.card_fin]
        have hrange : Set.range ![u, v, x] = {u, v, x} := by
          ext z; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨i, rfl⟩; fin_cases i <;> simp
          · rintro (rfl | rfl | rfl)
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
        rw [hrange, htop, finrank_top, Module.finrank_fin_fun] at hfin
        omega
      obtain ⟨y, hy⟩ : ∃ y : Fin 4 → K, y ∉ Submodule.span K {u, v, x} := by
        by_contra h
        push Not at h
        exact hspan_ne_top (eq_top_iff.mpr fun z _ => h z)
      have hli4 : LinearIndependent K ![u, v, x, y] := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hc3 : c 3 = 0 := by
          by_contra hc3_ne
          apply hy
          have hsum : c 0 • u + c 1 • v + c 2 • x + c 3 • y = 0 := by
            simpa [Fin.sum_univ_four, add_assoc] using hc
          have hcy : c 3 • y = -(c 0 • u + c 1 • v + c 2 • x) :=
            eq_neg_of_add_eq_zero_right hsum
          have hinv := congrArg (fun z : Fin 4 → K => (c 3)⁻¹ • z) hcy
          rw [smul_smul, inv_mul_cancel₀ hc3_ne, one_smul, smul_neg, smul_add, smul_add,
            smul_smul, smul_smul, smul_smul] at hinv
          rw [hinv]
          refine Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) <;>
            exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        have hsum3 : c 0 • u + c 1 • v + c 2 • x = 0 := by
          simpa [Fin.sum_univ_four, hc3, add_assoc] using hc
        have hlin3 := (Fintype.linearIndependent_iff.mp hli3) ![c 0, c 1, c 2]
          (by simpa [Fin.sum_univ_three, add_assoc] using hsum3)
        intro i
        fin_cases i
        · exact hlin3 0
        · exact hlin3 1
        · exact hlin3 2
        · exact hc3
      have hne4 : ExteriorAlgebra.ιMulti K 4 ![u, v, x, y] ≠ 0 :=
        ιMulti_ne_zero_of_linearIndependent ![u, v, x, y] hli4
      have hprod4 : ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v *
          ExteriorAlgebra.ι K x * ExteriorAlgebra.ι K y =
          ExteriorAlgebra.ιMulti K 4 ![u, v, x, y] := by
        rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
          ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
          ExteriorAlgebra.ιMulti_zero_apply, mul_one]
        simp [Matrix.vecTail, mul_assoc]
      have hzero_xy : complexForm C x y = 0 := LinearMap.congr_fun hx y
      rw [complexForm_eq_volCoord_wedge, huv, hprod4] at hzero_xy
      have hmem4 : ExteriorAlgebra.ιMulti K 4 ![u, v, x, y] ∈ ⋀[K]^4 (Fin 4 → K) :=
        ExteriorAlgebra.ιMulti_range K 4 ⟨![u, v, x, y], rfl⟩
      have hcoord := eq_volCoord_smul_volume (Pi.basisFun K (Fin 4)) hmem4
      rw [hzero_xy, zero_smul] at hcoord
      exact hne4 hcoord
    · intro hx
      apply LinearMap.ext
      intro y
      change complexForm C x y = 0
      rw [complexForm_eq_volCoord_wedge, huv]
      have hmem : x ∈ Submodule.span K {u, v} := hx
      rw [Submodule.mem_span_pair] at hmem
      obtain ⟨a, b', rfl⟩ := hmem
      have hzero3 : ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v *
          ExteriorAlgebra.ι K (a • u + b' • v) = 0 := by
        have hswap_vu : ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K u =
            -(ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) :=
          eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
        rw [map_add, map_smul, map_smul, mul_add, mul_smul_comm, mul_smul_comm,
          mul_assoc (ExteriorAlgebra.ι K u), hswap_vu, mul_neg, ← mul_assoc (ExteriorAlgebra.ι K u),
          ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero, smul_zero, zero_add,
          mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, smul_zero]
      rw [hzero3, zero_mul, map_zero]
  have hfin : Module.finrank K (LinearMap.ker (complexForm C)) = 2 := by
    rw [hker]
    have hrange : Set.range ![u, v] = {u, v} := by
      ext z; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]
  exact ⟨u, v, hli, huv, hker, hfin⟩

/-- **Plücker (`S2-04` Part I Nos. 26–148; `R3.2`)**:
complete `(0, 2, 4)` kernel-rank trichotomy of `complexForm C` over any field `K`
(general complex `C.kleinQ ≠ 0` has rank 0, nonzero special complex `C ≠ ⟨0,0,0,0,0,0⟩, C.kleinQ = 0`
has rank 2, zero complex `C = ⟨0,0,0,0,0,0⟩` has rank 4). -/
theorem complexForm_finrank_ker_trichotomy {K : Type*} [Field K] (C : Plucker6 K) :
    (C.kleinQ ≠ 0 → Module.finrank K (LinearMap.ker (complexForm C)) = 0) ∧
    (C ≠ ⟨0, 0, 0, 0, 0, 0⟩ → C.kleinQ = 0 →
      Module.finrank K (LinearMap.ker (complexForm C)) = 2) ∧
    (C = ⟨0, 0, 0, 0, 0, 0⟩ → Module.finrank K (LinearMap.ker (complexForm C)) = 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hQ
    rw [general_complexForm_ker_bot hQ, finrank_bot]
  · intro hC hQ
    obtain ⟨_, _, _, _, _, hfin⟩ := complexForm_ker_eq_span_of_special C hC hQ
    exact hfin
  · intro hC
    rw [hC]
    have hzero : complexForm (⟨0, 0, 0, 0, 0, 0⟩ : Plucker6 K) = 0 := by
      ext x y
      simp [complexForm, complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4,
        Matrix.toBilin'_apply, Fin.sum_univ_four]
    rw [hzero, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]

/-- **Plücker (`S2-04` Part I No. 25, Nos. 44–61; `R3.2`)**:
central-axis and pitch reduction of a real dyname `(d, m)` (`d ≠ 0`): translating by
`t = -(axisFoot d m)` sends `(d, m)` to the parallel screw `(d, pitch d m • d)`, decomposes
`m = m₀ + pitch d m • d` into a zero-pitch Klein line `(d, m₀)` plus a collinear couple
`pitch d m • d`, and preserves both `kleinQ` and `pitch`. -/
theorem dyname_centralAxis_and_pitch_decomposition
    (d m : PluckerAffineScrew.Vec3) (hd : d ≠ 0) :
    let k : ℝ := PluckerAffineScrew.pitch d m
    let t : PluckerAffineScrew.Vec3 := -(PluckerAffineScrew.axisFoot d m : PluckerAffineScrew.Vec3)
    let m0 : PluckerAffineScrew.Vec3 := m - k • d
    affineTranslateDirMom t (d, m) = (d, k • d) ∧
      (PluckerAffineScrew.directionMomentEquiv.symm (d, m0)).kleinQ = 0 ∧
      (PluckerAffineScrew.directionMomentEquiv.symm (d, m)).kleinQ = k * (d ⬝ᵥ d) ∧
      PluckerAffineScrew.pitch d (affineTranslateDirMom t (d, m)).2 = k := by
  intro k t m0
  have hfoot : (PluckerAffineScrew.axisFoot d m : PluckerAffineScrew.Vec3) ⨯₃ d = m - k • d :=
    PluckerAffineScrew.axisFoot_cross d m hd
  have hcross : t ⨯₃ d = -(m - k • d) := by
    have hneg : (-((PluckerAffineScrew.axisFoot d m : PluckerAffineScrew.Vec3))) ⨯₃ d =
        -((PluckerAffineScrew.axisFoot d m : PluckerAffineScrew.Vec3) ⨯₃ d) := by
      ext i
      fin_cases i <;> simp [cross_apply] <;> ring
    change (-((PluckerAffineScrew.axisFoot d m : PluckerAffineScrew.Vec3))) ⨯₃ d = -(m - k • d)
    rw [hneg, hfoot]
  have htrans : affineTranslateDirMom t (d, m) = (d, k • d) := by
    dsimp [affineTranslateDirMom]
    refine Prod.ext rfl ?_
    rw [hcross, neg_sub, add_sub_cancel]
  have hklein0 : (PluckerAffineScrew.directionMomentEquiv.symm (d, m0)).kleinQ = 0 := by
    rw [PluckerAffineScrew.kleinQ_directionMoment]
    have hdot : d ⬝ᵥ (k • d) = d ⬝ᵥ m := by
      dsimp only [k]
      rw [dotProduct_smul, smul_eq_mul, PluckerAffineScrew.pitch_apply]
      have hn := PluckerAffineScrew.direction_normSq_ne_zero hd
      field_simp [hn]
    dsimp [m0]
    rw [dotProduct_sub, hdot, sub_self]
  have hklein_m : (PluckerAffineScrew.directionMomentEquiv.symm (d, m)).kleinQ = k * (d ⬝ᵥ d) := by
    dsimp only [k]
    rw [PluckerAffineScrew.kleinQ_directionMoment, PluckerAffineScrew.pitch_apply]
    have hn := PluckerAffineScrew.direction_normSq_ne_zero hd
    field_simp [hn]
  have hpitch : PluckerAffineScrew.pitch d (affineTranslateDirMom t (d, m)).2 = k :=
    PluckerAffineScrew.pitch_translation d m t
  exact ⟨htrans, hklein0, hklein_m, hpitch⟩

/-- **Plücker (`S2-04` Part I Nos. 23–25, 44–61; `R3.2`)**:
combined dyname reduction packaging central-axis screw translation, decomposition into two
finite forces (`exists_two_finite_forces_for_dyname`), canonical central-axis slope law
(`canonicalCentralComplex_slope`), and real special-complex directrix dimension (`finrank_ker_of_special`). -/
theorem dyname_and_centralComplex_reduction
    (d m : PluckerAffineScrew.Vec3) (hd : d ≠ 0) (k r dy dz : ℝ) :
    (affineTranslateDirMom (-(PluckerAffineScrew.axisFoot d m : PluckerAffineScrew.Vec3)) (d, m) =
        (d, PluckerAffineScrew.pitch d m • d)) ∧
      (∃ (d₁ m₁ d₂ m₂ : PluckerAffineScrew.Vec3),
        d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ d₁ ⬝ᵥ m₁ = 0 ∧ d₂ ⬝ᵥ m₂ = 0 ∧ d₁ + d₂ = d ∧ m₁ + m₂ = m) ∧
      ((canonicalCentralComplex k).Incident (rayPlucker ![1, r, 0, 0] ![1, r, dy, dz]) ↔
        r * dy + k * dz = 0) ∧
      (∀ C : Plucker6 ℝ, complexMatrix C ≠ 0 → C.kleinQ = 0 →
        Module.finrank ℝ (LinearMap.ker (nativeComplexForm C)) = 2) := by
  refine ⟨(dyname_centralAxis_and_pitch_decomposition d m hd).1,
    exists_two_finite_forces_for_dyname d m (Or.inl hd),
    canonicalCentralComplex_slope k r dy dz, ?_⟩
  intro C hC hQ
  exact finrank_ker_of_special C hC hQ

end PluckerComplexAndDyname

/-! ## Part IV: Primary-Source Synthesis (`S2-01`..`S2-04`) -/

section Synthesis

/-- **Master Pillar Synthesis (`S2-01`..`S2-04`, `R3.2`)**:
unifies Grassmann's metric-free `SL(V)`-covariant dual-contraction regressive meet and Note 97
`GL(4)` vs. `O(1,3)` separation with Plücker's coordinate-free 4D Klein quadric decomposability,
arbitrary-field `(0, 2, 4)` linear-complex kernel-rank trichotomy, and dyname central-axis reduction. -/
theorem grassmann_plucker_primary_sources_synthesis :
    (∀ (K : Type*) [Field K] (vol : MetricFreeVolumeDatum K (Fin 4 → K)),
      vol.volumeBlade ∈ ⋀[K]^4 (Fin 4 → K) →
      ∀ (g : SpecialLinearGroup K (Fin 4 → K)) (x y : ExteriorAlgebra K (Fin 4 → K)),
        ExteriorAlgebra.map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) (dualContractionRegressive vol x y) =
          dualContractionRegressive vol
            (ExteriorAlgebra.map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) x)
            (ExteriorAlgebra.map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) y)) ∧
    (∃ (g : LinearMap.GeneralLinearGroup ℝ (Fin 4 → ℝ)) (u v : Fin 4 → ℝ),
      IsCircleTangent u v ∧ ¬ IsCircleTangent (g.toLinearEquiv u) (g.toLinearEquiv v)) ∧
    (∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
      (2 : K) ≠ 0 → Module.finrank K V = 4 →
      ∀ ω : ⋀[K]^2 V,
        (ω : ExteriorAlgebra K V) * (ω : ExteriorAlgebra K V) = 0 ↔
          ∃ u v : V, (ω : ExteriorAlgebra K V) = ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) ∧
    (∀ (K : Type*) [Field K] (C : Plucker6 K),
      (C.kleinQ ≠ 0 → Module.finrank K (LinearMap.ker (complexForm C)) = 0) ∧
      (C ≠ ⟨0, 0, 0, 0, 0, 0⟩ → C.kleinQ = 0 →
        Module.finrank K (LinearMap.ker (complexForm C)) = 2) ∧
      (C = ⟨0, 0, 0, 0, 0, 0⟩ → Module.finrank K (LinearMap.ker (complexForm C)) = 4)) ∧
    (∀ (d m : PluckerAffineScrew.Vec3), d ≠ 0 →
      let k : ℝ := PluckerAffineScrew.pitch d m
      let t : PluckerAffineScrew.Vec3 := -(PluckerAffineScrew.axisFoot d m : PluckerAffineScrew.Vec3)
      let m0 : PluckerAffineScrew.Vec3 := m - k • d
      affineTranslateDirMom t (d, m) = (d, k • d) ∧
        (PluckerAffineScrew.directionMomentEquiv.symm (d, m0)).kleinQ = 0 ∧
        (PluckerAffineScrew.directionMomentEquiv.symm (d, m)).kleinQ = k * (d ⬝ᵥ d) ∧
        PluckerAffineScrew.pitch d (affineTranslateDirMom t (d, m)).2 = k) := by
  refine ⟨?_, grassmann_note97_gl4_syncyclic_vs_orthogonal_tangency.2.2, ?_, ?_, ?_⟩
  · intro K _ vol hvol g x y
    have hvol' : vol.volumeBlade ∈ ⋀[K]^(Module.finrank K (Fin 4 → K)) (Fin 4 → K) := by
      simpa [Module.finrank_fin_fun] using hvol
    exact dualContractionRegressive_map_sl vol hvol' g x y
  · intro K V _ _ _ h2 hdim ω
    exact exteriorPower_two_sq_eq_zero_iff_decomposable h2 hdim ω
  · intro K _ C
    exact complexForm_finrank_ker_trichotomy C
  · intro d m hd
    exact dyname_centralAxis_and_pitch_decomposition d m hd

end Synthesis

end InfoGeometry.Projective.GrassmannPrimarySources
