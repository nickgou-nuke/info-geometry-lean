/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.GrassmannPluckerKleinFunctorialBridges
import InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
import InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
import InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
import InfoGeometry.Canonical.PluckerGrassmannKleinUnifiedSynthesis
import InfoGeometry.Canonical.FelixKleinGeometryUnification
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.Projective.PluckerLinearComplexGeometry
import InfoGeometry.Projective.PluckerRayAxisAndDyname
import InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
import InfoGeometry.Projective.ExteriorKleinDeterminantCovariance
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.Clifford.CliffordLieAlgebra
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.Erlangen.SmoothCartanGeometry

/-!
# Cross-Pillar Functorial Completion of Klein 1872, Grassmann [6,7,8], and Plücker Bridges

This module completes the five cross-pillar functorial and naturality bridges connecting
Felix Klein's 1872 *Erlanger Programm* (`ABN7632.0001.001` / `arXiv:0807.3161v1`), Hermann
Grassmann's *Ausdehnungslehre* (`[6]` 1844, `[7]` 1862, `[8]` 1852), and Julius Plücker's
*Neue Geometrie des Raumes* (1868–1869) with the repository's three pillars:

1. **Bridge B (`O(circleBilin)` & Dimension-Generic `(n+1,1) ↔ (n+1,2)` Lie Sphere)**:
   Upgrades `lieMobiusToCircleHom` to a group isomorphism `lieMobiusStabilizer ≃* OCircleBilin`
   and `lieMobiusOrthogonalStabilizer ≃* OCircleBilin`, extends generically to
   `lieQuadricMobiusStabilizer n ≃* O(moebiusQuadricBilin n)` for all `n : ℕ` (specializing at
   `n = 3` to 5D Möbius `(4,1)` ↔ 6D hexaspherical Lie `(4,2)` with `laguerreShift` non-stabilizer
   witness), and aligns `lieBilinForm` / `circleBilin` with `lieQuadricBilin 2` /
   `moebiusQuadricBilin 2`.

2. **Bridge A (`ExteriorAlgebra.map`, `PGK₅` Equivariance, and Grassmann's `regressive`)**:
   Proves `pluckerToExterior2 (transform A P) = ExteriorAlgebra.map (Matrix.toLin' A) ...`,
   equips all five `PGK₅` Grassmannian carriers with public `GL(4, ℝ)` and `SL(4, ℝ)` `MulAction`
   instances commuting across all four pentagon equivalences, and proves `GL(V)` `det`-weighted
   (and `SL(V)` strict) equivariance of Grassmann's regressive meet `regressive b`.

3. **Bridge C (Klein Note VI Curvature Stabilizer)**:
   Formalizes `complexStabilizerGL4` and `complexProjectiveStabilizerGL4`, establishes the exact
   `transform` scaling law `g.1.det * μ⁻¹`, `conjugatePolar` commutation, `cayleyKleinChord`
   invariance, the general (`kleinQ ≠ 0`) vs. special (`kleinQ = 0`, stabilized rank-2 radical
   and unconstrained `det` countermodel) dichotomy, and `klein_adjoining_equiv` for Note VI.

4. **Bridge C (Klein §9 Contact 1-Form ↔ R1 Exterior Calculus & Maurer–Cartan Tower)**:
   Establishes `contactChartEquiv : ContactJetSpace n ℝ ≃L[ℝ] Chart (Fin (2 * n + 1))`, lifts
   `contactOneForm n` into `RealOperatorFrechetForm`, `ActionOperatorForm` on
   `chartDirectionalLieAction`, and `DerivationOperatorForm` on `smoothJetDerivationLane n`,
   proves `dθ = ∑ dxᵢ ∧ dpᵢ = - ∑ dpᵢ ∧ dxᵢ` (matching `grassmann_pfaff_contact5` at `n = 2`),
   proves pullback invariance along `legendreContact` and general contactomorphisms, connects
   `SmoothCartanGeometry` flatness to `MaurerCartanTower.actionCurvature`, and proves
   `surfaceLegendrian` pullback `dθ = 0` (`BUCKET 1`).

   **Explicit `O-EXT` Smooth PDE Boundary (`BUCKET 3`, `[OPEN / bucket_3_open_debt]`)**:
   Converse local PDE integration theorems — specifically smooth Frobenius integration (integrating
   an involutive kernel `dθ|_{ker θ} = 0` or flat Cartan curvature `Ω = 0` to local Legendrian
   leaves or a local gauge `g⁻¹ dg`) and Darboux's normal-form PDE theorem (locally transforming
   any contact 1-form with `θ ∧ (dθ)^n ≠ 0` to `dz - ∑ pᵢ dxᵢ`) — remain open analytic PDE
   obligations (`O-EXT`) and are deliberately not bypassed with axioms or proxies.

5. **Cross-Pillar Packaging (`Erlangen20Datum`, `SymmetryAction`, M2 `Clifford`)**:
   Instantiates `cliffordSymmetryAction`, `hTraceInvariantReadout`, `cliffordKreinInvariantPairing`,
   and `graceOperator_equivariantLinearMap` on `circleBilin`, `lieBilinForm`, `moebiusQuadricBilin`,
   `lieQuadricBilin`, and `kleinQuadricForm` (`Cl(3,3)`), lifts `lieMobiusToCircleIsoHom` and
   `secondCompoundSL4ToO33` to Clifford intertwiners, and packages `ExteriorAlgebra.map`,
   `transform`, and `complexCongr` into `SymmetryAction` and `Erlangen20Datum`.
-/

noncomputable section

namespace InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges

open Matrix
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerLinearComplex
open InfoGeometry.Projective.PluckerLinearComplexGeometry
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact
open InfoGeometry.Erlangen.GrassmannPluckerKleinFunctorialBridges
open InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
open InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
open InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
open InfoGeometry.Canonical.PluckerGrassmannKleinUnifiedSynthesis
open InfoGeometry.Canonical.GrassmannianCartanInteroperability
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Algebra
open InfoGeometry.Clifford
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance

/-! ## Section 1: Bridge B — `O(circleBilin)`, Surjectivity, and Generic `(n+1, 1) ↔ (n+1, 2)` -/

section BridgeB

/-- `lieBilin` wrapped as a Mathlib `LinearMap.BilinForm ℝ (Fin 5 → ℝ)`. -/
def lieBilinForm : LinearMap.BilinForm ℝ (Fin 5 → ℝ) :=
  LinearMap.mk₂ ℝ lieBilin
    (fun u v w => by
      simp only [lieBilin, Pi.add_apply, add_mul, neg_add, sub_eq_add_neg]
      abel)
    (fun c u v => by
      simp only [lieBilin, Pi.smul_apply, smul_eq_mul, mul_add, mul_sub, mul_neg, neg_mul, mul_assoc])
    (fun u v w => by
      simp only [lieBilin, Pi.add_apply, mul_add, sub_eq_add_neg]
      abel)
    (fun c u v => by
      simp only [lieBilin, Pi.smul_apply, smul_eq_mul, mul_add, mul_sub, mul_neg, neg_mul]
      rw [mul_left_comm (u 0) c, mul_left_comm (u 1) c, mul_left_comm (u 2) c,
        mul_left_comm (u 3) c, mul_left_comm (u 4) c])

@[simp] theorem lieBilinForm_apply (u v : Fin 5 → ℝ) :
    lieBilinForm u v = lieBilin u v :=
  rfl

/-- Orthogonal group `O(circleBilin)` of Grassmann's 4D syncyclic circle space. -/
abbrev OCircleBilin : Type :=
  circleBilin.toQuadraticMap.IsometryEquiv circleBilin.toQuadraticMap

/-- Orthogonal group `O(lieBilinForm)` of Lie's 5D oriented circle space. -/
abbrev OLieBilin : Type :=
  lieBilinForm.toQuadraticMap.IsometryEquiv lieBilinForm.toQuadraticMap

/-- Polarization equivalence over `ℝ`: for any symmetric bilinear form `B`, preserving `B` is
equivalent to preserving `B.toQuadraticMap`. -/
theorem bilin_preserves_iff_quadratic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ u v, B u v = B v u) (f : V →ₗ[ℝ] V) :
    (∀ u v, B (f u) (f v) = B u v) ↔
      (∀ v, B.toQuadraticMap (f v) = B.toQuadraticMap v) := by
  constructor
  · intro hf v
    exact hf v v
  · intro hq u v
    have hadd := hq (u + v)
    have hu := hq u
    have hv := hq v
    change B (f (u + v)) (f (u + v)) = B (u + v) (u + v) at hadd
    change B (f u) (f u) = B u u at hu
    change B (f v) (f v) = B v v at hv
    simp only [map_add, LinearMap.add_apply] at hadd
    rw [hB (f v) (f u), hB v u, hu, hv] at hadd
    have hadd' : B u u + (2 : ℝ) * B (f u) (f v) + B v v =
        B u u + (2 : ℝ) * B u v + B v v := by
      rw [add_assoc (B u u), add_assoc (B u u), ← add_assoc (B (f u) (f v)),
        ← add_assoc (B u v), ← two_mul, ← two_mul] at hadd
      simpa only [add_assoc] using hadd
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
      (add_left_cancel (add_right_cancel hadd'))

theorem circleBilin_symm (u v : Fin 4 → ℝ) : circleBilin u v = circleBilin v u := by
  simp [circleBilin_apply]; ring

theorem lieBilin_symm (u v : Fin 5 → ℝ) : lieBilin u v = lieBilin v u := by
  simp [lieBilin]; ring

theorem circleBilin_nondegenerate :
    ∀ u : Fin 4 → ℝ, (∀ v, circleBilin u v = 0) → u = 0 := by
  intro u hu
  have h0 := hu (Pi.single 3 1)
  have h1 := hu (Pi.single 1 1)
  have h2 := hu (Pi.single 2 1)
  have h3 := hu (Pi.single 0 1)
  simp [circleBilin_apply] at h0 h1 h2 h3
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3]

theorem lieBilin_nondegenerate :
    ∀ u : Fin 5 → ℝ, (∀ v, lieBilin u v = 0) → u = 0 := by
  intro u hu
  have h0 := hu (Pi.single 0 1)
  have h1 := hu (Pi.single 1 1)
  have h2 := hu (Pi.single 2 1)
  have h3 := hu (Pi.single 3 1)
  have h4 := hu (Pi.single 4 1)
  simp [lieBilin] at h0 h1 h2 h3 h4
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4]

/-- Any linear endomorphism of `Fin n → ℝ` preserving a nondegenerate bilinear form
upgrades to a `QuadraticMap.IsometryEquiv`. -/
def isometryEquivOfPreservesBilin {n : ℕ} (B : LinearMap.BilinForm ℝ (Fin n → ℝ))
    (hB_nd : ∀ u, (∀ v, B u v = 0) → u = 0)
    (f : Module.End ℝ (Fin n → ℝ)) (hf : ∀ u v, B (f u) (f v) = B u v) :
    B.toQuadraticMap.IsometryEquiv B.toQuadraticMap :=
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    apply hB_nd u
    intro v
    rw [← hf u v, hu, map_zero, LinearMap.zero_apply]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  { toLinearEquiv := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
    map_app' := fun u => hf u u }

@[simp] theorem isometryEquivOfPreservesBilin_apply {n : ℕ}
    (B : LinearMap.BilinForm ℝ (Fin n → ℝ))
    (hB_nd : ∀ u, (∀ v, B u v = 0) → u = 0)
    (f : Module.End ℝ (Fin n → ℝ)) (hf : ∀ u v, B (f u) (f v) = B u v)
    (u : Fin n → ℝ) :
    isometryEquivOfPreservesBilin B hB_nd f hf u = f u :=
  rfl

/-- Upgraded Bridge B functor landing in the bundled orthogonal group `OCircleBilin`. -/
def lieMobiusToCircleIsoHom : lieMobiusStabilizer →* OCircleBilin where
  toFun g :=
    isometryEquivOfPreservesBilin circleBilin circleBilin_nondegenerate
      (circleReduce g.1) (circleReduce_preserves_circleBilin g.2)
  map_one' := by
    apply DFunLike.ext
    intro x
    change circleReduce (1 : Module.End ℝ (Fin 5 → ℝ)) x = x
    rw [circleReduce_one]
    rfl
  map_mul' g h := by
    apply DFunLike.ext
    intro x
    change circleReduce (g.1 * h.1) x = circleReduce g.1 (circleReduce h.1 x)
    rw [circleReduce_mul g.2.2]
    rfl

theorem lieMobiusToCircleIsoHom_toLinearMap (g : lieMobiusStabilizer) :
    ((lieMobiusToCircleIsoHom g : OCircleBilin) : Module.End ℝ (Fin 4 → ℝ)) =
      lieMobiusToCircleHom g :=
  rfl

/-- Inverse lift of an endomorphism of Grassmann circle space to Lie's 5D space fixing
`lieRadialAxis`. -/
def circleToLieEnd (f : Module.End ℝ (Fin 4 → ℝ)) : Module.End ℝ (Fin 5 → ℝ) :=
  circleToLieSection ∘ₗ f ∘ₗ lieToGrassmannCircleProj +
    (LinearMap.proj 4).smulRight lieRadialAxis

@[simp] theorem circleToLieEnd_apply (f : Module.End ℝ (Fin 4 → ℝ)) (u : Fin 5 → ℝ) :
    circleToLieEnd f u =
      circleToLieSection (f (lieToGrassmannCircleProj u)) + u 4 • lieRadialAxis :=
  rfl

theorem circleToLieEnd_radialAxis (f : Module.End ℝ (Fin 4 → ℝ)) :
    circleToLieEnd f lieRadialAxis = lieRadialAxis := by
  rw [circleToLieEnd_apply, lieToGrassmannCircleProj_radialAxis, map_zero, map_zero, zero_add]
  simp [lieRadialAxis]

theorem circleToLieEnd_apply_four (f : Module.End ℝ (Fin 4 → ℝ)) (u : Fin 5 → ℝ) :
    (circleToLieEnd f u) 4 = u 4 := by
  simp [circleToLieEnd, circleToLieSection, lieRadialAxis]

theorem lieToGrassmannCircleProj_circleToLieEnd (f : Module.End ℝ (Fin 4 → ℝ)) (u : Fin 5 → ℝ) :
    lieToGrassmannCircleProj (circleToLieEnd f u) = f (lieToGrassmannCircleProj u) := by
  simp [circleToLieEnd, lieToGrassmannCircleProj_section, lieToGrassmannCircleProj_radialAxis]

theorem circleToLieEnd_isLieMobius {f : Module.End ℝ (Fin 4 → ℝ)}
    (hf : ∀ u v, circleBilin (f u) (f v) = circleBilin u v) :
    IsLieMobius (circleToLieEnd f) := by
  refine ⟨fun u v => ?_, circleToLieEnd_radialAxis f⟩
  have h2 : -2 * (lieBilin (circleToLieEnd f u) (circleToLieEnd f v) +
      (circleToLieEnd f u) 4 * (circleToLieEnd f v) 4) =
      -2 * (lieBilin u v + u 4 * v 4) := by
    rw [← circleBilin_lieToGrassmannProj, ← circleBilin_lieToGrassmannProj,
      lieToGrassmannCircleProj_circleToLieEnd, lieToGrassmannCircleProj_circleToLieEnd, hf]
  rw [circleToLieEnd_apply_four, circleToLieEnd_apply_four] at h2
  exact add_right_cancel (mul_left_cancel₀ (by norm_num : (-2 : ℝ) ≠ 0) h2)

theorem circleToLieEnd_one : circleToLieEnd 1 = 1 := by
  apply LinearMap.ext
  intro u
  rw [circleToLieEnd_apply, Module.End.one_apply, Module.End.one_apply,
    section_lieToGrassmannCircleProj, sub_add_cancel]

theorem circleToLieEnd_mul (f g : Module.End ℝ (Fin 4 → ℝ)) :
    circleToLieEnd (f * g) = circleToLieEnd f * circleToLieEnd g := by
  apply LinearMap.ext
  intro u
  rw [circleToLieEnd_apply, Module.End.mul_apply, Module.End.mul_apply, circleToLieEnd_apply,
    lieToGrassmannCircleProj_circleToLieEnd, circleToLieEnd_apply_four]

/-- Group homomorphism lifting `O(circleBilin)` back into `lieMobiusStabilizer`. -/
def circleToLieMobiusLift : OCircleBilin →* lieMobiusStabilizer where
  toFun T := ⟨circleToLieEnd (T : Module.End ℝ (Fin 4 → ℝ)),
    circleToLieEnd_isLieMobius (fun u v =>
      (bilin_preserves_iff_quadratic circleBilin circleBilin_symm _).mpr T.map_app u v)⟩
  map_one' := Subtype.ext circleToLieEnd_one
  map_mul' _ _ := Subtype.ext (circleToLieEnd_mul _ _)

theorem lieMobiusToCircleIsoHom_comp_lift :
    lieMobiusToCircleIsoHom.comp circleToLieMobiusLift = MonoidHom.id OCircleBilin := by
  apply MonoidHom.ext
  intro T
  apply DFunLike.ext
  intro x
  change lieToGrassmannCircleProj (circleToLieEnd (T : Module.End ℝ (Fin 4 → ℝ))
    (circleToLieSection x)) = T x
  rw [lieToGrassmannCircleProj_circleToLieEnd, lieToGrassmannCircleProj_section]
  rfl

theorem lift_comp_lieMobiusToCircleIsoHom :
    circleToLieMobiusLift.comp lieMobiusToCircleIsoHom = MonoidHom.id lieMobiusStabilizer := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  change circleToLieSection (circleReduce g.1 (lieToGrassmannCircleProj u)) +
    u 4 • lieRadialAxis = g.1 u
  rw [← circleReduce_naturality g.2.2 u, section_lieToGrassmannCircleProj, g.2.apply_four,
    sub_add_cancel]

/-- Canonical group isomorphism `lieMobiusStabilizer ≃* O(circleBilin)`, proving surjectivity of
`lieMobiusToCircleHom` onto `O(circleBilin)` and full Klein §2 stabilizer equivalence. -/
def lieMobiusStabilizerEquivOCircle : lieMobiusStabilizer ≃* OCircleBilin where
  toFun := lieMobiusToCircleIsoHom
  invFun := circleToLieMobiusLift
  left_inv g := congrArg (fun φ => φ g) lift_comp_lieMobiusToCircleIsoHom
  right_inv T := congrArg (fun φ => φ T) lieMobiusToCircleIsoHom_comp_lift
  map_mul' := lieMobiusToCircleIsoHom.map_mul

/-- Every element of the `Submonoid` `lieMobiusStabilizer` is invertible in
`Module.End ℝ (Fin 5 → ℝ)`. -/
theorem lieMobiusStabilizer_isUnit (g : lieMobiusStabilizer) : IsUnit g.1 := by
  have hinj : Function.Injective g.1 := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    apply lieBilin_nondegenerate u
    intro v
    rw [← g.2.1 u v, hu, lieBilin_symm, show lieBilin (g.1 v) 0 = 0 by simp [lieBilin]]
  have hsurj : Function.Surjective g.1 :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  let e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) := LinearEquiv.ofBijective g.1 ⟨hinj, hsurj⟩
  exact ⟨⟨g.1, e.symm.toLinearMap,
    LinearMap.ext fun u => e.apply_symm_apply u,
    LinearMap.ext fun u => e.symm_apply_apply u⟩, rfl⟩

/-- Orthogonal-group stabilizer `{g ∈ O(lieBilinForm) | g lieRadialAxis = lieRadialAxis}`. -/
def lieMobiusOrthogonalStabilizer : Subgroup OLieBilin where
  carrier := {g | g lieRadialAxis = lieRadialAxis}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by
    change g (h lieRadialAxis) = lieRadialAxis
    rw [hh, hg]
  inv_mem' {g} hg := by
    change g.symm lieRadialAxis = lieRadialAxis
    calc
      g.symm lieRadialAxis = g.symm (g lieRadialAxis) := by rw [hg]
      _ = lieRadialAxis := g.left_inv lieRadialAxis

/-- Equivalence between `lieMobiusOrthogonalStabilizer` and `lieMobiusStabilizer`. -/
def lieMobiusOrthogonalStabilizerEquivSubmonoid :
    lieMobiusOrthogonalStabilizer ≃* lieMobiusStabilizer where
  toFun g := ⟨(g.1 : Module.End ℝ (Fin 5 → ℝ)),
    ⟨fun u v => (bilin_preserves_iff_quadratic lieBilinForm lieBilin_symm _).mpr g.1.map_app u v,
     g.2⟩⟩
  invFun g := ⟨isometryEquivOfPreservesBilin lieBilinForm lieBilin_nondegenerate g.1 g.2.1, g.2.2⟩
  left_inv g := by
    apply Subtype.ext
    apply DFunLike.ext
    intro u
    rfl
  right_inv g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    rfl
  map_mul' _ _ := rfl

/-- Group isomorphism `lieMobiusOrthogonalStabilizer ≃* O(circleBilin)`. -/
def lieMobiusOrthogonalStabilizerEquivOCircle :
    lieMobiusOrthogonalStabilizer ≃* OCircleBilin :=
  lieMobiusOrthogonalStabilizerEquivSubmonoid.trans lieMobiusStabilizerEquivOCircle

/-! ### Dimension-Generic `(n+1, 1) ↔ (n+1, 2)` Lie-to-Möbius Stabilizer Isomorphism -/

/-- Orthogonal projection `Fin (n + 3) → ℝ` onto `Fin (n + 2) → ℝ`, forgetting the radius axis. -/
def lieQuadricProj (n : ℕ) : (Fin (n + 3) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun := Fin.init
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zero-radius section embedding Möbius `(n+1, 1)` space into Lie `(n+1, 2)` space. -/
def moebiusToLieSection (n : ℕ) : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 3) → ℝ) where
  toFun w := Fin.snoc w 0
  map_add' u v := by
    ext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp
    · simp [Fin.snoc_castSucc]
  map_smul' c u := by
    ext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp
    · simp [Fin.snoc_castSucc]

/-- Radial axis `e_{n+2}` in Lie's `(n+3)`-dimensional sphere space. -/
def lieQuadricRadialAxis (n : ℕ) : Fin (n + 3) → ℝ :=
  Pi.single ⟨n + 2, by omega⟩ 1

@[simp] theorem lieQuadricProj_section (n : ℕ) (w : Fin (n + 2) → ℝ) :
    lieQuadricProj n (moebiusToLieSection n w) = w := by
  ext i
  change Fin.init (Fin.snoc (α := fun _ => ℝ) w (0 : ℝ)) i = w i
  rw [Fin.init_snoc]

@[simp] theorem lieQuadricProj_radialAxis (n : ℕ) :
    lieQuadricProj n (lieQuadricRadialAxis n) = 0 := by
  ext i
  change (Pi.single (⟨n + 2, by omega⟩ : Fin (n + 3)) (1 : ℝ) : Fin (n + 3) → ℝ) i.castSucc = 0
  rw [Pi.single_eq_of_ne]
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem section_lieQuadricProj (n : ℕ) (u : Fin (n + 3) → ℝ) :
    moebiusToLieSection n (lieQuadricProj n u) =
      u - u ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n := by
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have hlast : (Fin.last (n + 2) : Fin (n + 3)) = ⟨n + 2, by omega⟩ := rfl
    change Fin.snoc (α := fun _ => ℝ) (lieQuadricProj n u) (0 : ℝ) (Fin.last (n + 2)) = _
    rw [Fin.snoc_last, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hlast]
    simp [lieQuadricRadialAxis]
  · change Fin.snoc (α := fun _ => ℝ) (lieQuadricProj n u) (0 : ℝ) i.castSucc = _
    rw [Fin.snoc_castSucc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hne : i.castSucc ≠ (⟨n + 2, by omega⟩ : Fin (n + 3)) := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have h0 : lieQuadricRadialAxis n i.castSucc = 0 := by
      simp [lieQuadricRadialAxis, hne]
    rw [h0, mul_zero, sub_zero]
    rfl

theorem lieQuadricBilin_eq_moebius_sub (n : ℕ) (u v : Fin (n + 3) → ℝ) :
    lieQuadricBilin n u v =
      moebiusQuadricBilin n (lieQuadricProj n u) (lieQuadricProj n v) -
        u ⟨n + 2, by omega⟩ * v ⟨n + 2, by omega⟩ := by
  change ((∑ i : Fin n, u (Fin.castAdd 3 i) * v (Fin.castAdd 3 i)) +
      u ⟨n, by omega⟩ * v ⟨n, by omega⟩ -
      u ⟨n + 1, by omega⟩ * v ⟨n + 1, by omega⟩ -
      u ⟨n + 2, by omega⟩ * v ⟨n + 2, by omega⟩) =
    ((∑ i : Fin n, u ((Fin.castAdd 2 i).castSucc) * v ((Fin.castAdd 2 i).castSucc)) +
      u (Fin.castSucc ⟨n, by omega⟩) * v (Fin.castSucc ⟨n, by omega⟩) -
      u (Fin.castSucc ⟨n + 1, by omega⟩) * v (Fin.castSucc ⟨n + 1, by omega⟩)) -
      u ⟨n + 2, by omega⟩ * v ⟨n + 2, by omega⟩
  rfl

theorem lieQuadricProj_lieSphereVec_zero (n : ℕ) (c : Fin n → ℝ) :
    lieQuadricProj n (lieSphereVec n c 0) = stereoQuadricVec n c := by
  ext k
  change lieSphereVec n c 0 k.castSucc = stereoQuadricVec n c k
  dsimp [lieSphereVec, stereoQuadricVec]
  by_cases hk : k.val < n
  · simp [hk]
  · by_cases hkn : k.val = n
    · simp [hkn]
    · have hk1 : k.val = n + 1 := by omega
      simp [hk1]

theorem moebiusQuadricBilin_symm (n : ℕ) (u v : Fin (n + 2) → ℝ) :
    moebiusQuadricBilin n u v = moebiusQuadricBilin n v u := by
  change (∑ i : Fin n, u (Fin.castAdd 2 i) * v (Fin.castAdd 2 i)) +
      u ⟨n, by omega⟩ * v ⟨n, by omega⟩ -
      u ⟨n + 1, by omega⟩ * v ⟨n + 1, by omega⟩ =
    (∑ i : Fin n, v (Fin.castAdd 2 i) * u (Fin.castAdd 2 i)) +
      v ⟨n, by omega⟩ * u ⟨n, by omega⟩ -
      v ⟨n + 1, by omega⟩ * u ⟨n + 1, by omega⟩
  have hsum : (∑ i : Fin n, u (Fin.castAdd 2 i) * v (Fin.castAdd 2 i)) =
      ∑ i : Fin n, v (Fin.castAdd 2 i) * u (Fin.castAdd 2 i) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsum]
  ring

theorem moebiusQuadricBilin_nondegenerate (n : ℕ) :
    ∀ u : Fin (n + 2) → ℝ, (∀ v, moebiusQuadricBilin n u v = 0) → u = 0 := by
  intro u hu
  ext k
  change u k = 0
  by_cases hk : k.val < n
  · have h := hu (Pi.single k 1)
    have hsum : (∑ i : Fin n, u (Fin.castAdd 2 i) *
        (Pi.single k (1 : ℝ) : Fin (n + 2) → ℝ) (Fin.castAdd 2 i)) = u k := by
      have hk_eq : Fin.castAdd 2 (⟨k.val, hk⟩ : Fin n) = k := Fin.ext rfl
      rw [← hk_eq]
      rw [Finset.sum_eq_single ⟨k.val, hk⟩]
      · simp
      · intro j _ hj
        have hne : Fin.castAdd 2 j ≠ Fin.castAdd 2 ⟨k.val, hk⟩ := by
          intro heq
          apply hj
          exact Fin.ext (by simpa using congrArg Fin.val heq)
        rw [Pi.single_eq_of_ne hne, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have hne_n : (⟨n, by omega⟩ : Fin (n + 2)) ≠ k := Fin.ne_of_val_ne (by dsimp; omega)
    have hne_n1 : (⟨n + 1, by omega⟩ : Fin (n + 2)) ≠ k := Fin.ne_of_val_ne (by dsimp; omega)
    have hn : (Pi.single k (1 : ℝ) : Fin (n + 2) → ℝ) ⟨n, by omega⟩ = 0 := by
      simp [hne_n]
    have hn1 : (Pi.single k (1 : ℝ) : Fin (n + 2) → ℝ) ⟨n + 1, by omega⟩ = 0 := by
      simp [hne_n1]
    change (∑ i : Fin n, u (Fin.castAdd 2 i) *
        (Pi.single k (1 : ℝ) : Fin (n + 2) → ℝ) (Fin.castAdd 2 i)) +
        u ⟨n, by omega⟩ * (Pi.single k (1 : ℝ) : Fin (n + 2) → ℝ) ⟨n, by omega⟩ -
        u ⟨n + 1, by omega⟩ * (Pi.single k (1 : ℝ) : Fin (n + 2) → ℝ) ⟨n + 1, by omega⟩ = 0 at h
    rw [hsum, hn, hn1] at h
    linarith
  · by_cases hkn : k.val = n
    · have hk_eq : k = ⟨n, by omega⟩ := Fin.ext hkn
      rw [hk_eq]
      have h := hu (Pi.single ⟨n, by omega⟩ 1)
      have hsum : (∑ i : Fin n, u (Fin.castAdd 2 i) *
          (Pi.single (⟨n, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
            (Fin.castAdd 2 i)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have hne : (Fin.castAdd 2 i : Fin (n + 2)) ≠ ⟨n, by omega⟩ :=
          Fin.ne_of_val_ne (by simp; omega)
        simp [Pi.single_eq_of_ne hne]
      have hn1 : (Pi.single (⟨n, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
          ⟨n + 1, by omega⟩ = 0 := by
        simp [Fin.ext_iff]
      change (∑ i : Fin n, u (Fin.castAdd 2 i) *
          (Pi.single (⟨n, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
            (Fin.castAdd 2 i)) +
          u ⟨n, by omega⟩ * (Pi.single (⟨n, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
            ⟨n, by omega⟩ -
          u ⟨n + 1, by omega⟩ *
            (Pi.single (⟨n, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
              ⟨n + 1, by omega⟩ = 0 at h
      rw [hsum, hn1] at h
      simpa using h
    · have hk1 : k.val = n + 1 := by omega
      have hk_eq : k = ⟨n + 1, by omega⟩ := Fin.ext hk1
      rw [hk_eq]
      have h := hu (Pi.single ⟨n + 1, by omega⟩ 1)
      have hsum : (∑ i : Fin n, u (Fin.castAdd 2 i) *
          (Pi.single (⟨n + 1, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
            (Fin.castAdd 2 i)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have hne : (Fin.castAdd 2 i : Fin (n + 2)) ≠ ⟨n + 1, by omega⟩ :=
          Fin.ne_of_val_ne (by simp; omega)
        simp [Pi.single_eq_of_ne hne]
      have hn : (Pi.single (⟨n + 1, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
          ⟨n, by omega⟩ = 0 := by
        simp [Fin.ext_iff]
      change (∑ i : Fin n, u (Fin.castAdd 2 i) *
          (Pi.single (⟨n + 1, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
            (Fin.castAdd 2 i)) +
          u ⟨n, by omega⟩ * (Pi.single (⟨n + 1, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
            ⟨n, by omega⟩ -
          u ⟨n + 1, by omega⟩ *
            (Pi.single (⟨n + 1, by omega⟩ : Fin (n + 2)) (1 : ℝ) : Fin (n + 2) → ℝ)
              ⟨n + 1, by omega⟩ = 0 at h
      rw [hsum, hn] at h
      simp at h
      exact h

theorem lieQuadricBilin_symm (n : ℕ) (u v : Fin (n + 3) → ℝ) :
    lieQuadricBilin n u v = lieQuadricBilin n v u := by
  rw [lieQuadricBilin_eq_moebius_sub, lieQuadricBilin_eq_moebius_sub,
    moebiusQuadricBilin_symm, mul_comm (u ⟨n + 2, by omega⟩)]

theorem lieQuadricBilin_nondegenerate (n : ℕ) :
    ∀ u : Fin (n + 3) → ℝ, (∀ v, lieQuadricBilin n u v = 0) → u = 0 := by
  intro u hu
  have hlast : u ⟨n + 2, by omega⟩ = 0 := by
    have h := hu (lieQuadricRadialAxis n)
    rw [lieQuadricBilin_eq_moebius_sub, lieQuadricProj_radialAxis, map_zero, zero_sub] at h
    have h1 : lieQuadricRadialAxis n ⟨n + 2, by omega⟩ = 1 := by
      simp [lieQuadricRadialAxis]
    rw [h1, mul_one, neg_eq_zero] at h
    exact h
  have hinit : lieQuadricProj n u = 0 := by
    apply moebiusQuadricBilin_nondegenerate n (lieQuadricProj n u)
    intro w
    have h := hu (moebiusToLieSection n w)
    rw [lieQuadricBilin_eq_moebius_sub, lieQuadricProj_section] at h
    have hw : moebiusToLieSection n w ⟨n + 2, by omega⟩ = 0 := by
      change Fin.snoc (α := fun _ => ℝ) w (0 : ℝ) (Fin.last (n + 2)) = 0
      simp
    rw [hw, mul_zero, sub_zero] at h
    exact h
  have hsec := section_lieQuadricProj n u
  rw [hinit, map_zero, hlast, zero_smul, sub_zero] at hsec
  exact hsec.symm

/-- Stabilizer subgroup inside `O(lieQuadricBilin n)` fixing the radial axis `e_{n+2}`. -/
def lieQuadricMobiusStabilizer (n : ℕ) :
    Subgroup ((lieQuadricBilin n).toQuadraticMap.IsometryEquiv (lieQuadricBilin n).toQuadraticMap) where
  carrier := {g | g (lieQuadricRadialAxis n) = lieQuadricRadialAxis n}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by
    change g (h (lieQuadricRadialAxis n)) = lieQuadricRadialAxis n
    rw [hh, hg]
  inv_mem' {g} hg := by
    change g.symm (lieQuadricRadialAxis n) = lieQuadricRadialAxis n
    calc
      g.symm (lieQuadricRadialAxis n) = g.symm (g (lieQuadricRadialAxis n)) := by rw [hg]
      _ = lieQuadricRadialAxis n := g.left_inv (lieQuadricRadialAxis n)

theorem lieQuadricMobiusStabilizer_apply_last {n : ℕ} (g : lieQuadricMobiusStabilizer n)
    (u : Fin (n + 3) → ℝ) :
    (g.1 u) ⟨n + 2, by omega⟩ = u ⟨n + 2, by omega⟩ := by
  have hg := (bilin_preserves_iff_quadratic (lieQuadricBilin n) (lieQuadricBilin_symm n)
    (g.1 : Module.End ℝ (Fin (n + 3) → ℝ))).mpr g.1.map_app u (lieQuadricRadialAxis n)
  change lieQuadricBilin n (g.1 u) (g.1 (lieQuadricRadialAxis n)) =
    lieQuadricBilin n u (lieQuadricRadialAxis n) at hg
  rw [g.2, lieQuadricBilin_eq_moebius_sub, lieQuadricBilin_eq_moebius_sub,
    lieQuadricProj_radialAxis, map_zero, map_zero, zero_sub, zero_sub] at hg
  have h1 : lieQuadricRadialAxis n ⟨n + 2, by omega⟩ = 1 := by simp [lieQuadricRadialAxis]
  rw [h1, mul_one, mul_one] at hg
  linarith

/-- Induced Möbius endomorphism on `Fin (n + 2) → ℝ`. -/
def moebiusReduce (n : ℕ) (g : Module.End ℝ (Fin (n + 3) → ℝ)) :
    Module.End ℝ (Fin (n + 2) → ℝ) :=
  lieQuadricProj n ∘ₗ g ∘ₗ moebiusToLieSection n

theorem moebiusReduce_naturality (n : ℕ) {g : Module.End ℝ (Fin (n + 3) → ℝ)}
    (hg : g (lieQuadricRadialAxis n) = lieQuadricRadialAxis n) (u : Fin (n + 3) → ℝ) :
    lieQuadricProj n (g u) = moebiusReduce n g (lieQuadricProj n u) := by
  simp only [moebiusReduce, LinearMap.comp_apply, section_lieQuadricProj, map_sub, map_smul, hg,
    lieQuadricProj_radialAxis, smul_zero, sub_zero]

/-- Dimension-generic Klein §2 stabilizer homomorphism `lieQuadricMobiusStabilizer n →* O(n+1, 1)`. -/
def lieQuadricMobiusToMoebiusHom (n : ℕ) :
    lieQuadricMobiusStabilizer n →*
      (moebiusQuadricBilin n).toQuadraticMap.IsometryEquiv (moebiusQuadricBilin n).toQuadraticMap where
  toFun g := isometryEquivOfPreservesBilin (moebiusQuadricBilin n)
    (moebiusQuadricBilin_nondegenerate n) (moebiusReduce n (g.1 : Module.End ℝ (Fin (n + 3) → ℝ)))
    (fun u v => by
      have hg := (bilin_preserves_iff_quadratic (lieQuadricBilin n) (lieQuadricBilin_symm n)
        (g.1 : Module.End ℝ (Fin (n + 3) → ℝ))).mpr g.1.map_app
        (moebiusToLieSection n u) (moebiusToLieSection n v)
      change lieQuadricBilin n (g.1 (moebiusToLieSection n u))
          (g.1 (moebiusToLieSection n v)) =
        lieQuadricBilin n (moebiusToLieSection n u) (moebiusToLieSection n v) at hg
      rw [lieQuadricBilin_eq_moebius_sub, lieQuadricBilin_eq_moebius_sub] at hg
      have hu4 : (g.1 (moebiusToLieSection n u)) ⟨n + 2, by omega⟩ = 0 := by
        rw [lieQuadricMobiusStabilizer_apply_last g]
        change Fin.snoc (α := fun _ => ℝ) u (0 : ℝ) (Fin.last (n + 2)) = 0
        simp
      have hv4 : (g.1 (moebiusToLieSection n v)) ⟨n + 2, by omega⟩ = 0 := by
        rw [lieQuadricMobiusStabilizer_apply_last g]
        change Fin.snoc (α := fun _ => ℝ) v (0 : ℝ) (Fin.last (n + 2)) = 0
        simp
      have hu4' : (moebiusToLieSection n u) ⟨n + 2, by omega⟩ = 0 := by
        change Fin.snoc (α := fun _ => ℝ) u (0 : ℝ) (Fin.last (n + 2)) = 0
        simp
      have hv4' : (moebiusToLieSection n v) ⟨n + 2, by omega⟩ = 0 := by
        change Fin.snoc (α := fun _ => ℝ) v (0 : ℝ) (Fin.last (n + 2)) = 0
        simp
      rw [hu4, hv4, hu4', hv4', mul_zero, sub_zero, sub_zero] at hg
      simpa [moebiusReduce, lieQuadricProj_section] using hg)
  map_one' := by
    apply DFunLike.ext
    intro w
    change lieQuadricProj n (moebiusToLieSection n w) = w
    exact lieQuadricProj_section n w
  map_mul' g h := by
    apply DFunLike.ext
    intro w
    change lieQuadricProj n (g.1 (h.1 (moebiusToLieSection n w))) =
      moebiusReduce n (g.1 : Module.End ℝ (Fin (n + 3) → ℝ))
        (lieQuadricProj n (h.1 (moebiusToLieSection n w)))
    exact moebiusReduce_naturality n g.2 _

/-- Inverse lift from `O(moebiusQuadricBilin n)` to `lieQuadricMobiusStabilizer n`. -/
def moebiusToLieQuadricEnd (n : ℕ) (f : Module.End ℝ (Fin (n + 2) → ℝ)) :
    Module.End ℝ (Fin (n + 3) → ℝ) :=
  moebiusToLieSection n ∘ₗ f ∘ₗ lieQuadricProj n +
    (LinearMap.proj ⟨n + 2, by omega⟩).smulRight (lieQuadricRadialAxis n)

@[simp] theorem moebiusToLieQuadricEnd_apply (n : ℕ) (f : Module.End ℝ (Fin (n + 2) → ℝ))
    (u : Fin (n + 3) → ℝ) :
    moebiusToLieQuadricEnd n f u =
      moebiusToLieSection n (f (lieQuadricProj n u)) +
        u ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n :=
  rfl

theorem moebiusToLieQuadricEnd_radialAxis (n : ℕ) (f : Module.End ℝ (Fin (n + 2) → ℝ)) :
    moebiusToLieQuadricEnd n f (lieQuadricRadialAxis n) = lieQuadricRadialAxis n := by
  rw [moebiusToLieQuadricEnd_apply, lieQuadricProj_radialAxis, map_zero, map_zero, zero_add]
  have h1 : lieQuadricRadialAxis n ⟨n + 2, by omega⟩ = 1 := by simp [lieQuadricRadialAxis]
  rw [h1, one_smul]

theorem moebiusToLieQuadricEnd_apply_last (n : ℕ) (f : Module.End ℝ (Fin (n + 2) → ℝ))
    (u : Fin (n + 3) → ℝ) :
    (moebiusToLieQuadricEnd n f u) ⟨n + 2, by omega⟩ = u ⟨n + 2, by omega⟩ := by
  rw [moebiusToLieQuadricEnd_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsec : (moebiusToLieSection n (f (lieQuadricProj n u))) ⟨n + 2, by omega⟩ = 0 := by
    change Fin.snoc (α := fun _ => ℝ) (f (lieQuadricProj n u)) (0 : ℝ) (Fin.last (n + 2)) = 0
    simp
  have h1 : lieQuadricRadialAxis n ⟨n + 2, by omega⟩ = 1 := by simp [lieQuadricRadialAxis]
  rw [hsec, h1, zero_add, mul_one]

theorem lieQuadricProj_moebiusToLieQuadricEnd (n : ℕ) (f : Module.End ℝ (Fin (n + 2) → ℝ))
    (u : Fin (n + 3) → ℝ) :
    lieQuadricProj n (moebiusToLieQuadricEnd n f u) = f (lieQuadricProj n u) := by
  rw [moebiusToLieQuadricEnd_apply, map_add, map_smul, lieQuadricProj_section,
    lieQuadricProj_radialAxis, smul_zero, add_zero]

/-- Group homomorphism lifting `O(moebiusQuadricBilin n)` to `lieQuadricMobiusStabilizer n`. -/
def moebiusToLieQuadricLift (n : ℕ) :
    (moebiusQuadricBilin n).toQuadraticMap.IsometryEquiv (moebiusQuadricBilin n).toQuadraticMap →*
      lieQuadricMobiusStabilizer n where
  toFun T :=
    ⟨isometryEquivOfPreservesBilin (lieQuadricBilin n) (lieQuadricBilin_nondegenerate n)
      (moebiusToLieQuadricEnd n (T : Module.End ℝ (Fin (n + 2) → ℝ)))
      (fun u v => by
        rw [lieQuadricBilin_eq_moebius_sub, lieQuadricBilin_eq_moebius_sub,
          lieQuadricProj_moebiusToLieQuadricEnd, lieQuadricProj_moebiusToLieQuadricEnd,
          moebiusToLieQuadricEnd_apply_last, moebiusToLieQuadricEnd_apply_last]
        have hT := (bilin_preserves_iff_quadratic (moebiusQuadricBilin n)
          (moebiusQuadricBilin_symm n) (T : Module.End ℝ (Fin (n + 2) → ℝ))).mpr T.map_app
        rw [hT]),
     moebiusToLieQuadricEnd_radialAxis n _⟩
  map_one' := by
    apply Subtype.ext
    apply DFunLike.ext
    intro u
    change moebiusToLieQuadricEnd n 1 u = u
    rw [moebiusToLieQuadricEnd_apply, show (1 : Module.End ℝ (Fin (n + 2) → ℝ)) (lieQuadricProj n u) =
      lieQuadricProj n u from rfl, section_lieQuadricProj, sub_add_cancel]
  map_mul' f g := by
    apply Subtype.ext
    apply DFunLike.ext
    intro u
    change moebiusToLieSection n (f (g (lieQuadricProj n u))) +
        u ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n =
      moebiusToLieSection n (f (lieQuadricProj n (moebiusToLieQuadricEnd n
        (g : Module.End ℝ (Fin (n + 2) → ℝ)) u))) +
        (moebiusToLieQuadricEnd n (g : Module.End ℝ (Fin (n + 2) → ℝ)) u)
          ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n
    rw [lieQuadricProj_moebiusToLieQuadricEnd, moebiusToLieQuadricEnd_apply_last]
    rfl

/-- Dimension-generic Lie-to-Möbius stabilizer isomorphism `lieQuadricMobiusStabilizer n ≃* O(n+1, 1)`,
specializing at `n = 2` to 4D↔5D and at `n = 3` to 5D Möbius `(4,1)` ↔ 6D hexaspherical Lie `(4,2)`. -/
def lieQuadricMobiusStabilizerEquivOMoebius (n : ℕ) :
    lieQuadricMobiusStabilizer n ≃*
      (moebiusQuadricBilin n).toQuadraticMap.IsometryEquiv (moebiusQuadricBilin n).toQuadraticMap where
  toFun := lieQuadricMobiusToMoebiusHom n
  invFun := moebiusToLieQuadricLift n
  left_inv g := by
    apply Subtype.ext
    apply DFunLike.ext
    intro u
    change moebiusToLieSection n (moebiusReduce n (g.1 : Module.End ℝ (Fin (n + 3) → ℝ))
      (lieQuadricProj n u)) + u ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n = g.1 u
    have hnat := moebiusReduce_naturality n (g := (g.1 : Module.End ℝ (Fin (n + 3) → ℝ))) g.2 u
    rw [← hnat, section_lieQuadricProj]
    change g.1 u - (g.1 u) ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n +
      u ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n = g.1 u
    rw [lieQuadricMobiusStabilizer_apply_last g, sub_add_cancel]
  right_inv T := by
    apply DFunLike.ext
    intro w
    change lieQuadricProj n (moebiusToLieQuadricEnd n (T : Module.End ℝ (Fin (n + 2) → ℝ))
      (moebiusToLieSection n w)) = T w
    rw [lieQuadricProj_moebiusToLieQuadricEnd, lieQuadricProj_section]
    rfl
  map_mul' := (lieQuadricMobiusToMoebiusHom n).map_mul

/-- At `n = 3`, `moebiusQuadricBilin 3` coincides identically with `moebiusBilin5` (`O(4,1)`). -/
theorem moebiusQuadricBilin_three_eq_moebiusBilin5 (u v : Fin 5 → ℝ) :
    moebiusQuadricBilin 3 u v = moebiusBilin5 u v := by
  change (∑ i : Fin 3, u (Fin.castAdd 2 i) * v (Fin.castAdd 2 i)) +
      u 3 * v 3 - u 4 * v 4 =
    -u 4 * v 4 + u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3
  rw [Fin.sum_univ_three]
  change u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 - u 4 * v 4 = _
  ring

/-- **5D Möbius `(4,1)` ↔ 6D Hexaspherical Lie `(4,2)` (`n = 3`)**:
`laguerreShift n t` preserves `lieQuadricBilin n` (living in `O(lieQuadricBilin n)`) but fails
to stabilize `lieQuadricRadialAxis n` whenever `t ≠ 0` (`[countermodel_found]`). -/
theorem laguerreShift_not_in_lieQuadricMobiusStabilizer (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (∀ u v, lieQuadricBilin n (laguerreShift n t u) (laguerreShift n t v) =
        lieQuadricBilin n u v) ∧
      laguerreShift n t (lieQuadricRadialAxis n) ≠ lieQuadricRadialAxis n := by
  refine ⟨fun u v => (klein_sec7_laguerre_shift_theorems n 0 t u v 0 0).2.2.1, ?_⟩
  intro h
  have hdiff : lieSphereVec n 0 1 - lieSphereVec n 0 (-1) = (2 : ℝ) • lieQuadricRadialAxis n := by
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lieQuadricRadialAxis, Pi.single_apply]
    dsimp [lieSphereVec]
    by_cases hk : k.val < n
    · have hk2 : k ≠ ⟨n + 2, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
      simp [hk, hk2]
    · by_cases hkn : k.val = n
      · have hk2 : k ≠ ⟨n + 2, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
        simp [hkn, hk2]
      · by_cases hkn1 : k.val = n + 1
        · have hk2 : k ≠ ⟨n + 2, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
          simp [hkn1, hk2]
        · have hk2 : k = ⟨n + 2, by omega⟩ := Fin.ext (by dsimp; have := k.isLt; omega)
          simp [hk2]
          ring
  have h1 := (klein_sec7_laguerre_shift_theorems n 0 t 0 0 0 1).2.2.2.1
  have hm1 := (klein_sec7_laguerre_shift_theorems n 0 t 0 0 0 (-1)).2.2.2.1
  have h2axis : (2 : ℝ) • laguerreShift n t (lieQuadricRadialAxis n) =
      lieSphereVec n 0 (1 + t) - lieSphereVec n 0 (-1 + t) := by
    rw [← map_smul, ← hdiff, map_sub, h1, hm1]
  have hn := congrFun h2axis ⟨n, by omega⟩
  rw [h, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hn
  have hR : lieQuadricRadialAxis n ⟨n, by omega⟩ = 0 := by
    simp [lieQuadricRadialAxis, Fin.ext_iff]
  have hs1 : lieSphereVec n 0 (1 + t) ⟨n, by omega⟩ = (-(1 + t) ^ 2 - 1) / 2 := by
    dsimp [lieSphereVec]
    simp
  have hsm1 : lieSphereVec n 0 (-1 + t) ⟨n, by omega⟩ = (-(-1 + t) ^ 2 - 1) / 2 := by
    dsimp [lieSphereVec]
    simp
  rw [hR, mul_zero, hs1, hsm1] at hn
  apply ht
  linarith

/-! ### Alignment Between `lieBilinForm`/`circleBilin` and `lieQuadricBilin 2`/`moebiusQuadricBilin 2` -/

/-- Coordinate permutation `u ↦ ![u 2, u 3, -u 1, u 0, u 4]` aligning `lieBilinForm` (`(-,+,+,+,-)`)
with `lieQuadricBilin 2` (`(+,+,+,-,-)`) and `lieCircleVec a b r` with `lieSphereVec 2 ![a, b] r`. -/
def lieToLieQuadric2LinearEquiv : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun u := ![u 2, u 3, -u 1, u 0, u 4]
  invFun w := ![w 3, -w 2, w 0, w 1, w 4]
  map_add' u v := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' c u := by ext i; fin_cases i <;> (simp; try ring)
  left_inv u := by ext i; fin_cases i <;> simp
  right_inv w := by ext i; fin_cases i <;> simp

theorem lieQuadricBilin2_lieToLieQuadric2 (u v : Fin 5 → ℝ) :
    lieQuadricBilin 2 (lieToLieQuadric2LinearEquiv u) (lieToLieQuadric2LinearEquiv v) =
      lieBilin u v := by
  change (∑ i : Fin 2, lieToLieQuadric2LinearEquiv u (Fin.castAdd 3 i) *
      lieToLieQuadric2LinearEquiv v (Fin.castAdd 3 i)) +
      lieToLieQuadric2LinearEquiv u ⟨2, by omega⟩ * lieToLieQuadric2LinearEquiv v ⟨2, by omega⟩ -
      lieToLieQuadric2LinearEquiv u ⟨3, by omega⟩ * lieToLieQuadric2LinearEquiv v ⟨3, by omega⟩ -
      lieToLieQuadric2LinearEquiv u ⟨4, by omega⟩ * lieToLieQuadric2LinearEquiv v ⟨4, by omega⟩ =
    -u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 - u 4 * v 4
  rw [Fin.sum_univ_two]
  simp [lieToLieQuadric2LinearEquiv]
  ring

/-- Exact `IsometryEquiv` identifying `lieBilinForm.toQuadraticMap` with
`(lieQuadricBilin 2).toQuadraticMap`. -/
def lieBilin_isometryEquiv_lieQuadric2 :
    lieBilinForm.toQuadraticMap.IsometryEquiv (lieQuadricBilin 2).toQuadraticMap where
  toLinearEquiv := lieToLieQuadric2LinearEquiv
  map_app' u := lieQuadricBilin2_lieToLieQuadric2 u u

theorem lieToLieQuadric2LinearEquiv_lieCircleVec (a b r : ℝ) :
    lieToLieQuadric2LinearEquiv (lieCircleVec a b r) = lieSphereVec 2 ![a, b] r := by
  ext i
  fin_cases i <;> simp [lieToLieQuadric2LinearEquiv, lieCircleVec, lieSphereVec] <;> ring

theorem lieToLieQuadric2LinearEquiv_radialAxis :
    lieToLieQuadric2LinearEquiv lieRadialAxis = lieQuadricRadialAxis 2 := by
  ext i
  fin_cases i <;> simp [lieToLieQuadric2LinearEquiv, lieRadialAxis, lieQuadricRadialAxis]

/-- Linear equivalence aligning `circleBilin` with `moebiusQuadricBilin 2` up to factor `-1 / 2`. -/
def circleToMoebius2LinearEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := ![x 1, x 2, -(x 0 - x 3) / 2, (x 0 + x 3) / 2]
  invFun y := ![y 3 - y 2, y 0, y 1, y 2 + y 3]
  map_add' u v := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' c u := by ext i; fin_cases i <;> (simp; try ring)
  left_inv u := by ext i; fin_cases i <;> (simp; try ring)
  right_inv y := by ext i; fin_cases i <;> (simp; try ring)

theorem moebiusQuadricBilin2_circleToMoebius2 (x y : Fin 4 → ℝ) :
    moebiusQuadricBilin 2 (circleToMoebius2LinearEquiv x) (circleToMoebius2LinearEquiv y) =
      -(1 / 2 : ℝ) * circleBilin x y := by
  change (∑ i : Fin 2, circleToMoebius2LinearEquiv x (Fin.castAdd 2 i) *
      circleToMoebius2LinearEquiv y (Fin.castAdd 2 i)) +
      circleToMoebius2LinearEquiv x ⟨2, by omega⟩ * circleToMoebius2LinearEquiv y ⟨2, by omega⟩ -
      circleToMoebius2LinearEquiv x ⟨3, by omega⟩ * circleToMoebius2LinearEquiv y ⟨3, by omega⟩ =
    -(1 / 2 : ℝ) * (x 0 * y 3 + x 3 * y 0 - 2 * x 1 * y 1 - 2 * x 2 * y 2)
  rw [Fin.sum_univ_two]
  simp [circleToMoebius2LinearEquiv]
  ring

/-- Group isomorphism `O(circleBilin) ≃* O(moebiusQuadricBilin 2)` induced by conjugation along
`circleToMoebius2LinearEquiv`. -/
def oCircleEquivOMoebius2 :
    OCircleBilin ≃*
      (moebiusQuadricBilin 2).toQuadraticMap.IsometryEquiv (moebiusQuadricBilin 2).toQuadraticMap where
  toFun T :=
    { toLinearEquiv := circleToMoebius2LinearEquiv.symm.trans
        (T.toLinearEquiv.trans circleToMoebius2LinearEquiv)
      map_app' := fun y => by
        change (moebiusQuadricBilin 2)
            (circleToMoebius2LinearEquiv (T (circleToMoebius2LinearEquiv.symm y)))
            (circleToMoebius2LinearEquiv (T (circleToMoebius2LinearEquiv.symm y))) =
          moebiusQuadricBilin 2 y y
        rw [moebiusQuadricBilin2_circleToMoebius2]
        have hT := T.map_app (circleToMoebius2LinearEquiv.symm y)
        change circleBilin (T (circleToMoebius2LinearEquiv.symm y))
            (T (circleToMoebius2LinearEquiv.symm y)) =
          circleBilin (circleToMoebius2LinearEquiv.symm y)
            (circleToMoebius2LinearEquiv.symm y) at hT
        rw [hT, ← moebiusQuadricBilin2_circleToMoebius2]
        simp }
  invFun S :=
    { toLinearEquiv := circleToMoebius2LinearEquiv.trans
        (S.toLinearEquiv.trans circleToMoebius2LinearEquiv.symm)
      map_app' := fun x => by
        change circleBilin
            (circleToMoebius2LinearEquiv.symm (S (circleToMoebius2LinearEquiv x)))
            (circleToMoebius2LinearEquiv.symm (S (circleToMoebius2LinearEquiv x))) =
          circleBilin x x
        have hneg : ∀ z : Fin 4 → ℝ, circleBilin (circleToMoebius2LinearEquiv.symm z)
            (circleToMoebius2LinearEquiv.symm z) = -2 * moebiusQuadricBilin 2 z z := fun z => by
          have hz := moebiusQuadricBilin2_circleToMoebius2
            (circleToMoebius2LinearEquiv.symm z) (circleToMoebius2LinearEquiv.symm z)
          simp only [LinearEquiv.apply_symm_apply] at hz
          linarith
        rw [hneg (S (circleToMoebius2LinearEquiv x))]
        have hS := S.map_app (circleToMoebius2LinearEquiv x)
        change moebiusQuadricBilin 2 (S (circleToMoebius2LinearEquiv x))
            (S (circleToMoebius2LinearEquiv x)) =
          moebiusQuadricBilin 2 (circleToMoebius2LinearEquiv x)
            (circleToMoebius2LinearEquiv x) at hS
        rw [hS, moebiusQuadricBilin2_circleToMoebius2]
        ring }
  left_inv T := by
    apply DFunLike.ext
    intro x
    change circleToMoebius2LinearEquiv.symm
      (circleToMoebius2LinearEquiv (T (circleToMoebius2LinearEquiv.symm
        (circleToMoebius2LinearEquiv x)))) = T x
    simp
  right_inv S := by
    apply DFunLike.ext
    intro y
    change circleToMoebius2LinearEquiv
      (circleToMoebius2LinearEquiv.symm (S (circleToMoebius2LinearEquiv
        (circleToMoebius2LinearEquiv.symm y)))) = S y
    simp
  map_mul' T₁ T₂ := by
    apply DFunLike.ext
    intro y
    change circleToMoebius2LinearEquiv
        ((T₁ * T₂) (circleToMoebius2LinearEquiv.symm y)) =
      circleToMoebius2LinearEquiv
        (T₁ (circleToMoebius2LinearEquiv.symm (circleToMoebius2LinearEquiv
          (T₂ (circleToMoebius2LinearEquiv.symm y)))))
    simp
    rfl

end BridgeB

/-! ## Section 2: Bridge A — `ExteriorAlgebra.map`, `PGK₅` Equivariance, and `regressive` -/

section BridgeA

section PluckerExteriorMap

variable {R : Type*} [CommRing R]

/-- Alignment of `DahmPluckerKleinCollineation.compound` and `PluckerMatrixAction.transform`. -/
theorem compound_eq_transform (A : Matrix (Fin 4) (Fin 4) R) (P : Plucker6 R) :
    InfoGeometry.Projective.DahmPluckerKleinCollineation.compound A P = transform A P := by
  apply Plucker6.ext <;>
    simp [InfoGeometry.Projective.DahmPluckerKleinCollineation.compound,
      InfoGeometry.Projective.DahmPluckerKleinCollineation.compoundRow,
      InfoGeometry.Projective.DahmPluckerKleinCollineation.minor2,
      transform, coordinates, secondCompound, coordinatePair, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

private def e4Vec (i : Fin 4) : InfoGeometry.Projective.KleinQuadric.Vec4 R :=
  ⟨if i = 0 then 1 else 0, if i = 1 then 1 else 0,
   if i = 2 then 1 else 0, if i = 3 then 1 else 0⟩

private theorem vec4ToFin4_transformPoint (A : Matrix (Fin 4) (Fin 4) R)
    (u : InfoGeometry.Projective.KleinQuadric.Vec4 R) :
    vec4ToFin4 (transformPoint A u) = Matrix.toLin' A (vec4ToFin4 u) := by
  ext i
  fin_cases i <;>
    simp [vec4ToFin4, transformPoint, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

private theorem pluckerToExterior2_add (P Q : Plucker6 R) :
    pluckerToExterior2 (Plucker6.add P Q) = pluckerToExterior2 P + pluckerToExterior2 Q := by
  simp only [pluckerToExterior2, Plucker6.add, add_smul]
  abel

private theorem pluckerToExterior2_smul (c : R) (P : Plucker6 R) :
    pluckerToExterior2 (Plucker6.scale c P) = c • pluckerToExterior2 P := by
  simp only [pluckerToExterior2, Plucker6.scale, smul_add, smul_smul]

private theorem pluckerToExterior2_basis_decomp (P : Plucker6 R) :
    P = Plucker6.add (Plucker6.scale P.p01 (Vec4.wedge (e4Vec 0) (e4Vec 1)))
      (Plucker6.add (Plucker6.scale P.p02 (Vec4.wedge (e4Vec 0) (e4Vec 2)))
        (Plucker6.add (Plucker6.scale P.p03 (Vec4.wedge (e4Vec 0) (e4Vec 3)))
          (Plucker6.add (Plucker6.scale P.p12 (Vec4.wedge (e4Vec 1) (e4Vec 2)))
            (Plucker6.add (Plucker6.scale P.p13 (Vec4.wedge (e4Vec 1) (e4Vec 3)))
              (Plucker6.scale P.p23 (Vec4.wedge (e4Vec 2) (e4Vec 3))))))) := by
  apply Plucker6.ext <;>
    simp [Plucker6.add, Plucker6.scale, Vec4.wedge, e4Vec]

theorem transform_scale (A : Matrix (Fin 4) (Fin 4) R) (c : R) (P : Plucker6 R) :
    transform A (Plucker6.scale c P) = Plucker6.scale c (transform A P) := by
  apply Plucker6.ext <;>
    simp [transform, coordinates, secondCompound, coordinatePair, Plucker6.scale,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem pluckerToExterior2_transform_wedge (A : Matrix (Fin 4) (Fin 4) R)
    (u v : InfoGeometry.Projective.KleinQuadric.Vec4 R) :
    pluckerToExterior2 (transform A (Vec4.wedge u v)) =
      ExteriorAlgebra.map (Matrix.toLin' A) (pluckerToExterior2 (Vec4.wedge u v)) := by
  rw [transform_wedge, ← ι_vec4_mul_ι_vec4, ← ι_vec4_mul_ι_vec4, map_mul,
    ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
    vec4ToFin4_transformPoint, vec4ToFin4_transformPoint]

/-- **Bridge A Core Functoriality**: `pluckerToExterior2` strictly intertwines
`PluckerMatrixAction.transform A` with `ExteriorAlgebra.map (Matrix.toLin' A)` over `[CommRing R]`. -/
theorem pluckerToExterior2_transform (A : Matrix (Fin 4) (Fin 4) R) (P : Plucker6 R) :
    pluckerToExterior2 (transform A P) =
      ExteriorAlgebra.map (Matrix.toLin' A) (pluckerToExterior2 P) := by
  conv_lhs => rw [pluckerToExterior2_basis_decomp P]
  conv_rhs => rw [pluckerToExterior2_basis_decomp P]
  simp only [transform_add, transform_scale, pluckerToExterior2_add, pluckerToExterior2_smul,
    map_add, map_smul, pluckerToExterior2_transform_wedge]

end PluckerExteriorMap

/-! ### Public `GL(4, ℝ)` and `SL(4, ℝ)` Actions and Equivariance Across `PGK₅` -/

section PGK5Equivariance

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
open InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
open InfoGeometry.Projective.ExteriorKleinOperatorAction

/-- Left `GL(4, R)` linear equivalence on `Fin 4 → R`. -/
def gl4Fin4Equiv {R : Type*} [CommRing R] (g : Matrix.GeneralLinearGroup (Fin 4) R) :
    (Fin 4 → R) ≃ₗ[R] (Fin 4 → R) where
  toFun v := g.1 *ᵥ v
  invFun v := (g⁻¹).1 *ᵥ v
  map_add' := Matrix.mulVec_add g.1
  map_smul' c v := by simp [Matrix.mulVec_smul]
  left_inv v := by
    have h : (g⁻¹).1 * g.1 = 1 := by simp
    change (g⁻¹).1 *ᵥ (g.1 *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  right_inv v := by
    have h : g.1 * (g⁻¹).1 = 1 := by simp
    change g.1 *ᵥ ((g⁻¹).1 *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- Linear equivalence between `FierzKleinFoundation.Vec4` and `Fin 4 → ℝ`. -/
def vec4EquivFin4 : InfoGeometry.Canonical.FierzKleinFoundation.Vec4 ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v i := v (finFourIndexEquiv i)
  invFun x k := x (finFourIndexEquiv.symm k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    ext k
    cases k <;> rfl
  right_inv x := by
    ext i
    fin_cases i <;> rfl

/-- Left `GL(4, ℝ)` linear equivalence on `FierzKleinFoundation.Vec4`. -/
def gl4Vec4Equiv (g : GL (Fin 4) ℝ) :
    InfoGeometry.Canonical.FierzKleinFoundation.Vec4 ≃ₗ[ℝ]
      InfoGeometry.Canonical.FierzKleinFoundation.Vec4 :=
  vec4EquivFin4.trans ((gl4Fin4Equiv g).trans vec4EquivFin4.symm)

theorem vec4EquivFin4_gl4Vec4Equiv (g : GL (Fin 4) ℝ)
    (v : InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    vec4EquivFin4 (gl4Vec4Equiv g v) = g.1 *ᵥ vec4EquivFin4 v := by
  change vec4EquivFin4 (vec4EquivFin4.symm (g.1 *ᵥ vec4EquivFin4 v)) = g.1 *ᵥ vec4EquivFin4 v
  exact vec4EquivFin4.apply_symm_apply _

theorem gl4Vec4Equiv_one :
    gl4Vec4Equiv (1 : GL (Fin 4) ℝ) = LinearEquiv.refl ℝ _ := by
  ext v k
  change (vec4EquivFin4.symm ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ vec4EquivFin4 v)) k = v k
  rw [Matrix.one_mulVec, vec4EquivFin4.symm_apply_apply]

theorem gl4Vec4Equiv_mul (g h : GL (Fin 4) ℝ)
    (v : InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    gl4Vec4Equiv (g * h) v = gl4Vec4Equiv g (gl4Vec4Equiv h v) := by
  apply vec4EquivFin4.injective
  simp only [vec4EquivFin4_gl4Vec4Equiv, Units.val_mul, Matrix.mulVec_mulVec]

/-- Public left `MulAction (GL (Fin 4) ℝ)` on `FierzKleinFoundation.Vec4`. -/
instance instMulActionGL4Vec4 :
    MulAction (GL (Fin 4) ℝ) InfoGeometry.Canonical.FierzKleinFoundation.Vec4 where
  smul g v := gl4Vec4Equiv g v
  one_smul v := by change gl4Vec4Equiv 1 v = v; rw [gl4Vec4Equiv_one]; rfl
  mul_smul g h v := gl4Vec4Equiv_mul g h v

private theorem grassmannianRowExteriorVec4_mul_transpose
    (C : Matrix (Fin 2) (Fin 4) ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 2) :
    vec4EquivFin4 (grassmannianRowExteriorVec4 (C * Aᵀ) i) =
      A *ᵥ vec4EquivFin4 (grassmannianRowExteriorVec4 C i) := by
  ext j
  simp only [vec4EquivFin4, LinearEquiv.coe_mk, Matrix.mulVec, dotProduct]
  fin_cases j <;>
    simp [grassmannianRowExteriorVec4, finFourIndexEquiv, finFourIndex,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, mul_comm]

theorem grassmannianRowExteriorVec4_mul_gl_transpose
    (g : GL (Fin 4) ℝ) (C : Matrix (Fin 2) (Fin 4) ℝ) (i : Fin 2) :
    grassmannianRowExteriorVec4 (C * g.1ᵀ) i = g • grassmannianRowExteriorVec4 C i := by
  apply vec4EquivFin4.injective
  change vec4EquivFin4 (grassmannianRowExteriorVec4 (C * g.1ᵀ) i) =
    vec4EquivFin4 (gl4Vec4Equiv g (grassmannianRowExteriorVec4 C i))
  rw [vec4EquivFin4_gl4Vec4Equiv]
  exact grassmannianRowExteriorVec4_mul_transpose C g.1 i

/-- Left `GL(4, ℝ)` action on `FullRankMatrix24` by right-multiplying by `g.1ᵀ`. -/
def smulFullRankMatrix24 (g : GL (Fin 4) ℝ) (C : FullRankMatrix24) : FullRankMatrix24 :=
  ⟨C.1 * g.1ᵀ, by
    have hrow : grassmannianRowExteriorVec4 (C.1 * g.1ᵀ) =
        fun i => gl4Vec4Equiv g (grassmannianRowExteriorVec4 C.1 i) := by
      ext i k
      exact congrFun (grassmannianRowExteriorVec4_mul_gl_transpose g C.1 i) k
    rw [hrow]
    exact C.2.map' (gl4Vec4Equiv g).toLinearMap (LinearMap.ker_eq_bot.mpr (gl4Vec4Equiv g).injective)⟩

/-- Public left `MulAction (GL (Fin 4) ℝ)` on `FullRankMatrix24Quotient`. -/
instance instMulActionGL4FullRankMatrix24Quotient :
    MulAction (GL (Fin 4) ℝ) FullRankMatrix24Quotient where
  smul g := Quotient.map (smulFullRankMatrix24 g) (by
    intro C₁ C₂ ⟨L, hL⟩
    refine ⟨L, ?_⟩
    change L.1 * (C₁.1 * g.1ᵀ) = C₂.1 * g.1ᵀ
    rw [← Matrix.mul_assoc, hL])
  one_smul q := by
    refine Quotient.inductionOn q fun C => ?_
    apply Quotient.sound
    exact ⟨1, by simp [smulFullRankMatrix24]⟩
  mul_smul g h q := by
    refine Quotient.inductionOn q fun C => ?_
    apply Quotient.sound
    exact ⟨1, by simp [smulFullRankMatrix24, Matrix.mul_assoc, Matrix.transpose_mul]⟩

/-- Public left `MulAction (GL (Fin 4) ℝ)` on `RealTwoPlane`. -/
instance instMulActionGL4RealTwoPlane :
    MulAction (GL (Fin 4) ℝ) InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient.RealTwoPlane where
  smul g P := ⟨P.1.map (gl4Vec4Equiv g).toLinearMap, by
    rw [LinearEquiv.finrank_map_eq, P.2]⟩
  one_smul P := by
    apply Subtype.ext
    change P.1.map (gl4Vec4Equiv 1).toLinearMap = P.1
    rw [gl4Vec4Equiv_one]
    exact Submodule.map_id P.1
  mul_smul g h P := by
    apply Subtype.ext
    change P.1.map (gl4Vec4Equiv (g * h)).toLinearMap =
      (P.1.map (gl4Vec4Equiv h).toLinearMap).map (gl4Vec4Equiv g).toLinearMap
    rw [← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro v
    exact gl4Vec4Equiv_mul g h v

/-- Public left `MulAction (GL (Fin 4) ℝ)` on Mathlib's `Module.Grassmannian ℝ Vec4 2`. -/
instance instMulActionGL4MathlibGrassmannian :
    MulAction (GL (Fin 4) ℝ)
      (Module.Grassmannian ℝ InfoGeometry.Canonical.FierzKleinFoundation.Vec4 2) where
  smul g G :=
    realTwoPlaneEquivMathlibGrassmannian (g • realTwoPlaneEquivMathlibGrassmannian.symm G)
  one_smul G := by
    change realTwoPlaneEquivMathlibGrassmannian ((1 : GL (Fin 4) ℝ) •
      realTwoPlaneEquivMathlibGrassmannian.symm G) = G
    rw [one_smul, realTwoPlaneEquivMathlibGrassmannian.apply_symm_apply]
  mul_smul g h G := by
    change realTwoPlaneEquivMathlibGrassmannian
        ((g * h) • realTwoPlaneEquivMathlibGrassmannian.symm G) =
      realTwoPlaneEquivMathlibGrassmannian
        (g • realTwoPlaneEquivMathlibGrassmannian.symm
          (realTwoPlaneEquivMathlibGrassmannian (h • realTwoPlaneEquivMathlibGrassmannian.symm G)))
    rw [realTwoPlaneEquivMathlibGrassmannian.symm_apply_apply, mul_smul]

theorem gl4_mathlibGrassmannian_toSubmodule (g : GL (Fin 4) ℝ)
    (G : Module.Grassmannian ℝ InfoGeometry.Canonical.FierzKleinFoundation.Vec4 2) :
    (g • G).toSubmodule = G.toSubmodule.map (gl4Vec4Equiv g).toLinearMap := by
  change ((realTwoPlaneEquivMathlibGrassmannian
      (g • realTwoPlaneEquivMathlibGrassmannian.symm G)).toSubmodule) = _
  rw [realTwoPlaneEquivMathlibGrassmannian_toSubmodule]
  rfl

/-- Public left `MulAction (GL (Fin 4) ℝ)` on `KleinLocus`. -/
instance instMulActionGL4KleinLocus : MulAction (GL (Fin 4) ℝ) KleinLocus where
  smul g p :=
    ⟨Projectivization.map (exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap)
      (exteriorPower.map_injective_field (n := 2) (gl4Vec4Equiv g).injective) p.1, by
      rcases p with ⟨q, hq⟩
      induction q using Projectivization.ind with
      | _ X hX =>
        rw [isKlein_mk_iff] at hq
        change IsKlein (Projectivization.mk ℝ
          (exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap X) _)
        rw [isKlein_mk_iff]
        change kleinForm (exteriorBivectorLinearEquiv
          (exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap X)) = 0
        rw [← bivectorAction_intertwines, kleinForm_bivectorAction,
          show kleinForm (exteriorBivectorLinearEquiv X) = 0 from hq, mul_zero]⟩
  one_smul p := by
    rcases p with ⟨q, hq⟩
    apply Subtype.ext
    induction q using Projectivization.ind with
    | _ X hX =>
      have hmap : exteriorPower.map 2 (gl4Vec4Equiv (1 : GL (Fin 4) ℝ)).toLinearMap =
          LinearMap.id := by
        rw [gl4Vec4Equiv_one]
        exact exteriorPower.map_id
      simp only [HSMul.hSMul, SMul.smul, Projectivization.map_mk]
      congr 1
      exact congrArg (fun φ : ExteriorSquare →ₗ[ℝ] ExteriorSquare => φ X) hmap
  mul_smul g h p := by
    rcases p with ⟨q, hq⟩
    apply Subtype.ext
    induction q using Projectivization.ind with
    | _ X hX =>
      have hmap : exteriorPower.map 2 (gl4Vec4Equiv (g * h)).toLinearMap =
          (exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap).comp
            (exteriorPower.map 2 (gl4Vec4Equiv h).toLinearMap) := by
        rw [← exteriorPower.map_comp]
        congr 1
        apply LinearMap.ext
        intro v
        exact gl4Vec4Equiv_mul g h v
      simp only [HSMul.hSMul, SMul.smul, Projectivization.map_mk]
      congr 1
      exact congrArg (fun φ : ExteriorSquare →ₗ[ℝ] ExteriorSquare => φ X) hmap

/-- Public left `MulAction (GL (Fin 4) ℝ)` on `ProjectivePluckerQuadricLocus`. -/
instance instMulActionGL4ProjectivePluckerQuadricLocus :
    MulAction (GL (Fin 4) ℝ) ProjectivePluckerQuadricLocus where
  smul g q :=
    ⟨Projectivization.map (bivectorAction (gl4Vec4Equiv g).toLinearMap)
      (bivectorAction_injective _ (gl4Vec4Equiv g).injective) q.1, by
      rcases q with ⟨p, hp⟩
      induction p using Projectivization.ind with
      | _ P hP =>
        rw [projectiveIsKleinFormZero_mk_iff] at hp
        change ProjectiveIsKleinFormZero
          (Projectivization.mk ℝ (bivectorAction (gl4Vec4Equiv g).toLinearMap P) _)
        rw [projectiveIsKleinFormZero_mk_iff, kleinForm_bivectorAction, hp, mul_zero]⟩
  one_smul q := by
    rcases q with ⟨p, hp⟩
    apply Subtype.ext
    induction p using Projectivization.ind with
    | _ P hP =>
      have hmap : bivectorAction (gl4Vec4Equiv (1 : GL (Fin 4) ℝ)).toLinearMap = LinearMap.id := by
        rw [gl4Vec4Equiv_one]
        exact bivectorAction_id
      simp only [HSMul.hSMul, SMul.smul, Projectivization.map_mk]
      congr 1
      exact congrArg (fun φ : Bivector4 →ₗ[ℝ] Bivector4 => φ P) hmap
  mul_smul g h q := by
    rcases q with ⟨p, hp⟩
    apply Subtype.ext
    induction p using Projectivization.ind with
    | _ P hP =>
      have hmap : bivectorAction (gl4Vec4Equiv (g * h)).toLinearMap =
          (bivectorAction (gl4Vec4Equiv g).toLinearMap).comp
            (bivectorAction (gl4Vec4Equiv h).toLinearMap) := by
        rw [← bivectorAction_comp]
        congr 1
        apply LinearMap.ext
        intro v
        exact gl4Vec4Equiv_mul g h v
      simp only [HSMul.hSMul, SMul.smul, Projectivization.map_mk]
      congr 1
      exact congrArg (fun φ : Bivector4 →ₗ[ℝ] Bivector4 => φ P) hmap

/-- Public left `MulAction (SL (Fin 4) ℝ)` on all five `PGK₅` carriers via `toGL`. -/
instance instMulActionSL4FullRankMatrix24Quotient :
    MulAction (Matrix.SpecialLinearGroup (Fin 4) ℝ) FullRankMatrix24Quotient :=
  MulAction.compHom FullRankMatrix24Quotient Matrix.SpecialLinearGroup.toGL

instance instMulActionSL4RealTwoPlane :
    MulAction (Matrix.SpecialLinearGroup (Fin 4) ℝ)
      InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient.RealTwoPlane :=
  MulAction.compHom InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient.RealTwoPlane
    Matrix.SpecialLinearGroup.toGL

instance instMulActionSL4MathlibGrassmannian :
    MulAction (Matrix.SpecialLinearGroup (Fin 4) ℝ)
      (Module.Grassmannian ℝ InfoGeometry.Canonical.FierzKleinFoundation.Vec4 2) :=
  MulAction.compHom (Module.Grassmannian ℝ InfoGeometry.Canonical.FierzKleinFoundation.Vec4 2)
    Matrix.SpecialLinearGroup.toGL

instance instMulActionSL4KleinLocus :
    MulAction (Matrix.SpecialLinearGroup (Fin 4) ℝ) KleinLocus :=
  MulAction.compHom KleinLocus Matrix.SpecialLinearGroup.toGL

instance instMulActionSL4ProjectivePluckerQuadricLocus :
    MulAction (Matrix.SpecialLinearGroup (Fin 4) ℝ) ProjectivePluckerQuadricLocus :=
  MulAction.compHom ProjectivePluckerQuadricLocus Matrix.SpecialLinearGroup.toGL

/-- `PGK₅` Pentagon Edge 1 Equivariance (`FullRankMatrix24Quotient ≃ RealTwoPlane`). -/
theorem fullRankMatrix24QuotientEquivRealTwoPlane_gl4_equivariant
    (g : GL (Fin 4) ℝ) (q : FullRankMatrix24Quotient) :
    fullRankMatrix24QuotientEquivRealTwoPlane (g • q) =
      g • fullRankMatrix24QuotientEquivRealTwoPlane q := by
  refine Quotient.inductionOn q fun C => ?_
  apply Subtype.ext
  change (grassmannianMatrixToRealTwoPlane (smulFullRankMatrix24 g C).1
      (smulFullRankMatrix24 g C).2).1 =
    ((g • grassmannianMatrixToRealTwoPlane C.1 C.2).1)
  change Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 (C.1 * g.1ᵀ))) =
    (Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C.1))).map
      (gl4Vec4Equiv g).toLinearMap
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span ℝ) (congrArg Set.range ?_)
  funext i
  exact grassmannianRowExteriorVec4_mul_gl_transpose g C.1 i

/-- `PGK₅` Pentagon Edge 2 Equivariance (`RealTwoPlane ≃ Module.Grassmannian ℝ Vec4 2`). -/
theorem realTwoPlaneEquivMathlibGrassmannian_gl4_equivariant
    (g : GL (Fin 4) ℝ)
    (P : InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient.RealTwoPlane) :
    realTwoPlaneEquivMathlibGrassmannian (g • P) =
      g • realTwoPlaneEquivMathlibGrassmannian P := by
  change realTwoPlaneEquivMathlibGrassmannian (g • P) =
    realTwoPlaneEquivMathlibGrassmannian (g • realTwoPlaneEquivMathlibGrassmannian.symm
      (realTwoPlaneEquivMathlibGrassmannian P))
  rw [realTwoPlaneEquivMathlibGrassmannian.symm_apply_apply]

/-- `PGK₅` Pentagon Edge 3 Equivariance (`RealTwoPlane ≃ KleinLocus`). -/
theorem realTwoPlaneEquivKleinLocus_gl4_equivariant
    (g : GL (Fin 4) ℝ)
    (P : InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient.RealTwoPlane) :
    realTwoPlaneEquivKleinLocus (g • P) = g • realTwoPlaneEquivKleinLocus P := by
  obtain ⟨q, rfl⟩ := fullRankMatrix24QuotientEquivRealTwoPlane.surjective P
  refine Quotient.inductionOn q ?_
  intro C
  rw [← fullRankMatrix24QuotientEquivRealTwoPlane_gl4_equivariant]
  change realTwoPlaneEquivKleinLocus
      (grassmannianMatrixToRealTwoPlane (smulFullRankMatrix24 g C).1
        (smulFullRankMatrix24 g C).2) =
    g • realTwoPlaneEquivKleinLocus (grassmannianMatrixToRealTwoPlane C.1 C.2)
  rw [grassmannianMatrixToKleinLocus_eq_rowFrame, grassmannianMatrixToKleinLocus_eq_rowFrame]
  apply Subtype.ext
  change Projectivization.mk ℝ
      (exteriorPower.ιMulti ℝ 2 (grassmannianRowsExteriorFrame (C.1 * g.1ᵀ) _).1) _ =
    Projectivization.map (exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap)
      (exteriorPower.map_injective_field (n := 2) (gl4Vec4Equiv g).injective)
      (Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 (grassmannianRowsExteriorFrame C.1 C.2).1) _)
  rw [Projectivization.map_mk]
  have hvec : (grassmannianRowsExteriorFrame (C.1 * g.1ᵀ) (smulFullRankMatrix24 g C).2).1 =
      (gl4Vec4Equiv g).toLinearMap ∘ (grassmannianRowsExteriorFrame C.1 C.2).1 := by
    funext i
    exact grassmannianRowExteriorVec4_mul_gl_transpose g C.1 i
  have hv : exteriorPower.ιMulti ℝ 2 (grassmannianRowsExteriorFrame (C.1 * g.1ᵀ)
        (smulFullRankMatrix24 g C).2).1 =
      exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap
        (exteriorPower.ιMulti ℝ 2 (grassmannianRowsExteriorFrame C.1 C.2).1) := by
    rw [hvec, exteriorPower.map_apply_ιMulti]
  simp only [hv]

/-- `PGK₅` Pentagon Edge 4 Equivariance (`KleinLocus ≃ ProjectivePluckerQuadricLocus`). -/
theorem kleinLocusEquivProjectivePluckerQuadric_gl4_equivariant
    (g : GL (Fin 4) ℝ) (p : KleinLocus) :
    kleinLocusEquivProjectivePluckerQuadric (g • p) =
      g • kleinLocusEquivProjectivePluckerQuadric p := by
  rcases p with ⟨q, hq⟩
  apply Subtype.ext
  induction q using Projectivization.ind with
  | _ X hX =>
    change Projectivization.map exteriorBivectorLinearEquiv.toLinearMap
        exteriorBivectorLinearEquiv.injective
        (Projectivization.map (exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap)
          (exteriorPower.map_injective_field (n := 2) (gl4Vec4Equiv g).injective)
          (Projectivization.mk ℝ X hX)) =
      Projectivization.map (bivectorAction (gl4Vec4Equiv g).toLinearMap)
        (bivectorAction_injective _ (gl4Vec4Equiv g).injective)
        (Projectivization.map exteriorBivectorLinearEquiv.toLinearMap
          exteriorBivectorLinearEquiv.injective
          (Projectivization.mk ℝ X hX))
    rw [Projectivization.map_mk, Projectivization.map_mk, Projectivization.map_mk,
      Projectivization.map_mk]
    have hbw : exteriorBivectorLinearEquiv.toLinearMap
          (exteriorPower.map 2 (gl4Vec4Equiv g).toLinearMap X) =
        bivectorAction (gl4Vec4Equiv g).toLinearMap
          (exteriorBivectorLinearEquiv.toLinearMap X) := by
      first
        | exact bivectorAction_intertwines (gl4Vec4Equiv g).toLinearMap X
        | exact (bivectorAction_intertwines (gl4Vec4Equiv g).toLinearMap X).symm
    simp only [hbw]

/-- `plucker6OfMatrix` equivariance under `C ↦ C * Aᵀ` matching `transform A`. -/
theorem plucker6OfMatrix_mul_transpose
    (A : Matrix (Fin 4) (Fin 4) ℝ) (C : Matrix (Fin 2) (Fin 4) ℝ) :
    InfoGeometry.Canonical.FelixKleinGeometryUnification.pluckerQuadricEquivPluckerLine ℝ
        (transform A ((InfoGeometry.Canonical.FelixKleinGeometryUnification.pluckerQuadricEquivPluckerLine ℝ).symm
          (plucker6OfMatrix C))) =
      plucker6OfMatrix (C * Aᵀ) := by
  apply InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.ext <;>
    simp [InfoGeometry.Canonical.FelixKleinGeometryUnification.pluckerQuadricEquivPluckerLine,
      plucker6OfMatrix, InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor,
      transform, coordinates, secondCompound, coordinatePair, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_six, Fin.sum_univ_four] <;>
    ring

end PGK5Equivariance

/-! ### `GL(V)` Determinant-Weighted and `SL(V)` Strict Equivariance of Grassmann's `regressive` -/

section RegressiveEquivariance

private theorem hodge_map_linearEquiv_aux {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (g : V ≃ₗ[K] V) (x : ExteriorAlgebra K V) :
    ExteriorAlgebra.map g.toLinearMap
        (InfoGeometry.Projective.ExteriorRegressive.hodge b x) =
      InfoGeometry.Projective.ExteriorRegressive.hodge (b.map g)
        (ExteriorAlgebra.map g.toLinearMap x) := by
  have hL : (ExteriorAlgebra.map g.toLinearMap).toLinearMap.comp
      (InfoGeometry.Projective.ExteriorRegressive.hodge b).toLinearMap =
      (InfoGeometry.Projective.ExteriorRegressive.hodge (b.map g)).toLinearMap.comp
        (ExteriorAlgebra.map g.toLinearMap).toLinearMap := by
    apply b.ExteriorAlgebra.ext
    intro s
    change ExteriorAlgebra.map g.toLinearMap
        (InfoGeometry.Projective.ExteriorRegressive.hodge b (b.ExteriorAlgebra s)) =
      InfoGeometry.Projective.ExteriorRegressive.hodge (b.map g)
        (ExteriorAlgebra.map g.toLinearMap (b.ExteriorAlgebra s))
    have hbasis : ∀ t : Finset (Fin n),
        ExteriorAlgebra.map g.toLinearMap (b.ExteriorAlgebra t) = (b.map g).ExteriorAlgebra t := by
      intro t
      rw [ExteriorAlgebra.basis_apply, ExteriorAlgebra.basis_apply,
        ExteriorAlgebra.map_apply_ιMulti]
      congr 1
    rw [InfoGeometry.Projective.ExteriorRegressive.hodge_basis, map_smul, hbasis sᶜ,
      hbasis s, InfoGeometry.Projective.ExteriorRegressive.hodge_basis]
  exact congrArg (fun f : ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V => f x) hL

/-- `ExteriorAlgebra.map g` conjugates `regressive b` to `regressive (b.map g)`. -/
theorem exteriorMap_regressive_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (g : V ≃ₗ[K] V) (x y : ExteriorAlgebra K V) :
    ExteriorAlgebra.map g.toLinearMap
        (InfoGeometry.Projective.ExteriorRegressive.regressive b x y) =
      InfoGeometry.Projective.ExteriorRegressive.regressive (b.map g)
        (ExteriorAlgebra.map g.toLinearMap x) (ExteriorAlgebra.map g.toLinearMap y) := by
  apply (InfoGeometry.Projective.ExteriorRegressive.hodge (b.map g)).injective
  rw [InfoGeometry.Projective.ExteriorRegressive.hodge_regressive, ← hodge_map_linearEquiv_aux,
    InfoGeometry.Projective.ExteriorRegressive.hodge_regressive, map_mul,
    hodge_map_linearEquiv_aux, hodge_map_linearEquiv_aux]

/-- **`GL(V)` Determinant-Weighted Equivariance of Grassmann's Regressive Product**:
`det g • ExteriorAlgebra.map g (regressive b x y) = regressive b (map g x) (map g y)`. -/
theorem regressive_map_linearEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (g : V ≃ₗ[K] V) (x y : ExteriorAlgebra K V) :
    LinearMap.det g.toLinearMap •
        ExteriorAlgebra.map g.toLinearMap
          (InfoGeometry.Projective.ExteriorRegressive.regressive b x y) =
      InfoGeometry.Projective.ExteriorRegressive.regressive b
        (ExteriorAlgebra.map g.toLinearMap x) (ExteriorAlgebra.map g.toLinearMap y) := by
  have hdet : b.det (b.map g) = LinearMap.det g.toLinearMap := by
    rw [← LinearMap.det_toMatrix b g.toLinearMap, Module.Basis.det_apply]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  rw [exteriorMap_regressive_basis, ← hdet, det_smul_regressive_change_basis]

/-- **`SL(V)` Strict Equivariance of Grassmann's Regressive Product**. -/
theorem regressive_map_sl {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (g : V ≃ₗ[K] V)
    (hg : LinearMap.det g.toLinearMap = 1) (x y : ExteriorAlgebra K V) :
    ExteriorAlgebra.map g.toLinearMap
        (InfoGeometry.Projective.ExteriorRegressive.regressive b x y) =
      InfoGeometry.Projective.ExteriorRegressive.regressive b
        (ExteriorAlgebra.map g.toLinearMap x) (ExteriorAlgebra.map g.toLinearMap y) := by
  simpa [hg] using regressive_map_linearEquiv b g x y

/-- Specialization of `regressive` to `GL (Fin 4) K` and `Pi.basisFun K (Fin 4)`. -/
theorem regressive_map_gl4 {K : Type*} [Field K] (g : GL (Fin 4) K)
    (x y : ExteriorAlgebra K (Fin 4 → K)) :
    g.1.det • ExteriorAlgebra.map (Matrix.toLin' g.1)
        (InfoGeometry.Projective.ExteriorRegressive.regressive (Pi.basisFun K (Fin 4)) x y) =
      InfoGeometry.Projective.ExteriorRegressive.regressive (Pi.basisFun K (Fin 4))
        (ExteriorAlgebra.map (Matrix.toLin' g.1) x)
        (ExteriorAlgebra.map (Matrix.toLin' g.1) y) := by
  let ge : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := gl4Fin4Equiv g
  have hge : ge.toLinearMap = Matrix.toLin' g.1 := by
    ext v i; rfl
  have hdet : LinearMap.det ge.toLinearMap = g.1.det := by
    rw [hge, LinearMap.det_toLin']
  simpa [hge, hdet] using regressive_map_linearEquiv (Pi.basisFun K (Fin 4)) ge x y

/-- **Grassmann Regressive Meet on `pluckerToExterior2` Equals Plücker Polar**:
`regressive (Pi.basisFun K (Fin 4)) (pluckerToExterior2 P) (pluckerToExterior2 Q) = (P.polar Q) • 1`. -/
theorem regressive_pluckerToExterior2 {K : Type*} [Field K] (P Q : Plucker6 K) :
    InfoGeometry.Projective.ExteriorRegressive.regressive (Pi.basisFun K (Fin 4))
        (pluckerToExterior2 P) (pluckerToExterior2 Q) =
      Plucker6.polar P Q • (1 : ExteriorAlgebra K (Fin 4 → K)) := by
  let b := Pi.basisFun K (Fin 4)
  apply (InfoGeometry.Projective.ExteriorRegressive.hodge b).injective
  rw [InfoGeometry.Projective.ExteriorRegressive.hodge_regressive,
    hodge_pluckerToExterior2_eq_kleinHodgeDual, hodge_pluckerToExterior2_eq_kleinHodgeDual,
    pluckerToExterior2_mul_pluckerToExterior2]
  have hpol : Plucker6.polar
      (InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer.kleinHodgeDual P)
      (InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer.kleinHodgeDual Q) =
      Plucker6.polar P Q := by
    simp [Plucker6.polar_formula,
      InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer.kleinHodgeDual]
    ring
  have hvol : extVol4 (R := K) =
      InfoGeometry.Projective.ExteriorRegressive.volume b := by
    rw [extVol4_eq_ιMulti_basisFun]
    change ExteriorAlgebra.ιMulti K 4 b = b.ExteriorAlgebra Finset.univ
    rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin 4)]
    let g := Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_fin 4))
    have hg0 : g 0 = 0 := Fin.ext (by
      have h01 : g 0 < g 1 := g.strictMono (by decide)
      have h12 : g 1 < g 2 := g.strictMono (by decide)
      have h23 : g 2 < g 3 := g.strictMono (by decide)
      have hb3 : (g 3).val < 4 := (g 3).isLt
      omega)
    have hg1 : g 1 = 1 := Fin.ext (by
      have h01 : g 0 < g 1 := g.strictMono (by decide)
      have h12 : g 1 < g 2 := g.strictMono (by decide)
      have h23 : g 2 < g 3 := g.strictMono (by decide)
      have hb3 : (g 3).val < 4 := (g 3).isLt
      omega)
    have hg2 : g 2 = 2 := Fin.ext (by
      have h01 : g 0 < g 1 := g.strictMono (by decide)
      have h12 : g 1 < g 2 := g.strictMono (by decide)
      have h23 : g 2 < g 3 := g.strictMono (by decide)
      have hb3 : (g 3).val < 4 := (g 3).isLt
      omega)
    have hg3 : g 3 = 3 := Fin.ext (by
      have h01 : g 0 < g 1 := g.strictMono (by decide)
      have h12 : g 1 < g 2 := g.strictMono (by decide)
      have h23 : g 2 < g 3 := g.strictMono (by decide)
      have hb3 : (g 3).val < 4 := (g 3).isLt
      omega)
    have hfun : (fun i : Fin 4 => b (g i)) = b := by
      funext ⟨i, hi⟩
      interval_cases i <;> simp [hg0, hg1, hg2, hg3]
    change ExteriorAlgebra.ιMulti K 4 b = ExteriorAlgebra.ιMulti K 4 (fun i => b (g i))
    rw [hfun]
  rw [hpol, hvol, map_smul, InfoGeometry.Projective.ExteriorRegressive.hodge_one]

end RegressiveEquivariance

end BridgeA

/-! ## Section 3: Bridge C — Klein Note VI Curvature Stabilizer & General/Special Dichotomy -/

section BridgeCNoteVI

section RingStabilizer

variable {R : Type*} [CommRing R]

theorem complexCongr_scale (A : Matrix (Fin 4) (Fin 4) R) (c : R) (C : Plucker6 R) :
    complexCongr A (Plucker6.scale c C) = Plucker6.scale c (complexCongr A C) := by
  apply Plucker6.ext <;>
    simp [complexCongr, complexOfMatrix, complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4,
      Plucker6.scale, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- Exact `GL(4, R)` stabilizer of a linear complex `C` under congruence `complexCongr`. -/
def complexStabilizerGL4 (R : Type*) [CommRing R] (C : Plucker6 R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) R) where
  carrier := {g | complexCongr g.1 C = C}
  one_mem' := complexCongr_one C
  mul_mem' {g h} hg hh := by
    change complexCongr (g.1 * h.1) C = C
    rw [complexCongr_mul, hg, hh]
  inv_mem' {g} hg := by
    change complexCongr (g⁻¹).1 C = C
    calc
      complexCongr (g⁻¹).1 C = complexCongr (g⁻¹).1 (complexCongr g.1 C) := by rw [hg]
      _ = complexCongr (g.1 * (g⁻¹).1) C := (complexCongr_mul g.1 (g⁻¹).1 C).symm
      _ = C := by
        have hmul : g.1 * (g⁻¹).1 = 1 := by simp
        rw [hmul, complexCongr_one]

private theorem plucker_polar_symm {R : Type*} [CommRing R] (P Q : Plucker6 R) :
    Plucker6.polar P Q = Plucker6.polar Q P := by
  simp [Plucker6.polar_formula]; ring

/-- Projective `GL(4, R)` stabilizer of a linear complex `C`: `complexCongr g.1 C = μ • C`. -/
def complexProjectiveStabilizerGL4 (R : Type*) [CommRing R] (C : Plucker6 R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) R) where
  carrier := {g | ∃ μ : Rˣ, complexCongr g.1 C = Plucker6.scale (μ : R) C}
  one_mem' := ⟨1, by
    rw [Units.val_one, complexCongr_one]
    apply Plucker6.ext <;> simp [Plucker6.scale]⟩
  mul_mem' {g h} := by
    rintro ⟨μg, hg⟩ ⟨μh, hh⟩
    refine ⟨μg * μh, ?_⟩
    change complexCongr (g.1 * h.1) C = Plucker6.scale ((μg * μh : Rˣ) : R) C
    rw [complexCongr_mul, hg, complexCongr_scale, hh]
    apply Plucker6.ext <;> simp [Plucker6.scale] <;> ring
  inv_mem' {g} := by
    rintro ⟨μ, hg⟩
    refine ⟨μ⁻¹, ?_⟩
    change complexCongr (g⁻¹).1 C = Plucker6.scale ((μ⁻¹ : Rˣ) : R) C
    have h1 : complexCongr (g⁻¹).1 (complexCongr g.1 C) = C := by
      rw [← complexCongr_mul]
      have hmul : g.1 * (g⁻¹).1 = 1 := by simp
      rw [hmul, complexCongr_one]
    rw [hg, complexCongr_scale] at h1
    have h2 := congrArg (Plucker6.scale ((μ⁻¹ : Rˣ) : R)) h1
    have hscale : Plucker6.scale ((μ⁻¹ : Rˣ) : R) (Plucker6.scale (μ : R)
        (complexCongr (g⁻¹).1 C)) = complexCongr (g⁻¹).1 C := by
      apply Plucker6.ext <;> simp [Plucker6.scale, ← mul_assoc]
    rw [hscale] at h2
    exact h2

theorem complexStabilizerGL4_le_projective (C : Plucker6 R) :
    complexStabilizerGL4 R C ≤ complexProjectiveStabilizerGL4 R C := by
  intro g hg
  refine ⟨1, ?_⟩
  change complexCongr g.1 C = C at hg
  rw [hg]
  apply Plucker6.ext <;> simp [Plucker6.scale]

theorem complexCongr_inv_eq_scale_iff (g : Matrix.GeneralLinearGroup (Fin 4) R)
    (C : Plucker6 R) (μ : Rˣ) :
    complexCongr g.1 C = Plucker6.scale (μ : R) C ↔
      complexCongr (g⁻¹).1 C = Plucker6.scale ((μ⁻¹ : Rˣ) : R) C := by
  constructor
  · intro hg
    have h1 : complexCongr (g⁻¹).1 (complexCongr g.1 C) = C := by
      rw [← complexCongr_mul]
      have hmul : g.1 * (g⁻¹).1 = 1 := by simp
      rw [hmul, complexCongr_one]
    rw [hg, complexCongr_scale] at h1
    have h2 := congrArg (Plucker6.scale ((μ⁻¹ : Rˣ) : R)) h1
    have hscale : Plucker6.scale ((μ⁻¹ : Rˣ) : R) (Plucker6.scale (μ : R)
        (complexCongr (g⁻¹).1 C)) = complexCongr (g⁻¹).1 C := by
      apply Plucker6.ext <;> simp [Plucker6.scale, ← mul_assoc]
    rwa [hscale] at h2
  · intro hg
    have h1 : complexCongr g.1 (complexCongr (g⁻¹).1 C) = C := by
      rw [← complexCongr_mul]
      have hmul : (g⁻¹).1 * g.1 = 1 := by simp
      rw [hmul, complexCongr_one]
    rw [hg, complexCongr_scale] at h1
    have h2 := congrArg (Plucker6.scale (μ : R)) h1
    have hscale : Plucker6.scale (μ : R) (Plucker6.scale ((μ⁻¹ : Rˣ) : R)
        (complexCongr g.1 C)) = complexCongr g.1 C := by
      apply Plucker6.ext <;> simp [Plucker6.scale, ← mul_assoc]
    rwa [hscale] at h2

/-- Under `complexCongr g.1 C = μ • C`, Plücker's covariant second-compound action scales `C`
by `g.1.det * μ⁻¹`. -/
theorem transform_of_complexCongr_scale (C : Plucker6 R)
    (g : Matrix.GeneralLinearGroup (Fin 4) R) (μ : Rˣ)
    (hg : complexCongr g.1 C = Plucker6.scale (μ : R) C) :
    transform g.1 C = Plucker6.scale (g.1.det * ((μ⁻¹ : Rˣ) : R)) C := by
  apply coordinates.injective
  apply polarDotMatrix_mulVec_injective
  ext i
  have hdot : ∀ v w : Fin 6 → R, (∀ x : Fin 6 → R, x ⬝ᵥ v = x ⬝ᵥ w) → v = w := by
    intro v w hvw
    ext k
    have hk := hvw (Pi.single k 1)
    simpa [dotProduct, Pi.single_apply] using hk
  refine congrFun (hdot _ _ fun x => ?_) i
  let P : Plucker6 R := coordinates.symm x
  have hPx : coordinates P = x := coordinates.apply_symm_apply x
  rw [← hPx]
  change coordinates P ⬝ᵥ (polarDotMatrix *ᵥ coordinates (transform g.1 C)) =
    coordinates P ⬝ᵥ (polarDotMatrix *ᵥ coordinates
      (Plucker6.scale (g.1.det * ((μ⁻¹ : Rˣ) : R)) C))
  rw [← polar_eq_vec_dot_mulVec, ← polar_eq_vec_dot_mulVec]
  have hinv := (complexCongr_inv_eq_scale_iff g C μ).mp hg
  have hmul : g.1 * (g⁻¹).1 = 1 := by simp
  have h2 : Plucker6.polar P (transform g.1 C) =
      g.1.det * ((μ⁻¹ : Rˣ) : R) * Plucker6.polar P C := by
    calc
      Plucker6.polar P (transform g.1 C) =
          Plucker6.polar (transform g.1 C) P := plucker_polar_symm _ _
      _ = Plucker6.polar (transform g.1 C) (transform g.1 (transform (g⁻¹).1 P)) := by
        rw [← transform_mul, hmul, transform_one]
      _ = g.1.det * Plucker6.polar C (transform (g⁻¹).1 P) := polar_transform _ _ _
      _ = g.1.det * Plucker6.polar (complexCongr (g⁻¹).1 C) P := by rw [polar_complexCongr]
      _ = g.1.det * Plucker6.polar (Plucker6.scale ((μ⁻¹ : Rˣ) : R) C) P := by rw [hinv]
      _ = g.1.det * ((μ⁻¹ : Rˣ) : R) * Plucker6.polar P C := by
        rw [plucker_polar_symm (Plucker6.scale _ C) P]
        have hsc : ∀ c : R, ∀ A B : Plucker6 R,
            Plucker6.polar A (Plucker6.scale c B) = c * Plucker6.polar A B := fun c A B => by
          simp [Plucker6.polar_formula, Plucker6.scale]; ring
        rw [hsc]
        ring
  have hsc : Plucker6.polar P (Plucker6.scale (g.1.det * ((μ⁻¹ : Rˣ) : R)) C) =
      g.1.det * ((μ⁻¹ : Rˣ) : R) * Plucker6.polar P C := by
    simp [Plucker6.polar_formula, Plucker6.scale]; ring
  rw [h2, hsc]

/-- Exact `conjugatePolar C` equivariance under `transform g.1` when `g.1.det = μ^2`. -/
theorem conjugatePolar_transform_of_complexCongr_scale (C P : Plucker6 R)
    (g : Matrix.GeneralLinearGroup (Fin 4) R) (μ : Rˣ)
    (hg : complexCongr g.1 C = Plucker6.scale (μ : R) C)
    (hdet : g.1.det = (μ : R) ^ 2) :
    conjugatePolar C (transform g.1 P) = transform g.1 (conjugatePolar C P) := by
  have hpol : C.polar (transform g.1 P) = (μ : R) * C.polar P := by
    rw [← polar_complexCongr, hg]
    simp [Plucker6.polar_formula, Plucker6.scale]
    ring
  have hC : transform g.1 C = Plucker6.scale (μ : R) C := by
    rw [transform_of_complexCongr_scale C g μ hg, hdet]
    have hcalc : (μ : R) ^ 2 * ((μ⁻¹ : Rˣ) : R) = (μ : R) := by
      rw [sq, mul_assoc, Units.mul_inv, mul_one]
    rw [hcalc]
  rw [conjugatePolar_eq, conjugatePolar_eq, transform_add, transform_scale, transform_scale,
    hpol, hC]
  apply Plucker6.ext <;> simp [Plucker6.add, Plucker6.scale] <;> ring

/-- `cayleyKleinChord (complexForm C)` covariance under `complexProjectiveStabilizerGL4 R C`
(exact invariance for `complexStabilizerGL4 R C`). -/
theorem cayleyKleinChord_complexForm_of_complexCongr_scale (C : Plucker6 R)
    (g : Matrix.GeneralLinearGroup (Fin 4) R) (μ : Rˣ)
    (hg : complexCongr g.1 C = Plucker6.scale (μ : R) C) (x y : Fin 4 → R) :
    cayleyKleinChord (complexForm C) (g.1 *ᵥ x) (g.1 *ᵥ y) =
      (μ : R) ^ 2 * cayleyKleinChord (complexForm C) x y := by
  have hxx : complexForm C (g.1 *ᵥ x) (g.1 *ᵥ x) = 0 :=
    complexForm_isAlt C (g.1 *ᵥ x)
  have hyy : complexForm C (g.1 *ᵥ y) (g.1 *ᵥ y) = 0 :=
    complexForm_isAlt C (g.1 *ᵥ y)
  have hx0 : complexForm C x x = 0 := complexForm_isAlt C x
  have hy0 : complexForm C y y = 0 := complexForm_isAlt C y
  have hxy : complexForm C (g.1 *ᵥ x) (g.1 *ᵥ y) = (μ : R) * complexForm C x y := by
    rw [← complexForm_complexCongr, hg, complexForm_scale, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul]
  simp only [cayleyKleinChord, hxx, hyy, hx0, hy0, hxy, mul_zero, zero_sub, mul_pow, mul_neg]

/-- Polar incidence bilinear form `polarDotMatrix.toBilin'` on `Fin 6 → R`. -/
def polarBilin (R : Type*) [CommRing R] : LinearMap.BilinForm R (Fin 6 → R) :=
  (polarDotMatrix : Matrix (Fin 6) (Fin 6) R).toBilin'

/-- `cayleyKleinChord (polarBilin R)` covariance under `transform A`. -/
theorem cayleyKleinChord_polarBilin_transform (A : Matrix (Fin 4) (Fin 4) R)
    (P Q : Plucker6 R) :
    cayleyKleinChord (polarBilin R) (coordinates (transform A P)) (coordinates (transform A Q)) =
      A.det ^ 2 * cayleyKleinChord (polarBilin R) (coordinates P) (coordinates Q) := by
  have hval : ∀ U V : Plucker6 R,
      polarBilin R (coordinates U) (coordinates V) = Plucker6.polar U V := fun U V => by
    rw [polar_eq_vec_dot_mulVec]
    simp [polarBilin, Matrix.toBilin'_apply']
  simp only [cayleyKleinChord, hval, polar_transform]
  ring

end RingStabilizer

section GeneralVsSpecialDichotomy

/-- For a general complex (`kleinQ C ≠ 0`), `complexStabilizerGL4 K C ≤ SL(4, K)` (`det = 1`). -/
theorem general_complexStabilizer_det_eq_one {K : Type*} [Field K] {C : Plucker6 K}
    (hC : Plucker6.kleinQ C ≠ 0) {g : Matrix.GeneralLinearGroup (Fin 4) K}
    (hg : g ∈ complexStabilizerGL4 K C) : g.1.det = 1 := by
  have hq := kleinQ_complexCongr g.1 C
  change complexCongr g.1 C = C at hg
  rw [hg] at hq
  exact mul_right_cancel₀ hC (by simpa [one_mul] using hq.symm)

/-- For a general complex (`kleinQ C ≠ 0`), projective congruence `complexCongr g.1 C = μ • C`
forces `g.1.det = μ^2`, yielding automatic `conjugatePolar C` commutation. -/
theorem general_complexProjectiveStabilizer_det_eq_sq {K : Type*} [Field K] {C : Plucker6 K}
    (hC : Plucker6.kleinQ C ≠ 0) {g : Matrix.GeneralLinearGroup (Fin 4) K} {μ : Kˣ}
    (hg : complexCongr g.1 C = Plucker6.scale (μ : K) C) :
    g.1.det = (μ : K) ^ 2 := by
  have hq := kleinQ_complexCongr g.1 C
  have hsc : Plucker6.kleinQ (Plucker6.scale (μ : K) C) = (μ : K) ^ 2 * Plucker6.kleinQ C := by
    simp [Plucker6.kleinQ, Plucker6.scale]; ring
  rw [hg, hsc] at hq
  exact mul_right_cancel₀ hC hq.symm

/-- General linear complex (`kleinQ C ≠ 0`) has trivial Grassmann radical `ker (complexForm C) = ⊥`. -/
theorem general_complexForm_ker_bot {K : Type*} [Field K] {C : Plucker6 K}
    (hC : Plucker6.kleinQ C ≠ 0) :
    LinearMap.ker (complexForm C) = ⊥ :=
  ((complexForm_nondegenerate_iff C).mpr hC).ker_eq_bot

/-- Every projective stabilizer element of `C` fixes the Grassmann radical `ker (complexForm C)`. -/
theorem special_projectiveStabilizer_fixes_ker {K : Type*} [Field K] (C : Plucker6 K)
    {g : Matrix.GeneralLinearGroup (Fin 4) K} (hg : g ∈ complexProjectiveStabilizerGL4 K C) :
    (LinearMap.ker (complexForm C)).comap (Matrix.toLin' g.1) = LinearMap.ker (complexForm C) := by
  rcases hg with ⟨μ, hμ⟩
  have hdet : IsUnit g.1.det := (Matrix.isUnit_iff_isUnit_det g.1).mp g.isUnit
  rw [← ker_complexForm_complexCongr g.1 hdet C, hμ]
  ext x
  simp only [LinearMap.mem_ker, complexForm_scale]
  constructor
  · intro hx
    apply LinearMap.ext
    intro y
    have hy := LinearMap.congr_fun hx y
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at hy
    exact (mul_eq_zero.mp hy).resolve_left μ.ne_zero
  · intro hx
    apply LinearMap.ext
    intro y
    have hy := LinearMap.congr_fun hx y
    simp [hy]

/-- Special parabolic dichotomy countermodel (`[countermodel_found]`):
when `C₀.kleinQ = 0` (`C₀ = ⟨1, 0, 0, 0, 0, 0⟩`), `complexStabilizerGL4 ℝ C₀` contains
elements with `det ≠ 1` (`diag(2, 1, 1, 1)`), in contrast to general complexes. -/
theorem special_complexStabilizer_det_countermodel :
    let C₀ : Plucker6 ℝ := ⟨1, 0, 0, 0, 0, 0⟩
    C₀.kleinQ = 0 ∧ ∃ g ∈ complexStabilizerGL4 ℝ C₀, g.1.det ≠ 1 := by
  let C₀ : Plucker6 ℝ := ⟨1, 0, 0, 0, 0, 0⟩
  let A : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![2, 1, 1, 1]
  let Ainv : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1 / 2, 1, 1, 1]
  have hdet : A.det = 2 := by
    simp [A, Fin.prod_univ_four]
  have hmul1 : A * Ainv = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, Ainv]
  have hmul2 : Ainv * A = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, Ainv]
  let g : Matrix.GeneralLinearGroup (Fin 4) ℝ := ⟨A, Ainv, hmul1, hmul2⟩
  refine ⟨by simp [Plucker6.kleinQ], g, ?_, ?_⟩
  · change complexCongr g.1 C₀ = C₀
    apply Plucker6.ext <;>
      simp [g, A, C₀, complexCongr, complexOfMatrix, complexMatrix,
        InfoGeometry.Canonical.Pfaffian.skew4, Matrix.mul_apply, Fin.sum_univ_four]
  · change A.det ≠ 1
    rw [hdet]
    norm_num

end GeneralVsSpecialDichotomy

section NoteVIAdjoining

/-- Scoped left `GL(4, R)` action on linear complexes via `complexCongr g⁻¹.1` (avoiding collision
with covariant `transform` action on lines). -/
@[instance_reducible]
private def gl4ComplexMulAction (R : Type*) [CommRing R] :
    MulAction (Matrix.GeneralLinearGroup (Fin 4) R) (Plucker6 R) where
  smul g C := complexCongr (g⁻¹).1 C
  one_smul C := by
    change complexCongr ((1 : Matrix.GeneralLinearGroup (Fin 4) R)⁻¹).1 C = C
    rw [inv_one, Units.val_one, complexCongr_one]
  mul_smul g h C := by
    change complexCongr ((g * h)⁻¹).1 C = complexCongr (g⁻¹).1 (complexCongr (h⁻¹).1 C)
    rw [_root_.mul_inv_rev, Units.val_mul, complexCongr_mul]

@[instance_reducible]
private def gl4Vec4PairMulAction (R : Type*) [CommRing R] :
    MulAction (Matrix.GeneralLinearGroup (Fin 4) R) ((Fin 4 → R) × (Fin 4 → R)) where
  smul g p := (g.1 *ᵥ p.1, g.1 *ᵥ p.2)
  one_smul p := by
    change ((1 : Matrix (Fin 4) (Fin 4) R) *ᵥ p.1, (1 : Matrix (Fin 4) (Fin 4) R) *ᵥ p.2) = p
    simp
  mul_smul g h p := by
    change ((g * h).1 *ᵥ p.1, (g * h).1 *ᵥ p.2) =
      (g.1 *ᵥ (h.1 *ᵥ p.1), g.1 *ᵥ (h.1 *ᵥ p.2))
    simp [Matrix.mulVec_mulVec]

theorem stabilizer_gl4ComplexMulAction_eq (R : Type*) [CommRing R] (C₀ : Plucker6 R) :
    @MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 4) R) (Plucker6 R) _
        (gl4ComplexMulAction R) C₀ =
      complexStabilizerGL4 R C₀ := by
  ext g
  change complexCongr (g⁻¹).1 C₀ = C₀ ↔ complexCongr g.1 C₀ = C₀
  have hiff := complexCongr_inv_eq_scale_iff g C₀ 1
  have hsc : Plucker6.scale (1 : R) C₀ = C₀ := by
    apply Plucker6.ext <;> simp [Plucker6.scale]
  change (complexCongr g.1 C₀ = Plucker6.scale ((1 : Rˣ) : R) C₀ ↔
      complexCongr (g⁻¹).1 C₀ = Plucker6.scale (((1 : Rˣ)⁻¹ : Rˣ) : R) C₀) at hiff
  rw [Units.val_one, inv_one, Units.val_one, hsc] at hiff
  exact hiff.symm

/-- Klein §2 adjoining equivalence instantiated for Note VI line-space curvature:
studying `(Fin 4 → ℝ) × (Fin 4 → ℝ)` jointly with the `GL₄`-orbit of a linear complex `C₀`
is equivalent to studying invariants of its stabilizer `complexStabilizerGL4 ℝ C₀`. -/
def noteVI_klein_adjoining_equiv (C₀ : Plucker6 ℝ) :
    @JointOrbitInvariant (Matrix.GeneralLinearGroup (Fin 4) ℝ) (Plucker6 ℝ)
        ((Fin 4 → ℝ) × (Fin 4 → ℝ)) _ (gl4ComplexMulAction ℝ) (gl4Vec4PairMulAction ℝ) C₀ ≃
      @StabilizerInvariant (Matrix.GeneralLinearGroup (Fin 4) ℝ) (Plucker6 ℝ)
        ((Fin 4 → ℝ) × (Fin 4 → ℝ)) _ (gl4ComplexMulAction ℝ) (gl4Vec4PairMulAction ℝ) C₀ :=
  @klein_adjoining_equiv (Matrix.GeneralLinearGroup (Fin 4) ℝ) (Plucker6 ℝ)
    ((Fin 4 → ℝ) × (Fin 4 → ℝ)) _ (gl4ComplexMulAction ℝ) (gl4Vec4PairMulAction ℝ) C₀

/-- The Cayley–Klein chord vanishing predicate lifted via `noteVI_klein_adjoining_equiv` to a
joint `GL₄`-orbit invariant on `orbit C₀ × ((Fin 4 → ℝ) × (Fin 4 → ℝ))`. -/
def noteVI_chord_jointOrbitInvariant (C₀ : Plucker6 ℝ) :
    @JointOrbitInvariant (Matrix.GeneralLinearGroup (Fin 4) ℝ) (Plucker6 ℝ)
      ((Fin 4 → ℝ) × (Fin 4 → ℝ)) _ (gl4ComplexMulAction ℝ) (gl4Vec4PairMulAction ℝ) C₀ :=
  (noteVI_klein_adjoining_equiv C₀).symm
    ⟨fun p => cayleyKleinChord (complexForm C₀) p.1 p.2 = 0, by
      intro h p
      have hh : complexCongr (h : Matrix.GeneralLinearGroup (Fin 4) ℝ).1 C₀ = C₀ := by
        have hmem : (h : Matrix.GeneralLinearGroup (Fin 4) ℝ) ∈
            @MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 4) ℝ) (Plucker6 ℝ) _
              (gl4ComplexMulAction ℝ) C₀ := h.2
        have heq := stabilizer_gl4ComplexMulAction_eq ℝ C₀
        exact SetLike.ext_iff.mp heq h.1 |>.mp hmem
      have hsc : Plucker6.scale (1 : ℝ) C₀ = C₀ := by
        apply Plucker6.ext <;> simp [Plucker6.scale]
      have hch := cayleyKleinChord_complexForm_of_complexCongr_scale C₀ h.1 1
        (by rw [Units.val_one, hsc]; exact hh) p.1 p.2
      change cayleyKleinChord (complexForm C₀) (h.1.1 *ᵥ p.1) (h.1.1 *ᵥ p.2) = 0 ↔
        cayleyKleinChord (complexForm C₀) p.1 p.2 = 0
      rw [hch, Units.val_one, one_pow, one_mul]⟩

end NoteVIAdjoining

end BridgeCNoteVI

/-! ## Section 4: Bridge C — Klein §9 Contact 1-Form ↔ R1 Exterior Calculus & Maurer–Cartan Tower -/

section BridgeCKlein9ContactR1

open InfoGeometry.Continuous.DeRhamBridge
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open scoped Manifold

/-- Linear equivalence `ContactJetSpace n ℝ ≃ₗ[ℝ] (Fin (2 * n + 1) → ℝ)`. -/
def contactJetFinEquiv (n : ℕ) : ContactJetSpace n ℝ ≃ₗ[ℝ] (Fin (2 * n + 1) → ℝ) where
  toFun w k :=
    if hk : k.val < n then w.1 ⟨k.val, hk⟩
    else if hkn : k.val = n then w.2.1
    else w.2.2 ⟨k.val - (n + 1), by have := k.isLt; omega⟩
  invFun y :=
    (fun i => y ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by omega)⟩,
     y ⟨n, by omega⟩,
     fun i => y ⟨n + 1 + i.val, by have := i.isLt; omega⟩)
  map_add' u v := by
    ext k
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
    split_ifs <;> rfl
  map_smul' c u := by
    ext k
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> rfl
  left_inv w := by
    rcases w with ⟨x, z, p⟩
    ext i
    · have hlt : (⟨i.val, Nat.lt_of_lt_of_le i.isLt (by omega)⟩ : Fin (2 * n + 1)).val < n :=
        i.isLt
      simp [hlt]
    · have h1 : ¬(⟨n, by omega⟩ : Fin (2 * n + 1)).val < n := Nat.lt_irrefl n
      simp
    · have h1 : ¬(⟨n + 1 + i.val, by have := i.isLt; omega⟩ : Fin (2 * n + 1)).val < n := by
        dsimp; omega
      have h2 : (⟨n + 1 + i.val, by have := i.isLt; omega⟩ : Fin (2 * n + 1)).val ≠ n := by
        dsimp; omega
      simp [h1, h2]
  right_inv y := by
    ext k
    by_cases hk : k.val < n
    · simp [hk]
    · by_cases hkn : k.val = n
      · simp [hkn]
        congr 1; exact Fin.ext hkn.symm
      · have hgt : n + 1 ≤ k.val := by omega
        simp [hk, hkn]
        congr 1; exact Fin.ext (by dsimp; omega)

/-- Continuous linear equivalence between Klein §9's `ContactJetSpace n ℝ` and R1's
`Chart (Fin (2 * n + 1))`. -/
def contactChartEquiv (n : ℕ) : ContactJetSpace n ℝ ≃L[ℝ] Chart (Fin (2 * n + 1)) :=
  (contactJetFinEquiv n).toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin (2 * n + 1)) ℝ).symm

@[simp] theorem contactChartEquiv_symm_fst (n : ℕ) (y : Chart (Fin (2 * n + 1))) (i : Fin n) :
    ((contactChartEquiv n).symm y).1 i = y ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by omega)⟩ :=
  rfl

@[simp] theorem contactChartEquiv_symm_snd_fst (n : ℕ) (y : Chart (Fin (2 * n + 1))) :
    ((contactChartEquiv n).symm y).2.1 = y ⟨n, by omega⟩ :=
  rfl

@[simp] theorem contactChartEquiv_symm_snd_snd (n : ℕ) (y : Chart (Fin (2 * n + 1))) (i : Fin n) :
    ((contactChartEquiv n).symm y).2.2 i = y ⟨n + 1 + i.val, by have := i.isLt; omega⟩ :=
  rfl

/-! ### 4.1 Real Fréchet 1-Form Lift (`OperatorFrechetForms`) -/

/-- Continuous linear functional `dw ↦ contactOneForm n w dw` at point `w`. -/
def contactPointCLM (n : ℕ) (w : ContactJetSpace n ℝ) : ContactJetSpace n ℝ →L[ℝ] ℝ :=
  { toFun := InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n w
    map_add' := fun u v => by
      simp only [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm,
        Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring
    map_smul' := fun c u => by
      simp only [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm,
        Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_sub, Finset.mul_sum]
      refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
      ring
    cont := by
      have hfun : InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n w =
          fun dw => dw.2.1 - ∑ i : Fin n, w.2.2 i * dw.1 i := rfl
      rw [hfun]
      exact (continuous_fst.comp continuous_snd).sub
        (continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_fst)) }

@[simp] theorem contactPointCLM_apply (n : ℕ) (w dw : ContactJetSpace n ℝ) :
    contactPointCLM n w dw =
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n w dw :=
  rfl

/-- `contactOneForm n` lifted as a `RealOperatorFrechetForm` of degree `1`. -/
def contactFrechetOneForm (n : ℕ) :
    RealOperatorFrechetForm (ContactJetSpace n ℝ) (ContactJetSpace n ℝ) ℝ 1 :=
  fun w => ContinuousAlternatingMap.ofSubsingleton ℝ (ContactJetSpace n ℝ) ℝ (0 : Fin 1)
    (contactPointCLM n w)

@[simp] theorem contactFrechetOneForm_apply (n : ℕ) (w : ContactJetSpace n ℝ)
    (v : Fin 1 → ContactJetSpace n ℝ) :
    contactFrechetOneForm n w v =
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n w (v 0) :=
  rfl

private def contactCoeffSlopeCLM (n : ℕ) (dw : ContactJetSpace n ℝ) :
    ContactJetSpace n ℝ →L[ℝ] ℝ :=
  { toFun := fun u => -(∑ i : Fin n, u.2.2 i * dw.1 i)
    map_add' := fun u₁ u₂ => by simp [add_mul, Finset.sum_add_distrib]; ring
    map_smul' := fun c u => by
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_neg, Finset.mul_sum]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => by ring)
    cont := by
      refine Continuous.neg (continuous_finsetSum _ fun i _ => ?_)
      exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).mul continuous_const }

private theorem contactPointCLM_hasFDerivAt (n : ℕ) (w dw : ContactJetSpace n ℝ) :
    HasFDerivAt (fun y : ContactJetSpace n ℝ =>
        InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n y dw)
      (contactCoeffSlopeCLM n dw) w := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have heq : (fun h : ContactJetSpace n ℝ =>
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n (w + h) dw -
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n w dw -
      contactCoeffSlopeCLM n dw h) = 0 := by
    funext h
    simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm,
      contactCoeffSlopeCLM, add_mul, Finset.sum_add_distrib]
  rw [heq]
  exact Asymptotics.isLittleO_zero _ _

private def contactSlopeCLM (n : ℕ) :
    ContactJetSpace n ℝ →L[ℝ] (ContactJetSpace n ℝ →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun y =>
        LinearMap.mkContinuous
          { toFun := fun dw => ∑ i : Fin n, y.2.2 i * dw.1 i
            map_add' := fun u v => by simp [mul_add, Finset.sum_add_distrib]
            map_smul' := fun c u => by
              simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring }
          (∑ i : Fin n, |y.2.2 i|)
          (fun dw => by
            calc
              ‖∑ i : Fin n, y.2.2 i * dw.1 i‖ ≤ ∑ i : Fin n, ‖y.2.2 i * dw.1 i‖ :=
                norm_sum_le _ _
              _ ≤ ∑ i : Fin n, |y.2.2 i| * ‖dw‖ := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [Real.norm_eq_abs, abs_mul]
                exact mul_le_mul_of_nonneg_left
                  ((norm_le_pi_norm dw.1 i).trans (norm_fst_le dw)) (abs_nonneg _)
              _ = (∑ i : Fin n, |y.2.2 i|) * ‖dw‖ := by rw [Finset.sum_mul])
      map_add' := fun y₁ y₂ => by
        apply ContinuousLinearMap.ext
        intro dw
        change (∑ i : Fin n, (y₁.2.2 i + y₂.2.2 i) * dw.1 i) =
          (∑ i : Fin n, y₁.2.2 i * dw.1 i) + (∑ i : Fin n, y₂.2.2 i * dw.1 i)
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        apply ContinuousLinearMap.ext
        intro dw
        change (∑ i : Fin n, (c * y.2.2 i) * dw.1 i) = c * (∑ i : Fin n, y.2.2 i * dw.1 i)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
    (n : ℝ)
    (fun y => by
      rw [ContinuousLinearMap.opNorm_le_iff (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg y))]
      intro dw
      change ‖∑ i : Fin n, y.2.2 i * dw.1 i‖ ≤ (n : ℝ) * ‖y‖ * ‖dw‖
      calc
        ‖∑ i : Fin n, y.2.2 i * dw.1 i‖ ≤ ∑ i : Fin n, ‖y.2.2 i * dw.1 i‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, ‖y‖ * ‖dw‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, abs_mul]
          have hy : |y.2.2 i| ≤ ‖y‖ :=
            (norm_le_pi_norm y.2.2 i).trans (le_trans (norm_snd_le y.2) (norm_snd_le y))
          have hdw : |dw.1 i| ≤ ‖dw‖ :=
            (norm_le_pi_norm dw.1 i).trans (norm_fst_le dw)
          exact mul_le_mul hy hdw (abs_nonneg _) (norm_nonneg y)
        _ = (n : ℝ) * ‖y‖ * ‖dw‖ := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc])

private def ofSubsingletonCLM (n : ℕ) :
    (ContactJetSpace n ℝ →L[ℝ] ℝ) →L[ℝ]
      ContinuousAlternatingMap ℝ (ContactJetSpace n ℝ) ℝ (Fin 1) :=
  LinearMap.mkContinuous
    { toFun := ContinuousAlternatingMap.ofSubsingleton ℝ (ContactJetSpace n ℝ) ℝ (0 : Fin 1)
      map_add' := fun _ _ => by ext v; rfl
      map_smul' := fun _ _ => by ext v; rfl }
    1
    (fun L => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul,
        ContinuousAlternatingMap.opNorm_le_iff (norm_nonneg L)]
      intro v
      simpa [Fin.prod_univ_one] using L.le_opNorm (v 0))

theorem contactFrechetOneForm_differentiableAt (n : ℕ) (w : ContactJetSpace n ℝ) :
    DifferentiableAt ℝ (contactFrechetOneForm n) w := by
  have hmap : (fun y : ContactJetSpace n ℝ => contactPointCLM n y) =
      fun y => contactPointCLM n 0 - contactSlopeCLM n y := by
    funext y
    apply ContinuousLinearMap.ext
    intro dw
    change (dw.2.1 - ∑ i : Fin n, y.2.2 i * dw.1 i) =
      (dw.2.1 - ∑ i : Fin n, (0 : Fin n → ℝ) i * dw.1 i) - (∑ i : Fin n, y.2.2 i * dw.1 i)
    simp
  have h1 : DifferentiableAt ℝ (fun y : ContactJetSpace n ℝ => contactPointCLM n y) w := by
    rw [hmap]
    exact (differentiableAt_const _).sub (contactSlopeCLM n).differentiableAt
  exact (ofSubsingletonCLM n).differentiableAt.comp w h1

/-- **Fréchet Exterior Derivative of Klein's Contact 1-Form (`dθ = ∑ dxᵢ ∧ dpᵢ = - ∑ dpᵢ ∧ dxᵢ`)**. -/
theorem frechetExtDerivK_contactFrechetOneForm (n : ℕ) (w u v : ContactJetSpace n ℝ) :
    frechetExtDerivK (contactFrechetOneForm n) w ![u, v] =
      ∑ i : Fin n, (u.1 i * v.2.2 i - v.1 i * u.2.2 i) := by
  rw [frechetExtDerivK_apply (contactFrechetOneForm_differentiableAt n w) ![u, v]]
  rw [Fin.sum_univ_two]
  have h0rem : (0 : Fin 2).removeNth ![u, v] = ![v] := by
    funext j; fin_cases j; rfl
  have h1rem : (1 : Fin 2).removeNth ![u, v] = ![u] := by
    funext j; fin_cases j; rfl
  have hf0 : fderiv ℝ (fun y => contactFrechetOneForm n y ![v]) w u =
      -(∑ i : Fin n, u.2.2 i * v.1 i) := by
    have hfun : (fun y => contactFrechetOneForm n y ![v]) =
        fun y => InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n y v :=
      rfl
    rw [hfun, (contactPointCLM_hasFDerivAt n w v).fderiv]
    rfl
  have hf1 : fderiv ℝ (fun y => contactFrechetOneForm n y ![u]) w v =
      -(∑ i : Fin n, v.2.2 i * u.1 i) := by
    have hfun : (fun y => contactFrechetOneForm n y ![u]) =
        fun y => InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n y u :=
      rfl
    rw [hfun, (contactPointCLM_hasFDerivAt n w u).fderiv]
    rfl
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, h0rem, h1rem, hf0, hf1]
  simp only [neg_neg, neg_add_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Fréchet pullback of a `RealOperatorFrechetForm` along a smooth map `Φ`. -/
def pullbackFrechetForm {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup M] [NormedSpace ℝ M] {k : ℕ}
    (Φ : E → F) (ω : RealOperatorFrechetForm F F M k) :
    RealOperatorFrechetForm E E M k :=
  fun x => (ω (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x)

theorem fderiv_legendreContact (n : ℕ) (w dw : ContactJetSpace n ℝ) :
    fderiv ℝ (InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n) w dw =
      dLegendreContact n w dw := by
  let dLegCLM : ContactJetSpace n ℝ →L[ℝ] ContactJetSpace n ℝ :=
    { toLinearMap :=
        ({ toFun := dLegendreContact n w
           map_add' := fun u v => by
             refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ (funext fun i => ?_))
             · simp [dLegendreContact]
             · simp [dLegendreContact, mul_add, add_mul, Finset.sum_add_distrib]
               ring
             · simp [dLegendreContact]
           map_smul' := fun c u => by
             refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ (funext fun i => ?_))
             · simp [dLegendreContact]
             · simp [dLegendreContact, mul_sub, Finset.mul_sum]
               exact Finset.sum_congr rfl fun i _ => by ring
             · simp [dLegendreContact] } :
          ContactJetSpace n ℝ →ₗ[ℝ] ContactJetSpace n ℝ)
      cont := by
        refine (continuous_snd.comp continuous_snd).prodMk
          (((continuous_finsetSum _ fun i _ =>
            ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).mul continuous_const |>.add
            (continuous_const.mul ((continuous_apply i).comp continuous_fst))).sub
            (continuous_fst.comp continuous_snd)).prodMk continuous_fst) }
  have hCLM : HasFDerivAt
      (InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n)
      dLegCLM w := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hdiff : ∀ h : ContactJetSpace n ℝ,
        InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n (w + h) -
          InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n w -
          dLegCLM h =
        ((0 : Fin n → ℝ), ∑ i : Fin n, h.2.2 i * h.1 i, (0 : Fin n → ℝ)) := by
      intro h
      change InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n (w + h) -
          InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n w -
          dLegendreContact n w h =
        ((0 : Fin n → ℝ), ∑ i : Fin n, h.2.2 i * h.1 i, (0 : Fin n → ℝ))
      refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ (funext fun i => ?_))
      · simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact,
          dLegendreContact]
      · simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact,
          dLegendreContact, add_mul, mul_add, Finset.sum_add_distrib]
        ring
      · simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact,
          dLegendreContact]
    have hfun : (fun h : ContactJetSpace n ℝ =>
        InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n (w + h) -
          InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n w -
          dLegCLM h) =
        fun h => ((0 : Fin n → ℝ), ∑ i : Fin n, h.2.2 i * h.1 i, (0 : Fin n → ℝ)) := funext hdiff
    rw [hfun]
    have hO : (fun h : ContactJetSpace n ℝ =>
        ((0 : Fin n → ℝ), ∑ i : Fin n, h.2.2 i * h.1 i, (0 : Fin n → ℝ))) =o[nhds 0] id := by
      have hterm : ∀ i : Fin n, (fun h : ContactJetSpace n ℝ => h.2.2 i * h.1 i) =o[nhds 0]
          id := fun i => by
        refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
        have hcont : ContinuousAt (fun h : ContactJetSpace n ℝ => h.2.2 i) 0 :=
          ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).continuousAt
        filter_upwards [hcont.tendsto (Metric.ball_mem_nhds (0 : ℝ) hc)] with h hh
        have hh2 : |h.2.2 i| < c := by simpa [Real.dist_eq] using hh
        have hh1 : |h.1 i| ≤ ‖h‖ := (norm_le_pi_norm h.1 i).trans (norm_fst_le h)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hh2.le hh1 (abs_nonneg _) hc.le
      have hsum_eq : (fun h : ContactJetSpace n ℝ => ∑ i : Fin n, h.2.2 i * h.1 i) =
          ∑ i : Fin n, (fun h : ContactJetSpace n ℝ => h.2.2 i * h.1 i) := by
        ext h; simp
      have hsum : (fun h : ContactJetSpace n ℝ => ∑ i : Fin n, h.2.2 i * h.1 i) =o[nhds 0] id := by
        rw [hsum_eq]
        exact Asymptotics.IsLittleO.sum fun i _ => hterm i
      refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
      filter_upwards [Asymptotics.isLittleO_iff.mp hsum hc] with h hh
      simpa [Prod.norm_def, max_le_iff] using hh
    exact hO
  rw [hCLM.fderiv]
  rfl

/-- Pullback of `contactFrechetOneForm n` along `legendreContact n` equals `-contactFrechetOneForm n`. -/
theorem pullbackFrechetForm_legendreContact (n : ℕ) :
    pullbackFrechetForm
        (InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n)
        (contactFrechetOneForm n) =
      -(contactFrechetOneForm n) := by
  ext w v
  simp only [pullbackFrechetForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    contactFrechetOneForm_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    Function.comp_apply, fderiv_legendreContact,
    InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm,
    InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact,
    dLegendreContact, Finset.sum_add_distrib]
  have hcancel : (∑ i : Fin n, (v 0).2.2 i * w.1 i) = ∑ i : Fin n, w.1 i * (v 0).2.2 i :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hcancel]
  ring

/-- Pullback of `contactFrechetOneForm n` along any contactomorphism `(Φ, λ)` scales by `λ`. -/
theorem pullbackFrechetForm_contactomorphism (n : ℕ)
    (Φ : ContactJetSpace n ℝ → ContactJetSpace n ℝ) (lam : ContactJetSpace n ℝ → ℝ)
    (hΦ : ∀ w dw,
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n
        (Φ w) (fderiv ℝ Φ w dw) =
        lam w *
          InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n w dw)
    (w : ContactJetSpace n ℝ) (v : Fin 1 → ContactJetSpace n ℝ) :
    pullbackFrechetForm Φ (contactFrechetOneForm n) w v =
      lam w • contactFrechetOneForm n w v := by
  simp only [pullbackFrechetForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    contactFrechetOneForm_apply, smul_eq_mul]
  exact hΦ w (v 0)

/-! ### 4.2 `ActionOperatorForm (chartDirectionalLieAction ...)` & `SmoothJetFun` `DerivationLieLane` -/

private def jetCoordAt (n : ℕ) (y₀ : Chart (Fin (2 * n + 1))) (k : Fin (2 * n + 1)) :
    DifferentiableAtSubalgebra (Fin (2 * n + 1)) y₀ :=
  ⟨fun y => y k, (EuclideanSpace.proj (𝕜 := ℝ) k).differentiableAt⟩

/-- Contact 1-form lifted into `ActionOperatorForm (chartDirectionalLieAction (Fin (2 * n + 1)) y₀) 1`. -/
def contactActionOneForm (n : ℕ) (y₀ : Chart (Fin (2 * n + 1))) :
    ActionOperatorForm (chartDirectionalLieAction (Fin (2 * n + 1)) y₀) 1 :=
  AlternatingMap.ofSubsingleton ℝ (Chart (Fin (2 * n + 1)))
    (DifferentiableAtSubalgebra (Fin (2 * n + 1)) y₀) (0 : Fin 1)
    { toFun := fun v =>
        let dv := (contactChartEquiv n).symm v
        ⟨fun y => dv.2.1 - ∑ i : Fin n, ((contactChartEquiv n).symm y).2.2 i * dv.1 i, by
          refine DifferentiableAt.sub (differentiableAt_const _) ?_
          refine DifferentiableAt.fun_sum fun i _ => ?_
          exact ((EuclideanSpace.proj (𝕜 := ℝ) (⟨n + 1 + i.val, by omega⟩ : Fin (2 * n + 1))).differentiableAt).mul_const _⟩
      map_add' := fun u v => by
        apply Subtype.ext
        funext y
        simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, Subalgebra.coe_add,
          mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c u => by
        apply Subtype.ext
        funext y
        simp only [map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, Subalgebra.coe_smul]
        rw [mul_sub, Finset.mul_sum]
        refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun i _ => by ring) }

/-- Coordinate 1-forms `dxᵢ`, `dz`, `dpᵢ` in `ActionOperatorForm (chartDirectionalLieAction ...) 1`. -/
def dxActionForm (n : ℕ) (y₀ : Chart (Fin (2 * n + 1))) (i : Fin n) :
    ActionOperatorForm (chartDirectionalLieAction (Fin (2 * n + 1)) y₀) 1 :=
  AlternatingMap.ofSubsingleton ℝ _ _ (0 : Fin 1)
    { toFun := fun v => algebraMap ℝ _ (((contactChartEquiv n).symm v).1 i)
      map_add' := fun u v => by
        let u' : Chart (Fin (2 * n + 1)) := u
        let v' : Chart (Fin (2 * n + 1)) := v
        change algebraMap ℝ _ (((contactChartEquiv n).symm (u' + v')).1 i) =
          algebraMap ℝ _ (((contactChartEquiv n).symm u').1 i) +
            algebraMap ℝ _ (((contactChartEquiv n).symm v').1 i)
        rw [map_add, Prod.fst_add, Pi.add_apply, map_add]
      map_smul' := fun c u => by
        let u' : Chart (Fin (2 * n + 1)) := u
        change algebraMap ℝ _ (((contactChartEquiv n).symm (c • u')).1 i) =
          c • algebraMap ℝ _ (((contactChartEquiv n).symm u').1 i)
        rw [map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def] }

def dpActionForm (n : ℕ) (y₀ : Chart (Fin (2 * n + 1))) (i : Fin n) :
    ActionOperatorForm (chartDirectionalLieAction (Fin (2 * n + 1)) y₀) 1 :=
  AlternatingMap.ofSubsingleton ℝ _ _ (0 : Fin 1)
    { toFun := fun v => algebraMap ℝ _ (((contactChartEquiv n).symm v).2.2 i)
      map_add' := fun u v => by
        let u' : Chart (Fin (2 * n + 1)) := u
        let v' : Chart (Fin (2 * n + 1)) := v
        change algebraMap ℝ _ (((contactChartEquiv n).symm (u' + v')).2.2 i) =
          algebraMap ℝ _ (((contactChartEquiv n).symm u').2.2 i) +
            algebraMap ℝ _ (((contactChartEquiv n).symm v').2.2 i)
        rw [map_add, Prod.snd_add, Prod.snd_add, Pi.add_apply, map_add]
      map_smul' := fun c u => by
        let u' : Chart (Fin (2 * n + 1)) := u
        change algebraMap ℝ _ (((contactChartEquiv n).symm (c • u')).2.2 i) =
          c • algebraMap ℝ _ (((contactChartEquiv n).symm u').2.2 i)
        rw [map_smul, Prod.smul_snd, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul,
          Algebra.smul_def] }

@[simp] theorem contactActionOneForm_eval (n : ℕ) (y₀ y u : Chart (Fin (2 * n + 1))) :
    ((contactActionOneForm n y₀ ![u]).1 y) =
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n
        ((contactChartEquiv n).symm y) ((contactChartEquiv n).symm u) :=
  rfl

/-- **`actionExteriorDerivative` of `contactActionOneForm` equals `∑ dxᵢ ∧ dpᵢ = - ∑ dpᵢ ∧ dxᵢ`**:
matching `-Ω` in `ErlangenProgramMobiusLieAndContact.grassmann_pfaff_contact5` at `n = 2`. -/
theorem actionExteriorDerivative_contactActionOneForm (n : ℕ) (y₀ u v : Chart (Fin (2 * n + 1))) :
    ((actionExteriorDerivative (chartDirectionalLieAction (Fin (2 * n + 1)) y₀) 1
        (contactActionOneForm n y₀) ![u, v]).1 y₀) =
      (∑ i : Fin n,
        ((actionWedge (chartDirectionalLieAction (Fin (2 * n + 1)) y₀)
          (dxActionForm n y₀ i) (dpActionForm n y₀ i) ![u, v]).1 y₀)) ∧
      ((actionExteriorDerivative (chartDirectionalLieAction (Fin (2 * n + 1)) y₀) 1
        (contactActionOneForm n y₀) ![u, v]).1 y₀) =
      -(∑ i : Fin n,
        ((actionWedge (chartDirectionalLieAction (Fin (2 * n + 1)) y₀)
          (dpActionForm n y₀ i) (dxActionForm n y₀ i) ![u, v]).1 y₀)) := by
  let K := chartDirectionalLieAction (Fin (2 * n + 1)) y₀
  let uK : K.L := u
  let vK : K.L := v
  have h01 : ![uK, vK] = Matrix.vecCons uK ![vK] := by ext i; fin_cases i <;> rfl
  have hd : actionExteriorDerivative K 1 (contactActionOneForm n y₀) ![uK, vK] =
      K.operatorAction uK (contactActionOneForm n y₀ ![vK]) -
        K.operatorAction vK (contactActionOneForm n y₀ ![uK]) := by
    rw [h01, ← AlternatingMap.curryLeft_apply_apply, actionExteriorDerivative_succ_curryLeft]
    simp only [AlternatingMap.sub_apply, lieDeriv_apply, actionExteriorDerivative_zero_apply]
    have hbr : ∀ x y : K.L, (⁅x, y⁆ : K.L) = 0 := fun _ _ => rfl
    have hzero : (∑ i : Fin 1, contactActionOneForm n y₀
        (Function.update ![vK] i ⁅uK, ![vK] i⁆)) = 0 := by
      rw [Fin.sum_univ_one, hbr]
      apply Subtype.ext
      funext y
      have hz0 : Function.update ![vK] (0 : Fin 1) (0 : K.L) 0 = (0 : K.L) :=
        Function.update_self (0 : Fin 1) (0 : K.L) ![vK]
      change ((contactChartEquiv n).symm
          (Function.update ![vK] (0 : Fin 1) (0 : K.L) 0)).2.1 -
          ∑ i : Fin n, ((contactChartEquiv n).symm y).2.2 i *
            ((contactChartEquiv n).symm
              (Function.update ![vK] (0 : Fin 1) (0 : K.L) 0)).1 i = 0
      rw [hz0]
      change ((contactChartEquiv n).symm (0 : Chart (Fin (2 * n + 1)))).2.1 -
          ∑ i : Fin n, ((contactChartEquiv n).symm y).2.2 i *
            ((contactChartEquiv n).symm (0 : Chart (Fin (2 * n + 1)))).1 i = 0
      rw [map_zero]
      simp
    have hcur : (contactActionOneForm n y₀).curryLeft uK Fin.elim0 =
        contactActionOneForm n y₀ ![uK] := by
      rw [AlternatingMap.curryLeft_apply_apply]
      congr 1
    rw [hzero, sub_zero, hcur, Matrix.cons_val_zero]
  have hact : ∀ a b : Chart (Fin (2 * n + 1)),
      (K.operatorAction a (contactActionOneForm n y₀ ![b])).1 y₀ =
        -(∑ i : Fin n, ((contactChartEquiv n).symm a).2.2 i *
          ((contactChartEquiv n).symm b).1 i) := fun a b => by
    change fderiv ℝ (fun y : Chart (Fin (2 * n + 1)) =>
        ((contactChartEquiv n).symm b).2.1 -
          ∑ i : Fin n, ((contactChartEquiv n).symm y).2.2 i *
            ((contactChartEquiv n).symm b).1 i) y₀ a = _
    have hder : HasFDerivAt (fun y : Chart (Fin (2 * n + 1)) =>
        ((contactChartEquiv n).symm b).2.1 -
          ∑ i : Fin n, ((contactChartEquiv n).symm y).2.2 i *
            ((contactChartEquiv n).symm b).1 i)
        (-∑ i : Fin n, ((contactChartEquiv n).symm b).1 i •
          (EuclideanSpace.proj (𝕜 := ℝ) (⟨n + 1 + i.val, by omega⟩ : Fin (2 * n + 1)))) y₀ := by
      have h1 : HasFDerivAt (fun _ : Chart (Fin (2 * n + 1)) =>
          ((contactChartEquiv n).symm b).2.1) (0 : Chart (Fin (2 * n + 1)) →L[ℝ] ℝ) y₀ :=
        hasFDerivAt_const (((contactChartEquiv n).symm b).2.1) y₀
      have h2 : HasFDerivAt (fun y : Chart (Fin (2 * n + 1)) =>
          ∑ i : Fin n, ((contactChartEquiv n).symm y).2.2 i *
            ((contactChartEquiv n).symm b).1 i)
          (∑ i : Fin n, ((contactChartEquiv n).symm b).1 i •
            (EuclideanSpace.proj (𝕜 := ℝ) (⟨n + 1 + i.val, by omega⟩ : Fin (2 * n + 1)))) y₀ := by
        refine HasFDerivAt.fun_sum fun i _ => ?_
        have hp := (EuclideanSpace.proj (𝕜 := ℝ)
          (⟨n + 1 + i.val, by omega⟩ : Fin (2 * n + 1))).hasFDerivAt (x := y₀)
        simpa [mul_comm] using hp.mul_const (((contactChartEquiv n).symm b).1 i)
      have hsub := h1.fun_sub h2
      rw [zero_sub] at hsub
      exact hsub
    rw [hder.fderiv]
    simp only [_root_.neg_apply, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
      EuclideanSpace.proj]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by
      change ((contactChartEquiv n).symm b).1 i * a ⟨n + 1 + i.val, by omega⟩ =
        ((contactChartEquiv n).symm a).2.2 i * ((contactChartEquiv n).symm b).1 i
      rw [mul_comm]
      rfl
  have hL : ((actionExteriorDerivative K 1 (contactActionOneForm n y₀) ![uK, vK]).1 y₀) =
      ∑ i : Fin n, (((contactChartEquiv n).symm u).1 i * ((contactChartEquiv n).symm v).2.2 i -
        ((contactChartEquiv n).symm v).1 i * ((contactChartEquiv n).symm u).2.2 i) := by
    rw [hd, Subalgebra.coe_sub, Pi.sub_apply, hact u v, hact v u]
    simp only [sub_neg_eq_add, ← Finset.sum_sub_distrib, neg_add_eq_sub]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hw1 : (∑ i : Fin n, (actionWedge K (dxActionForm n y₀ i) (dpActionForm n y₀ i) ![uK, vK]).1 y₀) =
      ∑ i : Fin n, (((contactChartEquiv n).symm u).1 i * ((contactChartEquiv n).symm v).2.2 i -
        ((contactChartEquiv n).symm v).1 i * ((contactChartEquiv n).symm u).2.2 i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [actionWedge_one_one_apply]
    rfl
  have hw2 : (∑ i : Fin n, (actionWedge K (dpActionForm n y₀ i) (dxActionForm n y₀ i) ![uK, vK]).1 y₀) =
      ∑ i : Fin n, (((contactChartEquiv n).symm u).2.2 i * ((contactChartEquiv n).symm v).1 i -
        ((contactChartEquiv n).symm v).2.2 i * ((contactChartEquiv n).symm u).1 i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [actionWedge_one_one_apply]
    rfl
  refine ⟨hL.trans hw1.symm, ?_⟩
  rw [hL, hw2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Shifted contact 1-form at `y₁` viewed in `ActionOperatorForm (chartDirectionalLieAction ... y₀) 1`
so `pullbackActionForm` shares the same algebra `DifferentiableAtSubalgebra (Fin (2 * n + 1)) y₀`. -/
def shiftedContactActionOneForm (n : ℕ) (y₀ y₁ : Chart (Fin (2 * n + 1))) :
    ActionOperatorForm (chartDirectionalLieAction (Fin (2 * n + 1)) y₀) 1 :=
  AlternatingMap.ofSubsingleton ℝ (Chart (Fin (2 * n + 1)))
    (DifferentiableAtSubalgebra (Fin (2 * n + 1)) y₀) (0 : Fin 1)
    { toFun := fun v =>
        let dv := (contactChartEquiv n).symm v
        ⟨fun y => dv.2.1 -
            ∑ i : Fin n, ((contactChartEquiv n).symm (y + (y₁ - y₀))).2.2 i * dv.1 i, by
          refine DifferentiableAt.sub (differentiableAt_const _) ?_
          refine DifferentiableAt.fun_sum fun i _ => ?_
          have hmul : (fun y : Chart (Fin (2 * n + 1)) =>
              ((contactChartEquiv n).symm (y + (y₁ - y₀))).2.2 i * dv.1 i) =
              fun y => (y ⟨n + 1 + i.val, by omega⟩ + (y₁ - y₀) ⟨n + 1 + i.val, by omega⟩) *
                dv.1 i := rfl
          rw [hmul]
          exact ((EuclideanSpace.proj (𝕜 := ℝ) (⟨n + 1 + i.val, by omega⟩ :
            Fin (2 * n + 1))).differentiableAt.add (differentiableAt_const _)).mul_const _⟩
      map_add' := fun u v => by
        apply Subtype.ext
        funext y
        simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, Subalgebra.coe_add,
          mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c u => by
        apply Subtype.ext
        funext y
        simp only [map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, Subalgebra.coe_smul]
        rw [mul_sub, Finset.mul_sum]
        refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun i _ => by ring) }

/-- Pullback of `shiftedContactActionOneForm` along the Legendre differential `dLeg` at `y₀` negates
`contactActionOneForm` at `y₀`. -/
theorem pullbackActionForm_legendreContact_at (n : ℕ) (w₀ : ContactJetSpace n ℝ)
    (v : Chart (Fin (2 * n + 1))) :
    let y₀ := contactChartEquiv n w₀
    let y₁ := contactChartEquiv n
      (InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n w₀)
    let K₀ := chartDirectionalLieAction (Fin (2 * n + 1)) y₀
    let dLeg : K₀.L →ₗ[ℝ] K₀.L :=
      (contactChartEquiv n).toLinearMap ∘ₗ
        (fderiv ℝ
          (InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n)
          w₀).toLinearMap ∘ₗ
        (contactChartEquiv n).symm.toLinearMap
    ((pullbackActionForm (K₁ := K₀) (K₂ := K₀)
        dLeg 1 (shiftedContactActionOneForm n y₀ y₁) ![v]).1 y₀) =
      -((contactActionOneForm n y₀ ![v]).1 y₀) := by
  intro y₀ y₁ K₀ dLeg
  rw [pullbackActionForm_apply]
  change ((shiftedContactActionOneForm n y₀ y₁ ![dLeg v]).1 y₀) =
    -(InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n
      ((contactChartEquiv n).symm y₀) ((contactChartEquiv n).symm v))
  have hy01 : y₀ + (y₁ - y₀) = y₁ := add_sub_cancel y₀ y₁
  have hsh : ((shiftedContactActionOneForm n y₀ y₁ ![dLeg v]).1 y₀) =
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n
        ((contactChartEquiv n).symm y₁) ((contactChartEquiv n).symm (dLeg v)) := by
    change ((contactChartEquiv n).symm (dLeg v)).2.1 -
        ∑ i : Fin n, ((contactChartEquiv n).symm (y₀ + (y₁ - y₀))).2.2 i *
          ((contactChartEquiv n).symm (dLeg v)).1 i =
      ((contactChartEquiv n).symm (dLeg v)).2.1 -
        ∑ i : Fin n, ((contactChartEquiv n).symm y₁).2.2 i *
          ((contactChartEquiv n).symm (dLeg v)).1 i
    rw [hy01]
  rw [hsh]
  have hy₀ : (contactChartEquiv n).symm y₀ = w₀ := (contactChartEquiv n).symm_apply_apply w₀
  have hy₁ : (contactChartEquiv n).symm y₁ =
      InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n w₀ :=
    (contactChartEquiv n).symm_apply_apply _
  have hd : (contactChartEquiv n).symm (dLeg v) =
      dLegendreContact n w₀ ((contactChartEquiv n).symm v) := by
    change (contactChartEquiv n).symm
        ((contactChartEquiv n)
          ((fderiv ℝ
            (InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact n)
            w₀) ((contactChartEquiv n).symm v))) =
      dLegendreContact n w₀ ((contactChartEquiv n).symm v)
    rw [(contactChartEquiv n).symm_apply_apply, fderiv_legendreContact]
  rw [hy₀, hy₁, hd]
  dsimp only [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm,
    InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.legendreContact,
    dLegendreContact]
  simp only [Finset.sum_add_distrib]
  have hcancel : (∑ i : Fin n, ((contactChartEquiv n).symm v).2.2 i * w₀.1 i) =
      ∑ i : Fin n, w₀.1 i * ((contactChartEquiv n).symm v).2.2 i :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hcancel]
  ring

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Smooth functions `ContactJetSpace n ℝ → ℝ` (`C^∞`) forming the carrier of a global
`DerivationLieLane`. -/
def SmoothJetFun (n : ℕ) : Subalgebra ℝ (ContactJetSpace n ℝ → ℝ) where
  carrier := { f | ContDiff ℝ (⊤ : ℕ∞) f }
  mul_mem' {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) := hf.mul hg
  one_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : ContactJetSpace n ℝ => (1 : ℝ))
    exact contDiff_const
  add_mem' {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) := hf.add hg
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : ContactJetSpace n ℝ => (0 : ℝ))
    exact contDiff_const
  algebraMap_mem' r := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : ContactJetSpace n ℝ => r)
    exact contDiff_const

private theorem smoothJetFun_contDiff {n : ℕ} (f : SmoothJetFun n) :
    ContDiff ℝ (⊤ : ℕ∞) f.1 :=
  f.2

/-- Underlying `LieActionLane ℝ (SmoothJetFun n)` by directional derivatives on `C^∞` jet
functions. -/
def smoothJetLieActionLane (n : ℕ) : LieActionLane ℝ (SmoothJetFun n) :=
  letI : LieRing (ContactJetSpace n ℝ) :=
    { bracket := fun _ _ => 0
      add_lie := fun _ _ _ => (add_zero 0).symm
      lie_add := fun _ _ _ => (add_zero 0).symm
      lie_self := fun _ => rfl
      leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  letI : LieAlgebra ℝ (ContactJetSpace n ℝ) :=
    { lie_smul := fun _ _ _ => (smul_zero _).symm }
  { L := ContactJetSpace n ℝ
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act :=
      { toFun := fun v =>
          { toFun := fun f =>
              ⟨fun w => fderiv ℝ f.1 w v,
               show ContDiff ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ f.1 w v) from
                 ((smoothJetFun_contDiff f).fderiv_right (by simp)).clm_apply contDiff_const⟩
            map_add' := fun f g => Subtype.ext (funext fun w => by
              simp [fderiv_add ((smoothJetFun_contDiff f).differentiable (by simp)).differentiableAt
                ((smoothJetFun_contDiff g).differentiable (by simp)).differentiableAt])
            map_smul' := fun r f => Subtype.ext (funext fun w => by
              simp [fderiv_const_smul
                ((smoothJetFun_contDiff f).differentiable (by simp)).differentiableAt]) }
        map_add' := fun v w => by
          ext f y
          simp
        map_smul' := fun r v => by
          ext f y
          simp
        map_lie' := fun {v w} => by
          ext f y
          change fderiv ℝ f.1 y 0 =
            fderiv ℝ (fun z => fderiv ℝ f.1 z w) y v -
              fderiv ℝ (fun z => fderiv ℝ f.1 z v) y w
          rw [map_zero]
          have hsymm : fderiv ℝ (fun z => fderiv ℝ f.1 z w) y v =
              fderiv ℝ (fun z => fderiv ℝ f.1 z v) y w := by
            have hd : HasFDerivAt (fderiv ℝ f.1) (fderiv ℝ (fderiv ℝ f.1) y) y :=
              (((smoothJetFun_contDiff f).fderiv_right (m := (2 : ℕ∞)) (by simp)).differentiable
                (by simp)).differentiableAt.hasFDerivAt
            have hw : fderiv ℝ (fun z => fderiv ℝ f.1 z w) y v =
                fderiv ℝ (fderiv ℝ f.1) y v w := by
              have hclm := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp y hd
              change fderiv ℝ (⇑(ContinuousLinearMap.apply ℝ ℝ w) ∘ fderiv ℝ f.1) y v =
                fderiv ℝ (fderiv ℝ f.1) y v w
              rw [hclm.fderiv]
              rfl
            have hv : fderiv ℝ (fun z => fderiv ℝ f.1 z v) y w =
                fderiv ℝ (fderiv ℝ f.1) y w v := by
              have hclm := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hd
              change fderiv ℝ (⇑(ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ f.1) y w =
                fderiv ℝ (fderiv ℝ f.1) y w v
              rw [hclm.fderiv]
              rfl
            rw [hw, hv, (((smoothJetFun_contDiff f).contDiffAt.isSymmSndFDerivAt (by simp)).eq v w)]
          rw [hsymm, sub_self] } }

theorem smoothJetLieActionLane_isLeibniz (n : ℕ) :
    IsLeibnizAction (smoothJetLieActionLane n) := fun v f g =>
  Subtype.ext (funext fun w => by
    let v₀ : ContactJetSpace n ℝ := v
    change fderiv ℝ (f.1 * g.1) w v₀ =
      fderiv ℝ f.1 w v₀ * g.1 w + f.1 w * fderiv ℝ g.1 w v₀
    rw [fderiv_mul ((smoothJetFun_contDiff f).differentiable (by simp)).differentiableAt
      ((smoothJetFun_contDiff g).differentiable (by simp)).differentiableAt]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, mul_comm (g.1 w)]
    ring)

/-- Global `DerivationLieLane ℝ (SmoothJetFun n)` where constant jet-space directions act by
directional derivative on `C^∞` jet functions (commuting derivations). -/
def smoothJetDerivationLane (n : ℕ) : DerivationLieLane ℝ (SmoothJetFun n) where
  L := (smoothJetLieActionLane n).L
  lieRing := (smoothJetLieActionLane n).lieRing
  lieAlgebra := (smoothJetLieActionLane n).lieAlgebra
  act := lieActionToDerivationHom (smoothJetLieActionLane n) (smoothJetLieActionLane_isLeibniz n)
  faithful := fun {v w} h => by
    let v₀ : ContactJetSpace n ℝ := v
    let w₀ : ContactJetSpace n ℝ := w
    have hev : ∀ f : SmoothJetFun n,
        fderiv ℝ f.1 0 v₀ = fderiv ℝ f.1 0 w₀ := fun f =>
      congrArg (fun D : NonAssocDerivation.derivations ℝ (SmoothJetFun n) => ((D.1 f).1 0)) h
    change v₀ = w₀
    refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ (funext fun i => ?_))
    · let ℓ : ContactJetSpace n ℝ →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj (R := ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ)))
      have h0 := hev ⟨fun p => ℓ p, show ContDiff ℝ (⊤ : ℕ∞) (fun p => ℓ p) from ℓ.contDiff⟩
      have hf : fderiv ℝ (fun p : ContactJetSpace n ℝ => ℓ p) 0 = ℓ := ℓ.hasFDerivAt.fderiv
      rw [hf] at h0
      exact h0
    · let ℓ : ContactJetSpace n ℝ →L[ℝ] ℝ :=
        (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).comp
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ)))
      have h0 := hev ⟨fun p => ℓ p, show ContDiff ℝ (⊤ : ℕ∞) (fun p => ℓ p) from ℓ.contDiff⟩
      have hf : fderiv ℝ (fun p : ContactJetSpace n ℝ => ℓ p) 0 = ℓ := ℓ.hasFDerivAt.fderiv
      rw [hf] at h0
      exact h0
    · let ℓ : ContactJetSpace n ℝ →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj (R := ℝ) i).comp
          ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).comp
            (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ))))
      have h0 := hev ⟨fun p => ℓ p, show ContDiff ℝ (⊤ : ℕ∞) (fun p => ℓ p) from ℓ.contDiff⟩
      have hf : fderiv ℝ (fun p : ContactJetSpace n ℝ => ℓ p) 0 = ℓ := ℓ.hasFDerivAt.fderiv
      rw [hf] at h0
      exact h0

/-- Contact 1-form lifted as a genuine Chevalley–Eilenberg `DerivationOperatorForm` of degree `1`
on `smoothJetDerivationLane n`. -/
def contactCEOneForm (n : ℕ) : DerivationOperatorForm (smoothJetDerivationLane n) 1 :=
  AlternatingMap.ofSubsingleton ℝ (ContactJetSpace n ℝ) (SmoothJetFun n) (0 : Fin 1)
    { toFun := fun dw =>
        ⟨fun w =>
          InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n w dw,
         show ContDiff ℝ (⊤ : ℕ∞) (fun w : ContactJetSpace n ℝ =>
             dw.2.1 - ∑ i : Fin n, w.2.2 i * dw.1 i) from
           (contDiff_const (c := dw.2.1)).sub (ContDiff.sum fun i _ =>
             ((ContinuousLinearMap.proj (R := ℝ) i).comp
               ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).comp
                 (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ))))).contDiff.mul
               (contDiff_const (c := dw.1 i)))⟩
      map_add' := fun u v => by
        apply Subtype.ext; funext w
        simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm,
          mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c u => by
        apply Subtype.ext; funext w
        simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm]
        rw [mul_sub, Finset.mul_sum]
        refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun i _ => by ring) }

/-- `n = 2` exterior-algebra alignment: evaluation of `contactCEOneForm 2` and
`ceExteriorDerivative (contactCEOneForm 2)` matches `grassmann_pfaff_contact5` (`ω` and `-Ω`). -/
theorem contactCEOneForm_d_apply (n : ℕ) (w u v : ContactJetSpace n ℝ) :
    ((ceExteriorDerivative (smoothJetDerivationLane n) 1 (contactCEOneForm n) ![u, v]).1 w) =
      ∑ i : Fin n, (u.1 i * v.2.2 i - v.1 i * u.2.2 i) := by
  let K := (smoothJetDerivationLane n).toLieActionLane
  let ω : ActionOperatorForm K 1 := contactCEOneForm n
  let uK : K.L := u
  let vK : K.L := v
  have h01 : ![uK, vK] = Matrix.vecCons uK ![vK] := by ext i; fin_cases i <;> rfl
  have hd : ceExteriorDerivative (smoothJetDerivationLane n) 1 (contactCEOneForm n) ![uK, vK] =
      (smoothJetDerivationLane n).operatorAction uK (ω ![vK]) -
        (smoothJetDerivationLane n).operatorAction vK (ω ![uK]) := by
    change actionExteriorDerivative K 1 ω ![uK, vK] = _
    rw [h01, ← AlternatingMap.curryLeft_apply_apply, actionExteriorDerivative_succ_curryLeft]
    simp only [AlternatingMap.sub_apply, lieDeriv_apply, actionExteriorDerivative_zero_apply]
    have hbr : ∀ x y : K.L, (⁅x, y⁆ : K.L) = 0 :=
      fun _ _ => rfl
    have hzero : (∑ i : Fin 1, ω (Function.update ![vK] i ⁅uK, ![vK] i⁆)) = 0 := by
      rw [Fin.sum_univ_one, hbr]
      apply Subtype.ext
      funext y
      have hz0 : Function.update ![vK] (0 : Fin 1) (0 : K.L) 0 = (0 : K.L) :=
        Function.update_self (0 : Fin 1) (0 : K.L) ![vK]
      change InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n y
          (Function.update ![vK] (0 : Fin 1) (0 : K.L) 0 : ContactJetSpace n ℝ) = 0
      rw [hz0]
      change InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n y 0 = 0
      simp [InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm]
    have hcur : ω.curryLeft uK Fin.elim0 = ω ![uK] := by
      rw [AlternatingMap.curryLeft_apply_apply]
      congr 1
    rw [hzero, sub_zero, hcur, Matrix.cons_val_zero]
    rfl
  rw [hd, Subalgebra.coe_sub, Pi.sub_apply]
  have hact : ∀ a b : ContactJetSpace n ℝ,
      ((smoothJetDerivationLane n).operatorAction a (ω ![b])).1 w =
        -(∑ i : Fin n, a.2.2 i * b.1 i) := fun a b => by
    change fderiv ℝ (fun y =>
        InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms.contactOneForm n y b) w a = _
    rw [(contactPointCLM_hasFDerivAt n w b).fderiv]
    rfl
  rw [hact u v, hact v u]
  simp only [sub_neg_eq_add, neg_add_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-! ### 4.3 `SmoothCartanGeometry` ↔ `MaurerCartanTower`, & `surfaceLegendrian` `BUCKET 1` Pullback -/

/-- Constant-action `LieActionLane ℝ B` for any Lie algebra representation `ρ : 𝔤 →ₗ⁅ℝ⁆ B`
(realizing left-invariant Maurer–Cartan forms `dω + [ω, ω] = 0` inside `MaurerCartanTower`). -/
def leftInvariantLieActionLane (𝔤 B : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [Ring B] [Algebra ℝ B] : LieActionLane ℝ B where
  L := 𝔤
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := 0

/-- Left-invariant `ActionOperatorForm` associated to a Lie algebra homomorphism `ρ : 𝔤 →ₗ⁅ℝ⁆ B`. -/
def leftInvariantConnectionForm {𝔤 B : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [Ring B] [Algebra ℝ B] (ρ : 𝔤 →ₗ⁅ℝ⁆ B) :
    ActionOperatorForm (leftInvariantLieActionLane 𝔤 B) 1 :=
  AlternatingMap.ofSubsingleton ℝ 𝔤 B (0 : Fin 1) ρ.toLinearMap

/-- **Maurer–Cartan Flatness Alignment (`SmoothCartanGeometry` ↔ `MaurerCartanTower`)**:
For any Lie-algebra representation `ρ : 𝔤 →ₗ⁅ℝ⁆ B`, `actionCurvature` of `leftInvariantConnectionForm ρ`
vanishes identically (`dω + ω ∧ ω = 0`), mirroring `SmoothCartanGeometry.maurerCartan_cartanCurvature_eq_zero`
and `gl2R_maurerCartan_flat`. -/
theorem leftInvariantConnectionForm_actionCurvature_eq_zero {𝔤 B : Type*}
    [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Ring B] [Algebra ℝ B]
    (ρ : 𝔤 →ₗ⁅ℝ⁆ B) (v w : 𝔤) :
    actionCurvature (leftInvariantLieActionLane 𝔤 B) (leftInvariantConnectionForm ρ) ![v, w] = 0 := by
  let K := leftInvariantLieActionLane 𝔤 B
  let vK : K.L := v
  let wK : K.L := w
  change actionCurvature K (leftInvariantConnectionForm ρ) ![vK, wK] = 0
  rw [actionCurvature_apply]
  have h0 : ∀ x : 𝔤, ∀ b : B, K.operatorAction x b = 0 :=
    fun _ _ => rfl
  rw [h0, h0, sub_self, zero_sub]
  change -(ρ ⁅v, w⁆) + (ρ v * ρ w - ρ w * ρ v) = 0
  rw [ρ.map_lie]
  change -(ρ v * ρ w - ρ w * ρ v) + (ρ v * ρ w - ρ w * ρ v) = 0
  abel

/-- Pairing `SmoothCartanGeometry.gl2R_maurerCartan_flat` with `MaurerCartanTower.actionThetaL_flat`:
on any Leibniz `LieActionLane R A` and invertible `g : Aˣ`, `actionThetaL` has zero `actionCurvature`. -/
theorem smoothCartan_and_tower_maurerCartan_flat {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K) (g : Aˣ)
    (v w : GroupLieAlgebra 𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2)
      InfoGeometry.Erlangen.SmoothCartanGeometry.GL2R)
    (q : InfoGeometry.Erlangen.SmoothCartanGeometry.GL2R) :
    actionCurvature K (actionThetaL K g) = 0 ∧
      InfoGeometry.Erlangen.SmoothCartanGeometry.cartanCurvatureFormWith
        𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2)
        (tangentSpaceCastModel
          𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2)
          (1 : InfoGeometry.Erlangen.SmoothCartanGeometry.GL2R))
        (fun x =>
          (InfoGeometry.Erlangen.SmoothCartanGeometry.leftMaurerCartanEquiv
            𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2) x).toContinuousLinearMap)
        (mulInvariantVectorField v)
        (mulInvariantVectorField w) q = 0 := by
  exact ⟨actionThetaL_flat K hK g,
    InfoGeometry.Erlangen.SmoothCartanGeometry.gl2R_maurerCartan_flat v w q⟩

/-- **`BUCKET 1` Legendrian Integrability Necessity**:
For any `C^2` hypersurface `f : (Fin n → ℝ) → ℝ`, the pullback of `dθ`
(`frechetExtDerivK (contactFrechetOneForm n)`) along `surfaceLegendrian n f` vanishes identically
at every `x : Fin n → ℝ` by symmetry of second Fréchet derivatives (`ContDiffAt.isSymmSndFDerivAt`). -/
theorem surfaceLegendrian_pullback_dtheta_eq_zero (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (x u v : Fin n → ℝ) :
    let ds := fderiv ℝ (surfaceLegendrian n f) x
    frechetExtDerivK (contactFrechetOneForm n) (surfaceLegendrian n f x) ![ds u, ds v] = 0 := by
  intro ds
  rw [frechetExtDerivK_contactFrechetOneForm]
  have hf1 : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hgrad : DifferentiableAt ℝ (fun y : Fin n → ℝ => fun i : Fin n =>
      fderiv ℝ f y (Pi.single i 1)) x := by
    rw [differentiableAt_pi]
    intro i
    have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    exact ((hfd.clm_apply contDiff_const).differentiable (by simp)).differentiableAt
  have hsurf : DifferentiableAt ℝ (surfaceLegendrian n f) x :=
    differentiableAt_id.prodMk (hf1.prodMk hgrad)
  have hfst : ∀ w : Fin n → ℝ, (ds w).1 = w := fun w => by
    have h1 := ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ))).hasFDerivAt.comp x
      hsurf.hasFDerivAt)
    have hfun : (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ)) ∘
        surfaceLegendrian n f) = id := rfl
    rw [hfun] at h1
    have hid := h1.unique (hasFDerivAt_id x)
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L w) hid
  have hsnd : ∀ (w : Fin n → ℝ) (i : Fin n),
      (ds w).2.2 i = fderiv ℝ (fderiv ℝ f) x w (Pi.single i 1) := fun w i => by
    let proj : ContactJetSpace n ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) i).comp
        ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).comp
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ))))
    have hcomp := (proj.hasFDerivAt.comp x hsurf.hasFDerivAt).fderiv
    have hfun : (proj ∘ surfaceLegendrian n f) =
        fun y => fderiv ℝ f y (Pi.single i 1) := rfl
    have hderiv_grad : HasFDerivAt (fun y : Fin n → ℝ => fderiv ℝ f y (Pi.single i 1))
        ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).comp (fderiv ℝ (fderiv ℝ f) x)) x := by
      have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
        ((hf.fderiv_right (m := (1 : ℕ∞)) (by norm_num)).differentiable (by simp)).differentiableAt
      exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).hasFDerivAt.comp x hfd.hasFDerivAt
    have heq : (proj.comp ds) =
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).comp (fderiv ℝ (fderiv ℝ f) x) := by
      change proj.comp (fderiv ℝ (surfaceLegendrian n f) x) = _
      rw [← hcomp, hfun, hderiv_grad.fderiv]
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L w) heq
  have hsum_eval : ∀ a b : Fin n → ℝ,
      (∑ i : Fin n, a i * fderiv ℝ (fderiv ℝ f) x b (Pi.single i 1)) =
        fderiv ℝ (fderiv ℝ f) x b a := fun a b => by
    have ha : a = ∑ i : Fin n, a i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [ha]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
  simp only [hfst, hsnd, Finset.sum_sub_distrib, hsum_eval]
  rw [((hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq u v), sub_self]

end BridgeCKlein9ContactR1

/-! ## Section 5: Cross-Pillar Bridges (`Erlangen20Datum`, `SymmetryAction`, M2 `Clifford`) -/

section CrossPillarPackaging

/-! ### 5.1 `kleinQuadricForm R` (`Cl(3,3)`) and M2 `CoordinateLessCliffordInvariance` Instantiations -/

/-- Exact Klein quadric form `P ↦ P.kleinQ` on `Fin 6 → R` over any `[CommRing R]`
(matching `Plucker6.kleinQ` without the factor-of-2 polar scaling bug). -/
def kleinQuadricForm (R : Type*) [CommRing R] : QuadraticForm R (Fin 6 → R) where
  toFun x := Plucker6.kleinQ (coordinates.symm x)
  toFun_smul r x := by
    simp [Plucker6.kleinQ, coordinates]
    ring
  exists_companion' :=
    ⟨LinearMap.mk₂ R (fun x y => Plucker6.polar (coordinates.symm x) (coordinates.symm y))
      (fun x y z => by simp [Plucker6.polar_formula, coordinates]; ring)
      (fun c x y => by simp [Plucker6.polar_formula, coordinates]; ring)
      (fun x y z => by simp [Plucker6.polar_formula, coordinates]; ring)
      (fun c x y => by simp [Plucker6.polar_formula, coordinates]; ring),
     fun x y => by
      have hadd : coordinates.symm (x + y) =
          Plucker6.add (coordinates.symm x) (coordinates.symm y) := by
        apply coordinates.injective
        ext i; fin_cases i <;> rfl
      change Plucker6.kleinQ (coordinates.symm (x + y)) =
        Plucker6.kleinQ (coordinates.symm x) + Plucker6.kleinQ (coordinates.symm y) +
          Plucker6.polar (coordinates.symm x) (coordinates.symm y)
      rw [hadd, Plucker6.polar]
      ring⟩

@[simp] theorem kleinQuadricForm_apply {R : Type*} [CommRing R] (P : Plucker6 R) :
    kleinQuadricForm R (coordinates P) = Plucker6.kleinQ P := by
  change Plucker6.kleinQ (coordinates.symm (coordinates P)) = Plucker6.kleinQ P
  rw [coordinates.symm_apply_apply]

/-- M2 `Clifford` invariants instantiated on Grassmann's circle space `Cl(circleBilin)` (`Cl(1,3)`). -/
def circleCliffordSymmetryAction :
    SymmetryAction OCircleBilin (CliffordAlgebra circleBilin.toQuadraticMap) :=
  cliffordSymmetryAction circleBilin.toQuadraticMap

def circleCliffordHTraceReadout :
    InvariantReadout circleCliffordSymmetryAction ℝ :=
  hTraceInvariantReadout circleBilin.toQuadraticMap

def circleCliffordKreinPairing :
    InvariantPairing circleCliffordSymmetryAction ℝ :=
  cliffordKreinInvariantPairing circleBilin.toQuadraticMap

def circleCliffordGraceEquivariant :
    (cliffordOperatorSymmetryAction circleBilin.toQuadraticMap).EquivariantLinearMap
      (cliffordOperatorSymmetryAction circleBilin.toQuadraticMap) :=
  graceOperator_equivariantLinearMap circleBilin.toQuadraticMap

/-- M2 `Clifford` invariants instantiated on Lie's 5D sphere space `Cl(lieBilinForm)` (`Cl(3,2)`). -/
def lieCliffordSymmetryAction :
    SymmetryAction OLieBilin (CliffordAlgebra lieBilinForm.toQuadraticMap) :=
  cliffordSymmetryAction lieBilinForm.toQuadraticMap

def lieCliffordHTraceReadout :
    InvariantReadout lieCliffordSymmetryAction ℝ :=
  hTraceInvariantReadout lieBilinForm.toQuadraticMap

/-- M2 `Clifford` invariants instantiated on generic Möbius `(n+1, 1)` and Lie `(n+1, 2)` quadrics. -/
def moebiusQuadricCliffordSymmetryAction (n : ℕ) :
    SymmetryAction
      ((moebiusQuadricBilin n).toQuadraticMap.IsometryEquiv (moebiusQuadricBilin n).toQuadraticMap)
      (CliffordAlgebra (moebiusQuadricBilin n).toQuadraticMap) :=
  cliffordSymmetryAction (moebiusQuadricBilin n).toQuadraticMap

def lieQuadricCliffordSymmetryAction (n : ℕ) :
    SymmetryAction
      ((lieQuadricBilin n).toQuadraticMap.IsometryEquiv (lieQuadricBilin n).toQuadraticMap)
      (CliffordAlgebra (lieQuadricBilin n).toQuadraticMap) :=
  cliffordSymmetryAction (lieQuadricBilin n).toQuadraticMap

/-- M2 `Clifford` invariants instantiated on Klein's quadric `Cl(kleinQuadricForm R)` (`Cl(3,3)`). -/
def kleinCliffordSymmetryAction (R : Type*) [CommRing R] :
    SymmetryAction ((kleinQuadricForm R).IsometryEquiv (kleinQuadricForm R))
      (CliffordAlgebra (kleinQuadricForm R)) :=
  cliffordSymmetryAction (kleinQuadricForm R)

def kleinCliffordHTraceReadout (R : Type*) [CommRing R] [Invertible (2 : R)] :
    InvariantReadout (kleinCliffordSymmetryAction R) R :=
  hTraceInvariantReadout (kleinQuadricForm R)

def kleinCliffordKreinPairing (R : Type*) [CommRing R] [Invertible (2 : R)] :
    InvariantPairing (kleinCliffordSymmetryAction R) R :=
  cliffordKreinInvariantPairing (kleinQuadricForm R)

def kleinCliffordGraceEquivariant :
    (cliffordOperatorSymmetryAction (kleinQuadricForm ℝ)).EquivariantLinearMap
      (cliffordOperatorSymmetryAction (kleinQuadricForm ℝ)) :=
  graceOperator_equivariantLinearMap (kleinQuadricForm ℝ)

/-! ### 5.2 Lifting Bridge B (`lieMobiusToCircleIsoHom`) & Bridge A/C (`secondCompound`) to Clifford -/

/-- Pullback of `cliffordOperatorSymmetryAction circleBilin.toQuadraticMap` to
`lieMobiusOrthogonalStabilizer` along `lieMobiusOrthogonalStabilizerEquivOCircle`. -/
def lieMobiusCircleCliffordOperatorAction :
    OperatorSymmetryAction lieMobiusOrthogonalStabilizer
      (CliffordAlgebra circleBilin.toQuadraticMap) where
  toFun g := CliffordAlgebra.equivOfIsometry
    (lieMobiusOrthogonalStabilizerEquivOCircle g)⁻¹
  map_one' := by
    rw [_root_.map_one, inv_one]
    exact CliffordAlgebra.equivOfIsometry_refl
  map_mul' g h := by
    rw [_root_.map_mul, _root_.mul_inv_rev, CliffordAlgebra.equivOfIsometry_trans]
    rfl

@[simp] theorem lieMobiusCircleCliffordOperatorAction_act (g : lieMobiusOrthogonalStabilizer)
    (x : CliffordAlgebra circleBilin.toQuadraticMap) :
    lieMobiusCircleCliffordOperatorAction.act g x =
      CliffordAlgebra.equivOfIsometry (lieMobiusOrthogonalStabilizerEquivOCircle g) x := by
  change CliffordAlgebra.equivOfIsometry
    ((lieMobiusOrthogonalStabilizerEquivOCircle g⁻¹)⁻¹) x = _
  rw [_root_.map_inv, inv_inv]

/-- Clifford `AlgEquiv` intertwining `Cl(lieBilinForm)` with `Cl(lieQuadricBilin 2)`. -/
def cliffordLieBilinEquivLieQuadric2 :
    CliffordAlgebra lieBilinForm.toQuadraticMap ≃ₐ[ℝ]
      CliffordAlgebra (lieQuadricBilin 2).toQuadraticMap :=
  CliffordAlgebra.equivOfIsometry lieBilin_isometryEquiv_lieQuadric2

/-- Isometric embedding `(moebiusQuadricBilin n).toQuadraticMap →qᵢ (lieQuadricBilin n).toQuadraticMap`
given by `moebiusToLieSection n` (`u ↦ Fin.snoc u 0`). -/
def moebiusToLieIsometry (n : ℕ) :
    (moebiusQuadricBilin n).toQuadraticMap →qᵢ (lieQuadricBilin n).toQuadraticMap where
  toLinearMap := moebiusToLieSection n
  map_app' w := by
    change lieQuadricBilin n (moebiusToLieSection n w) (moebiusToLieSection n w) =
      moebiusQuadricBilin n w w
    rw [lieQuadricBilin_eq_moebius_sub, lieQuadricProj_section]
    have hw : moebiusToLieSection n w ⟨n + 2, by omega⟩ = 0 := by
      change Fin.snoc (α := fun _ => ℝ) w (0 : ℝ) (Fin.last (n + 2)) = 0; simp
    rw [hw, mul_zero, sub_zero]

/-- Pullback of `cliffordOperatorSymmetryAction (moebiusQuadricBilin n).toQuadraticMap` to
`lieQuadricMobiusStabilizer n` along `lieQuadricMobiusToMoebiusHom n`. -/
def lieQuadricStabilizerMoebiusCliffordAction (n : ℕ) :
    OperatorSymmetryAction (lieQuadricMobiusStabilizer n)
      (CliffordAlgebra (moebiusQuadricBilin n).toQuadraticMap) where
  toFun g := CliffordAlgebra.equivOfIsometry (lieQuadricMobiusToMoebiusHom n g)⁻¹
  map_one' := by
    rw [_root_.map_one, inv_one]
    exact CliffordAlgebra.equivOfIsometry_refl
  map_mul' g h := by
    rw [_root_.map_mul, _root_.mul_inv_rev, CliffordAlgebra.equivOfIsometry_trans]
    rfl

/-- Pullback of `cliffordOperatorSymmetryAction (lieQuadricBilin n).toQuadraticMap` to
`lieQuadricMobiusStabilizer n` via subgroup inclusion. -/
def lieQuadricStabilizerLieCliffordAction (n : ℕ) :
    OperatorSymmetryAction (lieQuadricMobiusStabilizer n)
      (CliffordAlgebra (lieQuadricBilin n).toQuadraticMap) where
  toFun g := CliffordAlgebra.equivOfIsometry g.1⁻¹
  map_one' := by
    change CliffordAlgebra.equivOfIsometry
      ((1 : (lieQuadricBilin n).toQuadraticMap.IsometryEquiv
        (lieQuadricBilin n).toQuadraticMap)⁻¹) = _
    rw [inv_one]
    exact CliffordAlgebra.equivOfIsometry_refl
  map_mul' g h := by
    change CliffordAlgebra.equivOfIsometry (g.1 * h.1)⁻¹ = _
    rw [_root_.mul_inv_rev, CliffordAlgebra.equivOfIsometry_trans]
    rfl

/-- **`Cl(moebiusQuadricBilin n) →ₐ[ℝ] Cl(lieQuadricBilin n)` Equivariant Algebra Map**:
lifts the Klein §2 stabilizer homomorphism `lieQuadricMobiusToMoebiusHom n` to an exact
`lieQuadricMobiusStabilizer n`-equivariant Clifford algebra morphism (`n = 3` gives 5D ↔ 6D!). -/
def cliffordMoebiusToLieEquivariantAlgMap (n : ℕ) :
    (lieQuadricStabilizerMoebiusCliffordAction n).EquivariantAlgebraMap
      (lieQuadricStabilizerLieCliffordAction n) where
  toLinearMap := CliffordAlgebra.map (moebiusToLieIsometry n)
  equivariant g x := by
    change CliffordAlgebra.map (moebiusToLieIsometry n)
        (CliffordAlgebra.equivOfIsometry (lieQuadricMobiusToMoebiusHom n g⁻¹)⁻¹ x) =
      CliffordAlgebra.equivOfIsometry (g⁻¹.1)⁻¹
        (CliffordAlgebra.map (moebiusToLieIsometry n) x)
    rw [_root_.map_inv, inv_inv, Subgroup.coe_inv, inv_inv]
    induction x using CliffordAlgebra.induction with
    | algebraMap r =>
      simp only [AlgEquiv.commutes, AlgHom.commutes]
    | ι w =>
      simp only [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
      congr 1
      change moebiusToLieSection n (moebiusReduce n (g.1 : Module.End ℝ (Fin (n + 3) → ℝ)) w) =
        g.1 (moebiusToLieSection n w)
      rw [← lieQuadricProj_section n w, ← moebiusReduce_naturality n g.2, section_lieQuadricProj,
        lieQuadricProj_section n w]
      have hlast : (g.1 (moebiusToLieSection n w)) ⟨n + 2, by omega⟩ = 0 := by
        rw [lieQuadricMobiusStabilizer_apply_last g]
        change Fin.snoc (α := fun _ => ℝ) w (0 : ℝ) (Fin.last (n + 2)) = 0; simp
      change g.1 (moebiusToLieSection n w) -
          (g.1 (moebiusToLieSection n w)) ⟨n + 2, by omega⟩ • lieQuadricRadialAxis n =
        g.1 (moebiusToLieSection n w)
      rw [hlast, zero_smul, sub_zero]
    | mul a b iha ihb =>
      simp only [map_mul, iha, ihb]
    | add a b iha ihb =>
      simp only [map_add, iha, ihb]

/-- `SL(4, R) →* O(kleinQuadricForm R)` group homomorphism via `secondCompound`. -/
def secondCompoundSL4ToO33 (R : Type*) [CommRing R] :
    Matrix.SpecialLinearGroup (Fin 4) R →*
      (kleinQuadricForm R).IsometryEquiv (kleinQuadricForm R) where
  toFun g :=
    { toLinearEquiv :=
        { toFun := fun x => secondCompound g.1 *ᵥ x
          invFun := fun x => secondCompound (g⁻¹).1 *ᵥ x
          map_add' := fun x y => Matrix.mulVec_add _ x y
          map_smul' := fun c x => by simp [Matrix.mulVec_smul]
          left_inv := fun x => by
            have hmul : (g⁻¹).1 * g.1 = 1 := by
              rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                Matrix.SpecialLinearGroup.coe_one]
            change secondCompound (g⁻¹).1 *ᵥ (secondCompound g.1 *ᵥ x) = x
            rw [Matrix.mulVec_mulVec, ← secondCompound_mul, hmul, secondCompound_one,
              Matrix.one_mulVec]
          right_inv := fun x => by
            have hmul : g.1 * (g⁻¹).1 = 1 := by
              rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
                Matrix.SpecialLinearGroup.coe_one]
            change secondCompound g.1 *ᵥ (secondCompound (g⁻¹).1 *ᵥ x) = x
            rw [Matrix.mulVec_mulVec, ← secondCompound_mul, hmul, secondCompound_one,
              Matrix.one_mulVec] }
      map_app' := fun x => by
        change Plucker6.kleinQ (coordinates.symm (secondCompound g.1 *ᵥ x)) =
          Plucker6.kleinQ (coordinates.symm x)
        have htr : coordinates.symm (secondCompound g.1 *ᵥ x) =
            transform g.1 (coordinates.symm x) := by
          apply coordinates.injective
          rw [coordinates_transform, coordinates.apply_symm_apply, coordinates.apply_symm_apply]
        rw [htr, kleinQ_transform, g.prop, one_mul] }
  map_one' := by
    apply DFunLike.ext
    intro x
    change secondCompound (1 : Matrix (Fin 4) (Fin 4) R) *ᵥ x = x
    rw [secondCompound_one, Matrix.one_mulVec]
  map_mul' g h := by
    apply DFunLike.ext
    intro x
    change secondCompound (g.1 * h.1) *ᵥ x = secondCompound g.1 *ᵥ (secondCompound h.1 *ᵥ x)
    rw [secondCompound_mul, Matrix.mulVec_mulVec]

/-- Pullback of `cliffordSymmetryAction (kleinQuadricForm R)` to `SL(4, R)` via
`secondCompoundSL4ToO33 R`. -/
def sl4CliffordSymmetryAction (R : Type*) [CommRing R] :
    SymmetryAction (Matrix.SpecialLinearGroup (Fin 4) R)
      (CliffordAlgebra (kleinQuadricForm R)) where
  act g := (CliffordAlgebra.equivOfIsometry (secondCompoundSL4ToO33 R g)).toRingEquiv
  act_one x := by
    change (CliffordAlgebra.equivOfIsometry ((secondCompoundSL4ToO33 R) 1)).toRingEquiv x = x
    rw [_root_.map_one]
    change (CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl _)).toRingEquiv x = x
    rw [CliffordAlgebra.equivOfIsometry_refl]
    rfl
  act_mul g h x := by
    rw [_root_.map_mul]
    change CliffordAlgebra.equivOfIsometry
        ((secondCompoundSL4ToO33 R h).trans (secondCompoundSL4ToO33 R g)) x = _
    rw [← CliffordAlgebra.equivOfIsometry_trans]
    rfl

def sl4CliffordOperatorSymmetryAction :
    OperatorSymmetryAction (Matrix.SpecialLinearGroup (Fin 4) ℝ)
      (CliffordAlgebra (kleinQuadricForm ℝ)) where
  toFun g := CliffordAlgebra.equivOfIsometry (secondCompoundSL4ToO33 ℝ g)⁻¹
  map_one' := by
    rw [_root_.map_one, inv_one]
    exact CliffordAlgebra.equivOfIsometry_refl
  map_mul' g h := by
    rw [_root_.map_mul, _root_.mul_inv_rev, CliffordAlgebra.equivOfIsometry_trans]
    rfl

/-! ### 5.3 `SymmetryAction` and `Erlangen20Datum` Packaging for Bridges A, B, C -/

/-- `SymmetryAction (GL (Fin 4) R) (ExteriorAlgebra R (Fin 4 → R))` via `ExteriorAlgebra.map`. -/
def gl4ExteriorSymmetryAction (R : Type*) [CommRing R] :
    SymmetryAction (Matrix.GeneralLinearGroup (Fin 4) R) (ExteriorAlgebra R (Fin 4 → R)) where
  act g :=
    let ge := Matrix.toLinearEquiv' g.1
      (Matrix.invertibleOfIsUnitDet g.1 ((Matrix.isUnit_iff_isUnit_det g.1).mp g.isUnit))
    { toFun := ExteriorAlgebra.map ge.toLinearMap
      invFun := ExteriorAlgebra.map ge.symm.toLinearMap
      left_inv := fun x => by
        suffices h : (ExteriorAlgebra.map ge.symm.toLinearMap).comp
            (ExteriorAlgebra.map ge.toLinearMap) =
            AlgHom.id R (ExteriorAlgebra R (Fin 4 → R)) from
          congrArg (fun φ => φ x) h
        exact ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by simp)
      right_inv := fun x => by
        suffices h : (ExteriorAlgebra.map ge.toLinearMap).comp
            (ExteriorAlgebra.map ge.symm.toLinearMap) =
            AlgHom.id R (ExteriorAlgebra R (Fin 4 → R)) from
          congrArg (fun φ => φ x) h
        exact ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by simp)
      map_mul' := map_mul _
      map_add' := map_add _ }
  act_one x := by
    suffices h1 : ExteriorAlgebra.map (Matrix.toLinearEquiv' (1 : Matrix.GeneralLinearGroup (Fin 4) R).1
        (Matrix.invertibleOfIsUnitDet _
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (1 : Matrix.GeneralLinearGroup (Fin 4) R).isUnit))).toLinearMap =
        AlgHom.id R (ExteriorAlgebra R (Fin 4 → R)) from
      congrArg (fun φ => φ x) h1
    exact ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by simp [Matrix.toLinearEquiv'])
  act_mul g h x := by
    suffices hcomp : ExteriorAlgebra.map (Matrix.toLinearEquiv' (g.1 * h.1)
        (Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp (g * h).isUnit))).toLinearMap =
      (ExteriorAlgebra.map (Matrix.toLinearEquiv' g.1
        (Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit))).toLinearMap).comp
        (ExteriorAlgebra.map (Matrix.toLinearEquiv' h.1
          (Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit))).toLinearMap) from
      congrArg (fun φ => φ x) hcomp
    exact ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by
      simp [Matrix.toLinearEquiv', Matrix.mulVec_mulVec])

/-- Bridge A intertwiner inside `gl4ExteriorSymmetryAction`: acting by `g` on `pluckerToExterior2 P`
equals `pluckerToExterior2 (transform g.1 P)`. -/
theorem gl4ExteriorSymmetryAction_pluckerToExterior2 {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Fin 4) R) (P : Plucker6 R) :
    (gl4ExteriorSymmetryAction R).act g (pluckerToExterior2 P) =
      pluckerToExterior2 (transform g.1 P) :=
  (pluckerToExterior2_transform g.1 P).symm

/-- Linear equivalence `(Fin 6 → R) ≃ₗ[R] (Fin 6 → R)` induced by `secondCompound g.1`. -/
def secondCompoundLinearEquiv {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Fin 4) R) : (Fin 6 → R) ≃ₗ[R] (Fin 6 → R) where
  toFun x := secondCompound g.1 *ᵥ x
  invFun x := secondCompound (g⁻¹).1 *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := by simp [Matrix.mulVec_smul]
  left_inv x := by
    have hmul : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    change secondCompound (g⁻¹).1 *ᵥ (secondCompound g.1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← secondCompound_mul, hmul, secondCompound_one, Matrix.one_mulVec]
  right_inv x := by
    have hmul : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change secondCompound g.1 *ᵥ (secondCompound (g⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← secondCompound_mul, hmul, secondCompound_one, Matrix.one_mulVec]

/-- Conjugation `SymmetryAction (GL (Fin 4) R) (Module.End R (Fin 6 → R))` from `secondCompound`. -/
def gl4PluckerEndSymmetryAction (R : Type*) [CommRing R] :
    SymmetryAction (Matrix.GeneralLinearGroup (Fin 4) R) (Module.End R (Fin 6 → R)) where
  act g :=
    let e := secondCompoundLinearEquiv g
    { toFun := fun T => e.toLinearMap.comp (T.comp e.symm.toLinearMap)
      invFun := fun T => e.symm.toLinearMap.comp (T.comp e.toLinearMap)
      left_inv := fun T => by ext x; simp
      right_inv := fun T => by ext x; simp
      map_mul' := fun T₁ T₂ => by ext x; simp [Module.End.mul_apply]
      map_add' := fun T₁ T₂ => by ext x; simp }
  act_one T := by
    apply LinearMap.ext
    intro x
    have he1 : secondCompoundLinearEquiv (1 : Matrix.GeneralLinearGroup (Fin 4) R) =
        LinearEquiv.refl R _ := by
      ext y i
      change (secondCompound (1 : Matrix (Fin 4) (Fin 4) R) *ᵥ y) i = y i
      rw [secondCompound_one, Matrix.one_mulVec]
    change secondCompoundLinearEquiv (1 : Matrix.GeneralLinearGroup (Fin 4) R)
        (T ((secondCompoundLinearEquiv (1 : Matrix.GeneralLinearGroup (Fin 4) R)).symm x)) = T x
    rw [he1]
    rfl
  act_mul g h T := by
    apply LinearMap.ext
    intro x
    have hemul : secondCompoundLinearEquiv (g * h) =
        (secondCompoundLinearEquiv h).trans (secondCompoundLinearEquiv g) := by
      ext y i
      change (secondCompound (g.1 * h.1) *ᵥ y) i =
        (secondCompound g.1 *ᵥ (secondCompound h.1 *ᵥ y)) i
      rw [secondCompound_mul, Matrix.mulVec_mulVec]
    change secondCompoundLinearEquiv (g * h) (T ((secondCompoundLinearEquiv (g * h)).symm x)) =
      secondCompoundLinearEquiv g (secondCompoundLinearEquiv h
        (T ((secondCompoundLinearEquiv h).symm ((secondCompoundLinearEquiv g).symm x))))
    rw [hemul]
    rfl

/-- Left `GL(4, R)` linear equivalence induced on linear complexes via `complexCongr g⁻¹.1`. -/
def complexCongrLinearEquiv {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Fin 4) R) : (Fin 6 → R) ≃ₗ[R] (Fin 6 → R) where
  toFun x := coordinates (complexCongr (g⁻¹).1 (coordinates.symm x))
  invFun x := coordinates (complexCongr g.1 (coordinates.symm x))
  map_add' x y := by
    have hmat : complexMatrix (coordinates.symm (x + y)) =
        complexMatrix (coordinates.symm x) + complexMatrix (coordinates.symm y) := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        (simp [complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4, coordinates]; try abel)
    have hM : (g⁻¹).1ᵀ * complexMatrix (coordinates.symm (x + y)) * (g⁻¹).1 =
        ((g⁻¹).1ᵀ * complexMatrix (coordinates.symm x) * (g⁻¹).1) +
          ((g⁻¹).1ᵀ * complexMatrix (coordinates.symm y) * (g⁻¹).1) := by
      rw [hmat, Matrix.mul_add, Matrix.add_mul]
    dsimp only [complexCongr, complexOfMatrix]
    rw [hM]
    ext i
    fin_cases i <;>
      (simp [coordinates, Matrix.add_apply]; try abel)
  map_smul' c x := by
    have hmat : complexMatrix (coordinates.symm (c • x)) =
        c • complexMatrix (coordinates.symm x) := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp [complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4, coordinates]
    have hM : (g⁻¹).1ᵀ * complexMatrix (coordinates.symm (c • x)) * (g⁻¹).1 =
        c • ((g⁻¹).1ᵀ * complexMatrix (coordinates.symm x) * (g⁻¹).1) := by
      rw [hmat, Matrix.mul_smul, Matrix.smul_mul]
    dsimp only [complexCongr, complexOfMatrix]
    rw [hM]
    ext i
    fin_cases i <;>
      simp [coordinates, Matrix.smul_apply, smul_eq_mul]
  left_inv x := by
    have hmul : (g⁻¹).1 * g.1 = 1 := by simp
    change coordinates (complexCongr g.1 (complexCongr (g⁻¹).1 (coordinates.symm x))) = x
    rw [← complexCongr_mul, hmul, complexCongr_one, coordinates.apply_symm_apply]
  right_inv x := by
    have hmul : g.1 * (g⁻¹).1 = 1 := by simp
    change coordinates (complexCongr (g⁻¹).1 (complexCongr g.1 (coordinates.symm x))) = x
    rw [← complexCongr_mul, hmul, complexCongr_one, coordinates.apply_symm_apply]

/-- Conjugation `SymmetryAction (GL (Fin 4) R) (Module.End R (Fin 6 → R))` from contravariant
`complexCongr` (left-regularized via `g⁻¹`). -/
def gl4ComplexCongrEndSymmetryAction (R : Type*) [CommRing R] :
    SymmetryAction (Matrix.GeneralLinearGroup (Fin 4) R) (Module.End R (Fin 6 → R)) where
  act g :=
    let e := complexCongrLinearEquiv g
    { toFun := fun T => e.toLinearMap.comp (T.comp e.symm.toLinearMap)
      invFun := fun T => e.symm.toLinearMap.comp (T.comp e.toLinearMap)
      left_inv := fun T => by ext x; simp
      right_inv := fun T => by ext x; simp
      map_mul' := fun T₁ T₂ => by ext x; simp [Module.End.mul_apply]
      map_add' := fun T₁ T₂ => by ext x; simp }
  act_one T := by
    apply LinearMap.ext
    intro x
    change (complexCongrLinearEquiv (1 : Matrix.GeneralLinearGroup (Fin 4) R))
        (T ((complexCongrLinearEquiv (1 : Matrix.GeneralLinearGroup (Fin 4) R)).symm x)) = T x
    have h1 : complexCongrLinearEquiv (1 : Matrix.GeneralLinearGroup (Fin 4) R) =
        LinearEquiv.refl R _ := by
      ext y i
      change coordinates (complexCongr (1 : Matrix (Fin 4) (Fin 4) R) (coordinates.symm y)) i = y i
      rw [complexCongr_one, coordinates.apply_symm_apply]
    rw [h1]
    rfl
  act_mul g h T := by
    apply LinearMap.ext
    intro x
    have hmul : complexCongrLinearEquiv (g * h) =
        (complexCongrLinearEquiv h).trans (complexCongrLinearEquiv g) := by
      ext y i
      change coordinates (complexCongr ((g * h)⁻¹).1 (coordinates.symm y)) i =
        coordinates (complexCongr (g⁻¹).1 (complexCongr (h⁻¹).1 (coordinates.symm y))) i
      rw [_root_.mul_inv_rev, Units.val_mul, complexCongr_mul]
    change complexCongrLinearEquiv (g * h) (T ((complexCongrLinearEquiv (g * h)).symm x)) =
      complexCongrLinearEquiv g (complexCongrLinearEquiv h
        (T ((complexCongrLinearEquiv h).symm ((complexCongrLinearEquiv g).symm x))))
    rw [hmul]
    rfl

section Erlangen20Packaging

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Generic `Erlangen20Datum` on `CliffordAlgebra Q` driven by M2's `soLieAlgebra Q` and
`cliffordSymmetryAction Q` (instantiated below on `circleBilin`, `lieBilinForm`,
`moebiusQuadricBilin`, `lieQuadricBilin`, and `kleinQuadricForm`). -/
def cliffordErlangen20Datum {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) :
    Erlangen20Datum R (CliffordAlgebra Q) (soLieAlgebra Q)
      (SymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q))
      (CliffordAlgebra Q → Prop) where
  operatorAlgebra := ⊤
  representation := (LieModule.toEnd R (CliffordAlgebra Q) (CliffordAlgebra Q)).comp
    (soLieAlgebra Q).incl
  representation_mem _ := Algebra.mem_top
  symmetryData := cliffordSymmetryAction Q
  invariantData := IsInvariant (cliffordSymmetryAction Q)

/-- Concrete Bridge B / A / C Clifford `Erlangen20Datum` instances. -/
def circleCliffordErlangen20Datum :
    Erlangen20Datum ℝ (CliffordAlgebra circleBilin.toQuadraticMap)
      (soLieAlgebra circleBilin.toQuadraticMap)
      (SymmetryAction OCircleBilin (CliffordAlgebra circleBilin.toQuadraticMap))
      (CliffordAlgebra circleBilin.toQuadraticMap → Prop) :=
  cliffordErlangen20Datum circleBilin.toQuadraticMap

def lieCliffordErlangen20Datum :
    Erlangen20Datum ℝ (CliffordAlgebra lieBilinForm.toQuadraticMap)
      (soLieAlgebra lieBilinForm.toQuadraticMap)
      (SymmetryAction OLieBilin (CliffordAlgebra lieBilinForm.toQuadraticMap))
      (CliffordAlgebra lieBilinForm.toQuadraticMap → Prop) :=
  cliffordErlangen20Datum lieBilinForm.toQuadraticMap

def lieQuadricCliffordErlangen20Datum (n : ℕ) :
    Erlangen20Datum ℝ (CliffordAlgebra (lieQuadricBilin n).toQuadraticMap)
      (soLieAlgebra (lieQuadricBilin n).toQuadraticMap)
      (SymmetryAction
        ((lieQuadricBilin n).toQuadraticMap.IsometryEquiv (lieQuadricBilin n).toQuadraticMap)
        (CliffordAlgebra (lieQuadricBilin n).toQuadraticMap))
      (CliffordAlgebra (lieQuadricBilin n).toQuadraticMap → Prop) :=
  cliffordErlangen20Datum (lieQuadricBilin n).toQuadraticMap

def kleinQuadricCliffordErlangen20Datum (R : Type*) [CommRing R] :
    Erlangen20Datum R (CliffordAlgebra (kleinQuadricForm R))
      (soLieAlgebra (kleinQuadricForm R))
      (SymmetryAction ((kleinQuadricForm R).IsometryEquiv (kleinQuadricForm R))
        (CliffordAlgebra (kleinQuadricForm R)))
      (CliffordAlgebra (kleinQuadricForm R) → Prop) :=
  cliffordErlangen20Datum (kleinQuadricForm R)

/-- Infinitesimal second-compound `6 × 6` matrix of `X : Matrix (Fin 4) (Fin 4) R`:
`(X eₐ) ∧ e_b + eₐ ∧ (X e_b)`. -/
def secondCompoundDerivMatrix {R : Type*} [CommRing R]
    (X : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  fun i j =>
    let a := (coordinatePair i).1
    let b := (coordinatePair i).2
    let c := (coordinatePair j).1
    let d := (coordinatePair j).2
    (if b = d then X a c else 0) - (if b = c then X a d else 0) +
      ((if a = c then X b d else 0) - (if a = d then X b c else 0))

private lemma secondCompoundDerivMatrix_neg {R : Type*} [CommRing R]
    (Z : Matrix (Fin 4) (Fin 4) R) :
    secondCompoundDerivMatrix (-Z) = -secondCompoundDerivMatrix Z := by
  ext i j
  simp only [secondCompoundDerivMatrix, Matrix.neg_apply]
  split_ifs <;> ring

private lemma secondCompoundDerivMatrix_lie {R : Type*} [CommRing R]
    (X Y : Matrix (Fin 4) (Fin 4) R) :
    secondCompoundDerivMatrix (X * Y - Y * X) =
      secondCompoundDerivMatrix X * secondCompoundDerivMatrix Y -
        secondCompoundDerivMatrix Y * secondCompoundDerivMatrix X := by
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_six]
  fin_cases i
  all_goals
    fin_cases j <;>
      (simp [secondCompoundDerivMatrix, coordinatePair, Matrix.sub_apply, Matrix.mul_apply,
        Fin.sum_univ_four]; ring)

/-- Lie-algebra representation `𝔤𝔩(4, R) →ₗ⁅R⁆ Module.End R (Fin 6 → R)` given by the
infinitesimal second compound on Plücker 6-vectors. -/
def secondCompoundDeriv (R : Type*) [CommRing R] :
    Matrix (Fin 4) (Fin 4) R →ₗ⁅R⁆ Module.End R (Fin 6 → R) where
  toFun X := Matrix.toLin' (secondCompoundDerivMatrix X)
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [secondCompoundDerivMatrix, coordinatePair, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  map_smul' r X := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [secondCompoundDerivMatrix, coordinatePair, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  map_lie' {X Y} := by
    change Matrix.toLin' (secondCompoundDerivMatrix (X * Y - Y * X)) =
      Matrix.toLin' (secondCompoundDerivMatrix X) * Matrix.toLin' (secondCompoundDerivMatrix Y) -
        Matrix.toLin' (secondCompoundDerivMatrix Y) * Matrix.toLin' (secondCompoundDerivMatrix X)
    rw [secondCompoundDerivMatrix_lie, map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul]
    rfl

/-- Bridge A `Erlangen20Datum` on Plücker 6-space `(Fin 6 → R)` under `𝔤𝔩(4, R)` via
`secondCompoundDeriv R` and `gl4PluckerEndSymmetryAction R`. -/
def pluckerErlangen20Datum (R : Type*) [CommRing R] :
    Erlangen20Datum R (Fin 6 → R) (Matrix (Fin 4) (Fin 4) R)
      (SymmetryAction (Matrix.GeneralLinearGroup (Fin 4) R) (Module.End R (Fin 6 → R)))
      ((Fin 6 → R) → Prop) where
  operatorAlgebra := ⊤
  representation := secondCompoundDeriv R
  representation_mem _ := Algebra.mem_top
  symmetryData := gl4PluckerEndSymmetryAction R
  invariantData := fun x => kleinQuadricForm R x = 0

/-- Dual infinitesimal congruence Lie representation `X ↦ -(secondCompoundDeriv X).dual`
for `complexCongr` on linear complexes. -/
def complexCongrDeriv (R : Type*) [CommRing R] :
    Matrix (Fin 4) (Fin 4) R →ₗ⁅R⁆ Module.End R (Fin 6 → R) where
  toFun X := Matrix.toLin' (-(secondCompoundDerivMatrix X)ᵀ)
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [secondCompoundDerivMatrix, coordinatePair, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  map_smul' r X := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [secondCompoundDerivMatrix, coordinatePair, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  map_lie' {X Y} := by
    change Matrix.toLin' (-(secondCompoundDerivMatrix (X * Y - Y * X))ᵀ) =
      Matrix.toLin' (-(secondCompoundDerivMatrix X)ᵀ) *
          Matrix.toLin' (-(secondCompoundDerivMatrix Y)ᵀ) -
        Matrix.toLin' (-(secondCompoundDerivMatrix Y)ᵀ) *
          Matrix.toLin' (-(secondCompoundDerivMatrix X)ᵀ)
    have hsub : Y * X - X * Y = -(X * Y - Y * X) := by abel
    have hmat : -(secondCompoundDerivMatrix (X * Y - Y * X))ᵀ =
        (-(secondCompoundDerivMatrix X)ᵀ) * (-(secondCompoundDerivMatrix Y)ᵀ) -
          (-(secondCompoundDerivMatrix Y)ᵀ) * (-(secondCompoundDerivMatrix X)ᵀ) := by
      rw [← Matrix.transpose_neg, ← secondCompoundDerivMatrix_neg, ← hsub,
        secondCompoundDerivMatrix_lie, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_mul, neg_mul_neg, neg_mul_neg]
    rw [hmat, map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul]
    rfl

/-- Bridge C `Erlangen20Datum` on linear-complex space `(Fin 6 → R)` under `𝔤𝔩(4, R)` via
`complexCongrDeriv R` and `gl4ComplexCongrEndSymmetryAction R`. -/
def complexCongrErlangen20Datum (R : Type*) [CommRing R] :
    Erlangen20Datum R (Fin 6 → R) (Matrix (Fin 4) (Fin 4) R)
      (SymmetryAction (Matrix.GeneralLinearGroup (Fin 4) R) (Module.End R (Fin 6 → R)))
      (Plucker6 R → Prop) where
  operatorAlgebra := ⊤
  representation := complexCongrDeriv R
  representation_mem _ := Algebra.mem_top
  symmetryData := gl4ComplexCongrEndSymmetryAction R
  invariantData := fun C => Plucker6.kleinQ C = 0

end Erlangen20Packaging

end CrossPillarPackaging

end InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges


