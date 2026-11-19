/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.SmoothCartanGeometry
import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Smooth Principal Bundles, Cartan-Form Packages, and Action-Compatible Cartan Connections

This module closes the principal-bundle extension gap documented on
`InfoGeometry.Erlangen.SmoothCartanGeometry`:

1. **`SmoothPrincipalTrivialization` & `SmoothPrincipalCartanGeometry`**:
   Packages the existing pointwise Cartan-form carrier with a `C³` Mathlib `LieGroup` structure
   on `H`, joint `C³` smoothness of the right action, and a covering atlas of equivariant bundle
   charts. These fields establish the principal-bundle structure but, on their own, do not tie the
   stored `fundamentalVec` or `AdH` to the differential of that action.
2. **`ActionCompatibleSmoothPrincipalCartanGeometry`**:
   Adds an explicit Lie-algebra/tangent-at-identity equivalence, identifies `fundamentalVec` with
   the derivative of each action orbit, and requires the isotropy inclusion to intertwine `AdH`
   with the differential of group conjugation. The generic Lie-group Maurer–Cartan model and its
   `GL₂(ℝ)` instance inhabit this stronger interface. This still does not package `ω` as a smooth
   section of the hom bundle `Hom(TP, 𝔤)`; the current owner provides pointwise continuous linear
   equivalences and curvature calculations, so full smoothness of the Cartan form remains open.
3. **Unconditional Principal-Bundle Properties**:
   For ANY `B : SmoothPrincipalCartanGeometry`, without adding extra axioms or hypotheses:
   - `principal_fiber_torsor_existsUnique`: every fiber is a right `H`-torsor (`proj p = proj q` iff
     `∃ h, rightAct h p = q`, with uniqueness);
   - `principal_proj_surjective`, `principal_proj_continuous`, `principal_proj_isOpenMap`;
   - `localPrincipalSection` & `sectionThrough`: genuine `C³` local sections;
   - `principalTransition`: `C³` principal transition functions `U₁ ∩ U₂ → H` satisfying the
     Čech 1-cocycle laws (`t_{1,1} = 1`, `t_{1,2} * t_{2,3} = t_{1,3}`, `t_{1,2}⁻¹ = t_{2,1}`, and
     `(e₁ p).2 = t_{1,2}(π p) * (e₂ p).2`);
   - **`principal_mfderiv_proj_surjective` & `principalCartanBaseTangentEquiv`**:
     differentiating `π ∘ sectionThrough e p = id` near `π p` unconditionally yields a right
     inverse to `dπₚ`, proving `mfderiv IP IM C.proj p` is surjective and identifying
     `TangentSpace IM (C.proj p) ≃ₗ[ℝ] (𝔤 ⧸ C.iotaH.range.toSubmodule)` with zero `hsubmersion`
     assumption;
   - `pullbackCartanGaugePotential`: smooth local base-level `𝔤`-valued 1-form `s* ω`.
4. **Constructive Closed Inhabitants (Flat/Curved Homothety & Noncommutative `GL2R`)**:
   - `multiplicativeRealLieGroup`: genuine `LieGroup multiplicativeRealModel ∞ (Multiplicative ℝ)`;
   - `homothetyPrincipalCartanGeometry κ` (`flatHomothetyPrincipalCartanGeometry` for `κ = 0`),
     upgrading the concrete homothety bundle (flat `κ = 0` vs. curved `κ ≠ 0`) into the full
     generic principal-bundle interface;
   - `lieGroupPrincipalCartanGeometry` & `gl2RPrincipalCartanGeometry`: genuine noncommutative
     principal Cartan bundle `(GL2R → Fin 0 → ℝ)` equipped with its left Maurer–Cartan form and
     adjoint Lie hom `Ad`.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

open Bundle Function Set
open scoped Topology Manifold ContDiff LieAlgebra
open InfoGeometry.Erlangen.SmoothCartanGeometry

namespace InfoGeometry.Canonical.SmoothPrincipalCartanBundleClosure

/-! ### The Cartan form as a regular map on the tangent bundle

`SmoothCartanGeometry.omega` is pointwise a continuous linear equivalence. Its values alone do
not assert that they vary smoothly with the base point. The following refinement records the
missing regularity as smoothness of the associated map on the total tangent bundle. Since the
fiber maps are already linear by `C.omega`, this is the total-space formulation of a smooth
`𝔤`-valued one-form; it does not replace the pointwise Cartan axioms. A `C³` manifold gives the
tangent bundle its natural `C²` structure, hence the order drop here.
-/

section CartanFormRegularity

variable {EP EM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HP HM : Type*} [TopologicalSpace HP] [TopologicalSpace HM]
  {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
  {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [Group H]
  {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
  {E𝔤 H𝔤 : Type*} [NormedAddCommGroup E𝔤] [NormedSpace ℝ E𝔤]
  [TopologicalSpace H𝔤] {I𝔤 : ModelWithCorners ℝ E𝔤 H𝔤}
  [ChartedSpace H𝔤 𝔤] [IsManifold I𝔤 (minSmoothness ℝ 2) 𝔤]

/-- The total-space function associated to the pointwise Cartan one-form. -/
def cartanOmegaTotal
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (v : TangentBundle IP P) : 𝔤 :=
  C.omega v.1 v.2

/-- Smoothness of the Cartan one-form at the regularity naturally supplied by a `C³` total
space. The field is a `C²` map on the full tangent bundle, while each fiber restriction is the
continuous linear equivalence already stored in `C.omega`. -/
structure SmoothCartanFormRegularity
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    where
  omega_total_contMDiff :
    letI : IsManifold IP (minSmoothness ℝ 3) P := C.smoothP
    ContMDiff IP.tangent I𝔤 (minSmoothness ℝ 2) (cartanOmegaTotal C)

end CartanFormRegularity

/-! ### Smoothness of the homothety Cartan form

For the trivial tangent bundle of a normed model space, the tangent-bundle model
identification has smooth coordinate map. The homothety form is an elementary smooth
function in those coordinates, giving a concrete inhabitant of the regularity refinement.
-/

section HomothetyCartanFormRegularity

open InfoGeometry.Erlangen.SmoothCartanGeometry

theorem homothetyCartanOmega_total_contMDiff (κ : ℝ) :
    ContMDiff (𝓘(ℝ, (Fin 2 → ℝ) × ℝ)).tangent 𝓘(ℝ, HomothetyLieAlg)
      (minSmoothness ℝ 2)
      (cartanOmegaTotal (homothetyCartanGeometry κ)) := by
  let E := (Fin 2 → ℝ) × ℝ
  let I := 𝓘(ℝ, E)
  let hcoord : E × E → HomothetyLieAlg :=
    fun z => ⟨Real.exp (-z.1.2) • z.2.1,
      z.2.2 + κ * (z.1.1 0 * z.2.1 1 - z.1.1 1 * z.2.1 0)⟩
  have hcoord_smooth : ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, HomothetyLieAlg)
      (minSmoothness ℝ 2) hcoord := by
    change ContDiff ℝ (minSmoothness ℝ 2) hcoord
    fun_prop
  have hTangent : ContMDiff I.tangent (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (tangentBundleModelSpaceHomeomorph I) := by
    simpa [I, E] using
      (contMDiff_tangentBundleModelSpaceHomeomorph (I := I))
  have hEq : cartanOmegaTotal (homothetyCartanGeometry κ) =
      hcoord ∘ tangentBundleModelSpaceHomeomorph I := by
    funext v
    simp [cartanOmegaTotal, hcoord, E, I, homothetyCartanGeometry,
      homothetyCartanOmega_apply, tangentBundleModelSpaceHomeomorph_coe]
  rw [hEq]
  exact hcoord_smooth.comp hTangent

def homothetyCartanFormRegularity (κ : ℝ) :
    SmoothCartanFormRegularity (homothetyCartanGeometry κ) :=
  ⟨homothetyCartanOmega_total_contMDiff κ⟩

end HomothetyCartanFormRegularity

section SmoothPrincipalInterface

/-- A smooth (`C³`), right-`H`-equivariant local bundle trivialization of `proj : P → M` with
structure group `H`. -/
structure SmoothPrincipalTrivialization
    (EP EM EH : Type*) [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EH] [NormedSpace ℝ EH]
    (HP HM HH : Type*) [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HH]
    (IP : ModelWithCorners ℝ EP HP) (IM : ModelWithCorners ℝ EM HM)
    (IH : ModelWithCorners ℝ EH HH)
    (P M : Type*) [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    (H : Type*) [Group H] [TopologicalSpace H] [ChartedSpace HH H]
    (proj : P → M) (rightAct : H → P → P) where
  toTrivialization : Bundle.Trivialization H proj
  contMDiffOn_toFun :
    ContMDiffOn IP (IM.prod IH) (minSmoothness ℝ 3) toTrivialization toTrivialization.source
  contMDiffOn_invFun :
    ContMDiffOn (IM.prod IH) IP (minSmoothness ℝ 3)
      toTrivialization.toPartialHomeomorph.symm toTrivialization.target
  action_compat :
    ∀ (h : H) (p : P), p ∈ toTrivialization.source →
      toTrivialization (rightAct h p) = (proj p, (toTrivialization p).2 * h)

/-- Full smooth principal-bundle Cartan geometry `(P → M, H, 𝔤, 𝔥 ↪ 𝔤, ω, atlas)`, combining
`SmoothCartanGeometry` with a Lie-group structure on `(H, IH)`, a jointly `C³` right action, and a
base-covering atlas of `SmoothPrincipalTrivialization`s. -/
structure SmoothPrincipalCartanGeometry
    (EP EM EH : Type*) [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EH] [NormedSpace ℝ EH]
    (HP HM HH : Type*) [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HH]
    (IP : ModelWithCorners ℝ EP HP) (IM : ModelWithCorners ℝ EM HM)
    (IH : ModelWithCorners ℝ EH HH)
    (P M : Type*) [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    (H : Type*) [Group H] [TopologicalSpace H] [ChartedSpace HH H]
    (𝔤 𝔥 : Type*) [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥] where
  toCartan : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥
  lieGroupH : LieGroup IH (minSmoothness ℝ 3) H
  contMDiff_rightAct_joint :
    ContMDiff (IH.prod IP) IP (minSmoothness ℝ 3)
      (fun hp : H × P => toCartan.rightAct hp.1 hp.2)
  atlas :
    Set (SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      toCartan.proj toCartan.rightAct)
  cover : ∀ x : M, ∃ e ∈ atlas, x ∈ e.toTrivialization.baseSet

/-- A principal Cartan geometry whose isotropy data are tied to the actual Lie-group action.

`SmoothCartanGeometry` is a useful carrier for a pointwise absolute parallelism, but its
`fundamentalVec` and `AdH` fields are abstract inputs. This refinement makes the missing
identifications explicit: `lieAlgAtIdentity` identifies the isotropy Lie algebra with the
tangent space of `H` at the identity; the fundamental vector is the differential of the orbit
map `h ↦ rightAct h p` at the identity; and the action of `H` on `𝔤` restricts along `iotaH` to the
differential of conjugation on `H`. These are the action-compatibility conditions needed to
interpret the stored Cartan form as a Cartan connection on the principal bundle.

This is deliberately a refinement, rather than an assertion that every value of
`SmoothPrincipalCartanGeometry` already satisfies those conditions. It does not add the separate
regularity proof that the pointwise family `p ↦ ωₚ` is a smooth section of `Hom(TP, 𝔤)`. -/
structure ActionCompatibleSmoothPrincipalCartanGeometry
    (EP EM EH : Type*) [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EH] [NormedSpace ℝ EH]
    (HP HM HH : Type*) [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HH]
    (IP : ModelWithCorners ℝ EP HP) (IM : ModelWithCorners ℝ EM HM)
    (IH : ModelWithCorners ℝ EH HH)
    (P M : Type*) [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    (H : Type*) [Group H] [TopologicalSpace H] [ChartedSpace HH H]
    (𝔤 𝔥 : Type*) [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    extends SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥 where
  lieAlgAtIdentity : 𝔥 ≃ₗ[ℝ] TangentSpace IH (1 : H)
  fundamentalVec_is_orbit_derivative : ∀ (A : 𝔥) (p : P),
    toCartan.fundamentalVec A p =
      mfderiv IH IP (fun h : H => toCartan.rightAct h p) 1 (lieAlgAtIdentity A)
  isotropy_inclusion_adjoint_compatible : ∀ (h : H) (A : 𝔥),
    toCartan.AdH h (toCartan.iotaH A) = toCartan.iotaH
      (lieAlgAtIdentity.symm
        (mfderiv IH IH (fun x : H => h * x * h⁻¹) 1 (lieAlgAtIdentity A)))

namespace ActionCompatibleSmoothPrincipalCartanGeometry

variable {EP EM EH : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [NormedAddCommGroup EH] [NormedSpace ℝ EH]
  {HP HM HH : Type*} [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HH]
  {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
  {IH : ModelWithCorners ℝ EH HH}
  {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
  {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]

/-- The Cartan form reproduces the isotropy generator when evaluated on the differential of its
actual principal-action orbit map. -/
theorem omega_orbit_derivative_eq_iotaH
    (C : ActionCompatibleSmoothPrincipalCartanGeometry
      EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥) (A : 𝔥) (p : P) :
    C.toCartan.omega p
        (mfderiv IH IP (fun h : H => C.toCartan.rightAct h p) 1 (C.lieAlgAtIdentity A)) =
      C.toCartan.iotaH A := by
  rw [← C.fundamentalVec_is_orbit_derivative]
  exact C.toCartan.omega_fundamental A p

end ActionCompatibleSmoothPrincipalCartanGeometry

section GenericPrincipalTheorems

variable {EP EM EH : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [NormedAddCommGroup EH] [NormedSpace ℝ EH]
  {HP HM HH : Type*} [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HH]
  {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
  {IH : ModelWithCorners ℝ EH HH}
  {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
  {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]

/-- Smooth local identity section `x ↦ e⁻¹(x, 1)` induced by a principal trivialization `e`. -/
def localPrincipalSection
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    (x : M) : P :=
  e.toTrivialization.toPartialHomeomorph.symm (x, 1)

theorem localPrincipalSection_proj
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {x : M} (hx : x ∈ e.toTrivialization.baseSet) :
    B.toCartan.proj (localPrincipalSection B e x) = x :=
  e.toTrivialization.proj_symm_apply' hx

theorem localPrincipalSection_apply
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {x : M} (hx : x ∈ e.toTrivialization.baseSet) :
    e.toTrivialization (localPrincipalSection B e x) = (x, (1 : H)) :=
  e.toTrivialization.apply_symm_apply' hx

theorem localPrincipalSection_contMDiffOn
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct) :
    ContMDiffOn IM IP (minSmoothness ℝ 3) (localPrincipalSection B e)
      e.toTrivialization.baseSet := by
  have hpair : ContMDiff IM (IM.prod IH) (minSmoothness ℝ 3)
      (fun x : M => (x, (1 : H))) :=
    (contMDiff_id (I := IM) (n := minSmoothness ℝ 3) (M := M)).prodMk
      (contMDiff_const (I := IM) (I' := IH) (c := (1 : H)))
  have hmaps : MapsTo (fun x : M => (x, (1 : H))) e.toTrivialization.baseSet
      e.toTrivialization.target := fun x hx => by
    rw [e.toTrivialization.target_eq]
    exact ⟨hx, Set.mem_univ _⟩
  exact e.contMDiffOn_invFun.comp hpair.contMDiffOn hmaps

/-- Smooth local section passing directly through a prescribed point `p ∈ e.source`. -/
def sectionThrough
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    (p : P) (x : M) : P :=
  B.toCartan.rightAct (e.toTrivialization p).2 (localPrincipalSection B e x)

theorem sectionThrough_proj
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    (p : P) {x : M} (hx : x ∈ e.toTrivialization.baseSet) :
    B.toCartan.proj (sectionThrough B e p x) = x := by
  rw [sectionThrough, B.toCartan.proj_rightAct, localPrincipalSection_proj B e hx]

theorem sectionThrough_self
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {p : P} (hp : p ∈ e.toTrivialization.source) :
    sectionThrough B e p (B.toCartan.proj p) = p := by
  have hx : B.toCartan.proj p ∈ e.toTrivialization.baseSet := e.toTrivialization.mem_source.mp hp
  have hs_mem : localPrincipalSection B e (B.toCartan.proj p) ∈ e.toTrivialization.source := by
    rw [e.toTrivialization.mem_source, localPrincipalSection_proj B e hx]
    exact hx
  have hact_mem : sectionThrough B e p (B.toCartan.proj p) ∈ e.toTrivialization.source := by
    rw [e.toTrivialization.mem_source, sectionThrough_proj B e p hx]
    exact hx
  have heq : e.toTrivialization (sectionThrough B e p (B.toCartan.proj p)) =
      e.toTrivialization p := by
    rw [sectionThrough, e.action_compat _ _ hs_mem, localPrincipalSection_proj B e hx]
    have hloc := congrArg Prod.snd (localPrincipalSection_apply B e hx)
    change (e.toTrivialization (localPrincipalSection B e (B.toCartan.proj p))).2 = (1 : H) at hloc
    rw [hloc, one_mul]
    exact e.toTrivialization.mk_proj_snd hp
  calc
    sectionThrough B e p (B.toCartan.proj p) =
        e.toTrivialization.toPartialEquiv.symm
          (e.toTrivialization (sectionThrough B e p (B.toCartan.proj p))) :=
      (e.toTrivialization.left_inv hact_mem).symm
    _ = e.toTrivialization.toPartialEquiv.symm (e.toTrivialization p) := by rw [heq]
    _ = p := e.toTrivialization.left_inv hp

theorem sectionThrough_contMDiffOn
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    (p : P) :
    ContMDiffOn IM IP (minSmoothness ℝ 3) (sectionThrough B e p)
      e.toTrivialization.baseSet :=
  (B.toCartan.contMDiff_rightAct (e.toTrivialization p).2).comp_contMDiffOn
    (localPrincipalSection_contMDiffOn B e)

/-- Generic fiber torsor theorem derived from the smooth principal atlas: any two points lie in
the same fiber iff they lie in the same right-`H` orbit, with a unique group element. -/
theorem principal_fiber_torsor_existsUnique
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (p q : P) (hbase : B.toCartan.proj p = B.toCartan.proj q) :
    ∃! h : H, B.toCartan.rightAct h p = q :=
  principal_atlas_action_transitive_unique B.toCartan
    (Bundle.Trivialization.toPretrivialization ∘ SmoothPrincipalTrivialization.toTrivialization '' B.atlas)
    (fun r => by
      obtain ⟨e, he, hxr⟩ := B.cover (B.toCartan.proj r)
      exact ⟨e.toTrivialization.toPretrivialization, ⟨e, he, rfl⟩,
        e.toTrivialization.mem_source.mpr hxr⟩)
    (fun _ ⟨e, _, heq⟩ h r hr => by
      subst heq
      exact e.action_compat h r hr)
    p q hbase

theorem principal_same_fiber_iff_orbit
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (p q : P) :
    B.toCartan.proj p = B.toCartan.proj q ↔ ∃ h : H, B.toCartan.rightAct h p = q := by
  constructor
  · intro hbase
    obtain ⟨h, hh, _⟩ := principal_fiber_torsor_existsUnique B p q hbase
    exact ⟨h, hh⟩
  · rintro ⟨h, rfl⟩
    exact (B.toCartan.proj_rightAct h p).symm

/-- Bundle projection of any `SmoothPrincipalCartanGeometry` is surjective. -/
theorem principal_proj_surjective
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥) :
    Function.Surjective B.toCartan.proj := by
  intro x
  obtain ⟨e, _, hx⟩ := B.cover x
  exact ⟨localPrincipalSection B e x, localPrincipalSection_proj B e hx⟩

/-- Bundle projection of any `SmoothPrincipalCartanGeometry` is continuous. -/
theorem principal_proj_continuous
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥) :
    Continuous B.toCartan.proj :=
  B.toCartan.contMDiff_proj.continuous

/-- Bundle projection of any `SmoothPrincipalCartanGeometry` is an open map, proved via smooth local
right-inverse sections on every chart domain. -/
theorem principal_proj_isOpenMap
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥) :
    IsOpenMap B.toCartan.proj := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, hpU, rfl⟩
  obtain ⟨e, _, hx⟩ := B.cover (B.toCartan.proj p)
  have hp_src : p ∈ e.toTrivialization.source := e.toTrivialization.mem_source.mpr hx
  have hcont : ContinuousOn (sectionThrough B e p) e.toTrivialization.baseSet :=
    (sectionThrough_contMDiffOn B e p).continuousOn
  have hcont_at : ContinuousAt (sectionThrough B e p) (B.toCartan.proj p) :=
    hcont.continuousAt (e.toTrivialization.open_baseSet.mem_nhds hx)
  have hmem_self : sectionThrough B e p (B.toCartan.proj p) ∈ U := by
    rw [sectionThrough_self B e hp_src]
    exact hpU
  have hpre : sectionThrough B e p ⁻¹' U ∈ 𝓝 (B.toCartan.proj p) :=
    hcont_at.preimage_mem_nhds (hU.mem_nhds hmem_self)
  have hinter : sectionThrough B e p ⁻¹' U ∩ e.toTrivialization.baseSet ∈ 𝓝 (B.toCartan.proj p) :=
    Filter.inter_mem hpre (e.toTrivialization.open_baseSet.mem_nhds hx)
  refine Filter.mem_of_superset hinter fun y ⟨hyU, hyBase⟩ => ?_
  refine ⟨sectionThrough B e p y, hyU, sectionThrough_proj B e p hyBase⟩

/-- Principal transition map `t_{e₁, e₂}(x) = (e₁(e₂⁻¹(x, 1))).2 ∈ H` on chart overlaps. -/
def principalTransition
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e₁ e₂ : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    (x : M) : H :=
  (e₁.toTrivialization (localPrincipalSection B e₂ x)).2

theorem principalTransition_contMDiffOn
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e₁ e₂ : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct) :
    ContMDiffOn IM IH (minSmoothness ℝ 3) (principalTransition B e₁ e₂)
      (e₁.toTrivialization.baseSet ∩ e₂.toTrivialization.baseSet) := by
  have hsec : ContMDiffOn IM IP (minSmoothness ℝ 3) (localPrincipalSection B e₂)
      (e₁.toTrivialization.baseSet ∩ e₂.toTrivialization.baseSet) :=
    (localPrincipalSection_contMDiffOn B e₂).mono Set.inter_subset_right
  have hmaps : MapsTo (localPrincipalSection B e₂)
      (e₁.toTrivialization.baseSet ∩ e₂.toTrivialization.baseSet)
      e₁.toTrivialization.source := fun x hx => by
    rw [e₁.toTrivialization.mem_source, localPrincipalSection_proj B e₂ hx.2]
    exact hx.1
  have htriv : ContMDiffOn IM (IM.prod IH) (minSmoothness ℝ 3)
      (e₁.toTrivialization ∘ localPrincipalSection B e₂)
      (e₁.toTrivialization.baseSet ∩ e₂.toTrivialization.baseSet) :=
    e₁.contMDiffOn_toFun.comp hsec hmaps
  exact (contMDiff_snd (I := IM) (J := IH)).comp_contMDiffOn htriv

theorem principalTransition_coord_change
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e₁ e₂ : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {p : P} (hp₁ : p ∈ e₁.toTrivialization.source) (hp₂ : p ∈ e₂.toTrivialization.source) :
    (e₁.toTrivialization p).2 =
      principalTransition B e₁ e₂ (B.toCartan.proj p) * (e₂.toTrivialization p).2 := by
  have hx₂ : B.toCartan.proj p ∈ e₂.toTrivialization.baseSet :=
    e₂.toTrivialization.mem_source.mp hp₂
  have hx₁ : B.toCartan.proj p ∈ e₁.toTrivialization.baseSet :=
    e₁.toTrivialization.mem_source.mp hp₁
  have hs₂ : localPrincipalSection B e₂ (B.toCartan.proj p) ∈ e₂.toTrivialization.source := by
    rw [e₂.toTrivialization.mem_source, localPrincipalSection_proj B e₂ hx₂]
    exact hx₂
  have hs₁ : localPrincipalSection B e₂ (B.toCartan.proj p) ∈ e₁.toTrivialization.source := by
    rw [e₁.toTrivialization.mem_source, localPrincipalSection_proj B e₂ hx₂]
    exact hx₁
  have hsec := sectionThrough_self B e₂ hp₂
  have hcomp := congrArg e₁.toTrivialization hsec
  rw [sectionThrough, e₁.action_compat _ _ hs₁] at hcomp
  exact (congrArg Prod.snd hcomp).symm

theorem principalTransition_self
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {x : M} (hx : x ∈ e.toTrivialization.baseSet) :
    principalTransition B e e x = 1 := by
  rw [principalTransition, localPrincipalSection_apply B e hx]

theorem principalTransition_cocycle
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e₁ e₂ e₃ : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {x : M} (hx₁ : x ∈ e₁.toTrivialization.baseSet) (hx₂ : x ∈ e₂.toTrivialization.baseSet)
    (hx₃ : x ∈ e₃.toTrivialization.baseSet) :
    principalTransition B e₁ e₃ x =
      principalTransition B e₁ e₂ x * principalTransition B e₂ e₃ x := by
  let p : P := localPrincipalSection B e₃ x
  have hp₁ : p ∈ e₁.toTrivialization.source := by
    rw [e₁.toTrivialization.mem_source, localPrincipalSection_proj B e₃ hx₃]
    exact hx₁
  have hp₂ : p ∈ e₂.toTrivialization.source := by
    rw [e₂.toTrivialization.mem_source, localPrincipalSection_proj B e₃ hx₃]
    exact hx₂
  have h12 := principalTransition_coord_change B e₁ e₂ hp₁ hp₂
  have hproj : B.toCartan.proj p = x := localPrincipalSection_proj B e₃ hx₃
  rw [hproj] at h12
  exact h12

theorem principalTransition_inv
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e₁ e₂ : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {x : M} (hx₁ : x ∈ e₁.toTrivialization.baseSet) (hx₂ : x ∈ e₂.toTrivialization.baseSet) :
    (principalTransition B e₁ e₂ x)⁻¹ = principalTransition B e₂ e₁ x := by
  apply inv_eq_of_mul_eq_one_right
  rw [← principalTransition_cocycle B e₁ e₂ e₁ hx₁ hx₂ hx₁]
  exact principalTransition_self B e₁ hx₁

private lemma mfderiv_comp_apply_eq_id
    {E₁ E₂ H₁ H₂ M₁ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₁] [TopologicalSpace H₂]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {g : M₂ → M₁} {f : M₁ → M₂} {x : M₁} {y : M₂}
    (hg : MDifferentiableAt I₂ I₁ g y) (hf : MDifferentiableAt I₁ I₂ f x)
    (hy : f x = y) (hev : (g ∘ f) =ᶠ[𝓝 x] id) (w : TangentSpace I₁ x) :
    mfderiv I₂ I₁ g y (mfderiv I₁ I₂ f x w) = w := by
  subst hy
  have hc := mfderiv_comp_apply x hg hf w
  rw [hev.mfderiv_eq, mfderiv_id] at hc
  exact hc.symm

private lemma mfderiv_comp_apply_model
    {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace H₃]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {I₃ : ModelWithCorners ℝ E₃ H₃}
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
    {g : M₂ → M₃} {f : M₁ → M₂} {x : M₁} {y : M₂}
    (hg : MDifferentiableAt I₂ I₃ g y) (hf : MDifferentiableAt I₁ I₂ f x)
    (hy : f x = y) (v : TangentSpace I₁ x) :
    (mfderiv I₁ I₃ (g ∘ f) x v : E₃) = (mfderiv I₂ I₃ g y (mfderiv I₁ I₂ f x v) : E₃) := by
  subst hy
  exact mfderiv_comp_apply x hg hf v

private lemma mfderiv_congr_fun_model
    {E₁ E₂ H₁ H₂ M₁ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₁] [TopologicalSpace H₂]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {φ₁ φ₂ : M₁ → M₂} (h : φ₁ = φ₂) (x : M₁) (v : TangentSpace I₁ x) :
    (mfderiv I₁ I₂ φ₁ x v : E₂) = (mfderiv I₁ I₂ φ₂ x v : E₂) := by
  subst h
  rfl

/-- **Automatic Submersion Theorem**: For ANY `SmoothPrincipalCartanGeometry`, the bundle
projection's manifold derivative `mfderiv IP IM C.proj p` is unconditionally surjective at every
point `p : P`, without requiring any extra `hsubmersion` assumption. -/
theorem principal_mfderiv_proj_surjective
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥) (p : P) :
    Function.Surjective (mfderiv IP IM B.toCartan.proj p).toLinearMap := by
  obtain ⟨e, _, hx⟩ := B.cover (B.toCartan.proj p)
  have hp_src : p ∈ e.toTrivialization.source := e.toTrivialization.mem_source.mpr hx
  have hM : minSmoothness ℝ 3 ≠ 0 := (lt_of_lt_of_le (by simp) le_minSmoothness).ne'
  have hs_at : ContMDiffAt IM IP (minSmoothness ℝ 3) (sectionThrough B e p) (B.toCartan.proj p) :=
    (sectionThrough_contMDiffOn B e p).contMDiffAt (e.toTrivialization.open_baseSet.mem_nhds hx)
  have hs_diff : MDifferentiableAt IM IP (sectionThrough B e p) (B.toCartan.proj p) :=
    hs_at.mdifferentiableAt hM
  have hproj_diff : MDifferentiableAt IP IM B.toCartan.proj p :=
    (B.toCartan.contMDiff_proj p).mdifferentiableAt hM
  have hev : (B.toCartan.proj ∘ sectionThrough B e p) =ᶠ[𝓝 (B.toCartan.proj p)] id := by
    refine Filter.eventually_of_mem (e.toTrivialization.open_baseSet.mem_nhds hx) fun y hy => ?_
    exact sectionThrough_proj B e p hy
  intro w
  exact ⟨mfderiv IM IP (sectionThrough B e p) (B.toCartan.proj p) w,
    mfderiv_comp_apply_eq_id hproj_diff hs_diff (sectionThrough_self B e hp_src) hev w⟩

/-- **Unconditional Cartan Base-Tangent Soldering Equivalence** for every
`SmoothPrincipalCartanGeometry`, eliminating the `hsubmersion` parameter of `cartanBaseTangentEquiv`. -/
noncomputable def principalCartanBaseTangentEquiv
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥) (p : P) :
    TangentSpace IM (B.toCartan.proj p) ≃ₗ[ℝ]
      (𝔤 ⧸ B.toCartan.iotaH.range.toSubmodule) :=
  cartanBaseTangentEquiv B.toCartan p (principal_mfderiv_proj_surjective B p)

/-- Smooth local pullback Cartan gauge potential `A_e(x) = s_e* ω : Tₓ M →L[ℝ] 𝔤`. -/
noncomputable def pullbackCartanGaugePotential
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    (x : M) : TangentSpace IM x →L[ℝ] 𝔤 :=
  (B.toCartan.omega (localPrincipalSection B e x)).toContinuousLinearMap.comp
    (mfderiv IM IP (localPrincipalSection B e) x)

theorem pullbackCartanGaugePotential_spec
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    (x : M) (v : TangentSpace IM x) :
    pullbackCartanGaugePotential B e x v =
      B.toCartan.omega (localPrincipalSection B e x)
        (mfderiv IM IP (localPrincipalSection B e) x v) :=
  rfl

end GenericPrincipalTheorems

/-! ## Concrete Closed Inhabitants (Homothety Principal Bundle & Noncommutative `GL2R`) -/

section HomothetyPrincipalBundle

private lemma contMDiff_ofAdd_multiplicative :
    ContMDiff 𝓘(ℝ, ℝ) multiplicativeRealModel ∞
      (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) := by
  have hrange : Set.range (multiplicativeRealModel : Multiplicative ℝ → ℝ) = Set.univ :=
    Set.range_eq_univ.mpr (Equiv.surjective Multiplicative.toAdd)
  have hsymm := multiplicativeRealModel.contMDiffOn_symm (n := ∞)
  rw [hrange] at hsymm
  exact contMDiffOn_univ.mp hsymm

/-- Genuine `LieGroup` instance on `Multiplicative ℝ` under `multiplicativeRealModel`. -/
theorem multiplicativeRealLieGroup :
    LieGroup multiplicativeRealModel (minSmoothness ℝ 3) (Multiplicative ℝ) where
  contMDiff_mul := by
    have hcomp :
        (fun p : Multiplicative ℝ × Multiplicative ℝ => p.1 * p.2) =
          (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) ∘
            (fun p : Multiplicative ℝ × Multiplicative ℝ =>
              (Multiplicative.toAdd : Multiplicative ℝ → ℝ) p.1 +
                (Multiplicative.toAdd : Multiplicative ℝ → ℝ) p.2) := by
      funext p
      rfl
    rw [hcomp]
    refine (contMDiff_ofAdd_multiplicative.of_le (by simp)).comp ?_
    have h1 : ContMDiff (multiplicativeRealModel.prod multiplicativeRealModel) 𝓘(ℝ, ℝ)
        (minSmoothness ℝ 3)
        (fun p : Multiplicative ℝ × Multiplicative ℝ =>
          (Multiplicative.toAdd : Multiplicative ℝ → ℝ) p.1) :=
      ((multiplicativeRealModel.contMDiff (n := ∞)).of_le (by simp)).comp contMDiff_fst
    have h2 : ContMDiff (multiplicativeRealModel.prod multiplicativeRealModel) 𝓘(ℝ, ℝ)
        (minSmoothness ℝ 3)
        (fun p : Multiplicative ℝ × Multiplicative ℝ =>
          (Multiplicative.toAdd : Multiplicative ℝ → ℝ) p.2) :=
      ((multiplicativeRealModel.contMDiff (n := ∞)).of_le (by simp)).comp contMDiff_snd
    exact h1.add h2
  contMDiff_inv := by
    have hcomp : (fun a : Multiplicative ℝ => a⁻¹) =
        (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) ∘ fun a : Multiplicative ℝ =>
          -((Multiplicative.toAdd : Multiplicative ℝ → ℝ) a) := by
      funext a
      rfl
    rw [hcomp]
    exact (contMDiff_ofAdd_multiplicative.of_le (by simp)).comp
      ((multiplicativeRealModel.contMDiff (n := ∞)).of_le (by simp)).neg

/-- Global smooth principal trivialization for the homothety Cartan bundle `ℝ² × ℝ → ℝ²`. -/
def homothetyPrincipalTrivialization (κ : ℝ) :
    SmoothPrincipalTrivialization
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) ℝ
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) multiplicativeRealModel
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      (homothetyCartanGeometry κ).proj (homothetyCartanGeometry κ).rightAct where
  toTrivialization :=
    { toOpenPartialHomeomorph := homothetyBundleDiffeomorph.toHomeomorph.toOpenPartialHomeomorph
      baseSet := Set.univ
      open_baseSet := isOpen_univ
      source_eq := by ext p; simp
      target_eq := by ext q; simp
      proj_toFun := fun p _ => rfl }
  contMDiffOn_toFun := by
    refine ContMDiff.contMDiffOn ?_
    change ContMDiff 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      ((𝓘(ℝ, Fin 2 → ℝ)).prod multiplicativeRealModel) (minSmoothness ℝ 3)
      (fun p : (Fin 2 → ℝ) × ℝ => (p.1, (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) p.2))
    have hf : ContMDiff 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) (minSmoothness ℝ 3)
        (fun p : (Fin 2 → ℝ) × ℝ => p.1) := contDiff_fst.contMDiff
    have hs : ContMDiff 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) multiplicativeRealModel (minSmoothness ℝ 3)
        (fun p : (Fin 2 → ℝ) × ℝ => (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) p.2) :=
      (contMDiff_ofAdd_multiplicative.of_le (by simp)).comp contDiff_snd.contMDiff
    exact hf.prodMk hs
  contMDiffOn_invFun := by
    refine ContMDiff.contMDiffOn ?_
    change ContMDiff ((𝓘(ℝ, Fin 2 → ℝ)).prod multiplicativeRealModel)
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) (minSmoothness ℝ 3)
      (fun q : (Fin 2 → ℝ) × Multiplicative ℝ =>
        (q.1, (Multiplicative.toAdd : Multiplicative ℝ → ℝ) q.2))
    have hf : ContMDiff ((𝓘(ℝ, Fin 2 → ℝ)).prod multiplicativeRealModel) 𝓘(ℝ, Fin 2 → ℝ)
        (minSmoothness ℝ 3) (fun q : (Fin 2 → ℝ) × Multiplicative ℝ => q.1) := contMDiff_fst
    have hs : ContMDiff ((𝓘(ℝ, Fin 2 → ℝ)).prod multiplicativeRealModel) 𝓘(ℝ, ℝ)
        (minSmoothness ℝ 3) (fun q : (Fin 2 → ℝ) × Multiplicative ℝ =>
          (Multiplicative.toAdd : Multiplicative ℝ → ℝ) q.2) :=
      ((multiplicativeRealModel.contMDiff (n := ∞)).of_le (by simp)).comp contMDiff_snd
    exact hf.prodMk_space hs
  action_compat t p _ := homothetyBundleDiffeomorph_action_compat κ t p

/-- Constructive closed T17 inhabitant for `SmoothPrincipalTrivialization` at `κ = 0`. -/
def flatHomothetyPrincipalTrivialization :
    SmoothPrincipalTrivialization
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) ℝ
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) multiplicativeRealModel
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      (homothetyCartanGeometry 0).proj (homothetyCartanGeometry 0).rightAct :=
  homothetyPrincipalTrivialization 0

/-- Generic `SmoothPrincipalCartanGeometry` package on the homothety family (`κ = 0` flat vs.
`κ ≠ 0` curved). -/
def homothetyPrincipalCartanGeometry (κ : ℝ) :
    SmoothPrincipalCartanGeometry
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) ℝ
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) multiplicativeRealModel
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      HomothetyLieAlg HomothetyH where
  toCartan := homothetyCartanGeometry κ
  lieGroupH := multiplicativeRealLieGroup
  contMDiff_rightAct_joint := by
    change ContMDiff (multiplicativeRealModel.prod 𝓘(ℝ, (Fin 2 → ℝ) × ℝ))
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) (minSmoothness ℝ 3)
      (fun hp : Multiplicative ℝ × ((Fin 2 → ℝ) × ℝ) =>
        (hp.2.1, hp.2.2 + Multiplicative.toAdd hp.1))
    have hfst : ContMDiff (multiplicativeRealModel.prod 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)) 𝓘(ℝ, Fin 2 → ℝ)
        (minSmoothness ℝ 3) (fun hp : Multiplicative ℝ × ((Fin 2 → ℝ) × ℝ) => hp.2.1) :=
      contDiff_fst.contMDiff.comp contMDiff_snd
    have hsnd : ContMDiff (multiplicativeRealModel.prod 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)) 𝓘(ℝ, ℝ)
        (minSmoothness ℝ 3)
        (fun hp : Multiplicative ℝ × ((Fin 2 → ℝ) × ℝ) => hp.2.2 + Multiplicative.toAdd hp.1) :=
      (contDiff_snd.contMDiff.comp contMDiff_snd).add
        ((multiplicativeRealModel.contMDiff.of_le le_top).comp contMDiff_fst)
    exact hfst.prodMk_space hsnd
  atlas := {homothetyPrincipalTrivialization κ}
  cover _ := ⟨homothetyPrincipalTrivialization κ, Set.mem_singleton _, Set.mem_univ _⟩

/-- Constructive closed T17 inhabitant for `SmoothPrincipalCartanGeometry` at `κ = 0`. -/
def flatHomothetyPrincipalCartanGeometry :
    SmoothPrincipalCartanGeometry
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) ℝ
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) multiplicativeRealModel
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) (Multiplicative ℝ)
      HomothetyLieAlg HomothetyH :=
  homothetyPrincipalCartanGeometry 0

end HomothetyPrincipalBundle

section LieGroupPrincipalModel

private def ptZero : Fin 0 → ℝ := fun i => Fin.elim0 i

/-- Adjoint Lie algebra automorphism `Ad_h := d(Conj_h)_1` on any smooth Lie group `G`, proved
to preserve the `GroupLieAlgebra` bracket via Mathlib's `mpullback_mlieBracket`. -/
noncomputable def lieGroupAdEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
    [LieGroup I (minSmoothness ℝ 3) G] (h : G) :
    GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G where
  toLinearMap :=
    { toFun := fun X => (mfderiv I I (fun x : G => h * x * h⁻¹) (1 : G) X : E)
      map_add' := fun u v => by rw [map_add]; rfl
      map_smul' := fun c u => by rw [map_smul]; rfl }
  map_lie' {v w} := by
    have hM : minSmoothness ℝ 3 ≠ 0 := (lt_of_lt_of_le (by simp) le_minSmoothness).ne'
    have hconj_smooth : ∀ g : G, ContMDiff I I (minSmoothness ℝ 3) (fun x : G => g * x * g⁻¹) :=
      fun g => (contMDiff_mul_left.mul contMDiff_const)
    have hconj_inv_smooth :
        ∀ g : G, ContMDiff I I (minSmoothness ℝ 3) (fun x : G => g⁻¹ * x * g) :=
      fun g => (contMDiff_mul_left.mul contMDiff_const)
    have hconj_inverse : ∀ (g a : G),
        (mfderiv I I (fun x : G => g⁻¹ * x * g) a).inverse =
          mfderiv I I (fun x : G => g * x * g⁻¹) (g⁻¹ * a * g) := by
      intro g a
      have hfix : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      have hD1 : mfderiv I I ((fun x : G => g * x * g⁻¹) ∘ (fun x : G => g⁻¹ * x * g)) a =
          ContinuousLinearMap.id ℝ _ := by
        have : (fun x : G => g * x * g⁻¹) ∘ (fun x : G => g⁻¹ * x * g) = id := by
          ext x; dsimp only [Function.comp_apply, id_eq]; group
        rw [this, id_eq, mfderiv_id]
      rw [mfderiv_comp _ ((hconj_smooth g).contMDiffAt.mdifferentiableAt hM)
        ((hconj_inv_smooth g).contMDiffAt.mdifferentiableAt hM)] at hD1
      have hD2 : mfderiv I I ((fun x : G => g⁻¹ * x * g) ∘ (fun x : G => g * x * g⁻¹))
          (g⁻¹ * a * g) = ContinuousLinearMap.id ℝ _ := by
        have : (fun x : G => g⁻¹ * x * g) ∘ (fun x : G => g * x * g⁻¹) = id := by
          ext x; dsimp only [Function.comp_apply, id_eq]; group
        rw [this, id_eq, mfderiv_id]
      rw [mfderiv_comp _ ((hconj_inv_smooth g).contMDiffAt.mdifferentiableAt hM)
        ((hconj_smooth g).contMDiffAt.mdifferentiableAt hM), hfix] at hD2
      exact ContinuousLinearMap.inverse_eq hD2 hD1
    have hconj_inv_pull : ∀ (g : G) (u : GroupLieAlgebra I G),
        VectorField.mpullback I I (fun x : G => g⁻¹ * x * g) (mulInvariantVectorField u) =
          mulInvariantVectorField
            (mfderiv I I (fun x : G => g * x * g⁻¹) (1 : G) u) := by
      intro g u
      ext a
      change ((mfderiv I I (fun x : G => g⁻¹ * x * g) a).inverse
          (mulInvariantVectorField u (g⁻¹ * a * g)) : E) =
        (mulInvariantVectorField (mfderiv I I (fun x : G => g * x * g⁻¹) (1 : G) u) a : E)
      rw [hconj_inverse g a]
      simp only [mulInvariantVectorField]
      have hcomm : (fun x : G => g * x * g⁻¹) ∘ (fun x : G => g⁻¹ * a * g * x) =
          (fun x : G => a * x) ∘ (fun x : G => g * x * g⁻¹) := by
        ext x; dsimp only [Function.comp_apply]; group
      have h1 := mfderiv_comp_apply_model
        ((hconj_smooth g).contMDiffAt.mdifferentiableAt hM)
        (contMDiff_mul_left.contMDiffAt.mdifferentiableAt hM) (by group : g⁻¹ * a * g * 1 = g⁻¹ * a * g) u
      have h2 := mfderiv_comp_apply_model
        ((contMDiff_mul_left (a := a)).contMDiffAt.mdifferentiableAt hM)
        ((hconj_smooth g).contMDiffAt.mdifferentiableAt hM) (by group : g * 1 * g⁻¹ = 1) u
      exact (h1.symm.trans (mfderiv_congr_fun_model hcomm 1 u)).trans h2
    change (mfderiv I I (fun x : G => h * x * h⁻¹) 1
        (VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) 1) : E) =
      (VectorField.mlieBracket I
        (mulInvariantVectorField (mfderiv I I (fun x : G => h * x * h⁻¹) 1 v))
        (mulInvariantVectorField (mfderiv I I (fun x : G => h * x * h⁻¹) 1 w)) 1 : E)
    rw [← hconj_inv_pull h v, ← hconj_inv_pull h w]
    have hid1 : h⁻¹ * (1 : G) * h = 1 := by group
    have hpb := VectorField.mpullback_mlieBracket (I := I) (I' := I)
      (n := minSmoothness ℝ 3)
      (f := fun x : G => h⁻¹ * x * h) (V := mulInvariantVectorField v)
      (W := mulInvariantVectorField w) (x₀ := (1 : G))
      (by simpa [hid1] using mdifferentiableAt_mulInvariantVectorField v)
      (by simpa [hid1] using mdifferentiableAt_mulInvariantVectorField w)
      ((hconj_inv_smooth h).contMDiffAt)
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
    simp only [VectorField.mpullback] at hpb
    rw [hconj_inverse h 1] at hpb
    have hpb_model :
        (mfderiv I I (fun x : G => h * x * h⁻¹) (h⁻¹ * 1 * h)
          (VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w)
            (h⁻¹ * 1 * h)) : E) =
          (VectorField.mlieBracket I
            (VectorField.mpullback I I (fun x : G => h⁻¹ * x * h) (mulInvariantVectorField v))
            (VectorField.mpullback I I (fun x : G => h⁻¹ * x * h) (mulInvariantVectorField w)) 1 : E) :=
      congrArg (fun z : TangentSpace I 1 => (z : E)) hpb
    have hpt :
        (mfderiv I I (fun x : G => h * x * h⁻¹) 1
          (VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) 1) : E) =
        (mfderiv I I (fun x : G => h * x * h⁻¹) (h⁻¹ * 1 * h)
          (VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w)
            (h⁻¹ * 1 * h)) : E) := by
      have hgen : ∀ y : G, y = 1 →
          (mfderiv I I (fun x : G => h * x * h⁻¹) 1
            (VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) 1) : E) =
          (mfderiv I I (fun x : G => h * x * h⁻¹) y
            (VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) y) : E) := by
        intro y hy
        subst hy
        rfl
      exact hgen (h⁻¹ * 1 * h) hid1
    exact hpt.trans hpb_model

private lemma lieGroupAdEquiv_apply
    {E H_mod G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace H_mod] (I : ModelWithCorners ℝ E H_mod)
    [TopologicalSpace G] [ChartedSpace H_mod G] [Group G]
    [LieGroup I (minSmoothness ℝ 3) G] (h : G) (X : GroupLieAlgebra I G) :
    (lieGroupAdEquiv I h X : E) =
      (mfderiv I I (fun x : G => h * x * h⁻¹) 1 X : E) :=
  rfl

/-- Noncommutative principal Cartan bundle `(G → ℝ⁰, G, Lie(G), Lie(G))` over a single-point
base using the canonical Maurer–Cartan form `leftMaurerCartanEquiv`. -/
def lieGroupPrincipalCartanGeometry
    {E H_mod G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace H_mod] (I : ModelWithCorners ℝ E H_mod)
    [TopologicalSpace G] [ChartedSpace H_mod G] [Group G]
    (hLG : LieGroup I (minSmoothness ℝ 3) G) :
    SmoothPrincipalCartanGeometry E (Fin 0 → ℝ) E H_mod (Fin 0 → ℝ) H_mod
      I 𝓘(ℝ, Fin 0 → ℝ) I G (Fin 0 → ℝ) G (GroupLieAlgebra I G) (GroupLieAlgebra I G) where
  toCartan :=
    { smoothP := hLG.toContMDiffMul.toIsManifold
      smoothM := inferInstance
      proj := fun _ => ptZero
      contMDiff_proj := contMDiff_const
      rightAct h g := g * h
      rightAct_one g := mul_one g
      rightAct_mul h₁ h₂ g := (mul_assoc g h₁ h₂).symm
      contMDiff_rightAct h := contMDiff_mul_right
      proj_rightAct _ _ := rfl
      iotaH := LieHom.id
      iotaH_injective _ _ h := h
      AdH := lieGroupAdEquiv I
      AdH_one X := by
        rw [lieGroupAdEquiv_apply]
        have hid : (fun x : G => (1 : G) * x * (1 : G)⁻¹) = id := by ext x; simp
        refine (mfderiv_congr_fun_model hid 1 X).trans ?_
        rw [mfderiv_id]
        rfl
      AdH_mul h₁ h₂ X := by
        rw [lieGroupAdEquiv_apply, lieGroupAdEquiv_apply, lieGroupAdEquiv_apply]
        have hM : minSmoothness ℝ 3 ≠ 0 := (lt_of_lt_of_le (by simp) le_minSmoothness).ne'
        have hcomp : (fun x : G => (h₁ * h₂) * x * (h₁ * h₂)⁻¹) =
            (fun x : G => h₁ * x * h₁⁻¹) ∘ (fun x : G => h₂ * x * h₂⁻¹) := by
          ext x; dsimp only [Function.comp_apply]; group
        refine (mfderiv_congr_fun_model hcomp 1 X).trans ?_
        exact mfderiv_comp_apply_model
          ((contMDiff_mul_left.mul contMDiff_const).contMDiffAt.mdifferentiableAt hM)
          ((contMDiff_mul_left.mul contMDiff_const).contMDiffAt.mdifferentiableAt hM)
          (by group : h₂ * 1 * h₂⁻¹ = 1) X
      fundamentalVec X g := mulInvariantVectorField X g
      mfderiv_proj_fundamentalVec _ _ := by
        funext i
        exact Fin.elim0 i
      omega g := leftMaurerCartanEquiv I g
      omega_fundamental X g := leftMaurerCartanEquiv_mulInvariantVectorField I g X
      omega_equivariant h g v := by
        have hM : minSmoothness ℝ 3 ≠ 0 := (lt_of_lt_of_le (by simp) le_minSmoothness).ne'
        have h1 : (fun x : G => (g * h)⁻¹ * x) ∘ (fun x : G => x * h) =
            (fun x : G => h⁻¹ * x * h⁻¹⁻¹) ∘ (fun x : G => g⁻¹ * x) := by
          ext x; dsimp only [Function.comp_apply]; group
        have hlhs := mfderiv_comp_apply_model
          (g := fun x : G => (g * h)⁻¹ * x) (f := fun x : G => x * h) (y := g * h)
          ((contMDiff_mul_left (a := (g * h)⁻¹)).contMDiffAt.mdifferentiableAt hM)
          ((contMDiff_mul_right (a := h)).contMDiffAt.mdifferentiableAt hM) rfl v
        have hrhs := mfderiv_comp_apply_model
          (g := fun x : G => h⁻¹ * x * h⁻¹⁻¹) (f := fun x : G => g⁻¹ * x) (y := (1 : G))
          ((contMDiff_mul_left.mul contMDiff_const).contMDiffAt.mdifferentiableAt hM)
          ((contMDiff_mul_left (a := g⁻¹)).contMDiffAt.mdifferentiableAt hM) (inv_mul_cancel g) v
        change ((leftMaurerCartanEquiv I (g * h)
            (mfderiv I I (fun x : G => x * h) g v) : GroupLieAlgebra I G) : E) =
          ((lieGroupAdEquiv I h⁻¹ (leftMaurerCartanEquiv I g v) : GroupLieAlgebra I G) : E)
        rw [lieGroupAdEquiv_apply]
        dsimp only [leftMaurerCartanEquiv, ContinuousLinearEquiv.equivOfInverse',
          ContinuousLinearEquiv.equivOfInverse]
        exact (hlhs.symm.trans (mfderiv_congr_fun_model h1 g v)).trans hrhs
      ker_proj_eq_vertical g v := by
        refine ⟨fun _ => ⟨leftMaurerCartanEquiv I g v, rfl⟩, fun _ => ?_⟩
        funext i
        exact Fin.elim0 i }
  lieGroupH := hLG
  contMDiff_rightAct_joint := by
    change ContMDiff (I.prod I) I (minSmoothness ℝ 3) (fun hp : G × G => hp.2 * hp.1)
    exact (contMDiff_mul I (minSmoothness ℝ 3)).comp (contMDiff_snd.prodMk contMDiff_fst)
  atlas :=
    { { toTrivialization :=
          { toFun := fun g => (ptZero, g)
            invFun := Prod.snd
            source := Set.univ
            target := Set.univ ×ˢ Set.univ
            map_source' := fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
            map_target' := fun _ _ => Set.mem_univ _
            left_inv' := fun _ _ => rfl
            right_inv' := fun p _ => Prod.ext (Subsingleton.elim _ _) rfl
            open_source := isOpen_univ
            open_target := isOpen_univ.prod isOpen_univ
            continuousOn_toFun := (continuous_const.prodMk continuous_id).continuousOn
            continuousOn_invFun := continuous_snd.continuousOn
            baseSet := Set.univ
            open_baseSet := isOpen_univ
            source_eq := by ext; simp
            target_eq := rfl
            proj_toFun := fun _ _ => rfl }
        contMDiffOn_toFun := by
          refine ContMDiff.contMDiffOn ?_
          exact (contMDiff_const (I := I) (I' := 𝓘(ℝ, Fin 0 → ℝ)) (c := ptZero)).prodMk
            contMDiff_id
        contMDiffOn_invFun := by
          refine ContMDiff.contMDiffOn ?_
          exact contMDiff_snd
        action_compat := fun _ _ _ => rfl } }
  cover x := by
    refine ⟨_, Set.mem_singleton _, Set.mem_univ x⟩

/-- The Maurer–Cartan principal geometry of a Lie group satisfies the stronger action-compatibility
conditions: its fundamental vectors are differentials of right-action orbits, and its adjoint
action is the differential of conjugation. -/
def actionCompatibleLieGroupPrincipalCartanGeometry
    {E H_mod G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace H_mod] (I : ModelWithCorners ℝ E H_mod)
    [TopologicalSpace G] [ChartedSpace H_mod G] [Group G]
    (hLG : LieGroup I (minSmoothness ℝ 3) G) :
    ActionCompatibleSmoothPrincipalCartanGeometry E (Fin 0 → ℝ) E H_mod (Fin 0 → ℝ)
      H_mod I 𝓘(ℝ, Fin 0 → ℝ) I G (Fin 0 → ℝ) G
      (GroupLieAlgebra I G) (GroupLieAlgebra I G) where
  toSmoothPrincipalCartanGeometry := lieGroupPrincipalCartanGeometry I hLG
  lieAlgAtIdentity := LinearEquiv.refl ℝ _
  fundamentalVec_is_orbit_derivative := by
    intro A p
    rfl
  isotropy_inclusion_adjoint_compatible := by
    intro h A
    change lieGroupAdEquiv I h A = lieGroupAdEquiv I h A
    rfl

/-- Concrete noncommutative principal Cartan bundle `(GL2R → ℝ⁰, GL2R, Lie(GL2R))` (flat via
`gl2R_maurerCartan_flat`). -/
def gl2RPrincipalCartanGeometry :
    SmoothPrincipalCartanGeometry EndR2 (Fin 0 → ℝ) EndR2 EndR2 (Fin 0 → ℝ) EndR2
      𝓘(ℝ, EndR2) 𝓘(ℝ, Fin 0 → ℝ) 𝓘(ℝ, EndR2) GL2R (Fin 0 → ℝ) GL2R
      (GroupLieAlgebra 𝓘(ℝ, EndR2) GL2R) (GroupLieAlgebra 𝓘(ℝ, EndR2) GL2R) :=
  lieGroupPrincipalCartanGeometry 𝓘(ℝ, EndR2) (inferInstance)

/-- Concrete `GL₂(ℝ)` Maurer–Cartan model with the orbit-derivative and conjugation-differential
compatibilities required of a standard principal Cartan connection. -/
def actionCompatibleGL2RPrincipalCartanGeometry :
    ActionCompatibleSmoothPrincipalCartanGeometry EndR2 (Fin 0 → ℝ) EndR2 EndR2
      (Fin 0 → ℝ) EndR2 𝓘(ℝ, EndR2) 𝓘(ℝ, Fin 0 → ℝ) 𝓘(ℝ, EndR2)
      GL2R (Fin 0 → ℝ) GL2R
      (GroupLieAlgebra 𝓘(ℝ, EndR2) GL2R) (GroupLieAlgebra 𝓘(ℝ, EndR2) GL2R) :=
  actionCompatibleLieGroupPrincipalCartanGeometry 𝓘(ℝ, EndR2) (inferInstance)

/-- Noncommutativity witnesses on `EndR2` and `GL2R` inherited via T16. -/
theorem principal_cartan_gl2R_noncommutative :
    shearUpperCLM * shearLowerCLM ≠ shearLowerCLM * shearUpperCLM ∧
      shearUpperGL2 * shearLowerGL2 ≠ shearLowerGL2 * shearUpperGL2 :=
  ⟨shearUpperCLM_mul_shearLowerCLM_ne, shearUpperGL2_mul_shearLowerGL2_ne⟩

end LieGroupPrincipalModel

end SmoothPrincipalInterface

end InfoGeometry.Canonical.SmoothPrincipalCartanBundleClosure
