/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The actual adjoint square of a closed real partial operator

For a densely defined real operator `S : E →ₗ.[ℝ] F`, the domain is exactly
`{x ∈ dom S | S x ∈ dom S†}`. No whole-range inclusion in the adjoint domain
is assumed. The operator remains on the original Hilbert space `E`.

Closedness of `S` supplies the orthogonal projection to its graph, which proves
surjectivity of `1 + S†S`. Positivity and that surjectivity then give density
and self-adjointness of the actual product operator. The result is applicable
to a real-linear closed Tomita operator after the required owner identification.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealAdjointSquare

open LinearPMap WithLp
open scoped Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The genuine composition domain of `S†S`, as a submodule of the original space. -/
def adjointSquareDomain (S : E →ₗ.[ℝ] F) : Submodule ℝ E :=
  (S.adjoint.domain.comap S.toFun).map S.domain.subtype

theorem mem_adjointSquareDomain (S : E →ₗ.[ℝ] F) (x : E) :
    x ∈ adjointSquareDomain S ↔
      ∃ hx : x ∈ S.domain, S ⟨x, hx⟩ ∈ S.adjoint.domain := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hSx⟩
    exact ⟨⟨x, hx⟩, hSx, rfl⟩

theorem adjointSquareDomain_le (S : E →ₗ.[ℝ] F) : adjointSquareDomain S ≤ S.domain := by
  intro x hx
  exact ((mem_adjointSquareDomain S x).mp hx).choose

/-- The original-domain inclusion, retaining the original ambient vector. -/
def squareDomainInclusion (S : E →ₗ.[ℝ] F) : adjointSquareDomain S →ₗ[ℝ] S.domain :=
  Submodule.inclusion (adjointSquareDomain_le S)

@[simp] theorem squareDomainInclusion_coe (S : E →ₗ.[ℝ] F)
    (x : adjointSquareDomain S) : (squareDomainInclusion S x : E) = (x : E) := rfl

theorem image_mem_adjointDomain (S : E →ₗ.[ℝ] F) (x : adjointSquareDomain S) :
    S (squareDomainInclusion S x) ∈ S.adjoint.domain := by
  obtain ⟨hx, hSx⟩ := (mem_adjointSquareDomain S (x : E)).mp x.property
  exact hSx

/-- `S` restricted to exactly those vectors whose images admit the adjoint. -/
def squareDomainImage (S : E →ₗ.[ℝ] F) : adjointSquareDomain S →ₗ[ℝ] S.adjoint.domain :=
  (S.toFun.comp (squareDomainInclusion S)).codRestrict _ (image_mem_adjointDomain S)

/-- The native partially defined product `S†S`, on the original Hilbert space. -/
def adjointSquare (S : E →ₗ.[ℝ] F) : E →ₗ.[ℝ] E where
  domain := adjointSquareDomain S
  toFun := S.adjoint.toFun.comp (squareDomainImage S)

@[simp] theorem adjointSquare_apply (S : E →ₗ.[ℝ] F) (x : adjointSquareDomain S) :
    adjointSquare S x = S.adjoint (squareDomainImage S x) := rfl

/-- The product's form identity on its true domain and the full original domain. -/
theorem adjointSquare_form (S : E →ₗ.[ℝ] F) (hS : Dense (S.domain : Set E))
    (x : adjointSquareDomain S) (y : S.domain) :
    inner ℝ (adjointSquare S x) (y : E) =
      inner ℝ (S (squareDomainInclusion S x)) (S y) :=
  LinearPMap.adjoint_isFormalAdjoint hS (squareDomainImage S x) y

/-- The adjoint-square quadratic form is the squared norm of the original operator. -/
theorem adjointSquare_quadratic (S : E →ₗ.[ℝ] F) (hS : Dense (S.domain : Set E))
    (x : adjointSquareDomain S) :
    inner ℝ (x : E) (adjointSquare S x) = ‖S (squareDomainInclusion S x)‖ ^ 2 := by
  rw [real_inner_comm]
  exact (adjointSquare_form S hS x (squareDomainInclusion S x)).trans
    (real_inner_self_eq_norm_sq _)

theorem adjointSquare_nonneg (S : E →ₗ.[ℝ] F) (hS : Dense (S.domain : Set E))
    (x : adjointSquareDomain S) : 0 ≤ inner ℝ (x : E) (adjointSquare S x) := by
  rw [adjointSquare_quadratic S hS]
  positivity

/-- Symmetry is derived from the actual adjoint pairing. -/
theorem adjointSquare_symmetric (S : E →ₗ.[ℝ] F) (hS : Dense (S.domain : Set E)) :
    (adjointSquare S).IsFormalAdjoint (adjointSquare S) := by
  intro x y
  calc
    inner ℝ (adjointSquare S x) (y : E) =
        inner ℝ (S (squareDomainInclusion S x)) (S (squareDomainInclusion S y)) :=
      adjointSquare_form S hS x (squareDomainInclusion S y)
    _ = inner ℝ (S (squareDomainInclusion S y)) (S (squareDomainInclusion S x)) :=
      real_inner_comm _ _
    _ = inner ℝ (adjointSquare S y) (x : E) :=
      (adjointSquare_form S hS y (squareDomainInclusion S x)).symm
    _ = inner ℝ (x : E) (adjointSquare S y) := real_inner_comm _ _

/-- The same graph, in the Hilbert direct sum used solely for orthogonal projection. -/
def hilbertGraph (S : E →ₗ.[ℝ] F) : Submodule ℝ (WithLp 2 (E × F)) :=
  S.graph.comap (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap

@[simp] theorem mem_hilbertGraph (S : E →ₗ.[ℝ] F) (z : WithLp 2 (E × F)) :
    z ∈ hilbertGraph S ↔ WithLp.ofLp z ∈ S.graph := Iff.rfl

theorem hilbertGraph_isClosed (S : E →ₗ.[ℝ] F) (hclosed : S.IsClosed) :
    IsClosed (hilbertGraph S : Set (WithLp 2 (E × F))) :=
  hclosed.preimage (WithLp.prod_continuous_ofLp 2 E F)

variable [CompleteSpace F]

/-- Projecting `(z,0)` to the closed graph constructs a solution of
`x + S†S x = z`; surjectivity is not an input certificate. -/
theorem exists_add_adjointSquare_eq (S : E →ₗ.[ℝ] F)
    (hS : Dense (S.domain : Set E)) (hclosed : S.IsClosed) (z : E) :
    ∃ x : adjointSquareDomain S, (x : E) + adjointSquare S x = z := by
  letI : CompleteSpace (hilbertGraph S) := (hilbertGraph_isClosed S hclosed).completeSpace_coe
  let p : hilbertGraph S :=
    (hilbertGraph S).orthogonalProjectionOnto (WithLp.toLp 2 (z, (0 : F)))
  obtain ⟨x, hx⟩ := (S.mem_graph_iff').mp ((mem_hilbertGraph S p).mp p.property)
  have hform (y : S.domain) : inner ℝ (z - (x : E)) (y : E) = inner ℝ (S x) (S y) := by
    have hw : WithLp.toLp 2 ((y : E), S y) ∈ hilbertGraph S := S.mem_graph y
    have h := (hilbertGraph S).starProjection_inner_eq_zero
      (WithLp.toLp 2 (z, (0 : F))) (WithLp.toLp 2 ((y : E), S y)) hw
    change inner ℝ (WithLp.toLp 2 (z, (0 : F)) - (p : WithLp 2 (E × F)))
      (WithLp.toLp 2 ((y : E), S y)) = 0 at h
    change inner ℝ (z - (WithLp.ofLp (p : WithLp 2 (E × F))).1) (y : E) +
      inner ℝ (0 - (WithLp.ofLp (p : WithLp 2 (E × F))).2) (S y) = 0 at h
    rw [← hx] at h
    simp only [Prod.fst, Prod.snd, zero_sub, inner_neg_left] at h
    linarith
  have hxadj : S x ∈ S.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨z - (x : E), hform⟩
  have hxd : (x : E) ∈ adjointSquareDomain S :=
    (mem_adjointSquareDomain S (x : E)).mpr ⟨x.property, hxadj⟩
  have hvalue : adjointSquare S ⟨(x : E), hxd⟩ = z - (x : E) := by
    apply LinearPMap.adjoint_apply_eq hS
    exact hform
  refine ⟨⟨(x : E), hxd⟩, ?_⟩
  change (x : E) + S.adjoint (squareDomainImage S ⟨(x : E), hxd⟩) = z
  change S.adjoint (squareDomainImage S ⟨(x : E), hxd⟩) = z - (x : E) at hvalue
  rw [hvalue]
  abel

/-- The true composition domain is dense for a densely defined closed operator. -/
theorem adjointSquare_dense_domain (S : E →ₗ.[ℝ] F)
    (hS : Dense (S.domain : Set E)) (hclosed : S.IsClosed) :
    Dense (adjointSquareDomain S : Set E) := by
  have horth : (adjointSquareDomain S)ᗮ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    change z = 0
    obtain ⟨x, hx⟩ := exists_add_adjointSquare_eq S hS hclosed z
    have hx' : (x : E) + S.adjoint (squareDomainImage S x) = z := hx
    have hquad : inner ℝ (x : E) (S.adjoint (squareDomainImage S x)) =
        ‖S (squareDomainInclusion S x)‖ ^ 2 := adjointSquare_quadratic S hS x
    have hi : inner ℝ (x : E) z = 0 := hz (x : E) x.property
    rw [← hx', inner_add_right, real_inner_self_eq_norm_sq, hquad] at hi
    have hx0 : (x : E) = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖S (squareDomainInclusion S x)‖, norm_nonneg (x : E)]
    have hxzero : x = 0 := Subtype.ext hx0
    simpa only [hxzero, Submodule.coe_zero, _root_.map_zero, LinearPMap.map_zero, add_zero]
      using hx'.symm
  rw [dense_iff_closure_eq]
  change ((adjointSquareDomain S).topologicalClosure : Set E) = Set.univ
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  rfl

/-- A symmetric densely defined real operator with surjective `1+A` is
self-adjoint. This lemma supplies no density or surjectivity by fiat in its
application to `S†S`: both are proved above. -/
theorem isSelfAdjoint_of_symmetric_of_one_add_surjective (A : E →ₗ.[ℝ] E)
    (hA : Dense (A.domain : Set E)) (hsym : A.IsFormalAdjoint A)
    (honto : ∀ z : E, ∃ x : A.domain, (x : E) + A x = z) : IsSelfAdjoint A := by
  have hle : A ≤ A.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hA hsym
  have hrev : A.adjoint.domain ≤ A.domain := by
    intro y hy
    let yA : A.adjoint.domain := ⟨y, hy⟩
    obtain ⟨x, hx⟩ := honto (y + A.adjoint yA)
    let xA : A.adjoint.domain := Submodule.inclusion hle.1 x
    have hxA : A.adjoint xA = A x := (hle.2 (x := x) (y := xA) rfl).symm
    let w : A.adjoint.domain := yA - xA
    have hw : (w : E) + A.adjoint w = 0 := by
      change y - (x : E) + A.adjoint (yA - xA) = 0
      rw [LinearPMap.map_sub, hxA]
      have hx' : (x : E) + A x = y + A.adjoint yA := hx
      calc
        y - (x : E) + (A.adjoint yA - A x) =
            (y + A.adjoint yA) - ((x : E) + A x) := by abel
        _ = 0 := by rw [hx']; simp
    obtain ⟨v, hv⟩ := honto (w : E)
    have hzero : inner ℝ (w : E) (w : E) = 0 := by
      calc
        inner ℝ (w : E) (w : E) = inner ℝ (w : E) ((v : E) + A v) := by rw [hv]
        _ = inner ℝ ((w : E) + A.adjoint w) (v : E) := by
          rw [inner_add_right, inner_add_left, LinearPMap.adjoint_isFormalAdjoint hA w v]
        _ = 0 := by rw [hw, inner_zero_left]
    have hwzero : (w : E) = 0 := (inner_self_eq_zero).mp hzero
    have hyx : y = (x : E) := sub_eq_zero.mp hwzero
    rw [hyx]
    exact x.property
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.ext (le_antisymm hrev hle.1)
  intro x hxadj hx
  exact (hle.2 (x := ⟨x, hx⟩) (y := ⟨x, hxadj⟩) rfl).symm

/-- The native adjoint square of every closed densely defined real operator
is positive and self-adjoint on its actual composition domain. -/
theorem adjointSquare_isSelfAdjoint (S : E →ₗ.[ℝ] F)
    (hS : Dense (S.domain : Set E)) (hclosed : S.IsClosed) :
    IsSelfAdjoint (adjointSquare S) :=
  isSelfAdjoint_of_symmetric_of_one_add_surjective (adjointSquare S)
    (adjointSquare_dense_domain S hS hclosed) (adjointSquare_symmetric S hS)
    (exists_add_adjointSquare_eq S hS hclosed)

theorem adjointSquare_isClosed (S : E →ₗ.[ℝ] F)
    (hS : Dense (S.domain : Set E)) (hclosed : S.IsClosed) :
    (adjointSquare S).IsClosed := (adjointSquare_isSelfAdjoint S hS hclosed).isClosed

end InfoGeometry.OperatorAlgebra.RealAdjointSquare
