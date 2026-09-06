import InfoGeometry.Categorical.FibonacciBraiding
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.TriFacetGeometry
import InfoGeometry.Convex.SelfDualCone
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Fibonacci Braided Tower Cone

Theorem-only categorical wiring surface.

This file deliberately avoids introducing a new record wrapper.  The repository
policy is that graph/tooling can navigate carrier-like data, but Lean proof
authority should expose owner theorems directly.  The closed surfaces here
therefore take explicit hypotheses and forward to existing owner theorems:

* mathlib `BraidedCategory.yang_baxter_iso`;
* mathlib/Zorn maximal-chain support;
* `TensorTowerColimit` induction and protection;
* `TriFacetGeometry` projection identities;
* `Convex.SelfDualCone` inner-duality.
-/

universe v u uR uA uInf uE

namespace InfoGeometry.Categorical.FibonacciBraidedTowerCone

open Set
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open InfoGeometry.Canonical.TriFacetGeometry
open InfoGeometry.Convex

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory C]

/-- Mathlib's braided Yang-Baxter coherence specialized to one object. -/
theorem fibonacci_yang_baxter_iso (τ : C) :
    (α_ τ τ τ).symm ≪≫ whiskerRightIso (β_ τ τ) τ ≪≫ α_ τ τ τ ≪≫
      whiskerLeftIso τ (β_ τ τ) ≪≫ (α_ τ τ τ).symm ≪≫
      whiskerRightIso (β_ τ τ) τ ≪≫ α_ τ τ τ =
        whiskerLeftIso τ (β_ τ τ) ≪≫ (α_ τ τ τ).symm ≪≫
          whiskerRightIso (β_ τ τ) τ ≪≫ α_ τ τ τ ≪≫
            whiskerLeftIso τ (β_ τ τ) := by
  simpa using (CategoryTheory.BraidedCategory.yang_baxter_iso τ τ τ)

/-- Mathlib's forward hexagon coherence specialized to one object. -/
theorem fibonacci_hexagon_forward_iso (τ : C) :
    α_ τ τ τ ≪≫ β_ τ (τ ⊗ τ) ≪≫ α_ τ τ τ =
      whiskerRightIso (β_ τ τ) τ ≪≫ α_ τ τ τ ≪≫ whiskerLeftIso τ (β_ τ τ) := by
  simpa using (CategoryTheory.BraidedCategory.hexagon_forward_iso τ τ τ)

/-- Zorn's lemma gives a maximal support in any chain-union-closed family. -/
theorem zorn_maximal_support
    (family : Set (Set ℕ))
    (chain_sUnion_mem : ∀ c ⊆ family, IsChain (· ⊆ ·) c → ⋃₀ c ∈ family)
    (nonempty : family.Nonempty) :
    ∃ M ∈ family, ∀ X ∈ family, M ⊆ X → X = M := by
  rcases nonempty with ⟨x, hx⟩
  rcases zorn_subset_nonempty family
      (fun c hcZ hchain _ =>
        ⟨⋃₀ c, chain_sUnion_mem c hcZ hchain, fun s hs => subset_sUnion_of_mem hs⟩)
      x hx with ⟨M, _hxM, hM⟩
  refine ⟨M, hM.left, ?_⟩
  intro X hXZ hMX
  exact subset_antisymm (hM.right hXZ hMX) hMX

variable {R : Type uR} [CommRing R] [Invertible (2 : R)]
variable {A : ℕ → Type uA} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable {A_inf : Type uInf} [AddCommGroup A_inf] [Module R A_inf]

omit [Invertible (2 : R)] in
/-- Existing tensor-tower induction gives finite cone compatibility along the
successor maps. -/
theorem tower_psi_comp_iota_seq
    (iota : ∀ n, A n →ₗ[R] A (n + 1))
    (psi : ∀ n, A n →ₗ[R] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (n m : ℕ) :
    (psi (n + m)).comp (iota_seq A iota n m) = psi n :=
  psi_comp_iota_seq A iota A_inf psi psi_comm n m

omit [Invertible (2 : R)] in
/-- Stagewise nonvanishing is transported to the target map under the explicit
kernel-lifting property. This wrapper preserves the categorical module's
legacy API; it asserts no topology or universal-property result. -/
theorem protected_state_survives
    (iota : ∀ n, A n →ₗ[R] A (n + 1))
    (psi : ∀ n, A n →ₗ[R] A_inf)
    (colimit_kernel : ∀ (n : ℕ) (x : A n), psi n x = 0 → ∃ m, iota_seq A iota n m x = 0)
    {n : ℕ} {x : A n}
    (h_prot : IsTopologicallyProtected A iota n x) : psi n x ≠ 0 :=
  protected_states_survive_colimit A iota A_inf psi colimit_kernel n x h_prot

/-- The tri-facet operator has the closed three-projector partition. -/
theorem triFacet_partition (T : R) :
    P_hyp T + P_ell T + P_par T = 1 :=
  P_sum T

/-- The hyperbolic tri-facet projector is idempotent under `T³ = T`. -/
theorem triFacet_hyp_idempotent (T : R) (hT : T ^ 3 = T) :
    P_hyp T * P_hyp T = P_hyp T :=
  P_hyp_idem T hT

/-- The elliptic tri-facet projector is idempotent under `T³ = T`. -/
theorem triFacet_ell_idempotent (T : R) (hT : T ^ 3 = T) :
    P_ell T * P_ell T = P_ell T :=
  P_ell_idem T hT

omit [Invertible (2 : R)] in
/-- The parabolic tri-facet projector is idempotent under `T³ = T`. -/
theorem triFacet_par_idempotent (T : R) (hT : T ^ 3 = T) :
    P_par T * P_par T = P_par T :=
  P_par_idem T hT

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A self-dual positive cone is equal to its inner dual. -/
theorem selfDual_positiveCone (K : SelfDualCone E) :
    ProperCone.innerDual (K.cone : Set E) = K.cone :=
  SelfDualCone.innerDual_eq K

end InfoGeometry.Categorical.FibonacciBraidedTowerCone
