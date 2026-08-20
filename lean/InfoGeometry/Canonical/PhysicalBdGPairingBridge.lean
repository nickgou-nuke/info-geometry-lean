import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Physical BdG pairing bridge

A native bounded-operator realization of a Bogoliubov--de Gennes block
Hamiltonian on the Hilbert direct sum

`WithLp 2 (H × H)`.

The raw `2 × 2` blocks are assembled with Mathlib's
`ContinuousLinearMap.prod` and `ContinuousLinearMap.coprod`, then transported
through `WithLp.prodContinuousLinearEquiv` to the genuine `L²` product.  This
avoids treating the ordinary product norm on `H × H` as a Hilbert norm.

The closed theorem surface contains:

* exact extraction of all four operator blocks;
* the adjoint formula and self-adjointness when `h† = h`;
* a complex-linear sheet-swap/chiral anticommutation proxy;
* genuine antiunitary particle--hole covariance from a supplied native
  `LinearIsometryEquiv` real structure;
* genuine bounded inverses witnessed by `ContinuousLinearEquiv`;
* the zero-energy Schur complement together with its graph-reduction theorem;
* the spectral-parameter Schur complement for `H_BdG - E`;
* kernel equivalences on the corresponding Schur graphs.

The linear sheet-swap section is deliberately kept separate from physical
particle--hole symmetry.  The antiunitary section uses an explicitly supplied
native conjugate-linear isometric involution; it does not postulate a canonical
real structure on an arbitrary Hilbert space.  No Zorn carrier or
Zorn-to-operator intertwiner is introduced here.
-/

noncomputable section

open scoped InnerProductSpace
open ContinuousLinearMap

namespace PhysicalBdGPairingBridge

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H
local notation "RawNambuH" => H × H
local notation "RawEndNambu" => RawNambuH →L[ℂ] RawNambuH
local notation "NambuH" => WithLp 2 (H × H)
local notation "EndNambu" => NambuH →L[ℂ] NambuH

/-! ## 1. The native Hilbert direct sum -/

/-- The canonical continuous linear equivalence from the `L²` product to the
ordinary product carrier. -/
noncomputable def nambuEquiv : NambuH ≃L[ℂ] RawNambuH :=
  WithLp.prodContinuousLinearEquiv 2 ℂ H H

/-- Constructor for a Nambu vector. -/
def nambuMk (u v : H) : NambuH :=
  WithLp.toLp 2 (u, v)

/-- Particle-sector projection. -/
def nambuFst : NambuH →L[ℂ] H :=
  WithLp.fstL 2 ℂ H H

/-- Hole-sector projection. -/
def nambuSnd : NambuH →L[ℂ] H :=
  WithLp.sndL 2 ℂ H H

/-- Particle-sector inclusion. -/
noncomputable def nambuInl : H →L[ℂ] NambuH :=
  (nambuEquiv (H := H)).symm.toContinuousLinearMap.comp
    (inl ℂ H H)

/-- Hole-sector inclusion. -/
noncomputable def nambuInr : H →L[ℂ] NambuH :=
  (nambuEquiv (H := H)).symm.toContinuousLinearMap.comp
    (inr ℂ H H)

/-- Package two maps with common domain as an `L²`-Nambu-valued map. -/
noncomputable def nambuPairMap (f g : EndH) : H →L[ℂ] NambuH :=
  (nambuEquiv (H := H)).symm.toContinuousLinearMap.comp (f.prod g)

@[simp] theorem nambuMk_fst (u v : H) :
    (nambuMk u v).fst = u :=
  rfl

@[simp] theorem nambuMk_snd (u v : H) :
    (nambuMk u v).snd = v :=
  rfl

@[simp] theorem nambuFst_apply (x : NambuH) :
    nambuFst x = x.fst :=
  rfl

@[simp] theorem nambuSnd_apply (x : NambuH) :
    nambuSnd x = x.snd :=
  rfl

@[simp] theorem nambuInl_apply (u : H) :
    nambuInl u = nambuMk u 0 :=
  rfl

@[simp] theorem nambuInr_apply (v : H) :
    nambuInr v = nambuMk 0 v :=
  rfl

@[simp] theorem nambuPairMap_apply (f g : EndH) (x : H) :
    nambuPairMap f g x = nambuMk (f x) (g x) :=
  rfl

/-- Extensionality through the two Nambu components. -/
theorem nambu_ext {x y : NambuH}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  apply (nambuEquiv (H := H)).injective
  change (x.fst, x.snd) = (y.fst, y.snd)
  exact Prod.ext hfst hsnd

/-- The `L²`-Nambu inner product is the sum of the two sector inner products. -/
@[simp] theorem nambu_inner (x y : NambuH) :
    inner ℂ x y = inner ℂ x.fst y.fst + inner ℂ x.snd y.snd := by
  simpa using (WithLp.prod_inner_apply x y)

/-! ## 2. Generic native block calculus -/

/-- Raw `2 × 2` block operator assembled with native product/coproduct maps. -/
def rawBlockOperator (A B C D : EndH) : RawEndNambu :=
  (A.coprod B).prod (C.coprod D)

/-- The same block operator transported to the genuine Hilbert direct sum. -/
noncomputable def blockOperator (A B C D : EndH) : EndNambu :=
  (nambuEquiv (H := H)).symm.toContinuousLinearMap.comp
    ((rawBlockOperator A B C D).comp
      (nambuEquiv (H := H)).toContinuousLinearMap)

@[simp] theorem rawBlockOperator_apply
    (A B C D : EndH) (u v : H) :
    rawBlockOperator A B C D (u, v) =
      (A u + B v, C u + D v) :=
  rfl

@[simp] theorem blockOperator_fst
    (A B C D : EndH) (x : NambuH) :
    (blockOperator A B C D x).fst = A x.fst + B x.snd :=
  rfl

@[simp] theorem blockOperator_snd
    (A B C D : EndH) (x : NambuH) :
    (blockOperator A B C D x).snd = C x.fst + D x.snd :=
  rfl

@[simp] theorem blockOperator_apply
    (A B C D : EndH) (u v : H) :
    blockOperator A B C D (nambuMk u v) =
      nambuMk (A u + B v) (C u + D v) :=
  rfl

/-- Upper-left block `[1,1]`. -/
def block11 (T : EndNambu) : EndH :=
  nambuFst.comp (T.comp nambuInl)

/-- Upper-right block `[1,2]`. -/
def block12 (T : EndNambu) : EndH :=
  nambuFst.comp (T.comp nambuInr)

/-- Lower-left block `[2,1]`. -/
def block21 (T : EndNambu) : EndH :=
  nambuSnd.comp (T.comp nambuInl)

/-- Lower-right block `[2,2]`. -/
def block22 (T : EndNambu) : EndH :=
  nambuSnd.comp (T.comp nambuInr)

@[simp] theorem block11_blockOperator (A B C D : EndH) :
    block11 (blockOperator A B C D) = A := by
  ext u
  simp [block11, comp_apply]

@[simp] theorem block12_blockOperator (A B C D : EndH) :
    block12 (blockOperator A B C D) = B := by
  ext v
  simp [block12, comp_apply]

@[simp] theorem block21_blockOperator (A B C D : EndH) :
    block21 (blockOperator A B C D) = C := by
  ext u
  simp [block21, comp_apply]

@[simp] theorem block22_blockOperator (A B C D : EndH) :
    block22 (blockOperator A B C D) = D := by
  ext v
  simp [block22, comp_apply]

/-- Native adjoint of a `2 × 2` bounded block operator. -/
theorem adjoint_blockOperator (A B C D : EndH) :
    adjoint (blockOperator A B C D) =
      blockOperator (adjoint A) (adjoint C) (adjoint B) (adjoint D) := by
  symm
  apply (eq_adjoint_iff
    (blockOperator (adjoint A) (adjoint C) (adjoint B) (adjoint D))
    (blockOperator A B C D)).2
  intro x y
  rw [nambu_inner, nambu_inner]
  change
    inner ℂ (adjoint A x.fst + adjoint C x.snd) y.fst +
        inner ℂ (adjoint B x.fst + adjoint D x.snd) y.snd =
      inner ℂ x.fst (A y.fst + B y.snd) +
        inner ℂ x.snd (C y.fst + D y.snd)
  rw [inner_add_left, inner_add_left, inner_add_right, inner_add_right]
  rw [adjoint_inner_left, adjoint_inner_left,
    adjoint_inner_left, adjoint_inner_left]
  ring

/-! ## 3. Physical bounded BdG block operator -/

/-- Hole-sector diagonal block `-h†`. -/
noncomputable def holeBlock (h : EndH) : EndH :=
  -(adjoint h)

/-- Raw product-coordinate form of the BdG block operator. -/
noncomputable def rawH_BdG (h Δ : EndH) : RawEndNambu :=
  rawBlockOperator h Δ (adjoint Δ) (holeBlock h)

@[simp] theorem rawH_BdG_apply (h Δ : EndH) (u v : H) :
    rawH_BdG h Δ (u, v) =
      (h u + Δ v, adjoint Δ u - adjoint h v) := by
  simp [rawH_BdG, holeBlock]

/--
Bounded Bogoliubov--de Gennes operator on the genuine Hilbert direct sum

`H_BdG = [[h, Δ], [Δ†, -h†]]`.
-/
noncomputable def H_BdG (h Δ : EndH) : EndNambu :=
  blockOperator h Δ (adjoint Δ) (holeBlock h)

/-- `H_BdG` is the `L²` transport of the raw product-coordinate block. -/
theorem H_BdG_eq_transport_raw (h Δ : EndH) :
    H_BdG h Δ =
      (nambuEquiv (H := H)).symm.toContinuousLinearMap.comp
        ((rawH_BdG h Δ).comp
          (nambuEquiv (H := H)).toContinuousLinearMap) := by
  rfl

@[simp] theorem H_BdG_fst (h Δ : EndH) (x : NambuH) :
    (H_BdG h Δ x).fst = h x.fst + Δ x.snd :=
  rfl

@[simp] theorem H_BdG_snd (h Δ : EndH) (x : NambuH) :
    (H_BdG h Δ x).snd = adjoint Δ x.fst - adjoint h x.snd := by
  simp [H_BdG, holeBlock]

@[simp] theorem H_BdG_apply (h Δ : EndH) (u v : H) :
    H_BdG h Δ (nambuMk u v) =
      nambuMk (h u + Δ v) (adjoint Δ u - adjoint h v) := by
  apply nambu_ext <;> simp [H_BdG, holeBlock]

@[simp] theorem block11_H_BdG (h Δ : EndH) :
    block11 (H_BdG h Δ) = h := by
  simp [H_BdG]

@[simp] theorem block12_H_BdG (h Δ : EndH) :
    block12 (H_BdG h Δ) = Δ := by
  simp [H_BdG]

@[simp] theorem block21_H_BdG (h Δ : EndH) :
    block21 (H_BdG h Δ) = adjoint Δ := by
  simp [H_BdG]

@[simp] theorem block22_H_BdG (h Δ : EndH) :
    block22 (H_BdG h Δ) = holeBlock h := by
  simp [H_BdG]

/-- The upper-right inter-sheet block is exactly the pairing operator. -/
@[simp] theorem upperRightBlock_eq_pairing (h Δ : EndH) :
    block12 (H_BdG h Δ) = Δ :=
  block12_H_BdG h Δ

/-- Compatibility alias.  No Zorn realization is asserted by this theorem. -/
@[simp] theorem xi_eq_delta_sc (h Δ : EndH) :
    block12 (H_BdG h Δ) = Δ :=
  upperRightBlock_eq_pairing h Δ

/-- Exact adjoint formula for the bounded BdG operator. -/
theorem adjoint_H_BdG (h Δ : EndH) :
    adjoint (H_BdG h Δ) = H_BdG (adjoint h) Δ := by
  simpa [H_BdG, holeBlock] using
    (adjoint_blockOperator h Δ (adjoint Δ) (holeBlock h))

/-- Self-adjointness requires only self-adjoint normal dynamics; the pairing
blocks were installed as `Δ` and `Δ†` by construction. -/
theorem H_BdG_selfAdjoint
    (h Δ : EndH) (hh : adjoint h = h) :
    adjoint (H_BdG h Δ) = H_BdG h Δ := by
  rw [adjoint_H_BdG, hh]

/-- Predicate form of bounded BdG self-adjointness. -/
theorem H_BdG_isSelfAdjoint
    (h Δ : EndH) (hh : adjoint h = h) :
    IsSelfAdjoint (H_BdG h Δ) := by
  show adjoint (H_BdG h Δ) = H_BdG h Δ
  exact H_BdG_selfAdjoint h Δ hh

/-! ## 4. Complex-linear sheet-swap/chiral symmetry proxy -/

/-- Complex-linear Nambu sheet swap with an internal linear map `C₀`. -/
noncomputable def linearSheetSwap (C₀ : EndH) : EndNambu :=
  blockOperator 0 C₀ C₀ 0

/-- Legacy name retained for compatibility.  This is complex-linear, not an
antiunitary physical particle-hole operator. -/
noncomputable abbrev PHS_operator (C₀ : EndH) : EndNambu :=
  linearSheetSwap C₀

@[simp] theorem linearSheetSwap_fst (C₀ : EndH) (x : NambuH) :
    (linearSheetSwap C₀ x).fst = C₀ x.snd := by
  simp [linearSheetSwap]

@[simp] theorem linearSheetSwap_snd (C₀ : EndH) (x : NambuH) :
    (linearSheetSwap C₀ x).snd = C₀ x.fst := by
  simp [linearSheetSwap]

@[simp] theorem linearSheetSwap_apply (C₀ : EndH) (u v : H) :
    linearSheetSwap C₀ (nambuMk u v) = nambuMk (C₀ v) (C₀ u) := by
  apply nambu_ext <;> simp

@[simp] theorem PHS_operator_apply (C₀ : EndH) (u v : H) :
    PHS_operator C₀ (nambuMk u v) = nambuMk (C₀ v) (C₀ u) := by
  exact linearSheetSwap_apply C₀ u v

/-- An involutive internal map gives an involutive linear sheet swap. -/
theorem linearSheetSwap_sq
    (C₀ : EndH)
    (hC : C₀.comp C₀ = id ℂ H) :
    (linearSheetSwap C₀).comp (linearSheetSwap C₀) = id ℂ NambuH := by
  apply ContinuousLinearMap.ext
  intro x
  have hfst : C₀ (C₀ x.fst) = x.fst := by
    have hx := congrArg (fun T : EndH => T x.fst) hC
    simpa [comp_apply] using hx
  have hsnd : C₀ (C₀ x.snd) = x.snd := by
    have hx := congrArg (fun T : EndH => T x.snd) hC
    simpa [comp_apply] using hx
  apply nambu_ext
  · simpa [comp_apply] using hfst
  · simpa [comp_apply] using hsnd

/--
Complex-linear BdG anticommutation:
`C H_BdG = -H_BdG C`.

The four hypotheses are the component intertwining relations. -/
theorem bdg_linearSheetSwap_anticommutes
    (h Δ C₀ : EndH)
    (h_comm1 : C₀.comp (adjoint h) = h.comp C₀)
    (h_anti1 : C₀.comp (adjoint Δ) = -(Δ.comp C₀))
    (h_comm2 : C₀.comp h = (adjoint h).comp C₀)
    (h_anti2 : C₀.comp Δ = -((adjoint Δ).comp C₀)) :
    (linearSheetSwap C₀).comp (H_BdG h Δ) =
      (-H_BdG h Δ).comp (linearSheetSwap C₀) := by
  have h1 (u : H) : C₀ (adjoint Δ u) = -Δ (C₀ u) := by
    have hu := congrArg (fun T : EndH => T u) h_anti1
    simpa [comp_apply] using hu
  have h2 (v : H) : C₀ (adjoint h v) = h (C₀ v) := by
    have hv := congrArg (fun T : EndH => T v) h_comm1
    simpa [comp_apply] using hv
  have h3 (u : H) : C₀ (h u) = adjoint h (C₀ u) := by
    have hu := congrArg (fun T : EndH => T u) h_comm2
    simpa [comp_apply] using hu
  have h4 (v : H) : C₀ (Δ v) = -adjoint Δ (C₀ v) := by
    have hv := congrArg (fun T : EndH => T v) h_anti2
    simpa [comp_apply] using hv
  apply ContinuousLinearMap.ext
  intro x
  apply nambu_ext
  · change
      C₀ (adjoint Δ x.fst - adjoint h x.snd) =
        -(h (C₀ x.snd) + Δ (C₀ x.fst))
    rw [map_sub, h1 x.fst, h2 x.snd]
    abel
  · change
      C₀ (h x.fst + Δ x.snd) =
        -(adjoint Δ (C₀ x.snd) - adjoint h (C₀ x.fst))
    rw [map_add, h3 x.fst, h4 x.snd]
    abel

/-- Legacy theorem name retained for compatibility. -/
theorem bdg_particle_hole_symmetry
    (h Δ C₀ : EndH)
    (h_comm1 : C₀.comp (adjoint h) = h.comp C₀)
    (h_anti1 : C₀.comp (adjoint Δ) = -(Δ.comp C₀))
    (h_comm2 : C₀.comp h = (adjoint h).comp C₀)
    (h_anti2 : C₀.comp Δ = -((adjoint Δ).comp C₀)) :
    (PHS_operator C₀).comp (H_BdG h Δ) =
      (-H_BdG h Δ).comp (PHS_operator C₀) := by
  exact bdg_linearSheetSwap_anticommutes h Δ C₀
    h_comm1 h_anti1 h_comm2 h_anti2

/-- Canonical linear-swap specialization. -/
theorem bdg_swap_particle_hole_symmetry
    (h Δ : EndH)
    (hh : adjoint h = h)
    (hΔ : adjoint Δ = -Δ) :
    (PHS_operator (id ℂ H)).comp (H_BdG h Δ) =
      (-H_BdG h Δ).comp (PHS_operator (id ℂ H)) := by
  apply bdg_particle_hole_symmetry h Δ (id ℂ H)
  · simp [hh]
  · simp [hΔ]
  · simp [hh]
  · simp [hΔ]

/-! ## 5. Genuine antiunitary particle--hole structure -/

/-- A chosen antiunitary real structure on the one-particle Hilbert space. -/
structure AntiunitaryRealStructure
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  conjugation : H ≃ₗᵢ⋆[ℂ] H
  involutive : Function.Involutive conjugation

/-- Antiunitary Nambu sheet swap induced by a one-particle real structure. -/
def antiunitarySheetSwap
    (R : AntiunitaryRealStructure H) (x : NambuH) : NambuH :=
  nambuMk (R.conjugation x.snd) (R.conjugation x.fst)

@[simp] theorem antiunitarySheetSwap_fst
    (R : AntiunitaryRealStructure H) (x : NambuH) :
    (antiunitarySheetSwap R x).fst = R.conjugation x.snd :=
  rfl

@[simp] theorem antiunitarySheetSwap_snd
    (R : AntiunitaryRealStructure H) (x : NambuH) :
    (antiunitarySheetSwap R x).snd = R.conjugation x.fst :=
  rfl

/-- The Nambu sheet swap is additive. -/
theorem antiunitarySheetSwap_add
    (R : AntiunitaryRealStructure H) (x y : NambuH) :
    antiunitarySheetSwap R (x + y) =
      antiunitarySheetSwap R x + antiunitarySheetSwap R y := by
  apply nambu_ext
  · change R.conjugation (x.snd + y.snd) =
      R.conjugation x.snd + R.conjugation y.snd
    exact map_add R.conjugation x.snd y.snd
  · change R.conjugation (x.fst + y.fst) =
      R.conjugation x.fst + R.conjugation y.fst
    exact map_add R.conjugation x.fst y.fst

/-- The Nambu sheet swap is conjugate-linear. -/
theorem antiunitarySheetSwap_smul
    (R : AntiunitaryRealStructure H) (c : ℂ) (x : NambuH) :
    antiunitarySheetSwap R (c • x) =
      star c • antiunitarySheetSwap R x := by
  apply nambu_ext
  · change R.conjugation (c • x.snd) =
      star c • R.conjugation x.snd
    exact R.conjugation.map_smulₛₗ c x.snd
  · change R.conjugation (c • x.fst) =
      star c • R.conjugation x.fst
    exact R.conjugation.map_smulₛₗ c x.fst

/-- The antiunitary Nambu swap is norm-preserving. -/
theorem antiunitarySheetSwap_norm
    (R : AntiunitaryRealStructure H) (x : NambuH) :
    ‖antiunitarySheetSwap R x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  simp [antiunitarySheetSwap, LinearIsometryEquiv.norm_map, add_comm]

/-- The antiunitary Nambu swap is involutive. -/
theorem antiunitarySheetSwap_involutive
    (R : AntiunitaryRealStructure H) :
    Function.Involutive (antiunitarySheetSwap R) := by
  intro x
  apply nambu_ext
  · change R.conjugation (R.conjugation x.fst) = x.fst
    exact R.involutive x.fst
  · change R.conjugation (R.conjugation x.snd) = x.snd
    exact R.involutive x.snd

/-- Hence the antiunitary Nambu swap is bijective. -/
theorem antiunitarySheetSwap_bijective
    (R : AntiunitaryRealStructure H) :
    Function.Bijective (antiunitarySheetSwap R) :=
  (antiunitarySheetSwap_involutive R).bijective

/-- The physical Nambu sheet swap bundled as a native conjugate-linear
isometry. -/
noncomputable def antiunitarySheetSwapL
    (R : AntiunitaryRealStructure H) :
    NambuH →ₗᵢ⋆[ℂ] NambuH where
  toFun := antiunitarySheetSwap R
  map_add' := antiunitarySheetSwap_add R
  map_smul' := by
    intro c x
    simpa only [starRingEnd_apply] using
      (antiunitarySheetSwap_smul R c x)
  norm_map' := antiunitarySheetSwap_norm R

@[simp] theorem antiunitarySheetSwapL_apply
    (R : AntiunitaryRealStructure H) (x : NambuH) :
    antiunitarySheetSwapL R x = antiunitarySheetSwap R x :=
  rfl

/-- The physical Nambu sheet swap bundled as a native antiunitary equivalence. -/
noncomputable def antiunitarySheetSwapEquiv
    (R : AntiunitaryRealStructure H) :
    NambuH ≃ₗᵢ⋆[ℂ] NambuH :=
  LinearIsometryEquiv.ofSurjective
    (antiunitarySheetSwapL R)
    (by
      intro y
      refine ⟨antiunitarySheetSwap R y, ?_⟩
      simpa using (antiunitarySheetSwap_involutive R y))

@[simp] theorem antiunitarySheetSwapEquiv_apply
    (R : AntiunitaryRealStructure H) (x : NambuH) :
    antiunitarySheetSwapEquiv R x = antiunitarySheetSwap R x :=
  rfl

@[simp] theorem antiunitarySheetSwapEquiv_involutive
    (R : AntiunitaryRealStructure H) (x : NambuH) :
    antiunitarySheetSwapEquiv R (antiunitarySheetSwapEquiv R x) = x := by
  simpa using (antiunitarySheetSwap_involutive R x)

/--
Genuine antiunitary BdG particle--hole covariance, stated pointwise because the
left- and right-hand sides are conjugate-linear maps.
-/
theorem bdg_antiunitary_particle_hole_symmetry
    (h Δ : EndH)
    (R : AntiunitaryRealStructure H)
    (h_comm1 : ∀ v : H,
      R.conjugation (adjoint h v) = h (R.conjugation v))
    (h_anti1 : ∀ u : H,
      R.conjugation (adjoint Δ u) = -Δ (R.conjugation u))
    (h_comm2 : ∀ u : H,
      R.conjugation (h u) = adjoint h (R.conjugation u))
    (h_anti2 : ∀ v : H,
      R.conjugation (Δ v) = -adjoint Δ (R.conjugation v))
    (x : NambuH) :
    antiunitarySheetSwap R (H_BdG h Δ x) =
      -(H_BdG h Δ (antiunitarySheetSwap R x)) := by
  apply nambu_ext
  · change
      R.conjugation (adjoint Δ x.fst - adjoint h x.snd) =
        -(h (R.conjugation x.snd) + Δ (R.conjugation x.fst))
    rw [map_sub, h_anti1 x.fst, h_comm1 x.snd]
    abel
  · change
      R.conjugation (h x.fst + Δ x.snd) =
        -(adjoint Δ (R.conjugation x.snd) -
          adjoint h (R.conjugation x.fst))
    rw [map_add, h_comm2 x.fst, h_anti2 x.snd]
    abel

/-- Bundled antiunitary-equivalence form of particle--hole covariance. -/
theorem bdg_antiunitary_particle_hole_symmetry_equiv
    (h Δ : EndH)
    (R : AntiunitaryRealStructure H)
    (h_comm1 : ∀ v : H,
      R.conjugation (adjoint h v) = h (R.conjugation v))
    (h_anti1 : ∀ u : H,
      R.conjugation (adjoint Δ u) = -Δ (R.conjugation u))
    (h_comm2 : ∀ u : H,
      R.conjugation (h u) = adjoint h (R.conjugation u))
    (h_anti2 : ∀ v : H,
      R.conjugation (Δ v) = -adjoint Δ (R.conjugation v))
    (x : NambuH) :
    antiunitarySheetSwapEquiv R (H_BdG h Δ x) =
      -(H_BdG h Δ (antiunitarySheetSwapEquiv R x)) := by
  simpa using bdg_antiunitary_particle_hole_symmetry
    h Δ R h_comm1 h_anti1 h_comm2 h_anti2 x

/-! ## 6. Genuine inversion of the hole block -/

/-- Invertibility of `-h†`, witnessed by a genuine continuous linear
equivalence. -/
structure InvertibleHoleBlock (h : EndH) where
  equiv : H ≃L[ℂ] H
  equiv_toContinuousLinearMap :
    equiv.toContinuousLinearMap = holeBlock h

namespace InvertibleHoleBlock

variable {h : EndH}
variable (I : InvertibleHoleBlock h)

/-- Genuine inverse of the physical hole block. -/
def inverse : EndH :=
  I.equiv.symm.toContinuousLinearMap

@[simp] theorem holeBlock_comp_inverse :
    (holeBlock h).comp I.inverse = id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change holeBlock h (I.equiv.symm x) = x
  rw [← I.equiv_toContinuousLinearMap]
  exact I.equiv.apply_symm_apply x

@[simp] theorem inverse_comp_holeBlock :
    I.inverse.comp (holeBlock h) = id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change I.equiv.symm (holeBlock h x) = x
  rw [← I.equiv_toContinuousLinearMap]
  exact I.equiv.symm_apply_apply x

@[simp] theorem holeBlock_inverse_apply (x : H) :
    holeBlock h (I.inverse x) = x := by
  have hx := congrArg (fun T : EndH => T x) I.holeBlock_comp_inverse
  simpa [comp_apply] using hx

@[simp] theorem inverse_holeBlock_apply (x : H) :
    I.inverse (holeBlock h x) = x := by
  have hx := congrArg (fun T : EndH => T x) I.inverse_comp_holeBlock
  simpa [comp_apply] using hx

end InvertibleHoleBlock

/-! ## 7. Zero-energy Schur complement and graph reduction -/

/-- Upper-sector zero-energy Schur complement
`h - Δ (-h†)⁻¹ Δ†`. -/
noncomputable def BdG_Schur_Complement
    (h Δ : EndH)
    (I : InvertibleHoleBlock h) : EndH :=
  h - Δ.comp (I.inverse.comp (adjoint Δ))

/-- Hole component solving the lower BdG equation at zero energy. -/
noncomputable def eliminatedHoleMap
    {h : EndH} (Δ : EndH)
    (I : InvertibleHoleBlock h) : EndH :=
  -(I.inverse.comp (adjoint Δ))

/-- Graph of the eliminated hole component. -/
noncomputable def schurGraphEmbedding
    {h : EndH} (Δ : EndH)
    (I : InvertibleHoleBlock h) : H →L[ℂ] NambuH :=
  nambuPairMap (id ℂ H) (eliminatedHoleMap Δ I)

@[simp] theorem BdG_Schur_Complement_apply
    (h Δ : EndH) (I : InvertibleHoleBlock h) (u : H) :
    BdG_Schur_Complement h Δ I u =
      h u - Δ (I.inverse (adjoint Δ u)) := by
  simp [BdG_Schur_Complement, comp_apply]

@[simp] theorem eliminatedHoleMap_apply
    {h : EndH} (Δ : EndH)
    (I : InvertibleHoleBlock h) (u : H) :
    eliminatedHoleMap Δ I u =
      -I.inverse (adjoint Δ u) := by
  simp [eliminatedHoleMap, comp_apply]

@[simp] theorem schurGraphEmbedding_fst
    {h : EndH} (Δ : EndH)
    (I : InvertibleHoleBlock h) (u : H) :
    (schurGraphEmbedding Δ I u).fst = u := by
  simp [schurGraphEmbedding]

@[simp] theorem schurGraphEmbedding_snd
    {h : EndH} (Δ : EndH)
    (I : InvertibleHoleBlock h) (u : H) :
    (schurGraphEmbedding Δ I u).snd =
      -I.inverse (adjoint Δ u) := by
  simp [schurGraphEmbedding]

/-- The Schur graph parametrization is injective because its particle
component is the identity. -/
theorem schurGraphEmbedding_injective
    {h : EndH} (Δ : EndH)
    (I : InvertibleHoleBlock h) :
    Function.Injective (schurGraphEmbedding Δ I) := by
  intro u v huv
  have hfst := congrArg (fun x : NambuH => x.fst) huv
  simpa using hfst

/-- Genuine zero-energy Schur reduction on the graph of the eliminated hole
sector. -/
theorem H_BdG_on_schurGraph
    (h Δ : EndH)
    (I : InvertibleHoleBlock h)
    (u : H) :
    H_BdG h Δ (schurGraphEmbedding Δ I u) =
      nambuMk (BdG_Schur_Complement h Δ I u) 0 := by
  have hInv :
      holeBlock h (I.inverse (adjoint Δ u)) = adjoint Δ u :=
    I.holeBlock_inverse_apply (adjoint Δ u)
  have hAdj :
      adjoint h (I.inverse (adjoint Δ u)) = -(adjoint Δ u) := by
    have hneg := congrArg Neg.neg hInv
    simpa [holeBlock] using hneg
  apply nambu_ext
  · simp [BdG_Schur_Complement_apply]
  · change
      adjoint Δ u - adjoint h (-I.inverse (adjoint Δ u)) = 0
    rw [map_neg, hAdj]
    simp

/-- Operator-level Schur graph identity. -/
theorem H_BdG_comp_schurGraphEmbedding
    (h Δ : EndH)
    (I : InvertibleHoleBlock h) :
    (H_BdG h Δ).comp (schurGraphEmbedding Δ I) =
      nambuPairMap (BdG_Schur_Complement h Δ I) 0 := by
  apply ContinuousLinearMap.ext
  intro u
  exact H_BdG_on_schurGraph h Δ I u

/-- Zero modes on the Schur graph are exactly zero modes of the Schur
complement. -/
theorem H_BdG_schurGraph_eq_zero_iff
    (h Δ : EndH)
    (I : InvertibleHoleBlock h)
    (u : H) :
    H_BdG h Δ (schurGraphEmbedding Δ I u) = 0 ↔
      BdG_Schur_Complement h Δ I u = 0 := by
  rw [H_BdG_on_schurGraph]
  constructor
  · intro hzero
    have hfst := congrArg (fun x : NambuH => x.fst) hzero
    simpa using hfst
  · intro hzero
    simp [hzero]

/-! ## 8. Spectral-parameter Schur complement -/

/-- Particle diagonal block of `H_BdG - E`. -/
noncomputable def shiftedParticleBlock (h : EndH) (E : ℂ) : EndH :=
  h - E • id ℂ H

/-- Hole diagonal block of `H_BdG - E`. -/
noncomputable def shiftedHoleBlock (h : EndH) (E : ℂ) : EndH :=
  holeBlock h - E • id ℂ H

/-- Spectrally shifted BdG operator `H_BdG - E I`. -/
noncomputable def spectralBdG (h Δ : EndH) (E : ℂ) : EndNambu :=
  H_BdG h Δ - E • id ℂ NambuH

@[simp] theorem shiftedParticleBlock_zero (h : EndH) :
    shiftedParticleBlock h 0 = h := by
  simp [shiftedParticleBlock]

@[simp] theorem shiftedHoleBlock_zero (h : EndH) :
    shiftedHoleBlock h 0 = holeBlock h := by
  simp [shiftedHoleBlock]

@[simp] theorem spectralBdG_zero (h Δ : EndH) :
    spectralBdG h Δ 0 = H_BdG h Δ := by
  simp [spectralBdG]

@[simp] theorem shiftedParticleBlock_apply
    (h : EndH) (E : ℂ) (u : H) :
    shiftedParticleBlock h E u = h u - E • u := by
  simp [shiftedParticleBlock]

@[simp] theorem shiftedHoleBlock_apply
    (h : EndH) (E : ℂ) (v : H) :
    shiftedHoleBlock h E v = -adjoint h v - E • v := by
  simp [shiftedHoleBlock, holeBlock]

@[simp] theorem spectralBdG_fst
    (h Δ : EndH) (E : ℂ) (x : NambuH) :
    (spectralBdG h Δ E x).fst =
      shiftedParticleBlock h E x.fst + Δ x.snd := by
  simp [spectralBdG, shiftedParticleBlock]
  abel

@[simp] theorem spectralBdG_snd
    (h Δ : EndH) (E : ℂ) (x : NambuH) :
    (spectralBdG h Δ E x).snd =
      adjoint Δ x.fst + shiftedHoleBlock h E x.snd := by
  simp [spectralBdG, shiftedHoleBlock, holeBlock]
  abel

/-- Invertibility of the shifted hole block, again witnessed by a genuine
continuous linear equivalence. -/
structure InvertibleShiftedHoleBlock (h : EndH) (E : ℂ) where
  equiv : H ≃L[ℂ] H
  equiv_toContinuousLinearMap :
    equiv.toContinuousLinearMap = shiftedHoleBlock h E

namespace InvertibleShiftedHoleBlock

variable {h : EndH} {E : ℂ}
variable (I : InvertibleShiftedHoleBlock h E)

/-- Genuine inverse of the shifted hole block. -/
def inverse : EndH :=
  I.equiv.symm.toContinuousLinearMap

@[simp] theorem shiftedHoleBlock_comp_inverse :
    (shiftedHoleBlock h E).comp I.inverse = id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change shiftedHoleBlock h E (I.equiv.symm x) = x
  rw [← I.equiv_toContinuousLinearMap]
  exact I.equiv.apply_symm_apply x

@[simp] theorem inverse_comp_shiftedHoleBlock :
    I.inverse.comp (shiftedHoleBlock h E) = id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change I.equiv.symm (shiftedHoleBlock h E x) = x
  rw [← I.equiv_toContinuousLinearMap]
  exact I.equiv.symm_apply_apply x

@[simp] theorem shiftedHoleBlock_inverse_apply (x : H) :
    shiftedHoleBlock h E (I.inverse x) = x := by
  have hx := congrArg (fun T : EndH => T x) I.shiftedHoleBlock_comp_inverse
  simpa [comp_apply] using hx

end InvertibleShiftedHoleBlock

/-- Energy-dependent upper Schur complement of `H_BdG - E`. -/
noncomputable def BdG_Schur_Complement_at
    (h Δ : EndH) (E : ℂ)
    (I : InvertibleShiftedHoleBlock h E) : EndH :=
  shiftedParticleBlock h E -
    Δ.comp (I.inverse.comp (adjoint Δ))

/-- Eliminated hole component at spectral parameter `E`. -/
noncomputable def eliminatedHoleMap_at
    {h : EndH} (Δ : EndH) {E : ℂ}
    (I : InvertibleShiftedHoleBlock h E) : EndH :=
  -(I.inverse.comp (adjoint Δ))

/-- Spectral Schur graph. -/
noncomputable def schurGraphEmbedding_at
    {h : EndH} (Δ : EndH) {E : ℂ}
    (I : InvertibleShiftedHoleBlock h E) : H →L[ℂ] NambuH :=
  nambuPairMap (id ℂ H) (eliminatedHoleMap_at Δ I)

@[simp] theorem BdG_Schur_Complement_at_apply
    (h Δ : EndH) (E : ℂ)
    (I : InvertibleShiftedHoleBlock h E) (u : H) :
    BdG_Schur_Complement_at h Δ E I u =
      shiftedParticleBlock h E u -
        Δ (I.inverse (adjoint Δ u)) := by
  simp [BdG_Schur_Complement_at, comp_apply]

@[simp] theorem eliminatedHoleMap_at_apply
    {h : EndH} (Δ : EndH) {E : ℂ}
    (I : InvertibleShiftedHoleBlock h E) (u : H) :
    eliminatedHoleMap_at Δ I u =
      -I.inverse (adjoint Δ u) := by
  simp [eliminatedHoleMap_at, comp_apply]

@[simp] theorem schurGraphEmbedding_at_fst
    {h : EndH} (Δ : EndH) {E : ℂ}
    (I : InvertibleShiftedHoleBlock h E) (u : H) :
    (schurGraphEmbedding_at Δ I u).fst = u := by
  simp [schurGraphEmbedding_at]

@[simp] theorem schurGraphEmbedding_at_snd
    {h : EndH} (Δ : EndH) {E : ℂ}
    (I : InvertibleShiftedHoleBlock h E) (u : H) :
    (schurGraphEmbedding_at Δ I u).snd =
      -I.inverse (adjoint Δ u) := by
  simp [schurGraphEmbedding_at]

/-- The spectral Schur graph parametrization is injective. -/
theorem schurGraphEmbedding_at_injective
    {h : EndH} (Δ : EndH) {E : ℂ}
    (I : InvertibleShiftedHoleBlock h E) :
    Function.Injective (schurGraphEmbedding_at Δ I) := by
  intro u v huv
  have hfst := congrArg (fun x : NambuH => x.fst) huv
  simpa using hfst

/-- Exact energy-dependent Schur/Feshbach reduction. -/
theorem spectralBdG_on_schurGraph
    (h Δ : EndH) (E : ℂ)
    (I : InvertibleShiftedHoleBlock h E)
    (u : H) :
    spectralBdG h Δ E (schurGraphEmbedding_at Δ I u) =
      nambuMk (BdG_Schur_Complement_at h Δ E I u) 0 := by
  have hInv :
      shiftedHoleBlock h E (I.inverse (adjoint Δ u)) = adjoint Δ u :=
    I.shiftedHoleBlock_inverse_apply (adjoint Δ u)
  apply nambu_ext
  · simp [BdG_Schur_Complement_at_apply, schurGraphEmbedding_at,
      eliminatedHoleMap_at]
  · change
      adjoint Δ u +
          shiftedHoleBlock h E (-I.inverse (adjoint Δ u)) = 0
    rw [map_neg, hInv]
    simp

/-- Operator-level energy-dependent Schur identity. -/
theorem spectralBdG_comp_schurGraphEmbedding
    (h Δ : EndH) (E : ℂ)
    (I : InvertibleShiftedHoleBlock h E) :
    (spectralBdG h Δ E).comp (schurGraphEmbedding_at Δ I) =
      nambuPairMap (BdG_Schur_Complement_at h Δ E I) 0 := by
  apply ContinuousLinearMap.ext
  intro u
  exact spectralBdG_on_schurGraph h Δ E I u

/-- Spectral zero modes on the Schur graph are exactly zero modes of the
energy-dependent Schur complement. -/
theorem spectralBdG_schurGraph_eq_zero_iff
    (h Δ : EndH) (E : ℂ)
    (I : InvertibleShiftedHoleBlock h E)
    (u : H) :
    spectralBdG h Δ E (schurGraphEmbedding_at Δ I u) = 0 ↔
      BdG_Schur_Complement_at h Δ E I u = 0 := by
  rw [spectralBdG_on_schurGraph]
  constructor
  · intro hzero
    have hfst := congrArg (fun x : NambuH => x.fst) hzero
    simpa using hfst
  · intro hzero
    simp [hzero]

/-! ## 9. Consolidated theorem packets -/

/-- Exact block packet. -/
theorem physical_BdG_block_packet
    (h Δ : EndH) :
    block11 (H_BdG h Δ) = h ∧
      block12 (H_BdG h Δ) = Δ ∧
      block21 (H_BdG h Δ) = adjoint Δ ∧
      block22 (H_BdG h Δ) = holeBlock h := by
  exact ⟨block11_H_BdG h Δ,
    block12_H_BdG h Δ,
    block21_H_BdG h Δ,
    block22_H_BdG h Δ⟩

/-- Self-adjoint block and zero-energy Schur closure packet. -/
theorem physical_BdG_schur_packet
    (h Δ : EndH)
    (hh : adjoint h = h)
    (I : InvertibleHoleBlock h)
    (u : H) :
    adjoint (H_BdG h Δ) = H_BdG h Δ ∧
      H_BdG h Δ (schurGraphEmbedding Δ I u) =
        nambuMk (BdG_Schur_Complement h Δ I u) 0 ∧
      (H_BdG h Δ (schurGraphEmbedding Δ I u) = 0 ↔
        BdG_Schur_Complement h Δ I u = 0) := by
  exact ⟨H_BdG_selfAdjoint h Δ hh,
    H_BdG_on_schurGraph h Δ I u,
    H_BdG_schurGraph_eq_zero_iff h Δ I u⟩

end PhysicalBdGPairingBridge

end noncomputable section
