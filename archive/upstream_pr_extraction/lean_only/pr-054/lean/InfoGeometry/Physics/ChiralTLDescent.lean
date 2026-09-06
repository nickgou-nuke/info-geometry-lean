import Mathlib.Tactic
import InfoGeometry.External.Auto.TLChain
import InfoGeometry.Physics.ChiralTensorRecoupling
import InfoGeometry.Physics.ChiralTensorMatrixBridge
import InfoGeometry.Physics.BraidIdealDescent

/-!
# Chiral TL Ideal Descent — projector and relation submodule

Defines:
- `Pchiral_matrix` : 4×4 normalized TL projector (using `TLChain.e4`)
- `Pchiral_matrix_sq` : `Pchiral² = Pchiral` (derived from `TLChain.e4_sq`)
- `R_chiral` : tensor product relation submodule `span{e}` in `M₂⊗M₂`
  (correct type for `BraidIdealDescent.IsLeftTauIdeal`)
- `chiral_left_tau_ideal` : `IsLeftTauIdeal R_chiral (qCrossMap i)` — proved.

The proof proceeds via:
1. `tauL_qCrossMap_on_pure_tmul` — pure tensor computation
2. `tauL_qCrossMap_on_e` — extension to `e = X+Y+Z`
3. `Submodule.mem_span_singleton` — span induction for general `r ∈ R_chiral`
-/

noncomputable section

namespace InfoGeometry.Physics.ChiralTLDescent

open InfoGeometry.External.Auto

open Matrix
open TensorProduct
open InfoGeometry.External.Auto
open ChiralCausalCone
open ChiralTensorRecoupling
open ChiralTensorMatrixBridge
open BraidIdealDescent

/- Bind Mathlib's tensor-algebra structures explicitly.  Leaving these to
global typeclass search is both slow and liable to explore irrelevant
nonassociative instances. -/
local instance spinPairSemiring : Semiring SpinPair :=
  Algebra.TensorProduct.instSemiring
local instance spinPairRing : Ring SpinPair :=
  Algebra.TensorProduct.instRing
local instance spinPairNonAssocSemiring : NonAssocSemiring SpinPair :=
  spinPairSemiring.toNonAssocSemiring
local instance spinPairNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring SpinPair :=
  spinPairSemiring.toNonUnitalNonAssocSemiring
local instance spinPairNonAssocRing : NonAssocRing SpinPair :=
  spinPairRing.toNonAssocRing
local instance spinPairNonUnitalNonAssocRing : NonUnitalNonAssocRing SpinPair :=
  spinPairRing.toNonAssocRing.toNonUnitalNonAssocRing
local instance spinPairAlgebra : Algebra ℂ SpinPair :=
  Algebra.TensorProduct.instAlgebra

/-- The normalized TL projector as a 4×4 matrix: `Pchiral = ½·e4`. -/
def Pchiral_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  (1/2 : ℂ) • TLChain.e4

/-- `Pchiral_matrix² = Pchiral_matrix`, by normalization of `TLChain.e4_sq`. -/
theorem Pchiral_matrix_sq : Pchiral_matrix * Pchiral_matrix = Pchiral_matrix := by
  rw [Pchiral_matrix, smul_mul_smul, TLChain.e4_sq]
  norm_num [smul_smul]

/-- The relation submodule in tensor product form: span of the TL generator `e`.
Type: `Submodule ℂ (M₂ ⊗ M₂)` — matches `IsLeftTauIdeal` type signature. -/
abbrev R_chiral := R_chiral_tensor

/-! ## Core computation: `tauL ∘ qCrossMap i` on pure tensors -/

/-- On a pure tensor `eta ⊗ (a ⊗ b)`, `tauL (qCrossMap i)` applies the swap and scales by `i`. -/
lemma tauL_qCrossMap_on_pure_tmul (eta a b : M2C) :
    tauL (qCrossMap (K := ℂ) (H := M2C) (H_dual := M2C) Complex.I) (eta ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) =
    Complex.I • ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] eta) := by
  unfold tauL qCrossMap
  dsimp
  simp [TensorProduct.map_tmul, TensorProduct.comm_tmul, LinearMap.id_apply,
    TensorProduct.smul_tmul, TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul]

/-- Extension to the TL generator `e = X + Y + Z` (sum of pure tensors). -/
lemma tauL_qCrossMap_on_e (eta : M2C) :
    tauL (qCrossMap (K := ℂ) (H := M2C) (H_dual := M2C) Complex.I) (eta ⊗ₜ[ℂ] e) =
    Complex.I • (e ⊗ₜ[ℂ] eta) := by
  unfold ChiralTensorRecoupling.e ChiralTensorRecoupling.X
    ChiralTensorRecoupling.Y ChiralTensorRecoupling.Z
  simp [add_tmul, tmul_add, tmul_sub, sub_tmul,
    tauL_qCrossMap_on_pure_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    smul_add, smul_sub]
  simp [smul_smul, mul_comm]

/-! ## Membership in `leftTarget` -/

/-- The generator `e ⊗ₜ eta` lies in `leftTarget R_chiral`. -/
lemma e_tmul_eta_mem_leftTarget (eta : M2C) :
    e ⊗ₜ[ℂ] eta ∈ leftTarget (H := M2C) (H_dual := M2C) R_chiral_tensor := by
  have he : e ∈ R_chiral_tensor := Submodule.subset_span (by simp)
  unfold leftTarget
  apply LinearMap.mem_range.mpr
  refine ⟨⟨e, he⟩ ⊗ₜ[ℂ] eta, ?_⟩
  simp

/-! ## Main theorem: `R_chiral` is a left τ-ideal -/

/-- The chiral TL relation submodule `R_chiral = span{e}` is a left τ-ideal
for the q-scaled swap exchange map `qCrossMap i`. This proves that the Kauffman
braid exchange preserves the relation submodule.

This proves the `ChiralLeftTauTarget` ideal condition. -/
theorem chiral_left_tau_ideal :
    IsLeftTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C)
    R_chiral_tensor (qCrossMap (K := ℂ) Complex.I) := by
  intro eta r
  have h_span : r.val ∈ Submodule.span ℂ {e} := r.property
  rcases Submodule.mem_span_singleton.mp h_span with ⟨c, hc⟩
  -- hc : c • e = r.val
  rw [← hc]
  rw [TensorProduct.tmul_smul]
  rw [map_smul]
  rw [tauL_qCrossMap_on_e]
  rw [smul_smul]
  have h_base : e ⊗ₜ[ℂ] eta ∈ leftTarget (H := M2C) (H_dual := M2C) R_chiral_tensor :=
    e_tmul_eta_mem_leftTarget eta
  exact Submodule.smul_mem _ (c * Complex.I) h_base

/-! ## Kernel version — the complementary τ-ideal

The previous theorem proved `IsLeftTauIdeal` for `R_chiral = span{e}` (the **image**
of the TL projector — states with eigenvalue 2). Here we prove the dual: the
**kernel** of `e` (states with eigenvalue 0) is also a left τ-ideal.

Together, both the image and kernel of the TL projector `e` are preserved by the
Kauffman braid exchange, establishing full topological stability of the projector
decomposition. -/

/-- `tauL (qCrossMap i)` acts on `η ⊗ v` for ANY `v : SpinPair` as `i · (v ⊗ η)`.
Lifted from the pure tensor lemma via `TensorProduct.induction_on`. -/
lemma tauL_qCrossMap_on_any (eta : M2C) (v : SpinPair) :
    tauL (qCrossMap (K := ℂ) (H := M2C) (H_dual := M2C) Complex.I) (eta ⊗ₜ[ℂ] v) =
    Complex.I • (v ⊗ₜ[ℂ] eta) := by
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · -- zero: v = 0
    simp
  · -- tmul: v = a ⊗ₜ b
    intro a b
    exact tauL_qCrossMap_on_pure_tmul eta a b
  · -- add: v = v₁ + v₂
    intro v₁ v₂ hv₁ hv₂
    rw [TensorProduct.tmul_add, map_add, hv₁, hv₂, TensorProduct.add_tmul, smul_add]

/-- The kernel of the TL generator `e` acting by left multiplication on `SpinPair`.
States v with e·v = 0 — the nullspace of the singlet projector. -/
def R_kernel : Submodule ℂ SpinPair :=
  LinearMap.ker (LinearMap.mulLeft ℂ e)

/-- For `v ∈ ker(e)`, the tensor `v ⊗ η` is in `leftTarget (ker e)`.
Uses `LinearMap.mem_ker` to extract the kernel condition. -/
lemma ker_tmul_eta_mem_leftTarget (eta : M2C) {v : SpinPair} (hv : v ∈ R_kernel) :
    v ⊗ₜ[ℂ] eta ∈ leftTarget (H := M2C) (H_dual := M2C) R_kernel := by
  -- v ∈ ker(e), so v ∈ R_kernel as a Submodule element
  have hv_sub : (⟨v, hv⟩ : R_kernel) = (⟨v, hv⟩ : R_kernel) := rfl
  unfold leftTarget
  apply LinearMap.mem_range.mpr
  refine ⟨⟨v, hv⟩ ⊗ₜ[ℂ] eta, ?_⟩
  simp

/-- **Kernel τ-ideal theorem.** The nullspace `ker(e)` of the TL singlet projector
is a left τ-ideal for the q-scaled Kauffman exchange `qCrossMap i`.

This is the dual to `chiral_left_tau_ideal` (which proved the span version).
Together they establish that the entire eigenspace decomposition of `e` (values 0 and 2)
is preserved by the braid exchange — full topological stability. -/
theorem chiral_kernel_is_left_tau_ideal :
    IsLeftTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C)
    R_kernel (qCrossMap (K := ℂ) Complex.I) := by
  intro eta r
  -- r : R_kernel, so r.val ∈ ker(e)
  have h_ker : r.val ∈ R_kernel := r.property
  -- Compute tauL action
  rw [tauL_qCrossMap_on_any eta r.val]
  -- Result: Complex.I • (r.val ⊗ eta)
  -- r.val ∈ ker(e), so r.val ⊗ eta ∈ leftTarget(ker e)
  have h_base : r.val ⊗ₜ[ℂ] eta ∈ leftTarget (H := M2C) (H_dual := M2C) R_kernel :=
    ker_tmul_eta_mem_leftTarget eta h_ker
  -- leftTarget is a Submodule, closed under scalar multiplication
  exact Submodule.smul_mem _ Complex.I h_base

/-- Compatibility alias for the active topological-spine theorem name: the chiral
TL relation submodule `span{e}` is a left τ-ideal for Kauffman exchange. -/
theorem chiral_relation_is_left_tau_ideal :
    IsLeftTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C)
    R_chiral_tensor (qCrossMap (K := ℂ) Complex.I) :=
  chiral_left_tau_ideal

/-- Compatibility alias for the kernel/nullspace version of the chiral relation. -/
theorem chiral_kernel_relation_is_left_tau_ideal :
    IsLeftTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C)
    R_kernel (qCrossMap (K := ℂ) Complex.I) :=
  chiral_kernel_is_left_tau_ideal

/-! ## Right τ-ideal — the symmetric dual

`IsRightTauIdeal S C` is the right-handed analogue: `tauR C (s ⊗ v) ∈ rightTarget S`
for `s ∈ S` (the relation in `H_dual ⊗ H_dual`) and `v ∈ H`.

The computation is symmetric to the left case: `tauR (qCrossMap i) (s ⊗ₜ eta) = i • (eta ⊗ₜ s)`.
Same winning tactic: `unfold tauR qCrossMap; dsimp; simp`. -/

/-- `tauR (qCrossMap i)` on a pure tensor `(a ⊗ b) ⊗ eta` → `i • (eta ⊗ (a ⊗ b))`. -/
lemma tauR_qCrossMap_on_pure_tmul (eta a b : M2C) :
    tauR (qCrossMap (K := ℂ) (H := M2C) (H_dual := M2C) Complex.I) ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] eta) =
    Complex.I • (eta ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) := by
  unfold tauR qCrossMap
  dsimp
  simp [TensorProduct.map_tmul, TensorProduct.comm_tmul, LinearMap.id_apply,
    TensorProduct.smul_tmul, TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul]

/-- `tauR (qCrossMap i)` acts on `s ⊗ η` for ANY `s : SpinPair` as `i • (η ⊗ s)`. -/
lemma tauR_qCrossMap_on_any (eta : M2C) (s : SpinPair) :
    tauR (qCrossMap (K := ℂ) (H := M2C) (H_dual := M2C) Complex.I) (s ⊗ₜ[ℂ] eta) =
    Complex.I • (eta ⊗ₜ[ℂ] s) := by
  refine TensorProduct.induction_on s ?_ ?_ ?_
  · simp
  · intro a b
    exact tauR_qCrossMap_on_pure_tmul eta a b
  · intro s₁ s₂ hs₁ hs₂
    rw [TensorProduct.add_tmul, map_add, hs₁, hs₂, TensorProduct.tmul_add, smul_add]

/-- For `s ∈ S` (where S is a submodule of SpinPair), `η ⊗ s ∈ rightTarget S`. -/
lemma eta_tmul_s_mem_rightTarget {S : Submodule ℂ SpinPair} (eta : M2C) {s : SpinPair} (hs : s ∈ S) :
    eta ⊗ₜ[ℂ] s ∈ rightTarget (H := M2C) (H_dual := M2C) S := by
  unfold rightTarget
  apply LinearMap.mem_range.mpr
  refine ⟨eta ⊗ₜ[ℂ] ⟨s, hs⟩, ?_⟩
  simp

/-- **Right τ-ideal — span version.** `R_chiral_tensor = span{e}` is a right τ-ideal
for `qCrossMap i`. The symmetric dual of `chiral_left_tau_ideal`. -/
theorem chiral_right_tau_ideal :
    IsRightTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C)
    R_chiral_tensor (qCrossMap (K := ℂ) Complex.I) := by
  intro s eta
  have h_span : s.val ∈ Submodule.span ℂ {e} := s.property
  rcases Submodule.mem_span_singleton.mp h_span with ⟨c, hc⟩
  -- hc : c • e = s.val
  -- Compute: tauR C ((s : SpinPair) ⊗ₜ eta) = (c*i) • (eta ⊗ₜ e) ∈ rightTarget S
  -- Use simpa to apply all the algebraic identities in one shot
  simpa [show (s : SpinPair) = s.1 from rfl, hc.symm,
    TensorProduct.smul_tmul, map_smul, tauR_qCrossMap_on_any, smul_smul]
    using (Submodule.smul_mem _ (c * Complex.I)
      (eta_tmul_s_mem_rightTarget eta (Submodule.subset_span (by simp : e ∈ ({e} : Set SpinPair)))))

/-- **Right τ-ideal — kernel version.** `R_kernel = ker(e·)` is a right τ-ideal
for `qCrossMap i`. The symmetric dual of `chiral_kernel_is_left_tau_ideal`. -/
theorem chiral_right_kernel_tau_ideal :
    IsRightTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C)
    R_kernel (qCrossMap (K := ℂ) Complex.I) := by
  intro s eta
  have h_ker : s.val ∈ R_kernel := s.property
  rw [tauR_qCrossMap_on_any eta s.val]
  have h_base : eta ⊗ₜ[ℂ] s.val ∈ rightTarget (H := M2C) (H_dual := M2C) R_kernel :=
    eta_tmul_s_mem_rightTarget eta h_ker
  exact Submodule.smul_mem _ Complex.I h_base

#check chiral_right_tau_ideal
#check chiral_right_kernel_tau_ideal

end InfoGeometry.Physics.ChiralTLDescent
