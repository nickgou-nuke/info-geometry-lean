/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ParaKahlerSymplecticLagrangian
import InfoGeometry.Clifford.FockSpaceCAR

/-!
# Super-Grassmannian Projector Envelope: Hyperbolic Polarization, Dual Cotangent Split, and Fock Exterior Algebra

This module unifies the kernel eigensheet definition of para-Kähler Lagrangian subspaces with
the spectral idempotent projector ranges, establishes the split-signature hyperbolic quadratic
polarization (`cl_nn_quadratic_form_split`), proves the canonical dual isomorphism
$T^- \simeq_{\mathbb{R}} (T^+)^*$ and cotangent-model decomposition
$V \simeq_{\mathbb{R}} T^+ \times (T^+)^*$, constructs the Fock exterior algebra envelope
$\bigwedge_{\mathbb{R}} T^+$, and bridges finite-rank coordinate duality to the doubled Krein
and CAR Fock modules:

1. **Archetype I — Kernel Eigensheet Submodules vs. Idempotent Projector Ranges**:
   - `primalSheet K := ker (K - id)` and `covectorVacuumSheet K := ker (K + id)`.
   - Coalescence with `InTPlus K`, `InTMinus K`, `range (paraProjectorPlus K)`,
     `range (paraProjectorMinus K)`, `ker (paraProjectorMinus K)`, and `ker (paraProjectorPlus K)`,
     plus complementary submodule decomposition `IsCompl (primalSheet K) (covectorVacuumSheet K)`.
2. **Archetype II — Split-Signature Hyperbolic Polarization (`cl_nn_quadratic_form_split`)**:
   - Total $g$-isotropy and $\omega$-isotropy on `primalSheet K` and `covectorVacuumSheet K`.
   - Off-diagonal bilinear cross-splits for $g$ and $\omega$, and the split-signature quadratic
     form theorem `g v v = 2 * g (paraProjectorPlus K v) (paraProjectorMinus K v)`.
3. **Archetype III — Canonical Dual Isomorphism $T^- \simeq_{\mathbb{R}} (T^+)^*$ & Cotangent Split**:
   - Cross-pairing linear maps `hyperbolicPairingPlusToDualMinus` and
     `hyperbolicPairingMinusToDualPlus`, their nondegeneracy, injectivity, and finite-dimensional
     bijectivity.
   - Linear equivalences `primalSheetDualEquiv`, `covectorVacuumSheetDualEquiv`, unique dual
     representation `existsUnique_covectorVacuumSheet_representing_dual`, and the cotangent-model
     decomposition `paraKahlerCotangentEquiv : V ≃ₗ[ℝ] primalSheet K × Dual ℝ (primalSheet K)`.
4. **Archetype IV — Fock Exterior Vacuum Envelope $\bigwedge T^+$ & Concrete 2D Witness**:
   - `FockExteriorEnvelope K := ExteriorAlgebra ℝ (primalSheet K)`, vacuum state `fockVacuum`,
     creation operator `fockCreate`, Grassmann nilpotency `fockCreate_sq_zero`, general
     anticommutation `fockCreate_anticomm`, and 1-particle covector vacuum contraction
     `fockVacuumContract`.
   - Bundled and unbundled 2D witness evaluations on `Fin 2 → ℝ` for `swapK`, `swapG`, and
     `swapOmega`.
5. **Archetype V — Symplectic Refutation of Unsymmetric Cross-Symmetry & Finite-Rank Doubled Krein Riesz / CAR Transport Bridge**:
   - Counterexample via `swapOmega` proving that split anti-invariance `B (K x) (K y) = -B x y`
     alone does not imply cross-sheet symmetry `B α u = B u α` without symmetry of `B`.
   - Bridge theorems `two_mul_dual_eval_eq_doubledKrein_quadratic` and
     `sheet_CAR_eq_riesz_inner_smul` connecting finite-rank coordinate duality and Fock CAR
     anticommutators to the doubled Krein quadratic form and Euclidean Riesz inner product.

## Scope Note
This module formalizes the ungraded linear/bilinear eigensheet decomposition
$V = T^+ \oplus T^- \simeq_{\mathbb{R}} T^+ \times (T^+)^*$ and the exterior algebra
$\bigwedge_{\mathbb{R}} T^+$ with wedge creation, 1-particle dual contraction, and finite-rank
bridges to `ClNNToDoubledKreinTransport` and `FockSpaceCAR`, without claiming a
$\mathbb{Z}_2$-graded supermanifold chart atlas.
-/

namespace InfoGeometry.Canonical.SuperGrassmannianProjectorEnvelope

open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Epistemology.SubmersionSplitFinrank
open InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis
open InfoGeometry.Canonical.ParaKahlerLagrangianDimension
open InfoGeometry.Canonical.ParaKahlerSymplecticLagrangian

/-! ### 1. Archetype I: Kernel Eigensheet Submodules vs. Idempotent Projector Ranges -/

section EigensheetSubmodules

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private lemma half_add_half : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num

/-- The primal $+1$ eigensheet submodule $T^+ = \ker(K - \mathrm{id})$. -/
def primalSheet (K : V →ₗ[ℝ] V) : Submodule ℝ V :=
  LinearMap.ker (K - LinearMap.id)

/-- The covector vacuum $-1$ eigensheet submodule $T^- = \ker(K + \mathrm{id})$. -/
def covectorVacuumSheet (K : V →ₗ[ℝ] V) : Submodule ℝ V :=
  LinearMap.ker (K + LinearMap.id)

/-- Membership in `primalSheet K` is equivalent to the $+1$ eigensheet predicate `InTPlus K`. -/
theorem mem_primalSheet_iff_inTPlus (K : V →ₗ[ℝ] V) (v : V) :
    v ∈ primalSheet K ↔ InTPlus K v := by
  rw [primalSheet, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero, InTPlus]

/-- Membership in `covectorVacuumSheet K` is equivalent to the $-1$ eigensheet predicate `InTMinus K`. -/
theorem mem_covectorVacuumSheet_iff_inTMinus (K : V →ₗ[ℝ] V) (v : V) :
    v ∈ covectorVacuumSheet K ↔ InTMinus K v := by
  rw [covectorVacuumSheet, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg, InTMinus]

/-- A vector lies in `primalSheet K` if and only if it is fixed by `paraProjectorPlus K`. -/
theorem mem_primalSheet_iff_paraProjectorPlus_eq (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (v : V) :
    v ∈ primalSheet K ↔ paraProjectorPlus K v = v := by
  rw [mem_primalSheet_iff_inTPlus]
  constructor
  · intro hv
    have h_kv : K v = v := hv
    dsimp [paraProjectorPlus]
    rw [h_kv, ← add_smul, half_add_half, one_smul]
  · intro hp
    exact inTPlus_of_mem_range hK ⟨v, hp⟩

/-- A vector lies in `covectorVacuumSheet K` if and only if it is fixed by `paraProjectorMinus K`. -/
theorem mem_covectorVacuumSheet_iff_paraProjectorMinus_eq (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (v : V) :
    v ∈ covectorVacuumSheet K ↔ paraProjectorMinus K v = v := by
  rw [mem_covectorVacuumSheet_iff_inTMinus]
  constructor
  · intro hv
    have h_kv : K v = -v := hv
    dsimp [paraProjectorMinus]
    rw [h_kv, smul_neg, sub_neg_eq_add, ← add_smul, half_add_half, one_smul]
  · intro hm
    exact inTMinus_of_mem_range hK ⟨v, hm⟩

/-- The kernel submodule `primalSheet K` coincides with the range of `paraProjectorPlus K`. -/
theorem primalSheet_eq_range_paraProjectorPlus (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    primalSheet K = LinearMap.range (paraProjectorPlus K) := by
  ext v
  rw [mem_primalSheet_iff_paraProjectorPlus_eq K hK v, LinearMap.mem_range]
  constructor
  · intro hv
    exact ⟨v, hv⟩
  · rintro ⟨x, rfl⟩
    exact para_projector_plus_idempotent K hK x

/-- The kernel submodule `covectorVacuumSheet K` coincides with the range of `paraProjectorMinus K`. -/
theorem covectorVacuumSheet_eq_range_paraProjectorMinus (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    covectorVacuumSheet K = LinearMap.range (paraProjectorMinus K) := by
  ext v
  rw [mem_covectorVacuumSheet_iff_paraProjectorMinus_eq K hK v, LinearMap.mem_range]
  constructor
  · intro hv
    exact ⟨v, hv⟩
  · rintro ⟨x, rfl⟩
    exact para_projector_minus_idempotent K hK x

/-- The $+1$ eigensheet `primalSheet K` is the kernel of `paraProjectorMinus K`. -/
theorem primalSheet_eq_ker_paraProjectorMinus (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    primalSheet K = LinearMap.ker (paraProjectorMinus K) := by
  rw [primalSheet_eq_range_paraProjectorPlus K hK]
  exact range_projH_eq_ker_projV (paraComplexSubmersionSplit K hK)

/-- The $-1$ eigensheet `covectorVacuumSheet K` is the kernel of `paraProjectorPlus K`. -/
theorem covectorVacuumSheet_eq_ker_paraProjectorPlus (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    covectorVacuumSheet K = LinearMap.ker (paraProjectorPlus K) := by
  rw [covectorVacuumSheet_eq_range_paraProjectorMinus K hK]
  exact range_projV_eq_ker_projH (paraComplexSubmersionSplit K hK)

/-- The $+1$ and $-1$ eigensheet submodules form a complementary direct-sum decomposition of $V$. -/
theorem isCompl_primalSheet_covectorVacuumSheet (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    IsCompl (primalSheet K) (covectorVacuumSheet K) := by
  rw [primalSheet_eq_range_paraProjectorPlus K hK,
    covectorVacuumSheet_eq_range_paraProjectorMinus K hK]
  exact isCompl_range_projH_range_projV (paraComplexSubmersionSplit K hK)

/-- The $+1$ and $-1$ eigensheet submodules span $V$. -/
theorem primalSheet_sup_covectorVacuumSheet (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    primalSheet K ⊔ covectorVacuumSheet K = ⊤ :=
  (isCompl_primalSheet_covectorVacuumSheet K hK).sup_eq_top

end EigensheetSubmodules

/-! ### 2. Archetype II: Split-Signature Hyperbolic Polarization (`cl_nn_quadratic_form_split`) -/

section HyperbolicPolarization

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}

/-- `primalSheet K` is totally isotropic for the neutral metric `g`. -/
theorem primalSheet_g_isotropic (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) {u w : V}
    (hu : u ∈ primalSheet K) (hw : w ∈ primalSheet K) :
    g u w = 0 :=
  tplus_isotropic hK hPK ((mem_primalSheet_iff_inTPlus K u).mp hu)
    ((mem_primalSheet_iff_inTPlus K w).mp hw)

/-- `covectorVacuumSheet K` is totally isotropic for the neutral metric `g`. -/
theorem covectorVacuumSheet_g_isotropic (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) {u w : V}
    (hu : u ∈ covectorVacuumSheet K) (hw : w ∈ covectorVacuumSheet K) :
    g u w = 0 :=
  tminus_isotropic hK hPK ((mem_covectorVacuumSheet_iff_inTMinus K u).mp hu)
    ((mem_covectorVacuumSheet_iff_inTMinus K w).mp hw)

/-- `primalSheet K` is totally isotropic for the fundamental symplectic form `omega`. -/
theorem primalSheet_omega_isotropic (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) {u w : V}
    (hu : u ∈ primalSheet K) (hw : w ∈ primalSheet K) :
    omega u w = 0 := by
  rw [primalSheet_eq_range_paraProjectorPlus K hK] at hu hw
  exact range_plus_omega_isotropic hK hPK u hu w hw

/-- `covectorVacuumSheet K` is totally isotropic for the fundamental symplectic form `omega`. -/
theorem covectorVacuumSheet_omega_isotropic (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) {u w : V}
    (hu : u ∈ covectorVacuumSheet K) (hw : w ∈ covectorVacuumSheet K) :
    omega u w = 0 := by
  rw [covectorVacuumSheet_eq_range_paraProjectorMinus K hK] at hu hw
  exact range_minus_omega_isotropic hK hPK u hu w hw

/-- Off-diagonal cross-sheet bilinear decomposition of a para-Kähler metric `g`:
the diagonal $(+,+)$ and $(-,-)$ pairings vanish identically by sheet isotropy, leaving
only the hyperbolic cross-pairings between $P^+$ and $P^-$. -/
theorem paraKahler_bilinear_cross_split (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v w : V) :
    g v w = g (paraProjectorPlus K v) (paraProjectorMinus K w) +
      g (paraProjectorMinus K v) (paraProjectorPlus K w) := by
  have hv : v = paraProjectorPlus K v + paraProjectorMinus K v :=
    (para_projectors_sum_id K v).symm
  have hw : w = paraProjectorPlus K w + paraProjectorMinus K w :=
    (para_projectors_sum_id K w).symm
  have h_expand : g v w =
      (g (paraProjectorPlus K v) (paraProjectorPlus K w) +
        g (paraProjectorMinus K v) (paraProjectorPlus K w)) +
      (g (paraProjectorPlus K v) (paraProjectorMinus K w) +
        g (paraProjectorMinus K v) (paraProjectorMinus K w)) := by
    conv_lhs => rw [hv, hw]
    simp only [map_add, LinearMap.add_apply]
  have h_pp : g (paraProjectorPlus K v) (paraProjectorPlus K w) = 0 :=
    range_plus_isotropic hK hPK _ (LinearMap.mem_range_self _ v)
      _ (LinearMap.mem_range_self _ w)
  have h_mm : g (paraProjectorMinus K v) (paraProjectorMinus K w) = 0 :=
    range_minus_isotropic hK hPK _ (LinearMap.mem_range_self _ v)
      _ (LinearMap.mem_range_self _ w)
  rw [h_expand, h_pp, h_mm, zero_add, add_zero, add_comm]

/-- **Split-signature hyperbolic quadratic polarization (`cl_nn_quadratic_form_split`).**
The quadratic form of any para-Kähler metric `g` splits purely into twice the cross-pairing
between the $+1$ primal projection `paraProjectorPlus K v` and the $-1$ covector projection
`paraProjectorMinus K v`. -/
theorem cl_nn_quadratic_form_split (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v : V) :
    g v v = 2 * g (paraProjectorPlus K v) (paraProjectorMinus K v) := by
  have h_split := paraKahler_bilinear_cross_split hK hPK v v
  have h_symm : g (paraProjectorMinus K v) (paraProjectorPlus K v) =
      g (paraProjectorPlus K v) (paraProjectorMinus K v) :=
    hPK.g_symm (paraProjectorMinus K v) (paraProjectorPlus K v)
  rw [h_split, h_symm, ← two_mul]

/-- Off-diagonal cross-sheet bilinear decomposition of the fundamental symplectic form `omega`. -/
theorem paraKahler_omega_cross_split (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v w : V) :
    omega v w = omega (paraProjectorPlus K v) (paraProjectorMinus K w) +
      omega (paraProjectorMinus K v) (paraProjectorPlus K w) := by
  have hv : v = paraProjectorPlus K v + paraProjectorMinus K v :=
    (para_projectors_sum_id K v).symm
  have hw : w = paraProjectorPlus K w + paraProjectorMinus K w :=
    (para_projectors_sum_id K w).symm
  have h_expand : omega v w =
      (omega (paraProjectorPlus K v) (paraProjectorPlus K w) +
        omega (paraProjectorMinus K v) (paraProjectorPlus K w)) +
      (omega (paraProjectorPlus K v) (paraProjectorMinus K w) +
        omega (paraProjectorMinus K v) (paraProjectorMinus K w)) := by
    conv_lhs => rw [hv, hw]
    simp only [map_add, LinearMap.add_apply]
  have h_pp : omega (paraProjectorPlus K v) (paraProjectorPlus K w) = 0 :=
    range_plus_omega_isotropic hK hPK _ (LinearMap.mem_range_self _ v)
      _ (LinearMap.mem_range_self _ w)
  have h_mm : omega (paraProjectorMinus K v) (paraProjectorMinus K w) = 0 :=
    range_minus_omega_isotropic hK hPK _ (LinearMap.mem_range_self _ v)
      _ (LinearMap.mem_range_self _ w)
  rw [h_expand, h_pp, h_mm, zero_add, add_zero, add_comm]

/-- On `range P⁺ × range P⁻`, the neutral metric `g` equals `-omega`. -/
theorem g_plus_minus_eq_neg_omega (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v w : V) :
    g (paraProjectorPlus K v) (paraProjectorMinus K w) =
      -omega (paraProjectorPlus K v) (paraProjectorMinus K w) := by
  have h_comp := hPK.compatibility (paraProjectorPlus K v) (paraProjectorMinus K w)
  have h_minus : K (paraProjectorMinus K w) = -paraProjectorMinus K w :=
    paraProjectorMinus_in_TMinus K hK w
  rw [h_minus, map_neg] at h_comp
  exact h_comp

/-- On `range P⁻ × range P⁺`, the neutral metric `g` equals `omega`. -/
theorem g_minus_plus_eq_omega (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v w : V) :
    g (paraProjectorMinus K v) (paraProjectorPlus K w) =
      omega (paraProjectorMinus K v) (paraProjectorPlus K w) := by
  have h_comp := hPK.compatibility (paraProjectorMinus K v) (paraProjectorPlus K w)
  have h_plus : K (paraProjectorPlus K w) = paraProjectorPlus K w :=
    paraProjectorPlus_in_TPlus K hK w
  rw [h_plus] at h_comp
  exact h_comp

/-- Expressing the split-signature quadratic form `g v v` via the symplectic pairing
between the $+1$ and $-1$ projections: `g v v = -(2 * omega (P⁺ v) (P⁻ v))`. -/
theorem cl_nn_quadratic_form_eq_neg_two_omega (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v : V) :
    g v v = -(2 * omega (paraProjectorPlus K v) (paraProjectorMinus K v)) := by
  rw [cl_nn_quadratic_form_split hK hPK v, g_plus_minus_eq_neg_omega hK hPK v v, mul_neg]

end HyperbolicPolarization

/-! ### 3. Archetype III: Canonical Dual Isomorphism $T^- \simeq_{\mathbb{R}} (T^+)^*$ & Cotangent Split -/

section CotangentDualModel

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}

/-- Canonical cross-pairing linear map $T^+ \to (T^-)^*$, $u \mapsto (w \mapsto g(u, w))$. -/
def hyperbolicPairingPlusToDualMinus (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V) :
    primalSheet K →ₗ[ℝ] Module.Dual ℝ (covectorVacuumSheet K) :=
  g.domRestrict₁₂ (primalSheet K) (covectorVacuumSheet K)

/-- Canonical cross-pairing linear map $T^- \to (T^+)^*$, $\alpha \mapsto (u \mapsto g(\alpha, u))$. -/
def hyperbolicPairingMinusToDualPlus (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V) :
    covectorVacuumSheet K →ₗ[ℝ] Module.Dual ℝ (primalSheet K) :=
  g.domRestrict₁₂ (covectorVacuumSheet K) (primalSheet K)

@[simp]
theorem hyperbolicPairingPlusToDualMinus_apply (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (u : primalSheet K) (w : covectorVacuumSheet K) :
    hyperbolicPairingPlusToDualMinus g K u w = g u.1 w.1 :=
  rfl

@[simp]
theorem hyperbolicPairingMinusToDualPlus_apply (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (u : primalSheet K) :
    hyperbolicPairingMinusToDualPlus g K α u = g α.1 u.1 :=
  rfl

/-- When `g` is nondegenerate, the hyperbolic pairing $T^+ \to (T^-)^*$ is injective. -/
theorem hyperbolicPairingPlusToDualMinus_injective (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Function.Injective (hyperbolicPairingPlusToDualMinus g K) :=
  crossPairing_injective g hnd (fun _ hu _ hu' => primalSheet_g_isotropic hK hPK hu hu')
    (primalSheet_sup_covectorVacuumSheet K hK)

/-- When `g` is nondegenerate, the hyperbolic pairing $T^- \to (T^+)^*$ is injective. -/
theorem hyperbolicPairingMinusToDualPlus_injective (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Function.Injective (hyperbolicPairingMinusToDualPlus g K) :=
  crossPairing_injective g hnd
    (fun _ hu _ hu' => covectorVacuumSheet_g_isotropic hK hPK hu hu')
    (by rw [sup_comm]; exact primalSheet_sup_covectorVacuumSheet K hK)

/-- Nondegeneracy of the cross-sheet pairing on `primalSheet K`: if $g(u, \alpha) = 0$
for all $\alpha \in T^-$, then $u = 0$. -/
theorem eq_zero_of_hyperbolicPairingPlusToDualMinus_eq_zero (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0)
    (u : primalSheet K)
    (hu : ∀ α : covectorVacuumSheet K, hyperbolicPairingPlusToDualMinus g K u α = 0) :
    u = 0 := by
  apply hyperbolicPairingPlusToDualMinus_injective hK hPK hnd
  rw [map_zero]
  ext α
  exact hu α

/-- Nondegeneracy of the cross-sheet pairing on `covectorVacuumSheet K`: if $g(\alpha, u) = 0$
for all $u \in T^+$, then $\alpha = 0$. -/
theorem eq_zero_of_hyperbolicPairingMinusToDualPlus_eq_zero (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0)
    (α : covectorVacuumSheet K)
    (hα : ∀ u : primalSheet K, hyperbolicPairingMinusToDualPlus g K α u = 0) :
    α = 0 := by
  apply hyperbolicPairingMinusToDualPlus_injective hK hPK hnd
  rw [map_zero]
  ext u
  exact hα u

variable [FiniteDimensional ℝ V]

/-- In finite dimension, the kernel submodules `primalSheet K` and `covectorVacuumSheet K`
have equal dimension when `g` is nondegenerate. -/
theorem finrank_primalSheet_eq_covectorVacuumSheet (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Module.finrank ℝ (primalSheet K) = Module.finrank ℝ (covectorVacuumSheet K) := by
  rw [primalSheet_eq_range_paraProjectorPlus K hK,
    covectorVacuumSheet_eq_range_paraProjectorMinus K hK]
  exact finrank_range_plus_eq_minus hK hPK hnd

/-- In finite dimension, `2 * finrank (primalSheet K) = finrank V`. -/
theorem two_mul_finrank_primalSheet (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    2 * Module.finrank ℝ (primalSheet K) = Module.finrank ℝ V := by
  rw [primalSheet_eq_range_paraProjectorPlus K hK]
  exact two_mul_finrank_range_plus hK hPK hnd

/-- In finite dimension, the hyperbolic cross-pairing $T^+ \to (T^-)^*$ is bijective. -/
theorem hyperbolicPairingPlusToDualMinus_bijective (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Function.Bijective (hyperbolicPairingPlusToDualMinus g K) := by
  have h_inj := hyperbolicPairingPlusToDualMinus_injective hK hPK hnd
  have h_dim : Module.finrank ℝ (primalSheet K) =
      Module.finrank ℝ (Module.Dual ℝ (covectorVacuumSheet K)) := by
    rw [Subspace.dual_finrank_eq]
    exact finrank_primalSheet_eq_covectorVacuumSheet hK hPK hnd
  exact ⟨h_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_dim).mp h_inj⟩

/-- In finite dimension, the hyperbolic cross-pairing $T^- \to (T^+)^*$ is bijective. -/
theorem hyperbolicPairingMinusToDualPlus_bijective (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Function.Bijective (hyperbolicPairingMinusToDualPlus g K) := by
  have h_inj := hyperbolicPairingMinusToDualPlus_injective hK hPK hnd
  have h_dim : Module.finrank ℝ (covectorVacuumSheet K) =
      Module.finrank ℝ (Module.Dual ℝ (primalSheet K)) := by
    rw [Subspace.dual_finrank_eq]
    exact (finrank_primalSheet_eq_covectorVacuumSheet hK hPK hnd).symm
  exact ⟨h_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_dim).mp h_inj⟩

/-- Canonical linear isomorphism $T^+ \simeq_{\mathbb{R}} (T^-)^*$ induced by the neutral metric `g`. -/
noncomputable def primalSheetDualEquiv (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    primalSheet K ≃ₗ[ℝ] Module.Dual ℝ (covectorVacuumSheet K) :=
  LinearEquiv.ofBijective (hyperbolicPairingPlusToDualMinus g K)
    (hyperbolicPairingPlusToDualMinus_bijective hK hPK hnd)

/-- Canonical linear isomorphism $T^- \simeq_{\mathbb{R}} (T^+)^*$ identifying the $-1$
eigensheet with the algebraic dual of the $+1$ eigensheet. -/
noncomputable def covectorVacuumSheetDualEquiv (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    covectorVacuumSheet K ≃ₗ[ℝ] Module.Dual ℝ (primalSheet K) :=
  LinearEquiv.ofBijective (hyperbolicPairingMinusToDualPlus g K)
    (hyperbolicPairingMinusToDualPlus_bijective hK hPK hnd)

/-- Every linear functional $\varphi \in (T^+)^*$ is represented by a unique covector
$\alpha \in T^-$ via $\varphi(u) = g(\alpha, u)$. -/
theorem existsUnique_covectorVacuumSheet_representing_dual (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0)
    (φ : Module.Dual ℝ (primalSheet K)) :
    ∃! α : covectorVacuumSheet K, hyperbolicPairingMinusToDualPlus g K α = φ := by
  obtain ⟨h_inj, h_surj⟩ := hyperbolicPairingMinusToDualPlus_bijective hK hPK hnd
  obtain ⟨α, hα⟩ := h_surj φ
  exact ⟨α, hα, fun β hβ => h_inj (hβ.trans hα.symm)⟩

/-- **Cotangent-model decomposition of a finite-dimensional para-Kähler vector space:**
$V \simeq_{\mathbb{R}} T^+ \times (T^+)^*$. -/
noncomputable def paraKahlerCotangentEquiv (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    V ≃ₗ[ℝ] (primalSheet K) × Module.Dual ℝ (primalSheet K) :=
  (Submodule.prodEquivOfIsCompl (primalSheet K) (covectorVacuumSheet K)
    (isCompl_primalSheet_covectorVacuumSheet K hK)).symm.trans
    ((LinearEquiv.refl ℝ (primalSheet K)).prodCongr (covectorVacuumSheetDualEquiv hK hPK hnd))

end CotangentDualModel

/-! ### 4. Archetype IV: Fock Exterior Vacuum Envelope $\bigwedge T^+$ & Concrete 2D Witness -/

section FockExteriorEnvelope

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The algebraic Fock exterior envelope $\bigwedge_{\mathbb{R}} T^+$ generated by the
primal $+1$ eigensheet `primalSheet K`. -/
abbrev FockExteriorEnvelope (K : V →ₗ[ℝ] V) :=
  ExteriorAlgebra ℝ (primalSheet K)

/-- The vacuum state $|0\rangle = 1 \in \bigwedge_{\mathbb{R}} T^+$. -/
def fockVacuum (K : V →ₗ[ℝ] V) : FockExteriorEnvelope K := 1

/-- Exterior wedge-creation operator $\psi \mapsto \iota(u) \wedge \psi$ on $\bigwedge_{\mathbb{R}} T^+$. -/
def fockCreate {K : V →ₗ[ℝ] V} (u : primalSheet K) (ψ : FockExteriorEnvelope K) :
    FockExteriorEnvelope K :=
  ExteriorAlgebra.ι ℝ u * ψ

/-- Pauli / Grassmann nilpotency of exterior creation: applying `fockCreate u` twice gives zero. -/
theorem fockCreate_sq_zero {K : V →ₗ[ℝ] V} (u : primalSheet K) (ψ : FockExteriorEnvelope K) :
    fockCreate u (fockCreate u ψ) = 0 := by
  dsimp [fockCreate]
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- General anticommutation of exterior creation operators on any state $\psi \in \bigwedge T^+$. -/
theorem fockCreate_anticomm {K : V →ₗ[ℝ] V} (u w : primalSheet K)
    (ψ : FockExteriorEnvelope K) :
    fockCreate u (fockCreate w ψ) + fockCreate w (fockCreate u ψ) = 0 := by
  dsimp [fockCreate]
  have h_anti : ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ w +
      ExteriorAlgebra.ι ℝ w * ExteriorAlgebra.ι ℝ u = 0 := by
    have h_sq : ExteriorAlgebra.ι ℝ (u + w) * ExteriorAlgebra.ι ℝ (u + w) = 0 :=
      ExteriorAlgebra.ι_sq_zero (u + w)
    rw [map_add, mul_add, add_mul, add_mul, ExteriorAlgebra.ι_sq_zero u,
      ExteriorAlgebra.ι_sq_zero w, zero_add, add_zero, add_comm] at h_sq
    exact h_sq
  rw [← mul_assoc, ← mul_assoc, ← add_mul, h_anti, zero_mul]

/-- Anticommutation of exterior creation operators acting on the vacuum state $|0\rangle$. -/
theorem fockCreate_anticomm_on_vacuum {K : V →ₗ[ℝ] V} (u w : primalSheet K) :
    fockCreate u (fockCreate w (fockVacuum K)) +
      fockCreate w (fockCreate u (fockVacuum K)) = 0 :=
  fockCreate_anticomm u w (fockVacuum K)

/-- 1-particle covector vacuum contraction: a covector $\alpha \in T^-$ contracts a
primal state $u \in T^+$ onto the vacuum line $\mathbb{R} \cdot |0\rangle \subseteq \bigwedge T^+$
via the hyperbolic pairing `hyperbolicPairingMinusToDualPlus`. -/
def fockVacuumContract (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (u : primalSheet K) : FockExteriorEnvelope K :=
  (hyperbolicPairingMinusToDualPlus g K α u) • fockVacuum K

/-- Evaluating `fockVacuumContract` embeds the scalar pairing $g(\alpha, u)$ into
the exterior algebra $\bigwedge T^+$ via `algebraMap`. -/
theorem fockVacuumContract_apply (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (u : primalSheet K) :
    fockVacuumContract g K α u =
      algebraMap ℝ (FockExteriorEnvelope K) (g α.1 u.1) := by
  dsimp [fockVacuumContract, fockVacuum]
  exact (Algebra.algebraMap_eq_smul_one (R := ℝ) (A := FockExteriorEnvelope K) (g α.1 u.1)).symm

end FockExteriorEnvelope

section SwapWitness

/-- Explicit primal sheet vector $u^+ = (1, 1)$ on `Fin 2 → ℝ`. -/
def swapPrimalVec : Fin 2 → ℝ := fun _ => 1

/-- Explicit covector vacuum sheet vector $u^- = (1, -1)$ on `Fin 2 → ℝ`. -/
def swapCovectorVec : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1

/-- `swapPrimalVec` lies in `primalSheet swapK`. -/
theorem swapPrimalVec_mem_primalSheet : swapPrimalVec ∈ primalSheet swapK := by
  rw [mem_primalSheet_iff_inTPlus, InTPlus]
  ext i
  simp [swapPrimalVec, swapK, LinearMap.funLeft_apply]

/-- `swapCovectorVec` lies in `covectorVacuumSheet swapK`. -/
theorem swapCovectorVec_mem_covectorVacuumSheet :
    swapCovectorVec ∈ covectorVacuumSheet swapK := by
  rw [mem_covectorVacuumSheet_iff_inTMinus, InTMinus]
  ext i
  fin_cases i <;> simp [swapCovectorVec, swapK, LinearMap.funLeft_apply]

/-- Bundled primal sheet element $u^+ \in \mathrm{primalSheet}(\mathrm{swapK})$. -/
def swapPrimalElem : primalSheet swapK :=
  ⟨swapPrimalVec, swapPrimalVec_mem_primalSheet⟩

/-- Bundled covector vacuum sheet element $u^- \in \mathrm{covectorVacuumSheet}(\mathrm{swapK})$. -/
def swapCovectorElem : covectorVacuumSheet swapK :=
  ⟨swapCovectorVec, swapCovectorVec_mem_covectorVacuumSheet⟩

/-- The hyperbolic cross-pairing of `swapPrimalVec` and `swapCovectorVec` under `swapG` equals `2`. -/
theorem swap_hyperbolic_pairing_eq_two :
    swapG swapPrimalVec swapCovectorVec = 2 := by
  simp only [swapG, LinearMap.mk₂_apply, swapPrimalVec, swapCovectorVec]
  norm_num

/-- Non-vacuity witness: the hyperbolic cross-pairing on `Fin 2 → ℝ` is non-zero. -/
theorem swap_hyperbolic_pairing_ne_zero :
    swapG swapPrimalVec swapCovectorVec ≠ 0 := by
  rw [swap_hyperbolic_pairing_eq_two]
  norm_num

/-- Evaluating the bundled cross-pairing `hyperbolicPairingPlusToDualMinus` on
`(swapPrimalElem, swapCovectorElem)` yields `2`. -/
theorem swap_bundled_hyperbolic_pairing_eq_two :
    hyperbolicPairingPlusToDualMinus swapG swapK swapPrimalElem swapCovectorElem = 2 :=
  swap_hyperbolic_pairing_eq_two

/-- Evaluating the 1-particle Fock vacuum contraction `fockVacuumContract` on
`(swapCovectorElem, swapPrimalElem)` yields `algebraMap ℝ (FockExteriorEnvelope swapK) 2`. -/
theorem swap_fockVacuumContract_eq :
    fockVacuumContract swapG swapK swapCovectorElem swapPrimalElem =
      algebraMap ℝ (FockExteriorEnvelope swapK) 2 := by
  rw [fockVacuumContract_apply, swapParaKahler.g_symm]
  exact congrArg (algebraMap ℝ (FockExteriorEnvelope swapK)) swap_hyperbolic_pairing_eq_two

end SwapWitness

/-! ### 5. Archetype V: Symplectic Refutation of Unsymmetric Cross-Symmetry & Finite-Rank Doubled Krein Riesz / CAR Transport Bridge -/

section SymplecticRefutationAndKreinCARBridge

private lemma two_mul_of_eq_half_mul (a b : ℝ) (h : a = (1 / 2 : ℝ) * b) :
    2 * a = b := by
  rw [h]
  ring

/-- `swapOmega` satisfies split anti-invariance `swapOmega (swapK u) (swapK v) = -swapOmega u v`
despite being skew-symmetric rather than symmetric. -/
theorem swapOmega_split_anti_invariant (u v : Fin 2 → ℝ) :
    swapOmega (swapK u) (swapK v) = -swapOmega u v :=
  swapParaKahler.omega_anti_inv u v

/-- Evaluating `swapOmega` on `(swapPrimalVec, swapCovectorVec)` gives `-2`. -/
theorem swapOmega_primal_covector_eq_neg_two :
    swapOmega swapPrimalVec swapCovectorVec = -2 := by
  simp only [swapOmega, LinearMap.mk₂_apply, swapPrimalVec, swapCovectorVec]
  norm_num

/-- Evaluating `swapOmega` in the reversed order `(swapCovectorVec, swapPrimalVec)` gives `2`. -/
theorem swapOmega_covector_primal_eq_two :
    swapOmega swapCovectorVec swapPrimalVec = 2 := by
  simp only [swapOmega, LinearMap.mk₂_apply, swapPrimalVec, swapCovectorVec]
  norm_num

/-- Counterexample to cross-sheet symmetry without intrinsic symmetry of the bilinear form:
although `swapOmega` is split anti-invariant under `swapK`, its cross-sheet values on
`swapPrimalVec ∈ primalSheet swapK` and `swapCovectorVec ∈ covectorVacuumSheet swapK`
satisfy `swapOmega swapCovectorVec swapPrimalVec ≠ swapOmega swapPrimalVec swapCovectorVec`. -/
theorem swapOmega_cross_asymmetric :
    swapOmega swapCovectorVec swapPrimalVec ≠ swapOmega swapPrimalVec swapCovectorVec := by
  rw [swapOmega_covector_primal_eq_two, swapOmega_primal_covector_eq_neg_two]
  norm_num

/-- Refutation theorem: split anti-invariance `∀ x y, B (K x) (K y) = -B x y` alone does not
imply cross-sheet symmetry `B α u = B u α` for `u ∈ primalSheet K` and
`α ∈ covectorVacuumSheet K` unless `B` is also symmetric. -/
theorem exists_split_anti_invariant_not_cross_symmetric :
    ∃ (B : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (u α : Fin 2 → ℝ),
      (∀ x y, B (swapK x) (swapK y) = -B x y) ∧
        u ∈ primalSheet swapK ∧
        α ∈ covectorVacuumSheet swapK ∧
        B α u ≠ B u α :=
  ⟨swapOmega, swapPrimalVec, swapCovectorVec, swapOmega_split_anti_invariant,
    swapPrimalVec_mem_primalSheet, swapCovectorVec_mem_covectorVacuumSheet,
    swapOmega_cross_asymmetric⟩

/-- Twice the finite-rank coordinate dual pairing `2 * (φ x)` equals the quadratic evaluation
of `hessian_indefinite_form` on the 45-degree doubled Krein realization of `(x, φ)`. -/
theorem two_mul_dual_eval_eq_doubledKrein_quadratic (n : ℕ)
    (x : InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n)
    (φ : Module.Dual ℝ (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n)) :
    2 * (φ x) =
      InfoGeometry.Krein.hessian_indefinite_form
        (InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.realizeToDoubledRho
          (E := InfoGeometry.Clifford.ClNNToDoubledKreinTransport.EucVector n)
          (InfoGeometry.Clifford.ClNNToDoubledKreinTransport.rieszEquiv n)
          (InfoGeometry.Clifford.ClNNToDoubledKreinTransport.toEuclideanPhase n (x, φ)))
        (InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.realizeToDoubledRho
          (E := InfoGeometry.Clifford.ClNNToDoubledKreinTransport.EucVector n)
          (InfoGeometry.Clifford.ClNNToDoubledKreinTransport.rieszEquiv n)
          (InfoGeometry.Clifford.ClNNToDoubledKreinTransport.toEuclideanPhase n (x, φ))) := by
  have h :=
    InfoGeometry.Clifford.ClNNToDoubledKreinTransport.Qsplit_eq_doubledKrein_form n (x, φ)
  rw [InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Qsplit_neutralToSplit,
    InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_apply] at h
  exact two_mul_of_eq_half_mul (φ x) _ h

/-- In the finite-rank `Cl(n,n)` exterior Fock space, the canonical anticommutation
relation `{c†(u), c(φ)} ψ` evaluates to the Euclidean inner product
`⟪toEuclidean n u, coordinateDualToEuclidean n φ⟫ • ψ` via the finite-rank Riesz equivalence. -/
theorem sheet_CAR_eq_riesz_inner_smul (n : ℕ)
    (u : InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n)
    (φ : Module.Dual ℝ (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n))
    (ψ : InfoGeometry.Clifford.FockSpaceCAR.FockSpace
      (InfoGeometry.Clifford.FockSpaceCAR.PrimalSheet n)) :
    InfoGeometry.Clifford.FockSpaceCAR.sheetCreation n
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralPrimalSheetParametrization n u)
        (InfoGeometry.Clifford.FockSpaceCAR.sheetAnnihilation n
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetParametrization n φ) ψ) +
      InfoGeometry.Clifford.FockSpaceCAR.sheetAnnihilation n
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetParametrization n φ)
        (InfoGeometry.Clifford.FockSpaceCAR.sheetCreation n
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralPrimalSheetParametrization n u) ψ) =
      (@inner ℝ (InfoGeometry.Clifford.ClNNToDoubledKreinTransport.EucVector n) _
        (InfoGeometry.Clifford.ClNNToDoubledKreinTransport.toEuclidean n u)
        (InfoGeometry.Clifford.ClNNToDoubledKreinTransport.coordinateDualToEuclidean n φ)) • ψ := by
  rw [InfoGeometry.Clifford.FockSpaceCAR.neutralTower_CAR,
    InfoGeometry.Clifford.ClNNToDoubledKreinTransport.coordinateDual_eval_eq_inner]

end SymplecticRefutationAndKreinCARBridge

end InfoGeometry.Canonical.SuperGrassmannianProjectorEnvelope
