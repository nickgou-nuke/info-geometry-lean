/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.External.Virasoro.WittAlgebra
import InfoGeometry.External.Virasoro.VirasoroCocycle
import InfoGeometry.External.Virasoro.VirasoroVerma

/-!
# InfoGeometry.Bridge.ModularVirasoro

Finite bridge readouts between low Virasoro modes and Verma-module interfaces.
This file is theorem-safe and witness-gated.
-/

noncomputable section

namespace InfoGeometry.Bridge.ModularVirasoro

open VirasoroProject

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem modularVirasoro_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- In any noncommutative ring `[Ring B]` acting on an additive group `M`, a `B`-linear
map `f : V →ₗ[B] M` intertwines the module action of every element `X : B`. -/
theorem ring_modular_intertwining_smul
    {B V M : Type*} [Ring B] [AddCommGroup V] [Module B V] [AddCommGroup M] [Module B M]
    (f : V →ₗ[B] M) (X : B) (v : V) :
    f (X • v) = X • f v :=
  f.map_smul X v

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Global `L`-mode seed in the Witt sector. -/
def modularFlux_to_Witt_L_minus_one : WittAlgebra 𝕜 :=
  WittAlgebra.lgen 𝕜 (-1)

/-- Modular-flow Hamiltonian seed in the Witt sector. -/
def modularHam_to_Witt_L_zero : WittAlgebra 𝕜 :=
  WittAlgebra.lgen 𝕜 0

/-- The Virasoro cocycle vanishes on global conformal modes `m ∈ {-1,0,1}`. -/
theorem virasoroCocycle_vanishes_on_sl2
    {m n : Int}
    (hm : m ∈ ({-1, 0, 1} : Set Int)) :
    WittAlgebra.virasoroCocycle 𝕜 (WittAlgebra.lgen 𝕜 m) (WittAlgebra.lgen 𝕜 n) = 0 := by
  have hm' : m = -1 ∨ m = 0 ∨ m = 1 := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_assoc] using hm
  by_cases hmn : m + n = 0
  · rw [WittAlgebra.virasoroCocycle_apply_lgen_lgen, if_pos hmn]
    rcases hm' with hm' | hm' | hm' <;> subst m <;> norm_num
  · simp [WittAlgebra.virasoroCocycle_apply_lgen_lgen, hmn]

/-- On global modes `m ∈ {-1,0,1}`, the Virasoro `L_m,L_n` bracket has no central term. -/
theorem bracket_no_central_on_sl2
    {m n : Int}
    (hm : m ∈ ({-1, 0, 1} : Set Int)) :
    ⁅VirasoroAlgebra.lgen 𝕜 m, VirasoroAlgebra.lgen 𝕜 n⁆
      = (m - n : 𝕜) • VirasoroAlgebra.lgen 𝕜 (m + n) := by
  have hm' : m = -1 ∨ m = 0 ∨ m = 1 := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_assoc] using hm
  rw [VirasoroAlgebra.lgen_bracket]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn]
    rcases hm' with hm' | hm' | hm' <;> subst m <;> norm_num
  · simp [hmn]

/-- Re-export the witness map with bridge naming. -/
def modularToLieVermaMap
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜}
    (map : VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M) :
    VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M :=
  map

/-- The map sends the Verma highest-weight vector to the witness vacuum. -/
theorem modularToLieVermaMap_hwVec
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜}
    (map : VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M) (omega : M)
    (hwVec_map : map (VirasoroVerma.hwVec 𝕜 c h) = omega) :
    modularToLieVermaMap (𝕜 := 𝕜) (M := M) (c := c) (h := h) map
      (VirasoroVerma.hwVec 𝕜 c h) = omega :=
  hwVec_map

/-- One-line intertwining clause for the enveloping action. -/
theorem modularToLieVermaMap_enveloping_smul
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜}
    (map : VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M)
    (X : VirasoroAlgebra 𝕜) (v : VirasoroVerma 𝕜 c h) :
    modularToLieVermaMap (𝕜 := 𝕜) (M := M) (c := c) (h := h) map
      (ιUEA 𝕜 X • v) =
      ιUEA 𝕜 X •
        modularToLieVermaMap (𝕜 := 𝕜) (M := M) (c := c) (h := h) map v := by
  simp [modularToLieVermaMap]

/-- A linear map between left modules preserves the action of a commutator as
the corresponding difference of iterated actions. -/
theorem ring_modular_intertwining_commutator_action
    {B V M : Type*} [Ring B] [AddCommGroup V] [Module B V] [AddCommGroup M] [Module B M]
    (f : V →ₗ[B] M) (X Y : B) (v : V) :
    f (X • (Y • v) - Y • (X • v)) =
      X • (Y • f v) - Y • (X • f v) := by
  rw [map_sub]
  simp only [f.map_smul]

/-- Construct the universal Virasoro Verma-module map from a target vector
satisfying the central, Cartan, and positive-mode highest-weight equations. -/
def constructedModularToLieVermaMap
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜}
    (omega : M)
    (omega_c : ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • omega =
      algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) c • omega)
    (omega_lzero : ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 0) • omega =
      algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) h • omega)
    (omega_lpos : ∀ n > 0, ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 n) • omega = 0) :
    VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M :=
  VirasoroVerma.universalMap 𝕜 M omega_c omega_lzero omega_lpos

/-- A module map out of the Virasoro Verma module is uniquely determined by
the image of its cyclic highest-weight vector. -/
theorem constructedModularToLieVermaMap_unique
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜} (omega : M)
    (omega_c : ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • omega =
      algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) c • omega)
    (omega_lzero : ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 0) • omega =
      algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) h • omega)
    (omega_lpos : ∀ n > 0, ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 n) • omega = 0)
    (map : VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M)
    (hmap : map (VirasoroVerma.hwVec 𝕜 c h) = omega) :
    map = constructedModularToLieVermaMap (𝕜 := 𝕜) omega omega_c omega_lzero omega_lpos := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span (𝓤 𝕜 (VirasoroAlgebra 𝕜))
      {VirasoroVerma.hwVec 𝕜 c h} := by
    rw [VirasoroVerma.hwVec_cyclic 𝕜 c h]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [hmap]
    exact (VirasoroVerma.universalMap_hwVec 𝕜 c h M omega_c
      omega_lzero omega_lpos).symm
  · simp
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro a x _ hx
    simp [hx]

/-- The target highest-weight equations give exactly one Virasoro Verma map
whose value on the cyclic highest-weight vector is `omega`. -/
theorem constructedModularToLieVermaMap_exists_unique
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜} (omega : M)
    (omega_c : ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • omega =
      algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) c • omega)
    (omega_lzero : ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 0) • omega =
      algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) h • omega)
    (omega_lpos : ∀ n > 0, ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 n) • omega = 0) :
    ∃! map : VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M,
      map (VirasoroVerma.hwVec 𝕜 c h) = omega := by
  refine ⟨constructedModularToLieVermaMap (𝕜 := 𝕜) omega omega_c omega_lzero omega_lpos,
    ?_, ?_⟩
  · exact VirasoroVerma.universalMap_hwVec 𝕜 c h M omega_c omega_lzero omega_lpos
  · intro map hmap
    exact constructedModularToLieVermaMap_unique (𝕜 := 𝕜) omega omega_c omega_lzero
      omega_lpos map hmap

end InfoGeometry.Bridge.ModularVirasoro
