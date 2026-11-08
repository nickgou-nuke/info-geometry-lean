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

/-- Witness-gated local highest-weight to Verma interface. -/
structure modularVirasoroHighestWeightData
    (M : Type*) [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    (c h : 𝕜) where
  omega : M
  map : VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M
  hwVec_map : map (VirasoroVerma.hwVec 𝕜 c h) = omega

/-- Re-export the witness map with bridge naming. -/
def modularToLieVermaMap
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜}
    (D : modularVirasoroHighestWeightData (𝕜 := 𝕜) M c h) :
    VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M :=
  D.map

/-- The map sends the Verma highest-weight vector to the witness vacuum. -/
theorem modularToLieVermaMap_hwVec
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜}
    (D : modularVirasoroHighestWeightData (𝕜 := 𝕜) M c h) :
    modularToLieVermaMap (𝕜 := 𝕜) (M := M) (c := c) (h := h) D
      (VirasoroVerma.hwVec 𝕜 c h) = D.omega :=
  D.hwVec_map

/-- One-line intertwining clause for the enveloping action. -/
theorem modularToLieVermaMap_enveloping_smul
    {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]
    {c h : 𝕜}
    (D : modularVirasoroHighestWeightData (𝕜 := 𝕜) M c h)
    (X : VirasoroAlgebra 𝕜) (v : VirasoroVerma 𝕜 c h) :
    modularToLieVermaMap (𝕜 := 𝕜) (M := M) (c := c) (h := h) D
      (ιUEA 𝕜 X • v) =
      ιUEA 𝕜 X •
        modularToLieVermaMap (𝕜 := 𝕜) (M := M) (c := c) (h := h) D v := by
  simpa [modularToLieVermaMap] using D.map.map_smul (ιUEA 𝕜 X) v

end InfoGeometry.Bridge.ModularVirasoro
