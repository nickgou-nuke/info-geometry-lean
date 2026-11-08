/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction
import InfoGeometry.OperatorAlgebra.ModeShiftInterface

/-!
# Heisenberg `ModuleCat` Colimit Canonical Commutation Relation & Virasoro Mode Shift

This module constructs the canonical singleton representatives
`heisenbergColimitMode k` inside the filtered `ModuleCat 𝕜` colimit
`heisenbergFiniteModeColimit`, proves the intrinsic categorical colimit
Heisenberg canonical commutation relation
$\bigl[\hat{J}_k, \hat{J}_l\bigr] = \delta_{k+l,0}\,k\,\hat{K}$, and connects
the colimit mode readout to the Sugawara Virasoro grading shift on charged Fock
space.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeColimit`:
    `heisenbergFiniteModeColimit`, `heisenbergFiniteModeColimitMap`,
    `heisenbergFiniteModeColimitEquiv`, `heisenbergFiniteModeColimitLieEquiv`,
    `heisenbergCentralColimitMode`.
  * `InfoGeometry.Canonical.CurrentSugawaraBridge`:
    `chargedFockSpaceCurrentHeisenbergRep`, `sugawara_current_mode_shift`.
- BUCKET 2 (Deconfabulation):
  * Replaced the diagnostic conjunction `colimit_mode_map_packet` and the
    definitional `rfl` wrapper `chargedFock_colimit_mode_representation_readout`
    with the intrinsic colimit Heisenberg commutator `heisenbergColimitMode_lie_eq`,
    central annihilation `heisenbergColimitMode_lie_central`, and the
    Sugawara Virasoro shift theorem `chargedFock_colimit_mode_virasoro_shift`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergColimitMode`, `heisenbergFiniteModeColimitMap_mode`,
    `heisenbergFiniteModeColimitEquiv_mode`: singleton colimit mode representatives
    and their comparison readouts.
  * `heisenbergColimitMode_lie_eq`, `heisenbergColimitMode_lie_central`:
    intrinsic Heisenberg CCR $\bigl[\hat{J}_k, \hat{J}_l\bigr] = \delta_{k+l,0}\,k\,\hat{K}$
    and centrality $\bigl[\hat{K}, \hat{J}_k\bigr] = 0$ inside `heisenbergFiniteModeColimit`.
  * `chargedFock_vira_mode_shift`, `chargedFock_hasModeShift`,
    `chargedFock_vira_mapsToModeSpanGrade`, `chargedFock_vira_mode_mem_shifted_span`,
    `chargedFock_double_vira_mode_shift`, `chargedFock_colimit_mode_virasoro_shift`:
    Sugawara Virasoro $[L_n, J_m] = -m J_{n+m}$ mode shift on charged Fock space.
-/

noncomputable section

namespace InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

open CategoryTheory CategoryTheory.Limits
open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SugawaraFiveGradingObstruction
open InfoGeometry.OperatorAlgebra

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Canonical singleton representative of the Heisenberg mode `J_k` inside the
categorical `ModuleCat 𝕜` colimit `heisenbergFiniteModeColimit`. -/
noncomputable def heisenbergColimitMode (k : ℤ) :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) :=
  let s : Finset (Option ℤ) := {some k}
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    ⟨HeisenbergAlgebra.jgen 𝕜 k, heisenberg_mode_stage_contains_jgen (𝕜 := 𝕜) k⟩
  (colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x

/-- The comparison map `heisenbergFiniteModeColimitMap` sends
`heisenbergColimitMode k` to `HeisenbergAlgebra.jgen 𝕜 k`. -/
theorem heisenbergFiniteModeColimitMap_mode (k : ℤ) :
    (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k := by
  let s : Finset (Option ℤ) := {some k}
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    ⟨HeisenbergAlgebra.jgen 𝕜 k, heisenberg_mode_stage_contains_jgen (𝕜 := 𝕜) k⟩
  change (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = _
  have h := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
  have hstage := congrArg (fun f => f.hom) h
  exact congrArg (fun g => g x) hstage

/-- Evaluating `heisenbergFiniteModeColimitEquiv` on `heisenbergColimitMode k`
returns `HeisenbergAlgebra.jgen 𝕜 k`. -/
@[simp] theorem heisenbergFiniteModeColimitEquiv_mode (k : ℤ) :
    heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k := by
  change (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      (heisenbergColimitMode (𝕜 := 𝕜) k) =
    HeisenbergAlgebra.jgen 𝕜 k
  exact heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) k

/-- **Intrinsic Categorical Colimit Heisenberg Canonical Commutation Relation**:
Directly inside `heisenbergFiniteModeColimit`, two singleton mode representatives
`heisenbergColimitMode k` and `heisenbergColimitMode l` satisfy
$\bigl[\hat{J}_k, \hat{J}_l\bigr] = \delta_{k+l,0}\,k\,\hat{K}$. -/
theorem heisenbergColimitMode_lie_eq (k l : ℤ) :
    ⁅heisenbergColimitMode (𝕜 := 𝕜) k,
      heisenbergColimitMode (𝕜 := 𝕜) l⁆ =
      if k + l = 0 then
        (k : 𝕜) • heisenbergCentralColimitMode (𝕜 := 𝕜)
      else 0 := by
  apply heisenbergFiniteModeColimitMap_injective (𝕜 := 𝕜)
  rw [heisenbergFiniteModeColimitMap_map_lie (𝕜 := 𝕜),
    heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) k,
    heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) l,
    HeisenbergAlgebra.lie_jgen]
  by_cases hkl : k + l = 0
  · simp only [hkl, ↓reduceIte, map_smul, heisenbergFiniteModeColimitMap_central (𝕜 := 𝕜)]
  · simp only [hkl, ↓reduceIte, map_zero]

/-- **Intrinsic Categorical Colimit Heisenberg Centrality**:
Directly inside `heisenbergFiniteModeColimit`, the central representative
`heisenbergCentralColimitMode` commutes with every mode `heisenbergColimitMode k`. -/
theorem heisenbergColimitMode_lie_central (k : ℤ) :
    ⁅heisenbergCentralColimitMode (𝕜 := 𝕜),
      heisenbergColimitMode (𝕜 := 𝕜) k⁆ = 0 := by
  apply heisenbergFiniteModeColimitMap_injective (𝕜 := 𝕜)
  rw [heisenbergFiniteModeColimitMap_map_lie (𝕜 := 𝕜),
    heisenbergFiniteModeColimitMap_central (𝕜 := 𝕜),
    heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) k,
    HeisenbergAlgebra.lie_kgen, map_zero]

/-- The Sugawara Virasoro generator $L_n$ shifts the charged-Fock Heisenberg
current $J_m$ according to $[L_n, J_m] = -m J_{n+m}$. -/
theorem chargedFock_vira_mode_shift
    (α : 𝕜) (n m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m) =
        (-m : 𝕜) • (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + m) := by
  rw [CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply]
  unfold CurrentHeisenbergRep.sugawaraStressMode
  have h := sugawara_current_mode_shift
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm n m
  rw [h]
  have hcast : ((-m : ℤ) : 𝕜) • (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + m) =
      (-m : 𝕜) • (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + m) := by
    norm_cast
  rw [← hcast]
  exact (Int.cast_smul_eq_zsmul 𝕜 (-m) ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + m))).symm

/-- The Sugawara Virasoro commutator action satisfies the `HasModeShift`
interface on the charged-Fock Heisenberg modes. -/
theorem chargedFock_hasModeShift (α : 𝕜) :
    HasModeShift
      (fun n X =>
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator X)
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
      (fun n m => n + m)
      (fun _ m => (-m : 𝕜)) := by
  intro n m
  exact chargedFock_vira_mode_shift (𝕜 := 𝕜) α n m

/-- The Sugawara Virasoro commutator maps `ModeSpanGrade m` into `ModeSpanGrade (n + m)`. -/
theorem chargedFock_vira_mapsToModeSpanGrade (α : 𝕜) :
    MapsToGrade
      (ModeSpanGrade (R := 𝕜)
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J))
      (fun n X =>
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator X)
      (fun n m => n + m) := by
  apply HasModeShift.mapsToModeSpanGrade
    (hlinear := by
      intro n c X
      simp only [LinearMap.commutator, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub])
  exact chargedFock_hasModeShift (𝕜 := 𝕜) α

/-- Commuting $L_n$ with $J_m$ lands in the shifted mode-span grade `n + m`. -/
theorem chargedFock_vira_mode_mem_shifted_span
    (α : 𝕜) (n m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m) ∈
      ModeSpanGrade (R := 𝕜)
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J) (n + m) := by
  apply HasModeShift.mode_mem_shifted_grade
    (chargedFock_hasModeShift (𝕜 := 𝕜) α)
  intro i c
  exact ⟨c, Eq.refl _⟩

/-- Iterated Sugawara Virasoro commutator $[L_n, [L_n, J_m]] = m(n+m) J_{2n+m}$. -/
theorem chargedFock_double_vira_mode_shift (α : 𝕜) (n m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      (((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m)) =
      (m * (n + m) : 𝕜) •
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + (n + m)) := by
  have h := HasModeShift.comp
    (shift₁ := fun r q => r + q)
    (shift₂ := fun r q => r + q)
    (coeff₁ := fun _ q => (-q : 𝕜))
    (coeff₂ := fun _ q => (-q : 𝕜))
    (hlinear := by
      intro r c X
      simp only [LinearMap.commutator, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub])
    (chargedFock_hasModeShift (𝕜 := 𝕜) α)
    (chargedFock_hasModeShift (𝕜 := 𝕜) α)
  have hh := h n m
  ring_nf at hh ⊢
  have hs : (m : 𝕜) * (n + m : 𝕜) =
      (m : 𝕜) * n + (m : 𝕜) ^ 2 := by
    ring
  push_cast at hh
  rw [hs] at hh
  exact hh

/-- The Sugawara Virasoro generator $L_n$ shifts the represented colimit mode
`chargedFockSpaceHeisenbergMode 𝕜 α m` to `(-m : 𝕜) • chargedFockSpaceHeisenbergMode 𝕜 α (n + m)`. -/
theorem chargedFock_colimit_mode_virasoro_shift
    (α : 𝕜) (n m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      (chargedFockSpaceHeisenbergMode 𝕜 α m) =
      (-m : 𝕜) • chargedFockSpaceHeisenbergMode 𝕜 α (n + m) := by
  change ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m) =
    (-m : 𝕜) • (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + m)
  exact chargedFock_vira_mode_shift α n m

end InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

end noncomputable section
