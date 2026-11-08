/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MajoranaPHSZeroMode
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Krein.PolarizedSector

/-!
# Majorana nilpotent maps between the two real Krein sheets

The split-null creation and annihilation maps connect the epsilon sheets in
opposite directions. Their vector kernels are the sheet on which each map
vanishes. The PHS-invariant Majorana sum is the modular sheet swap; it is not
asserted to be a vector zero mode.
-/

namespace InfoGeometry.Krein.MajoranaSheetConnectors

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.MajoranaPHSZeroMode
open InfoGeometry.Canonical.ChiralHodgeDecomposition

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Creation kills exactly the positive sheet and reads the second coordinate
into that sheet. -/
theorem creation_kernel_iff_plusSheet (u : H₂) :
    concreteCARCreation (E := E) u = 0 ↔ u ∈ plusSheet (E := E) := by
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  rw [cliffordConcreteCreation_apply_to_doubled]
  constructor
  · intro h
    apply (mem_plusSheet_iff_snd_eq_zero (E := E) _).2
    have hcoord := congrArg WithLp.fst h
    simpa [to_doubled] using hcoord
  · intro h
    have hsnd := (mem_plusSheet_iff_snd_eq_zero (E := E) _).1 h
    have hsnd' : WithLp.snd u = 0 := by simpa [to_doubled] using hsnd
    apply DoubledSpace.ext <;> simp [to_doubled, hsnd']

/-- Annihilation kills exactly the negative sheet and reads the first
coordinate into that sheet. -/
theorem annihilation_kernel_iff_minusSheet (u : H₂) :
    concreteCARAnnihilation (E := E) u = 0 ↔ u ∈ minusSheet (E := E) := by
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  rw [cliffordConcreteAnnihilation_apply_to_doubled]
  constructor
  · intro h
    apply (mem_minusSheet_iff_fst_eq_zero (E := E) _).2
    have hcoord := congrArg WithLp.snd h
    simpa [to_doubled] using hcoord
  · intro h
    have hfst := (mem_minusSheet_iff_fst_eq_zero (E := E) _).1 h
    have hfst' : WithLp.fst u = 0 := by simpa [to_doubled] using hfst
    apply DoubledSpace.ext <;> simp [to_doubled, hfst']

/-- The image of creation is exactly the positive sheet. -/
theorem creation_range_iff_plusSheet (u : H₂) :
    (∃ v : H₂, concreteCARCreation (E := E) v = u) ↔
      u ∈ plusSheet (E := E) := by
  constructor
  · rintro ⟨v, hv⟩
    have hv' : (to_doubled (WithLp.fst v) (WithLp.snd v) : H₂) = v := by
      apply DoubledSpace.ext <;> simp [to_doubled]
    rw [← hv'] at hv
    rw [cliffordConcreteCreation_apply_to_doubled] at hv
    apply (mem_plusSheet_iff_snd_eq_zero (E := E) u).2
    have hcoord := congrArg WithLp.snd hv
    simpa [to_doubled] using hcoord.symm
  · intro hu
    refine ⟨minusPoint (E := E) (WithLp.fst u), ?_⟩
    change cliffordConcreteCreation (E := E)
      (to_doubled 0 (WithLp.fst u)) = u
    rw [cliffordConcreteCreation_apply_to_doubled]
    exact (eq_plusPoint_of_mem_plusSheet hu).symm

/-- The image of annihilation is exactly the negative sheet. -/
theorem annihilation_range_iff_minusSheet (u : H₂) :
    (∃ v : H₂, concreteCARAnnihilation (E := E) v = u) ↔
      u ∈ minusSheet (E := E) := by
  constructor
  · rintro ⟨v, hv⟩
    have hv' : (to_doubled (WithLp.fst v) (WithLp.snd v) : H₂) = v := by
      apply DoubledSpace.ext <;> simp [to_doubled]
    rw [← hv'] at hv
    rw [cliffordConcreteAnnihilation_apply_to_doubled] at hv
    apply (mem_minusSheet_iff_fst_eq_zero (E := E) u).2
    have hcoord := congrArg WithLp.fst hv
    simpa [to_doubled] using hcoord.symm
  · intro hu
    refine ⟨plusPoint (E := E) (WithLp.snd u), ?_⟩
    change cliffordConcreteAnnihilation (E := E)
      (to_doubled (WithLp.snd u) 0) = u
    rw [cliffordConcreteAnnihilation_apply_to_doubled]
    exact (eq_minusPoint_of_mem_minusSheet hu).symm

/-- Creation transports a canonical negative-sheet vector to the positive
sheet with the same coordinate. -/
theorem creation_maps_minusPoint_to_plusPoint (ξ : E) :
    concreteCARCreation (E := E) (minusPoint (E := E) ξ) =
      plusPoint (E := E) ξ := by
  change cliffordConcreteCreation (E := E) (to_doubled 0 ξ) = to_doubled ξ 0
  rw [cliffordConcreteCreation_apply_to_doubled]

/-- Annihilation transports a canonical positive-sheet vector to the negative
sheet with the same coordinate. -/
theorem annihilation_maps_plusPoint_to_minusPoint (x : E) :
    concreteCARAnnihilation (E := E) (plusPoint (E := E) x) =
      minusPoint (E := E) x := by
  change cliffordConcreteAnnihilation (E := E) (to_doubled x 0) = to_doubled 0 x
  rw [cliffordConcreteAnnihilation_apply_to_doubled]

/-- The PHS-invariant Majorana sum swaps a positive-sheet vector to the
negative sheet. -/
theorem majorana_swap_maps_plusPoint_to_minusPoint (x : E) :
    (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))
        (plusPoint (E := E) x) = minusPoint (E := E) x := by
  rw [concrete_majorana_swap_eq_modular_j, modular_j_plusPoint]

/-- The PHS-invariant Majorana sum swaps a negative-sheet vector to the
positive sheet. -/
theorem majorana_swap_maps_minusPoint_to_plusPoint (ξ : E) :
    (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))
        (minusPoint (E := E) ξ) = plusPoint (E := E) ξ := by
  rw [concrete_majorana_swap_eq_modular_j, modular_j_minusPoint]

/-- The PHS-invariant Majorana sheet swap has trivial vector kernel.
This distinguishes the invertible sheet connector from a Hamiltonian
zero-mode vector. -/
theorem majorana_swap_kernel_iff_zero (u : H₂) :
    (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) u = 0 ↔
      u = 0 := by
  rw [concrete_majorana_swap_eq_modular_j]
  constructor
  · intro hu
    have hju := congrArg (modular_j (E := E)) hu
    have hinv : modular_j (E := E) (modular_j (E := E) u) = u := by
      change ((modular_j (E := E)).comp modular_j) u = u
      rw [modular_j_involution E]
      simp
    calc
      u = modular_j (E := E) (modular_j (E := E) u) := hinv.symm
      _ = modular_j (E := E) 0 := hju
      _ = 0 := map_zero _
  · rintro rfl
    simp

end Core

end InfoGeometry.Krein.MajoranaSheetConnectors
