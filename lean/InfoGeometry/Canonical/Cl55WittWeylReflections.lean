import InfoGeometry.Canonical.Cl55WittWeightReadout
import Mathlib.Data.ZMod.Basic

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittLieRouting

/-! Discrete Weyl data for the five-mode weight lattice.

This owner deliberately stops at the finite reflection action on weights.  It
does not claim that these reflections have already been lifted to Pin
operators on the 32-dimensional spinor carrier. -/

abbrev Weight := Fin 5 → ℤ

def permuteWeight (σ : Equiv.Perm (Fin 5)) (w : Weight) : Weight :=
  fun k => w (σ.symm k)

def signWeight (i : Fin 5) (w : Weight) : Weight :=
  fun k => if k = i then -w k else w k

def modeSwap (i j : Fin 5) : Equiv.Perm (Fin 5) := Equiv.swap i j

theorem permuteWeight_id (w : Weight) :
    permuteWeight (Equiv.refl (Fin 5)) w = w := by
  rfl

theorem permuteWeight_comp (σ τ : Equiv.Perm (Fin 5)) (w : Weight) :
    permuteWeight (τ.trans σ) w =
      permuteWeight σ (permuteWeight τ w) := by
  funext k
  simp [permuteWeight, Equiv.trans_apply]

theorem permuteWeight_add (σ : Equiv.Perm (Fin 5)) (w v : Weight) :
    permuteWeight σ (w + v) = permuteWeight σ w + permuteWeight σ v := by
  funext k
  simp [permuteWeight]

theorem permuteWeight_neg (σ : Equiv.Perm (Fin 5)) (w : Weight) :
    permuteWeight σ (-w) = -permuteWeight σ w := by
  funext k
  simp [permuteWeight]

theorem modeSwap_involutive (i j : Fin 5) (w : Weight) :
    permuteWeight (modeSwap i j) (permuteWeight (modeSwap i j) w) = w := by
  funext k
  simp [permuteWeight, modeSwap]

theorem signWeight_involutive (i : Fin 5) (w : Weight) :
    signWeight i (signWeight i w) = w := by
  funext k
  by_cases h : k = i <;> simp [signWeight, h]

theorem signWeight_add (i : Fin 5) (w v : Weight) :
    signWeight i (w + v) = signWeight i w + signWeight i v := by
  funext k
  by_cases h : k = i <;> simp [signWeight, h] <;> ring

theorem signWeight_neg (i : Fin 5) (w : Weight) :
    signWeight i (-w) = -signWeight i w := by
  funext k
  by_cases h : k = i <;> simp [signWeight, h]

theorem modeSwap_creationWeight (i j : Fin 5) :
    permuteWeight (modeSwap i j) (creationWeight i) = creationWeight j := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [permuteWeight, modeSwap, creationWeight, hki, hkj, eq_comm,
      Equiv.swap_apply_def]

theorem modeSwap_annihilationWeight (i j : Fin 5) :
    permuteWeight (modeSwap i j) (annihilationWeight i) =
      annihilationWeight j := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [permuteWeight, modeSwap, annihilationWeight, hki, hkj, eq_comm,
      Equiv.swap_apply_def]

theorem signWeight_creationWeight_self (i : Fin 5) :
    signWeight i (creationWeight i) = -(creationWeight i) := by
  funext k
  by_cases h : k = i <;> simp [signWeight, creationWeight, h]

theorem signWeight_annihilationWeight_self (i : Fin 5) :
    signWeight i (annihilationWeight i) = -(annihilationWeight i) := by
  funext k
  by_cases h : k = i <;> simp [signWeight, annihilationWeight, h]

/-! The finite label set has the cardinality of the hyperoctahedral Weyl
group.  It is a label set here, not yet a bundled semidirect-product group. -/

abbrev SignedModeWeylLabel :=
  (Fin 5 → Bool) × Equiv.Perm (Fin 5)

theorem signedModeWeylLabel_card :
    Fintype.card SignedModeWeylLabel = 3840 := by
  simp [SignedModeWeylLabel, Fintype.card_pi, Fintype.card_perm]
  norm_num

end InfoGeometry.Canonical.Cl55WittLieRouting
