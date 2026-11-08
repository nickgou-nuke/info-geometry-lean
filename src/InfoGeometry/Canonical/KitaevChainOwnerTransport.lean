/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Canonical.KitaevChainKernel

/-! Identify the two native finite bond sums by reindexing, preserving the
noncommutative operator carrier and the order of every bond product. -/
namespace InfoGeometry.Quantum.KitaevChain
open scoped BigOperators
open InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
variable {A : Type*} [Ring A] {N : ℕ}

theorem sweetSpotHamiltonian_eq_canonical (ops : MajoranaOperators N A) (t : A) :
    sweetSpotHamiltonian ops t = kitaevSweetSpotHamiltonian N t ops.γ := by
  unfold sweetSpotHamiltonian kitaevSweetSpotHamiltonian
  apply Finset.sum_bij (fun j _ => (⟨j.val, Finset.mem_range.mp j.property⟩ : Fin (N - 1)))
  · intro j hj
    exact Finset.mem_univ _
  · intro a ha b hb h
    apply Subtype.ext
    exact congrArg Fin.val h
  · intro b hb
    exact ⟨⟨b.val, Finset.mem_range.mpr b.isLt⟩, Finset.mem_attach _ _, rfl⟩
  · intro j hj
    rfl

theorem MajoranaCliffordOperators.isMajoranaBasis (ops : MajoranaCliffordOperators N A) :
    IsMajoranaBasis N ops.γ := by
  intro i j
  by_cases h : i = j
  · subst j
    simp [ops.h_sq, show (1 : A) + 1 = 2 by norm_num]
  · simpa only [h, ite_false] using ops.h_ortho i j h

/-- The full conserved-span characterization also holds for the attached-range
Hamiltonian in the original Quantum owner. -/
theorem sweetSpot_conserved_iff_interior_zero [Algebra ℝ A] [Nontrivial A]
    (ops : MajoranaCliffordOperators N A) (t : ℝ) (ht : t ≠ 0)
    (v : Fin (2 * N) → ℝ) :
    commutator (sweetSpotHamiltonian ops.toMajoranaOperators (t • (1 : A)))
        (Fintype.linearCombination ℝ ops.γ v) = 0 ↔
      ∀ i : Fin (2 * N), 0 < i.val ∧ i.val + 1 < 2 * N → v i = 0 := by
  rw [sweetSpotHamiltonian_eq_canonical]
  exact InfoGeometry.Canonical.KitaevChainKernel.chain_conserved_iff_interior_zero
    ops.γ ops.isMajoranaBasis t ht v

end InfoGeometry.Quantum.KitaevChain
