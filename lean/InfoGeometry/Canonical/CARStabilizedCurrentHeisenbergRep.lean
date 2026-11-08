/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner

/-!
# Canonical CAR-Stabilized Current Heisenberg Representation

This module proves the diagonal and off-diagonal mode commutator specializations
of the CAR-stabilized fermionic current modes `fermionicCurrentMode` on the
exterior-Fock carrier `FermionicFock`.

## 1. Real Math in This File
- `fermionicCurrentMode_commutator_diag`
- `fermionicCurrentMode_commutator_offDiag`

## 2. Meaningful Mathematical Results Used
- `InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner`
  (`fermionicCurrentMode`, `fermionicCurrentMode_commutator`)

## 3. Excluded Wrapper Patterns
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Canonical.CARStabilizedCurrentHeisenbergRep

open InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Diagonal Heisenberg commutator `[J_m, J_{-m}] = (m : 𝕜) • 1` for the
CAR-stabilized fermionic current modes on `FermionicFock (𝕜 := 𝕜)`. -/
theorem fermionicCurrentMode_commutator_diag (m : ℤ) :
    (fermionicCurrentMode (𝕜 := 𝕜) m).commutator
        (fermionicCurrentMode (𝕜 := 𝕜) (-m)) =
      (m : 𝕜) • (1 : Module.End 𝕜 (FermionicFock (𝕜 := 𝕜))) := by
  rw [fermionicCurrentMode_commutator (𝕜 := 𝕜) m (-m)]
  have hm : m + -m = 0 := add_neg_cancel m
  simp only [hm, ↓reduceIte]

/-- Off-diagonal commutator vanishing `[J_m, J_n] = 0` for `m + n ≠ 0` on
`FermionicFock (𝕜 := 𝕜)`. -/
theorem fermionicCurrentMode_commutator_offDiag {m n : ℤ} (hmn : m + n ≠ 0) :
    (fermionicCurrentMode (𝕜 := 𝕜) m).commutator
        (fermionicCurrentMode (𝕜 := 𝕜) n) = 0 := by
  rw [fermionicCurrentMode_commutator (𝕜 := 𝕜) m n]
  simp only [hmn, ↓reduceIte]

end InfoGeometry.Canonical.CARStabilizedCurrentHeisenbergRep
