/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Canonical.Cl11TensorTowerGlobalParity

/-!
# Chirality transport for the `Cl(1,1)` matrix tower

This module proves that the chirality conjugation of the finite `Cl(1,1)`
matrix tower is compatible with the tower bonding maps, and therefore
descends to an involutive ring endomorphism of the algebraic direct limit
`Cl11TensorTowerLimit.Limit`.

The one-step embedding `matStageEmbed n : A ↦ A ⊗ I₂` does **not** fix the
stage chirality element `globalChirality n` pointwise: it sends `Γ_n` to
`Γ_n ⊗ I₂`, while `Γ_{n+1} = Γ_n ⊗ γ_chiral_base`. The correct compatibility
is the conjugation identity `matStageEmbed_globalChirality_conj` below, i.e.
`A ↦ Γ A Γ` is natural for the bonding maps. This is the exact statement
that makes the conjugation a morphism of towers rather than a family of
unrelated stage automorphisms.

New results (nothing here restates an existing declaration):
* `matStageEmbed_globalChirality_conj` — the bond-compatibility of the
  conjugation at the matrix level.
* `normalizedTrace_globalChirality_conj` — the finite normalized trace is
  invariant under the conjugation.
* `Cl11TensorTowerLimit.stageChiralityConj` / `stageChiralityConj_bond` /
  `limitChiralityConj` — the induced stage automorphisms and their descended
  endomorphism of the algebraic direct limit.
* `limitChiralityConj_ofStage`, `limitChiralityConj_involutive` and the
  action on the Jordan–Wigner generators inserted into the limit.

No analytic completion, no operator-norm closure, and no second carrier are
introduced: the direct limit is the algebraic direct limit of the finite
matrix stages, and every statement is a kernel-checked consequence of
finite matrix identities and the existing exact direct-limit kit.
-/

noncomputable section

open scoped Matrix Kronecker

namespace InfoGeometry.Clifford.Cl11TensorTower

open Matrix

/-- Chirality conjugation is compatible with the one-step tensor embedding:
conjugation by `Γ_{n+1} = Γ_n ⊗ γ_chiral_base` on the `(n+1)`-stage
implements conjugation by `Γ_n` on the head factor. -/
theorem matStageEmbed_globalChirality_conj (n : ℕ) (x : MatStage n) :
    matStageEmbed n (globalChirality n * x * globalChirality n) =
      globalChirality (n + 1) * matStageEmbed n x * globalChirality (n + 1) := by
  show ((globalChirality n * x * globalChirality n) ⊗ₖ
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
    (globalChirality n ⊗ₖ gamma_chiral_base) *
      (x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (globalChirality n ⊗ₖ gamma_chiral_base)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [mul_one, InfoGeometry.Clifford.JordanWignerCAR.gamma_chiral_base_sq]

/-- The binary-volume normalized trace is invariant under chirality
conjugation. -/
theorem normalizedTrace_globalChirality_conj (n : ℕ) (x : MatStage n) :
    normalizedTrace n (globalChirality n * x * globalChirality n) =
      normalizedTrace n x := by
  have hΓ := InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
  unfold normalizedTrace
  congr 1
  rw [mul_assoc,
    Matrix.trace_mul_comm (globalChirality n) (x * globalChirality n),
    mul_assoc, hΓ, mul_one]

end InfoGeometry.Clifford.Cl11TensorTower

namespace InfoGeometry.Clifford.Cl11TensorTowerLimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The chirality conjugation `x ↦ Γ_n x Γ_n` as a ring endomorphism of the
stage-`n` matrix algebra. -/
noncomputable def stageChiralityConj (n : ℕ) : Stage n →+* Stage n where
  toFun x := globalChirality n * x * globalChirality n
  map_one' := by
    rw [mul_one, InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq]
  map_mul' x y := by
    have hΓ := InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
    calc globalChirality n * (x * y) * globalChirality n
        = (globalChirality n * x) * (globalChirality n * globalChirality n) *
            (y * globalChirality n) := by
          rw [hΓ]
          noncomm_ring
      _ = (globalChirality n * x * globalChirality n) *
            (globalChirality n * y * globalChirality n) := by
          noncomm_ring
  map_zero' := by
    simp
  map_add' x y := by
    show globalChirality n * (x + y) * globalChirality n =
      globalChirality n * x * globalChirality n +
        globalChirality n * y * globalChirality n
    rw [mul_add, add_mul]

/-- The stage chirality conjugations are compatible with the bonding maps of
the tower. -/
theorem stageChiralityConj_bond (n : ℕ) (x : Stage n) :
    stageChiralityConj (n + 1) (stageBond n x) =
      stageBond n (stageChiralityConj n x) := by
  show globalChirality (n + 1) * matStageEmbed n x * globalChirality (n + 1) =
    matStageEmbed n (globalChirality n * x * globalChirality n)
  exact (matStageEmbed_globalChirality_conj n x).symm

/-- The chirality conjugation descended to the algebraic direct limit. -/
noncomputable def limitChiralityConj : Limit →+* Limit :=
  directLimitEndomorphism stageBond stageChiralityConj stageChiralityConj_bond

/-- The descended conjugation acts on each finite stage as conjugation by the
stage chirality element. -/
@[simp]
theorem limitChiralityConj_ofStage (n : ℕ) (x : Stage n) :
    limitChiralityConj (ofStage n x) =
      ofStage n (globalChirality n * x * globalChirality n) :=
  directLimitEndomorphism_of stageBond stageChiralityConj stageChiralityConj_bond n x

/-- The descended chirality conjugation is an involution of the direct
limit. -/
theorem limitChiralityConj_involutive (x : Limit) :
    limitChiralityConj (limitChiralityConj x) = x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change limitChiralityConj (limitChiralityConj (ofStage n A)) = ofStage n A
      rw [limitChiralityConj_ofStage, limitChiralityConj_ofStage]
      congr 1
      have hΓ := InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
      calc globalChirality n * (globalChirality n * A * globalChirality n) *
            globalChirality n
          = (globalChirality n * globalChirality n) * A *
              (globalChirality n * globalChirality n) := by
            noncomm_ring
        _ = A := by
            rw [hΓ]
            simp

/-- The descended conjugation negates the Jordan–Wigner creation strings at
every insertion stage. -/
theorem limitChiralityConj_jwCreation (n : ℕ) (k : Fin n) :
    limitChiralityConj (ofStage n (jwCreation n k)) =
      -ofStage n (jwCreation n k) := by
  rw [limitChiralityConj_ofStage]
  have hΓ := InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
  have hanti :=
    InfoGeometry.Canonical.Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwCreation n k
  have hconj : globalChirality n * jwCreation n k * globalChirality n =
      -jwCreation n k := by
    calc globalChirality n * jwCreation n k * globalChirality n
        = -(jwCreation n k * (globalChirality n * globalChirality n)) := by
          rw [eq_neg_of_add_eq_zero_left hanti, neg_mul, mul_assoc]
      _ = -jwCreation n k := by
          rw [hΓ, mul_one]
  rw [hconj, ofStage_neg]

/-- The descended conjugation negates the Jordan–Wigner annihilation strings
at every insertion stage. -/
theorem limitChiralityConj_jwAnnihilation (n : ℕ) (k : Fin n) :
    limitChiralityConj (ofStage n (jwAnnihilation n k)) =
      -ofStage n (jwAnnihilation n k) := by
  rw [limitChiralityConj_ofStage]
  have hΓ := InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
  have hanti :=
    InfoGeometry.Canonical.Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwAnnihilation n k
  have hconj : globalChirality n * jwAnnihilation n k * globalChirality n =
      -jwAnnihilation n k := by
    calc globalChirality n * jwAnnihilation n k * globalChirality n
        = -(jwAnnihilation n k * (globalChirality n * globalChirality n)) := by
          rw [eq_neg_of_add_eq_zero_left hanti, neg_mul, mul_assoc]
      _ = -jwAnnihilation n k := by
          rw [hΓ, mul_one]
  rw [hconj, ofStage_neg]

end InfoGeometry.Clifford.Cl11TensorTowerLimit
