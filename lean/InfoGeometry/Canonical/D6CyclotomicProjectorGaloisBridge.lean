/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.CrystallographicRootCyclotomicBridge
import InfoGeometry.Algebra.CyclotomicOperatorProjectors
import InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge

/-!
# InfoGeometry.Canonical.D6CyclotomicProjectorGaloisBridge

Structural bridge connecting the three cyclotomic layers in the repository
without conflating distinct groups as equalities:

1. **Crystallographic `D₆` / `Φ₆` restriction**
   (`CrystallographicRootCyclotomicBridge`):
   `axialRotateEnd : Module.End ℤ ReciprocalCoord` satisfies `Φ₆(T) = T² - T + 1 = 0`,
   hence `T³ = -1` and `T⁶ = 1` (`IsRootOfUnity axialRotateEnd 6`), while the
   dihedral reflection `axialReflectEnd` satisfies `S² = 1` and
   `S * T * S = T⁵` (the order-2 conjugation matching `5 ∈ (ℤ/6)^×` on `ℤ[T]`).
2. **Cyclotomic operator projectors** (`CyclotomicOperatorProjectors`):
   `axialRotateEnd` is `7`-potent (`T⁷ = T`), so its `7`-potent spectral
   separation yields `npotentNonzeroProjector axialRotateEnd 7 = 1` and
   `npotentZeroProjector axialRotateEnd 7 = 0` (invertible unit on the lattice),
   and over `ℚ`/`ℝ` the reflection `S` yields the exact orthogonal `±1`
   spectral idempotents `p₊ = (1/2) • (1 + S)` and `p₋ = (1/2) • (1 - S)`.
3. **Cyclotomic Galois action & quadratic-character Boolean signs**
   (`CyclotomicQuadraticBooleanSignBridge`):
   connects `(ZMod 6)ˣ` (via `cyclotomicGaloisAction 6`) and the prime-`3`
   quadratic character `primeQuadCharHom 3 : (ZMod 3)ˣ →* ℤˣ` (surjective)
   to `weylSign (nonResidueWeyl L u)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.D6CyclotomicProjectorGaloisBridge

open InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone
open InfoGeometry.Canonical.CrystallographicRootCyclotomicBridge
open InfoGeometry.Algebra.CyclotomicOperatorProjectors
open InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge
open InfoGeometry.Canonical.FormalPrimeRootSystem

/-! ## 1. `D₆` reflection endomorphism and dihedral conjugation `S * T * S = T⁵` -/

/-- The axial `D₆` reflection as a `ℤ`-linear endomorphism of `ReciprocalCoord`. -/
def axialReflectEnd : Module.End ℤ ReciprocalCoord where
  toFun := axialReflect
  map_add' p q := by
    funext i
    fin_cases i <;> simp [axialReflect]
  map_smul' a p := by
    funext i
    fin_cases i <;> simp [axialReflect]

/-- `axialReflectEnd` is an involution (`S² = 1`). -/
theorem axialReflectEnd_sq : axialReflectEnd ^ 2 = 1 := by
  ext p i
  fin_cases i <;> simp [axialReflectEnd, axialReflect, pow_two]

/-- `axialRotateEnd` satisfies `T³ = -1` from `Φ₆(T) = T² - T + 1 = 0`. -/
theorem axialRotateEnd_cube : axialRotateEnd ^ 3 = -1 := by
  ext p i
  fin_cases i <;> simp [axialRotateEnd, axialRotate, pow_succ]

/-- Dihedral conjugation in `Module.End ℤ ReciprocalCoord`:
`S * T * S = T⁵` (the inverse of `T`, realizing the nontrivial Galois
automorphism `ζ₆ ↦ ζ₆⁵ = ζ₆⁻¹` of `(ℤ/6)^×` on the cyclotomic subring `ℤ[T]`). -/
theorem axialReflectEnd_conjugates_axialRotateEnd :
    axialReflectEnd * axialRotateEnd * axialReflectEnd = axialRotateEnd ^ 5 := by
  ext p i
  fin_cases i <;>
    simp [axialReflectEnd, axialRotateEnd, axialReflect, axialRotate, pow_succ]

/-- Explicit non-commutativity witness in `Module.End ℤ ReciprocalCoord`:
`D₆` reflection and order-6 rotation do not commute. -/
theorem axialReflectEnd_axialRotateEnd_noncomm :
    axialReflectEnd * axialRotateEnd ≠ axialRotateEnd * axialReflectEnd := by
  intro h
  have hp : (axialReflectEnd * axialRotateEnd) ![1, 0] 0 =
      (axialRotateEnd * axialReflectEnd) ![1, 0] 0 := by
    rw [h]
  simp [axialReflectEnd, axialRotateEnd, axialReflect, axialRotate] at hp

/-! ## 2. Bridge to `CyclotomicOperatorProjectors` -/

/-- `axialRotateEnd` is a 6th root of unity in `Module.End ℤ ReciprocalCoord`. -/
theorem axialRotateEnd_isRootOfUnity_six :
    IsRootOfUnity axialRotateEnd 6 :=
  axialRotateEnd_pow_six

/-- `axialRotateEnd` is 7-potent (`T⁷ = T`). -/
theorem axialRotateEnd_isNPotent_seven :
    IsNPotent axialRotateEnd 7 := by
  unfold IsNPotent
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, axialRotateEnd_pow_six, one_mul]

/-- The 7-potent nonzero-mode projector of `axialRotateEnd` is `1` (every vector
lies in the invertible unit sector), and the zero-mode projector is `0`. -/
theorem axialRotateEnd_npotent_projectors :
    npotentNonzeroProjector axialRotateEnd 7 = 1 ∧
    npotentZeroProjector axialRotateEnd 7 = 0 ∧
    IsIdempotent (npotentNonzeroProjector axialRotateEnd 7) ∧
    IsIdempotent (npotentZeroProjector axialRotateEnd 7) := by
  have h7 := axialRotateEnd_isNPotent_seven
  refine ⟨?_, ?_, npotent_nonzero_isIdempotent (by decide) h7,
    npotent_zero_isIdempotent (by decide) h7⟩
  · simpa [npotentNonzeroProjector] using axialRotateEnd_pow_six
  · simp [npotentZeroProjector, axialRotateEnd_pow_six]

/-- `axialReflectEnd` is 3-potent (`S³ = S`), with trivial zero-mode projector. -/
theorem axialReflectEnd_isNPotent_three :
    IsNPotent axialReflectEnd 3 := by
  unfold IsNPotent
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, axialReflectEnd_sq, one_mul]

/-! ## 3. Bridge to `(ℤ/6)^×` Galois action and prime-`3` quadratic Boolean sign -/

/-- The nontrivial unit `5 = -1 ∈ (ZMod 6)ˣ` acts on `ZMod 6` as negation under
`cyclotomicGaloisAction 6` (mirroring `T ↦ T⁵ = T⁻¹` on `ℤ[axialRotateEnd]`). -/
def zmod6NegUnit : (ZMod 6)ˣ where
  val := 5
  inv := 5
  val_inv := by decide
  inv_val := by decide

theorem cyclotomicGaloisAction_six_neg (γ : ZMod 6) :
    (cyclotomicGaloisAction 6).act zmod6NegUnit γ = -γ := by
  change (5 : ZMod 6) * γ = -γ
  have h5 : (5 : ZMod 6) = -1 := by decide
  rw [h5, neg_one_mul]

/-- The singleton prime-`3` root lattice (`p = 3`, the ramified prime of `Φ₃`/`Φ₆`). -/
def primeThreeLattice : FormalPrimeRootLattice where
  primes := {3}
  prime_mem := fun p hp => by
    have h3 : p = 3 := Finset.mem_singleton.mp hp
    subst h3
    decide

/-- **Master `D₆`–Cyclotomic–Projector–Galois Bridge**:
unites the crystallographic `Φ₆` operator relation, dihedral conjugation
`S * T * S = T⁵`, 7-potent spectral projectors, `(ℤ/6)^×` Galois negation,
surjectivity of the prime-3 quadratic character `(ℤ/3)^× →* {±1}`, and
the `weylSign` product identity. -/
theorem d6_cyclotomic_projector_galois_bridge
    (γ : ZMod 6)
    (u : (ZMod (squarefreeCode primeThreeLattice.primes))ˣ) :
    (axialRotateEnd ^ 2 - axialRotateEnd + 1 = 0) ∧
    (axialReflectEnd * axialRotateEnd * axialReflectEnd = axialRotateEnd ^ 5) ∧
    (IsRootOfUnity axialRotateEnd 6) ∧
    (npotentNonzeroProjector axialRotateEnd 7 = 1) ∧
    ((cyclotomicGaloisAction 6).act zmod6NegUnit γ = -γ) ∧
    (Function.Surjective (primeQuadCharHom 3)) ∧
    ((∏ p : {p // p ∈ primeThreeLattice.primes},
        ((cyclotomicToBooleanSign primeThreeLattice u p : ℤ) : ℝ)) =
      weylSign (nonResidueWeyl primeThreeLattice u)) :=
  ⟨axialRotateEnd_cyclotomic_six,
   axialReflectEnd_conjugates_axialRotateEnd,
   axialRotateEnd_isRootOfUnity_six,
   axialRotateEnd_npotent_projectors.1,
   cyclotomicGaloisAction_six_neg γ,
   primeQuadCharHom_surjective 3 (by decide),
   prod_cyclotomicToBooleanSign_eq_weylSign primeThreeLattice u⟩

end InfoGeometry.Canonical.D6CyclotomicProjectorGaloisBridge
