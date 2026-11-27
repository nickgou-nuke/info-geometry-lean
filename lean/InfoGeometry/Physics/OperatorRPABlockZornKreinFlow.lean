/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.OperatorRPABlock
import InfoGeometry.Algebra.ZornAlternativeLaws
import Mathlib.Tactic

/-!
# Operator RPA Block, Unitary/Krein-Bogoliubov Flows, and Zorn Singlet-Triplet Correspondence

This module unites the noncommutative `Block2 A` operator RPA/BdG formalism of
`InfoGeometry.Physics.OperatorRPABlock` with the non-associative split-octonion algebra
`InfoGeometry.Algebra.ZornVectorMatrix`:

1. **Unitary Schur Rotation Flow (`unitaryBlockU`)**:
   Over any `[StarRing A]` with commuting self-adjoint parameters `c, s : A` satisfying
   `c^2 + s^2 = 1`, `unitaryBlockU c s = blockHamiltonian c c (-s) s` is unitary
   (`U * star U = 1`, `star U * U = 1`), preserves the Hermitian form of `starBlockHamiltonian`,
   and decouples the off-diagonal coupling at `(c^2 - s^2) * V = c * s * (E0 - E1)`.

2. **Krein-Unitary Hyperbolic Bogoliubov Flow (`kreinBogoliubovU`)**:
   For the signed RPA block `M = blockHamiltonian a (-a) b (-b)`, the hyperbolic Bogoliubov
   matrix `U_K(c, s) = blockHamiltonian c c s s` (`c^2 - s^2 = 1`) preserves the Krein
   fundamental symmetry `externalFockParity` (`U_K * J * U_K = J`, `U_K(c, s) * U_K(c, -s) = 1`),
   transforms `M` into `blockHamiltonian a' (-a') b' (-b')`, leaves the squared RPA block
   `M^2` (and hence the noncommutativity curvature `[a, b]`) invariant, and proves that
   exact TDA decoupling (`b' = 0`) is impossible unless `[a, b] = 0`.

3. **Slice & Singlet Embeddings (`Block2 R → ZornVectorMatrix R`) and Nambu 3-Determinants**:
   Constructs the non-unital ring homomorphism `block2ToZornSlice` (with `map_one` preserved
   when `u ⋅ w = 1`) and the scaled `zornSinglet` specialization `block2ToZornSinglet`, proves
   that the `b = 0` TDA block lands strictly inside the associative Cartan singlet
   `zornSpinConnectionPart` whereas `b ≠ 0` activates `zornSpacetimeFramePart`, and bridges
   `OperatorRPABlock.rpa_square` (`[A, B]` commutator defect) with
   `zorn_tamm_dancoff_two_body_singlet_triplet_parts` and
   `zorn_tamm_dancoff_triplet_to_nambu_singlet`.
-/

noncomputable section

namespace InfoGeometry.Physics.OperatorRPABlockZornKreinFlow

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.Physics.OperatorRPABlock
open InfoGeometry.Algebra

/-! ## 1. Unitary Schur Rotation Flow on `starBlockHamiltonian` -/

section UnitarySchurFlow

variable {A : Type*} [Ring A] [StarRing A]

/-- Unitary `2 × 2` Schur rotation generator `!![c, s; -s, c] = blockHamiltonian c c s (-s)`
    (using `blockHamiltonian E0 E1 V W = !![E0, V; W, E1]`).
    Wait: for `U = !![c, -s; s, c] = blockHamiltonian c c (-s) s` and
    `star U = !![c, s; -s, c]` when `star c = c, star s = s`. -/
def unitaryBlockU (c s : A) : Block2 A :=
  blockHamiltonian c c (-s) s

/-- For self-adjoint commuting `(c, s)` with `c^2 + s^2 = 1`, `unitaryBlockU c s` is unitary:
    `U * star U = 1` and `star U * U = 1`. -/
theorem unitaryBlockU_unitary (c s : A)
    (hc : star c = c) (hs : star s = s)
    (hcs : c * s = s * c) (hnorm : c * c + s * s = 1) :
    unitaryBlockU c s * star (unitaryBlockU c s) = 1 ∧
    star (unitaryBlockU c s) * unitaryBlockU c s = 1 := by
  have hstar : star (unitaryBlockU c s) = blockHamiltonian c c s (-s) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitaryBlockU, blockHamiltonian, hc, hs, star_neg]
  rw [hstar]
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitaryBlockU, blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals
      first
      | exact hnorm
      | (rw [add_comm]; exact hnorm)
      | (rw [hcs]; abel)

/-- Exact Schur rotation flow of a Hermitian operator block `starBlockHamiltonian E0 E1 V`
    under `unitaryBlockU c s` when `c, s` are self-adjoint, commute with each other, and
    commute with `E0, E1, V, star V`. -/
theorem unitaryBlockU_schur_flow (E0 E1 V c s : A)
    (hc : star c = c) (hs : star s = s) (hcs : c * s = s * c)
    (hcE0 : c * E0 = E0 * c) (hcE1 : c * E1 = E1 * c)
    (hcV : c * V = V * c) (hcVs : c * star V = star V * c)
    (hsE0 : s * E0 = E0 * s) (hsE1 : s * E1 = E1 * s)
    (hsV : s * V = V * s) (hsVs : s * star V = star V * s) :
    let E0' := c * c * E0 - c * s * (V + star V) + s * s * E1
    let E1' := s * s * E0 + c * s * (V + star V) + c * c * E1
    let V' := c * c * V - s * s * star V + c * s * (E0 - E1)
    let W' := c * c * star V - s * s * V + c * s * (E0 - E1)
    unitaryBlockU c s * starBlockHamiltonian E0 E1 V * star (unitaryBlockU c s) =
      blockHamiltonian E0' E1' V' W' := by
  have hstar : star (unitaryBlockU c s) = blockHamiltonian c c s (-s) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitaryBlockU, blockHamiltonian, hc, hs, star_neg]
  rw [hstar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryBlockU, starBlockHamiltonian, blockHamiltonian,
      Matrix.mul_apply, Fin.sum_univ_two]
  · calc
      (c * E0 + -(s * star V)) * c + -((c * V + -(s * E1)) * s) =
        c * (E0 * c) - s * (star V * c) - c * (V * s) + s * (E1 * s) := by noncomm_ring
      _ = c * (c * E0) - s * (c * star V) - c * (s * V) + s * (s * E1) := by
        rw [hcE0, hcVs, hsV, hsE1]
      _ = c * c * E0 - c * s * (V + star V) + s * s * E1 := by
        rw [← mul_assoc s c (star V), ← hcs]; noncomm_ring
  · calc
      (c * E0 + -(s * star V)) * s + (c * V + -(s * E1)) * c =
        c * (E0 * s) - s * (star V * s) + c * (V * c) - s * (E1 * c) := by noncomm_ring
      _ = c * (s * E0) - s * (s * star V) + c * (c * V) - s * (c * E1) := by
        rw [hsE0, hsVs, hcV, hcE1]
      _ = c * c * V - s * s * star V + c * s * (E0 - E1) := by
        rw [← mul_assoc s c E1, ← hcs]; noncomm_ring
  · calc
      (s * E0 + c * star V) * c + -((s * V + c * E1) * s) =
        s * (E0 * c) + c * (star V * c) - s * (V * s) - c * (E1 * s) := by noncomm_ring
      _ = s * (c * E0) + c * (c * star V) - s * (s * V) - c * (s * E1) := by
        rw [hcE0, hcVs, hsV, hsE1]
      _ = c * c * star V - s * s * V + c * s * (E0 - E1) := by
        rw [← mul_assoc s c E0, ← hcs]; noncomm_ring
  · calc
      (s * E0 + c * star V) * s + (s * V + c * E1) * c =
        s * (E0 * s) + c * (star V * s) + s * (V * c) + c * (E1 * c) := by noncomm_ring
      _ = s * (s * E0) + c * (s * star V) + s * (c * V) + c * (c * E1) := by
        rw [hsE0, hsVs, hcV, hcE1]
      _ = s * s * E0 + c * s * (V + star V) + c * c * E1 := by
        rw [← mul_assoc s c V, ← hcs]; noncomm_ring

/-- When `V` is self-adjoint (`star V = V`), rotating by `unitaryBlockU c (-s)` diagonalizes
    `starBlockHamiltonian E0 E1 V` if and only if `(c^2 - s^2) * V = c * s * (E0 - E1)`. -/
theorem unitaryBlockU_decouples_iff (E0 E1 V c s : A)
    (hV : star V = V) (hc : star c = c) (hs : star s = s) (hcs : c * s = s * c)
    (hcE0 : c * E0 = E0 * c) (hcE1 : c * E1 = E1 * c) (hcV : c * V = V * c)
    (hsE0 : s * E0 = E0 * s) (hsE1 : s * E1 = E1 * s) (hsV : s * V = V * s) :
    let E0' := c * c * E0 + c * s * (V + V) + s * s * E1
    let E1' := s * s * E0 - c * s * (V + V) + c * c * E1
    unitaryBlockU c (-s) * starBlockHamiltonian E0 E1 V * star (unitaryBlockU c (-s)) =
        blockHamiltonian E0' E1' 0 0 ↔
      (c * c - s * s) * V = c * s * (E0 - E1) := by
  have hflow := unitaryBlockU_schur_flow E0 E1 V c (-s) hc (by simp [hs])
    (by simp [hcs]) hcE0 hcE1 hcV (by simpa [hV] using hcV)
    (by simp [hsE0]) (by simp [hsE1]) (by simp [hsV]) (by simp [hV, hsV])
  dsimp only at hflow ⊢
  rw [hV] at hflow
  have hE0' :
      c * c * E0 - c * -s * (V + V) + -s * -s * E1 =
        c * c * E0 + c * s * (V + V) + s * s * E1 := by noncomm_ring
  have hE1' :
      -s * -s * E0 + c * -s * (V + V) + c * c * E1 =
        s * s * E0 - c * s * (V + V) + c * c * E1 := by noncomm_ring
  have hV' :
      c * c * V - -s * -s * V + c * -s * (E0 - E1) =
        (c * c - s * s) * V - c * s * (E0 - E1) := by noncomm_ring
  rw [hE0', hE1', hV'] at hflow
  rw [hflow]
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp only [blockHamiltonian, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h01
    exact sub_eq_zero.mp h01
  · intro h
    rw [sub_eq_zero.mpr h]

end UnitarySchurFlow

/-! ## 2. Krein-Unitary Hyperbolic Bogoliubov Flow on Signed RPA Blocks -/

section KreinBogoliubovFlow

variable {A : Type*} [Ring A]

/-- Krein-unitary hyperbolic Bogoliubov block `U_K(c, s) = !![c, s; s, c]`. -/
def kreinBogoliubovU (c s : A) : Block2 A :=
  blockHamiltonian c c s s

/-- `U_K(c, s)` preserves the Krein fundamental symmetry `externalFockParity` and has inverse
    `U_K(c, -s)` whenever `c, s` commute and `c^2 - s^2 = 1`. -/
theorem kreinBogoliubovU_krein_unitary (c s : A)
    (hcs : c * s = s * c) (hhyper : c * c - s * s = 1) :
    kreinBogoliubovU c s * kreinBogoliubovU c (-s) = 1 ∧
    kreinBogoliubovU c (-s) * kreinBogoliubovU c s = 1 ∧
    kreinBogoliubovU c s * (externalFockParity : Block2 A) * kreinBogoliubovU c s =
      (externalFockParity : Block2 A) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kreinBogoliubovU, externalFockParity, blockHamiltonian,
        Matrix.mul_apply, Fin.sum_univ_two]
    all_goals
      first
      | (calc c * c + -(s * s) = c * c - s * s := (sub_eq_add_neg _ _).symm
          _ = 1 := hhyper)
      | (calc -(s * s) + c * c = c * c - s * s := by rw [add_comm]; exact (sub_eq_add_neg _ _).symm
          _ = 1 := hhyper)
      | (calc s * s + -(c * c) = -(c * c - s * s) := by noncomm_ring
          _ = -1 := by rw [hhyper])
      | (rw [hcs]; abel)

/-- Exact Krein-Bogoliubov flow of the signed RPA block `blockHamiltonian a (-a) b (-b)`:
    it maps to `blockHamiltonian a' (-a') b' (-b')`, leaves `M_RPA^2` (hence `[a, b]` and
    `a^2 - b^2`) invariant when `c^2 - s^2 = 1`, and proves that TDA reduction (`b' = 0`)
    forces `[a, b] = 0`. -/
theorem kreinBogoliubovU_rpa_flow_and_curvature_invariance (a b c s : A)
    (hcs : c * s = s * c) (hca : c * a = a * c) (hcb : c * b = b * c)
    (hsa : s * a = a * s) (hsb : s * b = b * s) :
    let a' := (c * c + s * s) * a - (2 : ℕ) • (c * s * b)
    let b' := (c * c + s * s) * b - (2 : ℕ) • (c * s * a)
    let κ := c * c - s * s
    kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s) =
      blockHamiltonian a' (-a') b' (-b') ∧
    a' * b' - b' * a' = (κ * κ) * (a * b - b * a) ∧
    (c * c - s * s = 1 →
      (kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s)) *
        (kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s)) =
        blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) ∧
      a' * b' - b' * a' = a * b - b * a ∧
      (b' = 0 → a * b = b * a)) := by
  intro a' b' κ
  have h_flow :
      kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s) =
        blockHamiltonian a' (-a') b' (-b') := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kreinBogoliubovU, blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]
    · calc
        (c * a + -(s * b)) * c + -((c * b + -(s * a)) * s) =
          c * (a * c) - s * (b * c) - c * (b * s) + s * (a * s) := by noncomm_ring
        _ = c * (c * a) - s * (c * b) - c * (s * b) + s * (s * a) := by
          rw [hca, hcb, hsb, hsa]
        _ = (c * c + s * s) * a - (2 : ℕ) • (c * s * b) := by
          rw [← mul_assoc s c b, ← hcs, two_nsmul]; noncomm_ring
    · calc
        -((c * a + -(s * b)) * s) + (c * b + -(s * a)) * c =
          -c * (a * s) + s * (b * s) + c * (b * c) - s * (a * c) := by noncomm_ring
        _ = -c * (s * a) + s * (s * b) + c * (c * b) - s * (c * a) := by
          rw [hsa, hsb, hcb, hca]
        _ = (c * c + s * s) * b - (2 : ℕ) • (c * s * a) := by
          rw [← mul_assoc s c a, ← hcs, two_nsmul]; noncomm_ring
    · calc
        (s * a + -(c * b)) * c + -((s * b + -(c * a)) * s) =
          s * (a * c) - c * (b * c) - s * (b * s) + c * (a * s) := by noncomm_ring
        _ = s * (c * a) - c * (c * b) - s * (s * b) + c * (s * a) := by
          rw [hca, hcb, hsb, hsa]
        _ = -((c * c + s * s) * b - (2 : ℕ) • (c * s * a)) := by
          rw [← mul_assoc s c a, ← hcs, two_nsmul]; noncomm_ring
    · calc
        -((s * a + -(c * b)) * s) + (s * b + -(c * a)) * c =
          -s * (a * s) + c * (b * s) + s * (b * c) - c * (a * c) := by noncomm_ring
        _ = -s * (s * a) + c * (s * b) + s * (c * b) - c * (c * a) := by
          rw [hsa, hsb, hcb, hca]
        _ = -((c * c + s * s) * a - (2 : ℕ) • (c * s * b)) := by
          rw [← mul_assoc s c b, ← hcs, two_nsmul]; noncomm_ring
  have hc2a : (c * c) * a = a * (c * c) := by
    calc (c * c) * a = c * (c * a) := by noncomm_ring
    _ = c * (a * c) := by rw [hca]
    _ = (c * a) * c := by noncomm_ring
    _ = a * (c * c) := by rw [hca]; noncomm_ring
  have hs2a : (s * s) * a = a * (s * s) := by
    calc (s * s) * a = s * (s * a) := by noncomm_ring
    _ = s * (a * s) := by rw [hsa]
    _ = (s * a) * s := by noncomm_ring
    _ = a * (s * s) := by rw [hsa]; noncomm_ring
  have hc2b : (c * c) * b = b * (c * c) := by
    calc (c * c) * b = c * (c * b) := by noncomm_ring
    _ = c * (b * c) := by rw [hcb]
    _ = (c * b) * c := by noncomm_ring
    _ = b * (c * c) := by rw [hcb]; noncomm_ring
  have hs2b : (s * s) * b = b * (s * s) := by
    calc (s * s) * b = s * (s * b) := by noncomm_ring
    _ = s * (b * s) := by rw [hsb]
    _ = (s * b) * s := by noncomm_ring
    _ = b * (s * s) := by rw [hsb]; noncomm_ring
  have hcsa : (c * s) * a = a * (c * s) := by
    calc (c * s) * a = c * (s * a) := by noncomm_ring
    _ = c * (a * s) := by rw [hsa]
    _ = (c * a) * s := by noncomm_ring
    _ = a * (c * s) := by rw [hca]; noncomm_ring
  have hcsb : (c * s) * b = b * (c * s) := by
    calc (c * s) * b = c * (s * b) := by noncomm_ring
    _ = c * (b * s) := by rw [hsb]
    _ = (c * b) * s := by noncomm_ring
    _ = b * (c * s) := by rw [hcb]; noncomm_ring
  have h_comm_curv : a' * b' - b' * a' = (κ * κ) * (a * b - b * a) := by
    let α := c * c + s * s
    let β := c * s
    have hαa : α * a = a * α := by
      dsimp [α]; rw [add_mul, mul_add, hc2a, hs2a]
    have hαb : α * b = b * α := by
      dsimp [α]; rw [add_mul, mul_add, hc2b, hs2b]
    have hαβ : α * β = β * α := by
      have hcβ : c * β = β * c := by
        dsimp [β]
        calc c * (c * s) = c * (s * c) := by rw [hcs]
        _ = (c * s) * c := by noncomm_ring
      have hsβ : s * β = β * s := by
        dsimp [β]
        calc s * (c * s) = (s * c) * s := by noncomm_ring
        _ = (c * s) * s := by rw [← hcs]
      dsimp [α]
      calc (c * c + s * s) * β = c * (c * β) + s * (s * β) := by noncomm_ring
      _ = c * (β * c) + s * (β * s) := by rw [hcβ, hsβ]
      _ = (c * β) * c + (s * β) * s := by noncomm_ring
      _ = (β * c) * c + (β * s) * s := by rw [hcβ, hsβ]
      _ = β * (c * c + s * s) := by noncomm_ring
    have hκ : α * α - 4 * (β * β) = κ * κ := by
      have h22 : s * s * (c * c) = c * c * (s * s) := by
        calc s * s * (c * c) = s * (s * c) * c := by noncomm_ring
        _ = s * (c * s) * c := by rw [← hcs]
        _ = (s * c) * (s * c) := by noncomm_ring
        _ = (c * s) * (c * s) := by rw [hcs]
        _ = c * (s * c) * s := by noncomm_ring
        _ = c * c * (s * s) := by rw [← hcs]; noncomm_ring
      have hβ2 : β * β = c * c * (s * s) := by
        dsimp [β]
        calc (c * s) * (c * s) = c * (s * c) * s := by noncomm_ring
        _ = c * (c * s) * s := by rw [← hcs]
        _ = c * c * (s * s) := by noncomm_ring
      dsimp [α, κ]
      rw [hβ2]
      calc (c * c + s * s) * (c * c + s * s) - 4 * (c * c * (s * s)) =
          c * c * (c * c) + s * s * (c * c) + c * c * (s * s) + s * s * (s * s) -
          4 * (c * c * (s * s)) := by noncomm_ring
      _ = c * c * (c * c) + 2 * (c * c * (s * s)) + s * s * (s * s) -
          4 * (c * c * (s * s)) := by rw [h22]; noncomm_ring
      _ = c * c * (c * c) - c * c * (s * s) - c * c * (s * s) + s * s * (s * s) := by noncomm_ring
      _ = c * c * (c * c) - c * c * (s * s) - s * s * (c * c) + s * s * (s * s) := by rw [h22]
      _ = (c * c - s * s) * (c * c - s * s) := by noncomm_ring
    have hcurv_aux :
        ∀ (α' β' κ' a₀ b₀ : A),
          α' * a₀ = a₀ * α' → α' * b₀ = b₀ * α' →
          β' * a₀ = a₀ * β' → β' * b₀ = b₀ * β' →
          α' * β' = β' * α' → α' * α' - 4 * (β' * β') = κ' * κ' →
          (α' * a₀ - (2 : ℕ) • (β' * b₀)) * (α' * b₀ - (2 : ℕ) • (β' * a₀)) -
              (α' * b₀ - (2 : ℕ) • (β' * a₀)) * (α' * a₀ - (2 : ℕ) • (β' * b₀)) =
            (κ' * κ') * (a₀ * b₀ - b₀ * a₀) := by
      intro α' β' κ' a₀ b₀ hαa' hαb' hβa' hβb' hαβ' hκ'
      calc
        (α' * a₀ - (2 : ℕ) • (β' * b₀)) * (α' * b₀ - (2 : ℕ) • (β' * a₀)) -
            (α' * b₀ - (2 : ℕ) • (β' * a₀)) * (α' * a₀ - (2 : ℕ) • (β' * b₀)) =
          (α' * (a₀ * α') * b₀ - 2 * (α' * (a₀ * β') * a₀) - 2 * (β' * (b₀ * α') * b₀) +
            4 * (β' * (b₀ * β') * a₀)) -
          (α' * (b₀ * α') * a₀ - 2 * (α' * (b₀ * β') * b₀) - 2 * (β' * (a₀ * α') * a₀) +
            4 * (β' * (a₀ * β') * b₀)) := by
          simp only [two_nsmul]; noncomm_ring
        _ = (α' * α' * (a₀ * b₀) - 2 * (α' * β') * (a₀ * a₀) - 2 * (β' * α') * (b₀ * b₀) +
              4 * (β' * β') * (b₀ * a₀)) -
            (α' * α' * (b₀ * a₀) - 2 * (α' * β') * (b₀ * b₀) - 2 * (β' * α') * (a₀ * a₀) +
              4 * (β' * β') * (a₀ * b₀)) := by
          rw [← hαa', ← hαb', ← hβa', ← hβb']; noncomm_ring
        _ = (α' * α' - 4 * (β' * β')) * (a₀ * b₀ - b₀ * a₀) := by
          rw [hαβ']; noncomm_ring
        _ = (κ' * κ') * (a₀ * b₀ - b₀ * a₀) := by rw [hκ']
    exact hcurv_aux α β κ a b hαa hαb hcsa hcsb hαβ hκ
  refine ⟨h_flow, h_comm_curv, ?_⟩
  intro hhyper
  have hcurv1 : a' * b' - b' * a' = a * b - b * a := by
    rw [h_comm_curv]
    dsimp [κ]
    rw [hhyper, one_mul, one_mul]
  have h_sq :
      (kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s)) *
        (kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s)) =
        blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) := by
    have hU := kreinBogoliubovU_krein_unitary c s hcs hhyper
    calc
      (kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s)) *
          (kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s)) =
        kreinBogoliubovU c s * blockHamiltonian a (-a) b (-b) *
          (kreinBogoliubovU c (-s) * kreinBogoliubovU c s) *
          blockHamiltonian a (-a) b (-b) * kreinBogoliubovU c (-s) := by noncomm_ring
      _ = kreinBogoliubovU c s *
          (blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b)) *
          kreinBogoliubovU c (-s) := by
        rw [hU.2.1, mul_one]
        noncomm_ring
      _ = blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) := by
        rw [rpa_square]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kreinBogoliubovU, blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]
        all_goals
          have hc_sq : c * (a * a - b * b) = (a * a - b * b) * c := by
            calc c * (a * a - b * b) = (c * a) * a - (c * b) * b := by noncomm_ring
            _ = (a * c) * a - (b * c) * b := by rw [hca, hcb]
            _ = a * (c * a) - b * (c * b) := by noncomm_ring
            _ = a * (a * c) - b * (b * c) := by rw [hca, hcb]
            _ = (a * a - b * b) * c := by noncomm_ring
          have hs_sq : s * (a * a - b * b) = (a * a - b * b) * s := by
            calc s * (a * a - b * b) = (s * a) * a - (s * b) * b := by noncomm_ring
            _ = (a * s) * a - (b * s) * b := by rw [hsa, hsb]
            _ = a * (s * a) - b * (s * b) := by noncomm_ring
            _ = a * (a * s) - b * (b * s) := by rw [hsa, hsb]
            _ = (a * a - b * b) * s := by noncomm_ring
          have hc_comm : c * (a * b - b * a) = (a * b - b * a) * c := by
            calc c * (a * b - b * a) = (c * a) * b - (c * b) * a := by noncomm_ring
            _ = (a * c) * b - (b * c) * a := by rw [hca, hcb]
            _ = a * (c * b) - b * (c * a) := by noncomm_ring
            _ = a * (b * c) - b * (a * c) := by rw [hcb, hca]
            _ = (a * b - b * a) * c := by noncomm_ring
          have hs_comm : s * (a * b - b * a) = (a * b - b * a) * s := by
            calc s * (a * b - b * a) = (s * a) * b - (s * b) * a := by noncomm_ring
            _ = (a * s) * b - (b * s) * a := by rw [hsa, hsb]
            _ = a * (s * b) - b * (s * a) := by noncomm_ring
            _ = a * (b * s) - b * (a * s) := by rw [hsb, hsa]
            _ = (a * b - b * a) * s := by noncomm_ring
        · calc
            (c * (a * a - b * b) + s * (a * b - b * a)) * c +
                -((c * (a * b - b * a) + s * (a * a - b * b)) * s) =
              c * ((a * a - b * b) * c) + s * ((a * b - b * a) * c) -
                c * ((a * b - b * a) * s) - s * ((a * a - b * b) * s) := by noncomm_ring
            _ = (c * c - s * s) * (a * a - b * b) + (s * c - c * s) * (a * b - b * a) := by
              rw [← hc_sq, ← hc_comm, ← hs_comm, ← hs_sq]; noncomm_ring
            _ = a * a - b * b := by
              rw [hhyper, hcs, _root_.sub_self, one_mul, zero_mul, add_zero]
        · calc
            -((c * (a * a - b * b) + s * (a * b - b * a)) * s) +
                (c * (a * b - b * a) + s * (a * a - b * b)) * c =
              -c * ((a * a - b * b) * s) - s * ((a * b - b * a) * s) +
                c * ((a * b - b * a) * c) + s * ((a * a - b * b) * c) := by noncomm_ring
            _ = (s * c - c * s) * (a * a - b * b) + (c * c - s * s) * (a * b - b * a) := by
              rw [← hs_sq, ← hs_comm, ← hc_comm, ← hc_sq]; noncomm_ring
            _ = a * b - b * a := by
              rw [hhyper, hcs, _root_.sub_self, one_mul, zero_mul, zero_add]
        · calc
            (s * (a * a - b * b) + c * (a * b - b * a)) * c +
                -((s * (a * b - b * a) + c * (a * a - b * b)) * s) =
              s * ((a * a - b * b) * c) + c * ((a * b - b * a) * c) -
                s * ((a * b - b * a) * s) - c * ((a * a - b * b) * s) := by noncomm_ring
            _ = (s * c - c * s) * (a * a - b * b) + (c * c - s * s) * (a * b - b * a) := by
              rw [← hc_sq, ← hc_comm, ← hs_comm, ← hs_sq]; noncomm_ring
            _ = a * b - b * a := by
              rw [hhyper, hcs, _root_.sub_self, one_mul, zero_mul, zero_add]
        · calc
            -((s * (a * a - b * b) + c * (a * b - b * a)) * s) +
                (s * (a * b - b * a) + c * (a * a - b * b)) * c =
              -s * ((a * a - b * b) * s) - c * ((a * b - b * a) * s) +
                s * ((a * b - b * a) * c) + c * ((a * a - b * b) * c) := by noncomm_ring
            _ = (c * c - s * s) * (a * a - b * b) + (s * c - c * s) * (a * b - b * a) := by
              rw [← hs_sq, ← hs_comm, ← hc_comm, ← hc_sq]; noncomm_ring
            _ = a * a - b * b := by
              rw [hhyper, hcs, _root_.sub_self, one_mul, zero_mul, add_zero]
  refine ⟨h_sq, hcurv1, ?_⟩
  intro hb'0
  rw [hb'0, mul_zero, zero_mul, sub_self] at hcurv1
  exact sub_eq_zero.mp hcurv1.symm

end KreinBogoliubovFlow

/-! ## 3. `OperatorRPABlock` ↔ `ZornAlternativeLaws` Slice, `zornSinglet`, and TDA/Nambu Bridge -/

section ZornBridge

open InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- Explicit non-unital ring homomorphism `Block2 R →ₙ+* ZornVectorMatrix R` induced by a
    dually normalized direction pair `(u, w)` with `ZornVec3.dot u w = 1`, plus `map_one`. -/
def block2ToZornSlice (u w : ZornVec3 R) (hdot : ZornVec3.dot u w = 1) :
    Block2 R →ₙ+* ZornVectorMatrix R where
  toFun := sliceEmbed u w
  map_zero' := by
    ext k
    · rfl
    · fin_cases k <;> simp [sliceEmbed]
    · fin_cases k <;> simp [sliceEmbed]
    · rfl
  map_add' := fun X Y => by
    ext k
    · rfl
    · fin_cases k <;> simp [sliceEmbed, _root_.add_mul]
    · fin_cases k <;> simp [sliceEmbed, _root_.add_mul]
    · rfl
  map_mul' := fun X Y => by
    rw [(master_slice_embedding_unification u w X Y X 0 0 0).1]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [deformedMatMul, Matrix.mul_apply, Fin.sum_univ_two, hdot]; try ring)

theorem block2ToZornSlice_apply (u w : ZornVec3 R) (hdot : ZornVec3.dot u w = 1)
    (X : Block2 R) : block2ToZornSlice u w hdot X = sliceEmbed u w X := rfl

theorem block2ToZornSlice_one (u w : ZornVec3 R) (hdot : ZornVec3.dot u w = 1) :
    block2ToZornSlice u w hdot (1 : Block2 R) = (ZornVectorMatrix.one : ZornVectorMatrix R) := by
  rw [block2ToZornSlice_apply]
  ext k
  · rfl
  · fin_cases k <;> simp [sliceEmbed, ZornVectorMatrix.one]
  · fin_cases k <;> simp [sliceEmbed, ZornVectorMatrix.one]
  · rfl

/-- Scaled `zornSinglet` embedding `Block2 R →ₙ+* ZornVectorMatrix R` for any inverse `threeInv`
    of `3` (`3 * threeInv = 1`), realized as the diagonal slice `(zornDiagVec threeInv, zornDiagVec 1)`. -/
def block2ToZornSinglet (threeInv : R) (h3 : 3 * threeInv = 1) :
    Block2 R →ₙ+* ZornVectorMatrix R :=
  block2ToZornSlice (zornDiagVec threeInv) (zornDiagVec 1) (by
    simp [zornDiagVec, ZornVec3.dot, Fin.sum_univ_three]
    linear_combination h3)

theorem block2ToZornSinglet_apply (threeInv : R) (h3 : 3 * threeInv = 1) (X : Block2 R) :
    block2ToZornSinglet threeInv h3 X =
      zornSinglet (X 0 0) (threeInv * X 0 1) (X 1 0) (X 1 1) := by
  dsimp [block2ToZornSinglet]
  rw [block2ToZornSlice_apply]
  ext k
  · rfl
  · fin_cases k <;> simp [sliceEmbed, zornSinglet, zornDiagVec, mul_comm]
  · fin_cases k <;> simp [sliceEmbed, zornSinglet, zornDiagVec]
  · rfl

/-- **TDA vs Full RPA Cartan Grading in `ZornVectorMatrix R`**:
    1. Every `b = 0` (`Y = 0`) TDA block `blockHamiltonian a (-a) 0 0` maps strictly into the
       associative Cartan singlet `zornSpinConnectionPart` (`zornGradeZero a (-a)`), with
       vanishing `zornSpacetimeFramePart`, zero triplet cross-product, and zero associator.
    2. A full RPA block `blockHamiltonian a (-a) b (-b)` maps to
       `zornGradeZero a (-a) + ⟨0, b • u, (-b) • w, 0⟩`, activating `zornSpacetimeFramePart`
       whenever `b ≠ 0` (given `dot u w = 1`). -/
theorem rpa_tda_vs_full_zorn_grading (u w : ZornVec3 R) (hdot : ZornVec3.dot u w = 1)
    (a b : R) :
    let Φ := block2ToZornSlice u w hdot
    Φ (blockHamiltonian a (-a) 0 0) = zornGradeZero a (-a) ∧
    zornSpinConnectionPart (Φ (blockHamiltonian a (-a) 0 0)) =
      Φ (blockHamiltonian a (-a) 0 0) ∧
    zornSpacetimeFramePart (Φ (blockHamiltonian a (-a) 0 0)) = 0 ∧
    (∀ Y Z : ZornVectorMatrix R,
      zornAssociator (Φ (blockHamiltonian a (-a) 0 0)) Y Z =
        ⟨0, (2 * a) • ZornVec3.cross Y.w Z.w, (2 * a) • ZornVec3.cross Y.v Z.v, 0⟩) ∧
    (∀ Y Z : Block2 R,
      zornAssociator (Φ (blockHamiltonian a (-a) 0 0)) (Φ Y) (Φ Z) = 0) ∧
    zornSpacetimeFramePart (Φ (blockHamiltonian a (-a) b (-b))) =
      ⟨0, b • u, (-b) • w, 0⟩ ∧
    (b ≠ 0 → zornSpacetimeFramePart (Φ (blockHamiltonian a (-a) b (-b))) ≠ 0) := by
  intro Φ
  have htda : Φ (blockHamiltonian a (-a) 0 0) = zornGradeZero a (-a) := by
    dsimp [Φ]
    rw [block2ToZornSlice_apply]
    ext k
    · rfl
    · fin_cases k <;> simp [sliceEmbed, blockHamiltonian, zornGradeZero]
    · fin_cases k <;> simp [sliceEmbed, blockHamiltonian, zornGradeZero]
    · rfl
  have hframe : zornSpacetimeFramePart (Φ (blockHamiltonian a (-a) b (-b))) =
      ⟨0, b • u, (-b) • w, 0⟩ := by
    dsimp [Φ]
    rw [block2ToZornSlice_apply]
    ext k
    · rfl
    · fin_cases k <;> simp [sliceEmbed, blockHamiltonian, zornSpacetimeFramePart, offDiagonalPart]
    · fin_cases k <;> simp [sliceEmbed, blockHamiltonian, zornSpacetimeFramePart, offDiagonalPart]
    · rfl
  have hassoc : ∀ Y Z : ZornVectorMatrix R,
      zornAssociator (Φ (blockHamiltonian a (-a) 0 0)) Y Z =
        ⟨0, (2 * a) • ZornVec3.cross Y.w Z.w, (2 * a) • ZornVec3.cross Y.v Z.v, 0⟩ := by
    intro Y Z
    rw [htda]
    have hmul_zvm : ∀ P Q : ZornVectorMatrix R, P * Q = mul P Q := fun _ _ => rfl
    have hsub_zvm : ∀ P Q : ZornVectorMatrix R, P - Q = sub P Q := fun _ _ => rfl
    simp only [zornAssociator, hmul_zvm, hsub_zvm]
    ext k
    · simp [zornGradeZero, mul, sub, neg, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
    · fin_cases k <;>
        (simp [zornGradeZero, mul, sub, neg, ZornVec3.dot, ZornVec3.cross]; ring)
    · fin_cases k <;>
        (simp [zornGradeZero, mul, sub, neg, ZornVec3.dot, ZornVec3.cross]; ring)
    · simp [zornGradeZero, mul, sub, neg, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
  refine ⟨htda, ?_, ?_, hassoc, ?_, hframe, ?_⟩
  · rw [htda]
    ext k <;> simp [zornSpinConnectionPart, diagonalPart, zornGradeZero]
  · rw [htda]
    ext k <;> simp [zornSpacetimeFramePart, offDiagonalPart, zornGradeZero]
  · intro Y Z
    simp only [zornAssociator, ← map_mul, ← mul_assoc]
    rw [_root_.sub_self]
  · intro hb hzero
    rw [hframe] at hzero
    have hv : b • u = 0 := congrArg ZornVectorMatrix.v hzero
    have hdot0 : ZornVec3.dot (b • u) w = 0 := by
      rw [hv]; simp [ZornVec3.dot]
    have hdotb : ZornVec3.dot (b • u) w = b := by
      calc ZornVec3.dot (b • u) w = b * ZornVec3.dot u w := by
            simp [ZornVec3.dot, Finset.mul_sum, mul_assoc]
      _ = b := by rw [hdot, _root_.mul_one]
    exact hb (hdotb.symm.trans hdot0)

/-- **Noncommutative `OperatorRPABlock.rpa_square` ↔ Zorn Triplet Cross-Product & Nambu 3-Determinant**:
    1. On any operator slice `Φ = block2ToZornSlice u w hdot` (`u ⋅ w = 1`), the squared RPA block
       of two `2×2` matrices `A, B : Block2 R` has off-diagonal commutator defect `A * B - B * A`
       via `OperatorRPABlock.rpa_square`, whose image under `Φ` equals the Zorn commutator
       `Φ A * Φ B - Φ B * Φ A`.
    2. For two genuinely non-parallel Zorn triplet frame elements `e(X)` and `e(Y)`, the
       Zorn commutator `[e(X), e(Y)]` decomposes via
       `zorn_tamm_dancoff_two_body_singlet_triplet_parts` into singlet Riemann curvature plus
       octonionic color cross-product torsion `⟨0, -2(X.w × Y.w), 2(X.v × Y.v), 0⟩`, and
       contracting with a third triplet `e(Z)` via
       `zorn_tamm_dancoff_triplet_to_nambu_singlet` extracts the Nambu 3-determinant! -/
theorem rpa_square_commutator_vs_zorn_triplet_nambu (u w : ZornVec3 R)
    (hdot : ZornVec3.dot u w = 1) (A B : Block2 R) (X Y Z : ZornVectorMatrix R) :
    let Φ := block2ToZornSlice u w hdot
    let eX := zornSpacetimeFramePart X
    let eY := zornSpacetimeFramePart Y
    let eZ := zornSpacetimeFramePart Z
    Φ ((blockHamiltonian A (-A) B (-B) * blockHamiltonian A (-A) B (-B)) 0 1) =
      Φ A * Φ B - Φ B * Φ A ∧
    (eX * eY - eY * eX =
      ⟨ZornVec3.dot X.v Y.w - ZornVec3.dot X.w Y.v, fun _ => 0, fun _ => 0,
        ZornVec3.dot X.w Y.v - ZornVec3.dot X.v Y.w⟩ +
      ⟨0, fun i => (-2 : R) * ZornVec3.cross X.w Y.w i,
          fun i => (2 : R) * ZornVec3.cross X.v Y.v i, 0⟩) ∧
    zornSpinConnectionPart (zornSpacetimeFramePart (eX * eY) * eZ) =
      ⟨-zornNambuDet X.w Y.w Z.w, fun _ => 0, fun _ => 0, zornNambuDet X.v Y.v Z.v⟩ := by
  intro Φ eX eY eZ
  refine ⟨?_, ?_, ?_⟩
  · rw [rpa_square]
    simp only [blockHamiltonian, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsub : ∀ P Q : Block2 R, Φ (P - Q) = Φ P - Φ Q := by
      intro P Q
      rw [_root_.sub_eq_add_neg, map_add]
      have hneg : Φ (-Q) = -Φ Q := by
        apply eq_neg_of_add_eq_zero_left
        rw [← map_add, neg_add_cancel, map_zero]
      rw [hneg, ← _root_.sub_eq_add_neg]
    rw [hsub, map_mul, map_mul]
  · have hXY := zorn_tamm_dancoff_two_body_singlet_triplet_parts X Y
    have hYX := zorn_tamm_dancoff_two_body_singlet_triplet_parts Y X
    have hdecomp_XY : eX * eY = zornSpinConnectionPart (eX * eY) + zornSpacetimeFramePart (eX * eY) := by
      ext k <;> simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart]
    have hdecomp_YX : eY * eX = zornSpinConnectionPart (eY * eX) + zornSpacetimeFramePart (eY * eX) := by
      ext k <;> simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart]
    have hadd_zvm : ∀ P Q : ZornVectorMatrix R, P + Q = add P Q := fun _ _ => rfl
    have hsub_zvm : ∀ P Q : ZornVectorMatrix R, P - Q = sub P Q := fun _ _ => rfl
    rw [hdecomp_XY, hdecomp_YX, hXY.1, hXY.2, hYX.1, hYX.2]
    simp only [hadd_zvm, hsub_zvm]
    ext k
    · simp [add, sub, neg, ZornVec3.dot, Fin.sum_univ_three]; ring
    · fin_cases k <;> (simp [add, sub, neg, ZornVec3.cross]; ring)
    · fin_cases k <;> (simp [add, sub, neg, ZornVec3.cross]; ring)
    · simp [add, sub, neg, ZornVec3.dot, Fin.sum_univ_three]; ring
  · exact zorn_tamm_dancoff_triplet_to_nambu_singlet X Y Z

end ZornBridge

end InfoGeometry.Physics.OperatorRPABlockZornKreinFlow
