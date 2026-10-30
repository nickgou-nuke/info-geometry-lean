/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Core.IdempotentGraphGrassmannian

/-!
# Pure non-commutative operator spine: cones, tetraktys, Cayley-Weyl, Steinberg braids

Owner module for the "drunken professor" deconfabulation of the Erlangen-2.0 stream
archetypes `A16`-`A19` (with the `A8`, `A3`, `A12` support layer).

Everything is stated for an **arbitrary associative unital ring `B` with the single
hypothesis `hP : P * P = P`**: no commutativity, no division, no scalar carrier beyond
`ℤ`-multiples.  The two nilpotent Peirce cones

* `N₊ = conePlus P A = P * A * (1 - P)` (upper chart motion),
* `N₋ = coneMinus P C = (1 - P) C P` (lower chart motion)

generate the tetraktys `Φ = N₊ + N₋`, `J = N₊ - N₋`, `V = N₊N₋ + N₋N₊`,
`Σ = N₊N₋ - N₋N₊`:

* cones are square-zero and same-cone products vanish (A8);
* `Φ² = V`, `J² = -V`, `JΦ = Σ`, `ΦJ = -Σ`, `Σ² = V²`; `V` commutes with both cones
  and anticommutes `Σ` against both cones (A3);
* `S = P - (1 - P)` grades everything (`S² = 1`, `SN₊ = N₊`, `SN₋ = -N₋`, `SV = Σ`,
  `SΣ = V`, `SΦ = J`, `SJ = Φ`, with the mirrored right laws);
* conjugation by `1 ± N₊` (and by `1 ± N₋`) is a genuine involution grouping (A12);
* the Cayley-Weyl element `W = J + (1 - V)` has the exact unitarity **defect**
  `W W' - 1 = V V - V` (both orders): `W` is *not* invertible off-shell; the mass block
  sandwiches exchange `11 ↔ 00` squares (A16);
* the Steinberg triple braids `B₊ = (1 + N₊)(1 - N₋)(1 + N₊)` and
  `B₋ = (1 - N₋)(1 + N₊)(1 - N₋)` are **exact units** with inverses `B₊'`, `B₋'`,
  and `B₊ = W + (1 - V) N₊`, `B₊ - B₋ = (1 - V) Φ` (A17, A18).

Every statement below was first arbitrated by the exact word model plus the `Mat₃(ℚ)`
witness in `proofs/steinberg_braid_defect_spine.py` (92 strict checks, zero failures)
before transcription.  The stream's draft `B₊ S B₊'` reflection form
`S - 2J - 2Σ - 2(1 - 2V)N₊` was refuted by the model; the verified 9-chain form is
`braid_reflection_s` below.  The abstract square-zero layer of
`InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.UnipotentSteinberg`
(`weyl`, `steinbergPlus`, …) is the structural ancestor of the `W`/braid section.
-/

namespace PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

/-! ### Stream-conformant definitions (single `P * P = P` hypothesis) -/

/-- Commutator, free of division: `X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Anti-commutator: `X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Cartan grading involution `S = P - (1 - P) = 2P - 1`. -/
def invS (P : B) : B := P - (1 - P)

/-- Upper-chart cone `N₊ = P A (1 - P)`. -/
def conePlus (P A : B) : B := P * A * (1 - P)

/-- Lower-chart cone `N₋ = (1 - P) C P`. -/
def coneMinus (P C : B) : B := (1 - P) * C * P

/-- Peirce `11`-block sandwich `P X P`. -/
def peirce11 (P X : B) : B := P * X * P

/-- Peirce `00`-block sandwich `(1 - P) X (1 - P)`. -/
def peirce00 (P X : B) : B := (1 - P) * X * (1 - P)

/-- `Φ = N₊ + N₋`: the nilpotent plekton generator. -/
def genPhi (P A C : B) : B := conePlus P A + coneMinus P C

/-- `J = N₊ - N₋`: the block-swapping difference. -/
def genJ (P A C : B) : B := conePlus P A - coneMinus P C

/-- `V = N₊ N₋ + N₋ N₊`: the Jordan mass. -/
def genV (P A C : B) : B := anticomm (conePlus P A) (coneMinus P C)

/-- `Σ = N₊ N₋ - N₋ N₊`: the spin / symplectic generator. -/
def genSig (P A C : B) : B := comm (conePlus P A) (coneMinus P C)

/-- Forward nilpotent-BCH conjugation by `1 + N₊`. -/
def conjPlus (P A X : B) : B := (1 + conePlus P A) * X * (1 - conePlus P A)

/-- Its inverse action: conjugation by `1 - N₊`. -/
def conjPlusInv (P A X : B) : B := (1 - conePlus P A) * X * (1 + conePlus P A)

/-- Forward conjugation by `1 + N₋`. -/
def conjMinus (P C X : B) : B := (1 + coneMinus P C) * X * (1 - coneMinus P C)

/-- Its inverse action: conjugation by `1 - N₋`. -/
def conjMinusInv (P C X : B) : B := (1 - coneMinus P C) * X * (1 + coneMinus P C)

/-- Cayley-Weyl reflection element `W = J + (1 - V)`.
**Not** a unit off-shell: the defect `W W' - 1` is `V * V - V`. -/
def weylJ (P A C : B) : B := genJ P A C + (1 - genV P A C)

/-- Cayley-Weyl partner `W' = -J + (1 - V)`. -/
def weylJInv (P A C : B) : B := -genJ P A C + (1 - genV P A C)

/-- Steinberg triple braid `B₊ = (1 + N₊)(1 - N₋)(1 + N₊)`. -/
def steinbergBraid (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * (1 + conePlus P A)

/-- Exact inverse of the positive braid: `B₊' = (1 - N₊)(1 + N₋)(1 - N₊)`. -/
def steinbergBraidInv (P A C : B) : B :=
  (1 - conePlus P A) * (1 + coneMinus P C) * (1 - conePlus P A)

/-- Dual Steinberg braid `B₋ = (1 - N₋)(1 + N₊)(1 - N₋)`. -/
def steinbergBraidDual (P A C : B) : B :=
  (1 - coneMinus P C) * (1 + conePlus P A) * (1 - coneMinus P C)

/-- Exact inverse of the dual braid: `B₋' = (1 + N₋)(1 - N₊)(1 + N₋)`. -/
def steinbergBraidDualInv (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A) * (1 + coneMinus P C)

/-! ### The idempotent reduction core -/

/-- Right-associative idempotent confluence lemma for `⟨P * P - P⟩`. -/
lemma P_assoc {P : B} (hP : P * P = P) (X : B) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

/-! ### Cone nilpotence and same-cone closure (A8) -/

theorem conePlus_sq_zero {P : B} (hP : P * P = P) (A : B) :
    conePlus P A * conePlus P A = 0 := by
  simp only [conePlus]
  noncomm_ring [hP, P_assoc hP]

theorem coneMinus_sq_zero {P : B} (hP : P * P = P) (C : B) :
    coneMinus P C * coneMinus P C = 0 := by
  simp only [coneMinus]
  noncomm_ring [hP, P_assoc hP]

private lemma sq_zero_left_mul {u : B} (hu : u * u = 0) (X : B) :
    u * (u * X) = 0 := by
  rw [← mul_assoc, hu, zero_mul]

private lemma left_mul_zero_of_mul_eq {u v : B} (huv : u * v = 0) (X : B) :
    u * (v * X) = 0 := by
  rw [← mul_assoc, huv, zero_mul]

private lemma right_mul_zero_of_mul_eq {u v : B} (huv : u * v = 0) (X : B) :
    (X * u) * v = 0 := by
  rw [mul_assoc, huv, mul_zero]

/-- Cone additivity: `P * (A₁ + A₂) * (1 - P)` splits (distributivity only). -/
theorem conePlus_add (P A₁ A₂ : B) :
    conePlus P (A₁ + A₂) = conePlus P A₁ + conePlus P A₂ := by
  simp only [conePlus, mul_add, add_mul]

/-- Cone additivity for the lower chart. -/
theorem coneMinus_add (P C₁ C₂ : B) :
    coneMinus P (C₁ + C₂) = coneMinus P C₁ + coneMinus P C₂ := by
  simp only [coneMinus, mul_add, add_mul]

/-- Same-cone products vanish: upper with upper (A8.a). -/
theorem conePlus_annihilate {P : B} (hP : P * P = P) (A₁ A₂ : B) :
    conePlus P A₁ * conePlus P A₂ = 0 := by
  simp only [conePlus]
  noncomm_ring [hP, P_assoc hP]

/-- Same-cone products vanish: lower with lower (A8.b). -/
theorem coneMinus_annihilate {P : B} (hP : P * P = P) (C₁ C₂ : B) :
    coneMinus P C₁ * coneMinus P C₂ = 0 := by
  simp only [coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- Same-cone closure makes the upper cone abelian under multiplication (A8). -/
theorem conePlus_commute {P : B} (hP : P * P = P) (A₁ A₂ : B) :
    comm (conePlus P A₁) (conePlus P A₂) = 0 := by
  simp only [comm]
  rw [conePlus_annihilate hP A₁ A₂, conePlus_annihilate hP A₂ A₁, sub_self]

/-- Same-cone closure makes the lower cone abelian under multiplication (A8). -/
theorem coneMinus_commute {P : B} (hP : P * P = P) (C₁ C₂ : B) :
    comm (coneMinus P C₁) (coneMinus P C₂) = 0 := by
  simp only [comm]
  rw [coneMinus_annihilate hP C₁ C₂, coneMinus_annihilate hP C₂ C₁, sub_self]

/-! ### Tetraktys census (A3): the multiplication table of `(Φ, J, V, Σ)` -/

/-- `Φ * Φ = V`: the plekton squares into the mass. -/
theorem genPhi_sq {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C := by
  simp only [genPhi, genV, anticomm, add_mul, mul_add]
  noncomm_ring [conePlus_sq_zero hP A, coneMinus_sq_zero hP C]

/-- `J * J = -V`: hyperbolic square of the block difference. -/
theorem genJ_sq {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genJ P A C = -(genV P A C) := by
  simp only [genJ, genV, anticomm, add_mul, mul_add]
  noncomm_ring [conePlus_sq_zero hP A, coneMinus_sq_zero hP C]

/-- `J * Φ = Σ`. -/
theorem genJ_mul_genPhi {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genPhi P A C = genSig P A C := by
  simp only [genJ, genPhi, genSig, comm, add_mul, mul_add, sub_mul]
  noncomm_ring [conePlus_sq_zero hP A, coneMinus_sq_zero hP C]

/-- `Φ * J = -Σ`. -/
theorem genPhi_mul_genJ {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genJ P A C = -(genSig P A C) := by
  simp only [genJ, genPhi, genSig, comm, add_mul, mul_add, sub_mul]
  noncomm_ring [conePlus_sq_zero hP A, coneMinus_sq_zero hP C]

/-- The plekton and the difference anticommutator vanish: `ΦJ + JΦ = 0`. -/
theorem genPhi_genJ_anticomm {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genPhi P A C) (genJ P A C) = 0 := by
  simp only [anticomm, genPhi, genJ, add_mul, mul_add, sub_mul]
  noncomm_ring [conePlus_sq_zero hP A, coneMinus_sq_zero hP C]

/-- `Σ * Σ = V * V`: spin squares into the mass square. -/
theorem genSig_sq {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * genSig P A C = genV P A C * genV P A C := by
  simp only [genSig, genV, anticomm, comm, add_mul, mul_add, sub_mul]
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- The mass commutes with the upper cone: `N₊ V = V N₊`. -/
theorem genV_commute_conePlus {P : B} (hP : P * P = P) (A C : B) :
    comm (conePlus P A) (genV P A C) = 0 := by
  simp only [comm, genV, anticomm, add_mul, mul_add]
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- The mass commutes with the lower cone: `N₋ V = V N₋`. -/
theorem genV_commute_coneMinus {P : B} (hP : P * P = P) (A C : B) :
    comm (coneMinus P C) (genV P A C) = 0 := by
  simp only [comm, genV, anticomm, add_mul, mul_add]
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- A polynomial in an element commutes with every element commuting with its
argument. This specializes the general defect calculation to `x² - x`. -/
private theorem idempotencyDefect_commute_of_commute {x y : B}
    (hxy : x * y = y * x) : comm (x * x - x) y = 0 := by
  have hxx : x * x * y = y * (x * x) := by
    calc
      x * x * y = x * (x * y) := by rw [mul_assoc]
      _ = x * (y * x) := by rw [hxy]
      _ = (x * y) * x := by rw [mul_assoc]
      _ = (y * x) * x := by rw [hxy]
      _ = y * (x * x) := by rw [mul_assoc]
  unfold comm
  rw [sub_mul, mul_sub, hxx, hxy]
  noncomm_ring

/-- The off-shell defect `V² - V` commutes with every Tetraktys generator.
This is centrality in the generated four-element family, not centrality in the
whole ambient ring. -/
theorem genV_idempotencyDefect_commutes_with_tetraktys
    {P : B} (hP : P * P = P) (A C : B) :
    comm (genV P A C * genV P A C - genV P A C) (genPhi P A C) = 0 ∧
    comm (genV P A C * genV P A C - genV P A C) (genJ P A C) = 0 ∧
    comm (genV P A C * genV P A C - genV P A C) (genV P A C) = 0 ∧
    comm (genV P A C * genV P A C - genV P A C) (genSig P A C) = 0 := by
  have hPlus : conePlus P A * genV P A C = genV P A C * conePlus P A :=
    sub_eq_zero.mp (genV_commute_conePlus hP A C)
  have hMinus : coneMinus P C * genV P A C = genV P A C * coneMinus P C :=
    sub_eq_zero.mp (genV_commute_coneMinus hP A C)
  have hPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by
    simp only [genPhi, add_mul, mul_add]
    rw [hPlus.symm, hMinus.symm]
  have hJ : genV P A C * genJ P A C = genJ P A C * genV P A C := by
    simp only [genJ, sub_mul, mul_sub]
    rw [hPlus.symm, hMinus.symm]
  have hSig : genV P A C * genSig P A C = genSig P A C * genV P A C := by
    unfold genSig comm
    calc
      genV P A C * (conePlus P A * coneMinus P C -
          coneMinus P C * conePlus P A) =
          (genV P A C * conePlus P A) * coneMinus P C -
            (genV P A C * coneMinus P C) * conePlus P A := by noncomm_ring
      _ = (conePlus P A * genV P A C) * coneMinus P C -
            (coneMinus P C * genV P A C) * conePlus P A := by
          rw [hPlus.symm, hMinus.symm]
      _ = conePlus P A * (genV P A C * coneMinus P C) -
            coneMinus P C * (genV P A C * conePlus P A) := by noncomm_ring
      _ = conePlus P A * (coneMinus P C * genV P A C) -
            coneMinus P C * (conePlus P A * genV P A C) := by
          rw [hMinus.symm, hPlus.symm]
      _ = (conePlus P A * coneMinus P C) * genV P A C -
            (coneMinus P C * conePlus P A) * genV P A C := by noncomm_ring
      _ = (conePlus P A * coneMinus P C -
            coneMinus P C * conePlus P A) * genV P A C := by noncomm_ring
  exact ⟨idempotencyDefect_commute_of_commute hPhi,
    idempotencyDefect_commute_of_commute hJ,
    idempotencyDefect_commute_of_commute rfl,
    idempotencyDefect_commute_of_commute hSig⟩

/-- The two-sided product of `V ± Φ` is the idempotency defect of `V`.
This is the Tetraktys-specific factorization; the generic defect polynomial
and its level-set consequences are owned by `Core.IdempotentGraphGrassmannian`. -/
theorem genV_genPhi_unit_pair_factorization
    {P : B} (hP : P * P = P) (A C : B) :
    (genV P A C + genPhi P A C) * (genV P A C - genPhi P A C) =
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          (genV P A C) ∧
    (genV P A C - genPhi P A C) * (genV P A C + genPhi P A C) =
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          (genV P A C) := by
  have hVPhi : genV P A C * genPhi P A C =
      genPhi P A C * genV P A C := by
    have hPlus := sub_eq_zero.mp (genV_commute_conePlus hP A C)
    have hMinus := sub_eq_zero.mp (genV_commute_coneMinus hP A C)
    simp only [genPhi, add_mul, mul_add]
    rw [hPlus.symm, hMinus.symm]
  have hPhiSq := genPhi_sq hP A C
  constructor <;>
    calc
      _ = genV P A C * genV P A C - genPhi P A C * genPhi P A C := by
        noncomm_ring [hVPhi]
      _ = InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
            (genV P A C) := by
        rw [hPhiSq]
        rfl

/-- On the level set `δ(V)=1`, the factor pair `V ± Φ` is two-sided inverse.
The same hypothesis yields the cubic recurrence for `V`. -/
theorem genV_omega_seed_consequences
    {P : B} (hP : P * P = P) (A C : B)
    (hOmega : InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (genV P A C) = 1) :
    (genV P A C + genPhi P A C) * (genV P A C - genPhi P A C) = 1 ∧
    (genV P A C - genPhi P A C) * (genV P A C + genPhi P A C) = 1 ∧
    genV P A C * genV P A C * genV P A C =
      (2 : ℤ) • genV P A C + 1 ∧
    (genPhi P A C * genPhi P A C) *
        (genPhi P A C * genPhi P A C) * genPhi P A C =
      genV P A C * genPhi P A C + genPhi P A C := by
  have hpair := genV_genPhi_unit_pair_factorization hP A C
  have hcube :=
    InfoGeometry.Core.IdempotentGraphGrassmannian.cube_eq_two_smul_add_one_of_idempotencyDefect_eq_one
      hOmega
  have hV2 : genV P A C * genV P A C = genV P A C + 1 := by
    unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect at hOmega
    exact sub_eq_iff_eq_add'.mp hOmega
  have hPhiSq := genPhi_sq hP A C
  have hPhiFive :
      (genPhi P A C * genPhi P A C) *
          (genPhi P A C * genPhi P A C) * genPhi P A C =
        genV P A C * genPhi P A C + genPhi P A C := by
    calc
      (genPhi P A C * genPhi P A C) *
          (genPhi P A C * genPhi P A C) * genPhi P A C =
          (genV P A C * genV P A C) * genPhi P A C := by rw [hPhiSq]
      _ = (genV P A C + 1) * genPhi P A C := by rw [hV2]
      _ = genV P A C * genPhi P A C + genPhi P A C := by simp [add_mul]
  exact ⟨by rw [hpair.1, hOmega], by rw [hpair.2, hOmega], hcube, hPhiFive⟩

/-- `N₊ Σ + Σ N₊ = 0`. -/
theorem genSig_anticomm_conePlus {P : B} (hP : P * P = P) (A C : B) :
    anticomm (conePlus P A) (genSig P A C) = 0 := by
  simp only [anticomm, genSig, comm, add_mul, mul_add, sub_mul]
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- `N₋ Σ + Σ N₋ = 0`. -/
theorem genSig_anticomm_coneMinus {P : B} (hP : P * P = P) (A C : B) :
    anticomm (coneMinus P C) (genSig P A C) = 0 := by
  simp only [anticomm, genSig, comm, add_mul, mul_add, sub_mul]
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-! ### Cartan grading involution `S = P - (1 - P)` -/

/-- `S * S = 1` (additive-only, `4P² - 4P + 1`). -/
theorem invS_sq {P : B} (hP : P * P = P) : invS P * invS P = 1 := by
  simp only [invS]
  noncomm_ring [hP, P_assoc hP]

theorem invS_mul_conePlus {P : B} (hP : P * P = P) (A : B) :
    invS P * conePlus P A = conePlus P A := by
  simp only [invS, conePlus]
  noncomm_ring [hP, P_assoc hP]

theorem conePlus_mul_invS {P : B} (hP : P * P = P) (A : B) :
    conePlus P A * invS P = -(conePlus P A) := by
  simp only [invS, conePlus]
  noncomm_ring [hP, P_assoc hP]

theorem invS_mul_coneMinus {P : B} (hP : P * P = P) (C : B) :
    invS P * coneMinus P C = -(coneMinus P C) := by
  simp only [invS, coneMinus]
  noncomm_ring [hP, P_assoc hP]

theorem coneMinus_mul_invS {P : B} (hP : P * P = P) (C : B) :
    coneMinus P C * invS P = coneMinus P C := by
  simp only [invS, coneMinus]
  noncomm_ring [hP, P_assoc hP]

theorem invS_mul_genPhi {P : B} (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C = genJ P A C := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem genPhi_mul_invS {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * invS P = -(genJ P A C) := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem invS_mul_genJ {P : B} (hP : P * P = P) (A C : B) :
    invS P * genJ P A C = genPhi P A C := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem genJ_mul_invS {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * invS P = -(genPhi P A C) := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem invS_mul_genV {P : B} (hP : P * P = P) (A C : B) :
    invS P * genV P A C = genSig P A C := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, genV, anticomm, genSig, comm,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem genV_mul_invS {P : B} (hP : P * P = P) (A C : B) :
    genV P A C * invS P = genSig P A C := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, genV, anticomm, genSig, comm,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem invS_mul_genSig {P : B} (hP : P * P = P) (A C : B) :
    invS P * genSig P A C = genV P A C := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, genV, anticomm, genSig, comm,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem genSig_mul_invS {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * invS P = genV P A C := by
  simp only [invS, genPhi, genJ, conePlus, coneMinus, genV, anticomm, genSig, comm,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-! ### Nilpotent-BCH conjugation group (A12) -/

theorem conjPlus_comp_conjPlusInv {P : B} (hP : P * P = P) (A X : B) :
    conjPlus P A (conjPlusInv P A X) = X := by
  simp only [conjPlus, conjPlusInv, conePlus]
  noncomm_ring [hP, P_assoc hP]

theorem conjPlusInv_comp_conjPlus {P : B} (hP : P * P = P) (A X : B) :
    conjPlusInv P A (conjPlus P A X) = X := by
  simp only [conjPlus, conjPlusInv, conePlus]
  noncomm_ring [hP, P_assoc hP]

theorem conjMinus_comp_conjMinusInv {P : B} (hP : P * P = P) (C X : B) :
    conjMinus P C (conjMinusInv P C X) = X := by
  simp only [conjMinus, conjMinusInv, coneMinus]
  noncomm_ring [hP, P_assoc hP]

theorem conjMinusInv_comp_conjMinus {P : B} (hP : P * P = P) (C X : B) :
    conjMinusInv P C (conjMinus P C X) = X := by
  simp only [conjMinus, conjMinusInv, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- Same-chart BCH additivity: two upper shifts compose into one
(`N₊(A₁) N₊(A₂) = 0`). -/
theorem conjPlus_add {P : B} (hP : P * P = P) (A₁ A₂ X : B) :
    conjPlus P A₁ (conjPlus P A₂ X) = conjPlus P (A₁ + A₂) X := by
  simp only [conjPlus, conePlus_add]
  have h12 := conePlus_annihilate hP A₁ A₂
  have h21 := conePlus_annihilate hP A₂ A₁
  noncomm_ring [hP, P_assoc hP, h12, h21,
    left_mul_zero_of_mul_eq h12, left_mul_zero_of_mul_eq h21,
    right_mul_zero_of_mul_eq h12, right_mul_zero_of_mul_eq h21]

/-- Same-chart BCH additivity for the lower chart. -/
theorem conjMinus_add {P : B} (hP : P * P = P) (C₁ C₂ X : B) :
    conjMinus P C₁ (conjMinus P C₂ X) = conjMinus P (C₁ + C₂) X := by
  simp only [conjMinus, coneMinus_add]
  have h12 := coneMinus_annihilate hP C₁ C₂
  have h21 := coneMinus_annihilate hP C₂ C₁
  noncomm_ring [hP, P_assoc hP, h12, h21,
    left_mul_zero_of_mul_eq h12, left_mul_zero_of_mul_eq h21,
    right_mul_zero_of_mul_eq h12, right_mul_zero_of_mul_eq h21]

/-! ### Cayley-Weyl defect and mass-block exchange (A16) -/

/-- **Unitarity defect** `W W' - 1 = V² - V` (both orders). So `W` fails invertibility
exactly where the off-shell mass is not idempotent. -/
theorem weyl_defect {P : B} (hP : P * P = P) (A C : B) :
    weylJ P A C * weylJInv P A C - 1 = genV P A C * genV P A C - genV P A C := by
  simp only [weylJ, weylJInv, genJ, genV, anticomm, conePlus, coneMinus, add_mul,
    mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

theorem partner_defect {P : B} (hP : P * P = P) (A C : B) :
    weylJInv P A C * weylJ P A C - 1 = genV P A C * genV P A C - genV P A C := by
  simp only [weylJ, weylJInv, genJ, genV, anticomm, conePlus, coneMinus, add_mul,
    mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- The Weyl element commutes with the mass. -/
theorem weyl_mass_commute {P : B} (hP : P * P = P) (A C : B) :
    comm (weylJ P A C) (genV P A C) = 0 := by
  simp only [comm, weylJ, genJ, genV, anticomm, conePlus, coneMinus, add_mul, mul_add,
    sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- Steinberg decomposition `B₊ = W + (1 - V) N₊`. -/
theorem braid_eq_weyl {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A := by
  simp only [steinbergBraid, weylJ, genJ, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- Dual Steinberg decomposition `B₋ = W - (1 - V) N₋`. -/
theorem braidDual_eq_weyl {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidDual P A C = weylJ P A C - (1 - genV P A C) * coneMinus P C := by
  simp only [steinbergBraidDual, weylJ, genJ, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- `B₊ - B₋ = (1 - V) Φ`: the exact Yang-Baxter braid defect. -/
theorem braid_defect {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C - steinbergBraidDual P A C
      = (1 - genV P A C) * genPhi P A C := by
  simp only [steinbergBraid, steinbergBraidDual, genPhi, genV, anticomm, conePlus,
    coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- Mass-block exchange under `J`: `J (P V P) (-J) = (1 - P) V² (1 - P)`. -/
theorem genJ_swap_upper {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * peirce11 P (genV P A C) * -(genJ P A C)
      = peirce00 P (genV P A C * genV P A C) := by
  simp only [peirce11, peirce00, genJ, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul, mul_sub]
  noncomm_ring [hP, P_assoc hP]

/-- Mass-block exchange under `J`: `J ((1 - P) V (1 - P)) (-J) = P V² P`. -/
theorem genJ_swap_lower {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * peirce00 P (genV P A C) * -(genJ P A C)
      = peirce11 P (genV P A C * genV P A C) := by
  simp only [peirce11, peirce00, genJ, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul, mul_sub]
  noncomm_ring [hP, P_assoc hP]

/-- Mass-block exchange under `Φ`: `Φ (P V P) Φ = (1 - P) V² (1 - P)`. -/
theorem genPhi_swap_upper {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * peirce11 P (genV P A C) * genPhi P A C
      = peirce00 P (genV P A C * genV P A C) := by
  simp only [peirce11, peirce00, genPhi, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- Mass-block exchange under `Φ`: `Φ ((1 - P) V (1 - P)) Φ = P V² P`. -/
theorem genPhi_swap_lower {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * peirce00 P (genV P A C) * genPhi P A C
      = peirce11 P (genV P A C * genV P A C) := by
  simp only [peirce11, peirce00, genPhi, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-! ### Dual braids and their defects (A17) -/

/-- `B₊' = W' - (1 - V) N₊`. -/
theorem braidInv_eq_weylPartner {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidInv P A C = weylJInv P A C - (1 - genV P A C) * conePlus P A := by
  simp only [steinbergBraidInv, weylJInv, genJ, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- `B₋' = W' + (1 - V) N₋`. -/
theorem braidDualInv_eq_weylPartner {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidDualInv P A C = weylJInv P A C + (1 - genV P A C) * coneMinus P C := by
  simp only [steinbergBraidDualInv, weylJInv, genJ, genV, anticomm, conePlus, coneMinus,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- `B₋' - B₊' = (1 - V) Φ`. -/
theorem braidDualInv_defect {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidDualInv P A C - steinbergBraidInv P A C
      = (1 - genV P A C) * genPhi P A C := by
  simp only [steinbergBraidDualInv, steinbergBraidInv, genPhi, genV, anticomm, conePlus,
    coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-! ### Universal braid invertibility (A18) -/

theorem braid_mul_inv {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C * steinbergBraidInv P A C = 1 := by
  simp only [steinbergBraid, steinbergBraidInv, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

theorem braidInv_mul_braid {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidInv P A C * steinbergBraid P A C = 1 := by
  simp only [steinbergBraid, steinbergBraidInv, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

theorem braidDual_mul_braidDualInv {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidDual P A C * steinbergBraidDualInv P A C = 1 := by
  simp only [steinbergBraidDual, steinbergBraidDualInv, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

theorem braidDualInv_mul_braidDual {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidDualInv P A C * steinbergBraidDual P A C = 1 := by
  simp only [steinbergBraidDual, steinbergBraidDualInv, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-! ### Cartan involution sandwiches (A19 core, verified subset) -/

/-- `J S (-J) = -V S` (exact `V`-shell sign reversal). -/
theorem genJ_sandwich_s {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * invS P * -(genJ P A C) = -(genV P A C * invS P) := by
  simp only [genJ, genV, anticomm, invS, conePlus, coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- `Φ S Φ = -V S`. -/
theorem genPhi_sandwich_s {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * invS P * genPhi P A C = -(genV P A C * invS P) := by
  simp only [genPhi, genV, anticomm, invS, conePlus, coneMinus, add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- Weyl reflection of the grading: `W S W' = ((1 - V)² - V) S - 2(1 - V)Φ`
(the stream form, confirmed by the word model). -/
theorem weyl_sandwich_s {P : B} (hP : P * P = P) (A C : B) :
    weylJ P A C * invS P * weylJInv P A C
      = ((1 - genV P A C) * (1 - genV P A C) - genV P A C) * invS P
        - (2 : ℤ) • ((1 - genV P A C) * genPhi P A C) := by
  simp only [weylJ, weylJInv, genPhi, genJ, genV, anticomm, invS, conePlus, coneMinus,
    add_mul, mul_add, sub_mul]
  noncomm_ring [hP, P_assoc hP]

/-- **Corrected braid reflection of the Cartan grading** (the stream's draft
`S - 2J - 2Σ - 2(1 - 2V)N₊` form was refuted by the exact word model; this is the
verified transcribed 9-chain form). -/
theorem braid_reflection_s {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C * invS P * steinbergBraidInv P A C
      = invS P
        - (4 : ℤ) • (conePlus P A)
        - (2 : ℤ) • (coneMinus P C)
        - (4 : ℤ) • (conePlus P A * coneMinus P C)
        + (4 : ℤ) • (coneMinus P C * conePlus P A)
        + (6 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A)
        + (2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C)
        + (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A * coneMinus P C)
        - (2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C * conePlus P A)
        - (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
            * conePlus P A) := by
  simp only [steinbergBraid, steinbergBraidInv, invS, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-! ### `Mat₃(ℚ)`-over-`ℂ` witness (non-vacuity of the off-shell identities) -/

/-!
The witness is `P₃ = E₁₁`, `A₃ = E₁₂ + 2E₁₃`, `C₃ = E₂₁ + E₃₁`.  On it the witness
mass has `3` at the `(0, 0)` entry, so `genV ≠ 0`, and `V² - V` has `6` at `(0, 0)`:
the Cayley-Weyl defect is **real**, while the braids still invert exactly.
-/

section Witness

open InfoGeometry.Algebra.FiniteSpin

/-- Witness idempotent `P₃ = E₁₁`. -/
noncomputable def wP : Mat3C := ![![(1 : ℂ), 0, 0], ![0, 0, 0], ![0, 0, 0]]

/-- Witness upper coordinate `A₃ = E₁₂ + 2E₁₃`. -/
noncomputable def wA : Mat3C := ![![(0 : ℂ), 1, 2], ![0, 0, 0], ![0, 0, 0]]

/-- Witness lower coordinate `C₃ = E₂₁ + E₃₁`. -/
noncomputable def wC : Mat3C := ![![(0 : ℂ), 0, 0], ![1, 0, 0], ![1, 0, 0]]

/-- Upper mass part `N₊ N₋ = 3E₁₁`. -/
noncomputable def wVNp : Mat3C := ![![(3 : ℂ), 0, 0], ![0, 0, 0], ![0, 0, 0]]

/-- Lower mass part `N₋ N₊ = E₂₂ + 2E₂₃ + E₃₂ + 2E₃₃`. -/
noncomputable def wVNn : Mat3C := ![![(0 : ℂ), 0, 0], ![0, 1, 2], ![0, 1, 2]]

/-- The witness mass `V = N₊N₋ + N₋N₊ = 3E₁₁ + E₂₂ + 2E₂₃ + E₃₂ + 2E₃₃`. -/
noncomputable def wV : Mat3C := ![![(3 : ℂ), 0, 0], ![0, 1, 2], ![0, 1, 2]]

theorem wP_idem : wP * wP = wP := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    norm_num [wP, Fin.sum_univ_three]

theorem wP_mul_wA : wP * wA = wA := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    norm_num [wP, wA, Fin.sum_univ_three]

theorem wA_mul_wP : wA * wP = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    norm_num [wP, wA, Fin.sum_univ_three]

theorem wP_mul_wC : wP * wC = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    norm_num [wP, wC, Fin.sum_univ_three]

theorem wOne_subP_mul_wC : (1 - wP) * wC = wC := by
  calc
    (1 - wP) * wC = wC - wP * wC := by rw [sub_mul, one_mul]
    _ = wC := by rw [wP_mul_wC, sub_zero]

theorem wC_mul_wP : wC * wP = wC := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    norm_num [wP, wC, Fin.sum_univ_three]

/-- The witness upper cone is `A₃` itself. -/
theorem wNp_eq : conePlus wP wA = wA := by
  simp only [conePlus]
  rw [wP_mul_wA, mul_sub, mul_one, wA_mul_wP, sub_zero]

/-- The witness lower cone is again the coordinate matrix `C₃` (the `C P` block reduces
back onto `C₃`). -/
theorem wNm_eq : coneMinus wP wC = wC := by
  simp only [coneMinus]
  rw [wOne_subP_mul_wC, wC_mul_wP]

theorem wA_mul_wC : wA * wC = wVNp := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    norm_num [wA, wC, wVNp, Fin.sum_univ_three]

theorem wC_mul_wA : wC * wA = wVNn := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    norm_num [wA, wC, wVNn, Fin.sum_univ_three]

/-- The witness mass equals its explicit numeric form. -/
theorem wV_eq : genV wP wA wC = wV := by
  simp only [genV, anticomm, add_mul]
  rw [wNp_eq, wNm_eq]
  rw [wA_mul_wC, wC_mul_wA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    change wVNp _ _ + wVNn _ _ = wV _ _ <;>
    norm_num [wVNp, wVNn, wV]

/-- The mass is nonzero on the witness (no off-shell identity is vacuous). -/
theorem witness_genV_ne_zero : genV wP wA wC ≠ 0 := by
  intro h
  have h3 : genV wP wA wC 0 0 = 3 := by
    rw [wV_eq]
    norm_num [wV]
  rw [h, Matrix.zero_apply] at h3
  norm_num at h3

/-- The off-shell idempotency defect `V² - V` is real on the witness. -/
theorem witness_defect_ne_zero :
    genV wP wA wC * genV wP wA wC - genV wP wA wC ≠ 0 := by
  intro h
  have h6 : (genV wP wA wC * genV wP wA wC - genV wP wA wC) 0 0 = 6 := by
    rw [wV_eq, Matrix.sub_apply, Matrix.mul_apply]
    norm_num [wV, Fin.sum_univ_three]
  rw [h, Matrix.zero_apply] at h6
  norm_num at h6

/-- The Cayley-Weyl unitarity defect is real on the witness (`W W' - 1 ≠ 0`). -/
theorem witness_weyl_defect_ne_zero :
    weylJ wP wA wC * weylJInv wP wA wC - 1 ≠ 0 := by
  rw [weyl_defect wP_idem wA wC]
  exact witness_defect_ne_zero

/-- The braids still invert exactly on the witness while `W` does not
(a nontrivial unit in the very same ring). -/
theorem witness_braid_inverts :
    steinbergBraid wP wA wC * steinbergBraidInv wP wA wC = 1 :=
  braid_mul_inv wP_idem wA wC

end Witness

end PureNonCommutativeOperatorSpine
