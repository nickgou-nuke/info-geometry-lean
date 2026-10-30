/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SteinbergMoebiusProjectiveLine
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Bergman-Hua, symplectic form, Jordan triple and Zorn-Krein extensions (A23-A25)

Owner module for the "drunken professor" deconfabulation of the Erlangen-2.0 stream
archetypes `A23`-`A25`.  Everything extends
`PureNonCommutativeOperatorSpine` (cones, tetraktys, braids, charts) over an arbitrary
associative unital ring `B`, still with the single hypothesis `hP : P * P = P`:
no commutativity, no division, no scalar carrier beyond integer multiples
(the `peirce_abel` macro is deliberately not used; every proof is
`simp only [defs]; noncomm_ring [hP, P_assoc hP]`).

* the Bergman operator `X ↦ (1 - N₊N₋) X (1 - N₋N₊)` is computed on the generator
  set `1, N₊, N₋, Φ, V` in the model-corrected forms (A23.1-A23.3) - the drafts
  `(1-V)N₊`, `N₋(1-V)`, `(1-V)Φ` were refuted;
* the Hua pair `conjPlus(A)(1 - vu)` and `conjMinusInv(C)(1 - uv)` are two distinct
  identities (A23.4a, A23.4b with its factorized variant); the drafts declaring
  them equal, or equal to the common value `(1-V)(1+J)`, were refuted (A23.5, A23.6);
* the chart commutator pairing is `Sigma` of the chart differences and is
  alternating; it is shift-invariant, with `S · Ω = V` (A24.1-A24.4), and the sandwich laws
  `ΦΣΦ = Φ(-J)Σ(-J) = -VΣ` (A24.5, A24.6);
* the Jordan triples `{N₊, N₋, N₊} = 2VN₊`, `{N₋, N₊, N₋} = 2VN₋`, `{Φ, Φ, Φ} = 2VΦ`,
  `{Φ, J, Φ} = -2VJ` (A25.1-A25.4), and the Zorn-Krein conjugation
  `S(V ± Φ)S = V - (±Φ)`, `S(V + J)S = V - J` with norms `V² ∓ V` (A25.5-A25.8).

Every statement was first arbitrated by the exact reduced-word model in
`proofs/steinberg_braid_defect_spine.py` (7 draft refutations archived there)
before transcription.
-/

namespace PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

/-! ### A23: Bergman operator and the two Hua identities -/

/-- The Bergman sandwich operator at the base pair `(A, C)`:
`X ↦ (1 - N₊N₋) X (1 - N₋N₊)`. -/
def bergmanOp (P A C X : B) : B :=
  (1 - conePlus P A * coneMinus P C) * X * (1 - coneMinus P C * conePlus P A)

/-- Exact composition law for the Bergman sandwich. In general its two
outside factors are not involutions, so the sandwich itself need not be an
involution. -/
theorem bergmanOp_iterate (P A C X : B) :
    bergmanOp P A C (bergmanOp P A C X) =
      ((1 - conePlus P A * coneMinus P C) *
        (1 - conePlus P A * coneMinus P C)) * X *
        ((1 - coneMinus P C * conePlus P A) *
          (1 - coneMinus P C * conePlus P A)) := by
  simp only [bergmanOp]
  noncomm_ring

/-! A concrete matrix model shows why `bergmanOp` is called an operator rather
than an involution. The generic theorems above remain over arbitrary rings. -/

abbrev BergmanWitnessMatrix := Matrix (Fin 2) (Fin 2) ℤ

def bergmanWitnessP : BergmanWitnessMatrix := Matrix.single 0 0 1
def bergmanWitnessA : BergmanWitnessMatrix := Matrix.single 0 1 1
def bergmanWitnessC : BergmanWitnessMatrix := Matrix.single 1 0 1

/-- With a noncentral idempotent and noncommuting off-diagonal inputs, the
Bergman sandwich sends `1` to `0`; hence it is not an involution. -/
theorem bergmanOp_matrix_not_involutive :
    bergmanWitnessP * bergmanWitnessP = bergmanWitnessP ∧
    bergmanWitnessA * bergmanWitnessC ≠ bergmanWitnessC * bergmanWitnessA ∧
    ∃ X : BergmanWitnessMatrix,
      bergmanOp bergmanWitnessP bergmanWitnessA bergmanWitnessC
        (bergmanOp bergmanWitnessP bergmanWitnessA bergmanWitnessC X) ≠ X := by
  refine ⟨?_, ?_, ⟨1, ?_⟩⟩ <;> decide

/-- **A23.1**: `bergman(1) = 1 - V`. -/
theorem bergmanOp_one {P : B} (hP : P * P = P) (A C : B) :
    bergmanOp P A C 1 = 1 - genV P A C := by
  simp only [bergmanOp, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A23.2a** (corrected): `bergman(N₊) = (1-V)² N₊`.  The draft
`bergman(N₊) = (1-V) N₊` was refuted (it misses the `(1-V)(V-1)` factor). -/
theorem bergmanOp_conePlus {P : B} (hP : P * P = P) (A C : B) :
    bergmanOp P A C (conePlus P A)
      = (1 - genV P A C) * (1 - genV P A C) * conePlus P A := by
  simp only [bergmanOp, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A23.2b** (corrected): `bergman(N₋) = N₋` exactly (no right action of `V`).
The draft `N₋ (1-V)` was refuted in the model. -/
theorem bergmanOp_coneMinus {P : B} (hP : P * P = P) (A C : B) :
    bergmanOp P A C (coneMinus P C) = coneMinus P C := by
  simp only [bergmanOp, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A23.2c** (corrected): `bergman(Φ) = (1-V)² N₊ + N₋`.  The draft `(1-V)Φ`
was refuted. -/
theorem bergmanOp_genPhi {P : B} (hP : P * P = P) (A C : B) :
    bergmanOp P A C (genPhi P A C)
      = (1 - genV P A C) * (1 - genV P A C) * conePlus P A + coneMinus P C := by
  simp only [bergmanOp, genPhi, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A23.3**: `bergman(V) = (1-V) V`. -/
theorem bergmanOp_genV {P : B} (hP : P * P = P) (A C : B) :
    bergmanOp P A C (genV P A C) = (1 - genV P A C) * genV P A C := by
  simp only [bergmanOp, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A23.4a** (corrected Hua upper identity):
`conjPlus(A)(1 - vu) = 1 - vu - V N₊`. -/
theorem hua_pair_upper {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (1 - coneMinus P C * conePlus P A)
      = 1 - coneMinus P C * conePlus P A - genV P A C * conePlus P A := by
  simp only [conjPlus, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A23.4a'** (factorized variant of the same identity):
`conjPlus(A)(1 - vu) = 1 - (1 + N₊)(vu)`. -/
theorem hua_pair_upper_variant {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (1 - coneMinus P C * conePlus P A)
      = 1 - (1 + conePlus P A) * (coneMinus P C * conePlus P A) := by
  simp only [conjPlus, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A23.4b** (corrected Hua lower identity):
`conjMinusInv(C)(1 - uv) = 1 - uv + V N₋` (a *separate* identity; the draft
declaring the two Hua sides equal, and the draft common value `(1-V)(1+J)`,
were both refuted). -/
theorem hua_pair_lower {P : B} (hP : P * P = P) (A C : B) :
    conjMinusInv P C (1 - conePlus P A * coneMinus P C)
      = 1 - conePlus P A * coneMinus P C + genV P A C * coneMinus P C := by
  simp only [conjMinusInv, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-! ### A24: chart commutator pairing and operator sandwich identities -/

/-- Commutator pairing on the two Peirce chart differences. This definition
alone asserts neither alternatingness nor nondegeneracy, so it is not promoted
to a symplectic or Kähler form. -/
def operatorSymplecticForm (P X₁ X₂ Y₁ Y₂ : B) : B :=
  comm (projChartPlus P X₁ - projChartPlus P X₂)
    (projChartMinus P Y₁ - projChartMinus P Y₂)

/-- **A24.1**: `Omega(dX, dY) = Sigma(dX, dY)`. -/
theorem operatorSymplecticForm_eq_genSig {P : B} (hP : P * P = P) (X₁ X₂ Y₁ Y₂ : B) :
    operatorSymplecticForm P X₁ X₂ Y₁ Y₂ = genSig P (X₁ - X₂) (Y₁ - Y₂) := by
  simp only [operatorSymplecticForm, genSig, comm, projChartPlus, projChartMinus,
    conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A24.2**: base form `Omega(A, 0; C, 0) = Sigma(A, C)`. -/
theorem operatorSymplecticForm_base {P : B} (hP : P * P = P) (A C : B) :
    operatorSymplecticForm P A 0 C 0 = genSig P A C := by
  rw [operatorSymplecticForm_eq_genSig hP]
  simp only [sub_zero]

/-- **A24.3**: shift invariance of the symplectic form. -/
theorem operatorSymplecticForm_shift {P : B} (hP : P * P = P) (X Z Y C A : B) :
    operatorSymplecticForm P (X + A) (Z + A) (Y + C) (0 + C)
      = operatorSymplecticForm P X Z Y 0 := by
  simp only [operatorSymplecticForm, comm, projChartPlus, projChartMinus,
    conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A24.4**: `S · Ω = V(dX, dY)`; with A24.1 this reads
`S · Ω = ` the operator cross ratio of the differences. -/
theorem operatorSymplecticForm_S_mul {P : B} (hP : P * P = P) (X Z Y : B) :
    invS P * operatorSymplecticForm P X Z Y 0 = genV P (X - Z) Y := by
  rw [operatorSymplecticForm_eq_genSig hP, invS_mul_genSig hP]
  simp only [sub_zero]

/-- **A24.5**: `Φ Σ Φ = -V Σ`. -/
theorem genPhi_sandwich_genSig {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genSig P A C * genPhi P A C = -(genV P A C * genSig P A C) := by
  simp only [genPhi, genSig, genV, comm, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A24.6**: `J Σ (-J) = -V Σ`. -/
theorem genJ_neg_sandwich_genSig {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genSig P A C * -(genJ P A C) = -(genV P A C * genSig P A C) := by
  simp only [genJ, genSig, genV, comm, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-! ### A25: Jordan triple and Zorn-Krein conjugation -/

/-- Jordan triple product `{a, b, c} = (ab)c + (cb)a`. -/
def jordanTriple (a b c : B) : B := a * b * c + c * b * a

/-- `S`-conjugation in the Zorn-Krein grading: `X ↦ S X S`. -/
def zornConj (P X : B) : B := invS P * X * invS P

/-- **A25.1**: `{N₊, N₋, N₊} = 2 V N₊` (the model's doubled form equals the
triple product because the triple ends agree). -/
theorem jordanTriple_conePlusUp {P : B} (hP : P * P = P) (A C : B) :
    jordanTriple (conePlus P A) (coneMinus P C) (conePlus P A)
      = 2 * (genV P A C * conePlus P A) := by
  simp only [jordanTriple, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A25.2**: `{N₋, N₊, N₋} = 2 V N₋`. -/
theorem jordanTriple_coneMinusDn {P : B} (hP : P * P = P) (A C : B) :
    jordanTriple (coneMinus P C) (conePlus P A) (coneMinus P C)
      = 2 * (genV P A C * coneMinus P C) := by
  simp only [jordanTriple, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A25.3**: `{Φ, Φ, Φ} = 2 V Φ`. -/
theorem jordanTriple_genPhi_self {P : B} (hP : P * P = P) (A C : B) :
    jordanTriple (genPhi P A C) (genPhi P A C) (genPhi P A C)
      = 2 * (genV P A C * genPhi P A C) := by
  simp only [jordanTriple, genPhi, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A25.4**: `{Φ, J, Φ} = -2 V J`. -/
theorem jordanTriple_genPhi_genJ {P : B} (hP : P * P = P) (A C : B) :
    jordanTriple (genPhi P A C) (genJ P A C) (genPhi P A C)
      = -(2 * (genV P A C * genJ P A C)) := by
  simp only [jordanTriple, genPhi, genJ, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A25.5**: `S (V + Φ) S = V - Φ`. -/
theorem zornConj_genPhi {P : B} (hP : P * P = P) (A C : B) :
    zornConj P (genV P A C + genPhi P A C) = genV P A C - genPhi P A C := by
  simp only [zornConj, invS, genPhi, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A25.6**: `S (V + J) S = V - J`. -/
theorem zornConj_genJ {P : B} (hP : P * P = P) (A C : B) :
    zornConj P (genV P A C + genJ P A C) = genV P A C - genJ P A C := by
  simp only [zornConj, invS, genJ, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A25.7**: `S`-norm of `V + Φ` is `V² - V`. -/
theorem zorn_norm_genPhi {P : B} (hP : P * P = P) (A C : B) :
    (genV P A C + genPhi P A C) * zornConj P (genV P A C + genPhi P A C)
      = genV P A C * genV P A C - genV P A C := by
  simp only [zornConj, invS, genPhi, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A25.8**: `S`-norm of `V + J` is `V² + V`. -/
theorem zorn_norm_genJ {P : B} (hP : P * P = P) (A C : B) :
    (genV P A C + genJ P A C) * zornConj P (genV P A C + genJ P A C)
      = genV P A C * genV P A C + genV P A C := by
  simp only [zornConj, invS, genJ, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]
