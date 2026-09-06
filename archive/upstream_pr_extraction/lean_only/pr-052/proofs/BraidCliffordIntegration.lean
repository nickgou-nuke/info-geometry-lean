import Mathlib
import proofs.FibonacciCliffordBridge
import proofs.MajoranaBraidGroup

/-!
# Braid--Clifford Integration

A compact bridge from the Artin braid skeleton to the local Clifford atom.
The external `BraidProject` supplies a richer presented-monoid/group backend;
this file internalizes the finite core we need here:

* adjacent and separated Artin moves on words;
* length preservation under those moves;
* a uniform Clifford/Witten amplitude depending only on word length;
* a degenerate but honest Clifford-atom representation of braid generators by
  the two-atom parity channel, satisfying the Artin relations.
-/

noncomputable section

open Matrix Real
open scoped BigOperators

namespace InfoGeometry.GrandUnification.BraidCliffordIntegration

abbrev M4R := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- Imported two-atom parity channel from the Fibonacci--Clifford bridge. -/
def localTwoAtomParity : M4R :=
  InfoGeometry.GrandUnification.FibonacciCliffordBridge.twoAtomParity

/-- Square-one property of the imported two-atom parity channel. -/
theorem localTwoAtomParity_sq : localTwoAtomParity * localTwoAtomParity = (1 : M4R) := by
  exact InfoGeometry.GrandUnification.FibonacciCliffordBridge.twoAtomParity_sq

/-- Elementary Artin moves for the infinite braid skeleton. -/
inductive ArtinMove : List ℕ → List ℕ → Prop
  | adjacent (i : ℕ) :
      ArtinMove [i, i + 1, i] [i + 1, i, i + 1]
  | adjacent_symm (i : ℕ) :
      ArtinMove [i + 1, i, i + 1] [i, i + 1, i]
  | separated (i j : ℕ) (h : i + 2 ≤ j) :
      ArtinMove [i, j] [j, i]
  | separated_symm (i j : ℕ) (h : i + 2 ≤ j) :
      ArtinMove [j, i] [i, j]

/-- Artin moves preserve braid-word length. -/
theorem ArtinMove.length_eq {u v : List ℕ} (h : ArtinMove u v) :
    u.length = v.length := by
  cases h <;> rfl

/-- Uniform Clifford-atom amplitude attached to a braid word. -/
def uniformCliffordAmplitude (q : ℝ) (w : List ℕ) : ℝ :=
  q ^ w.length

/-- Uniform amplitude is invariant under elementary Artin moves. -/
theorem artinMove_preserves_uniformCliffordAmplitude
    {u v : List ℕ} (h : ArtinMove u v) (q : ℝ) :
    uniformCliffordAmplitude q u = uniformCliffordAmplitude q v := by
  simp [uniformCliffordAmplitude, h.length_eq]

/-- The local pure-squeeze Witten weight of one Clifford atom. -/
def atomWittenWeight (α : ℝ) : ℝ :=
  2 * Real.sinh α

/-- Braid word interpreted as a uniform tensor product of identical Clifford atoms. -/
def braidWordWittenWeight (α : ℝ) (w : List ℕ) : ℝ :=
  uniformCliffordAmplitude (atomWittenWeight α) w

/-- The Witten weight of a uniform Clifford braid word is Artin-invariant. -/
theorem artinMove_preserves_braidWordWittenWeight
    {u v : List ℕ} (h : ArtinMove u v) (α : ℝ) :
    braidWordWittenWeight α u = braidWordWittenWeight α v := by
  exact artinMove_preserves_uniformCliffordAmplitude h (atomWittenWeight α)

/-- Degenerate local Clifford representation of each braid generator by two-atom parity. -/
def cliffordBraidGate (_i : ℕ) : M4R :=
  localTwoAtomParity

/-- The two-atom parity gate is tripotent. -/
theorem cliffordBraidGate_cubed (i : ℕ) :
    cliffordBraidGate i * cliffordBraidGate i * cliffordBraidGate i = cliffordBraidGate i := by
  calc
    cliffordBraidGate i * cliffordBraidGate i * cliffordBraidGate i
        = (cliffordBraidGate i * cliffordBraidGate i) * cliffordBraidGate i := by
          simp [mul_assoc]
    _ = (1 : M4R) * cliffordBraidGate i := by
          rw [show cliffordBraidGate i * cliffordBraidGate i = (1 : M4R) by
            simp [cliffordBraidGate, localTwoAtomParity_sq]]
    _ = cliffordBraidGate i := by
          rw [one_mul]

/-- Adjacent Artin relation under the local two-atom parity representation. -/
theorem clifford_adjacent_artin (i : ℕ) :
    cliffordBraidGate i * cliffordBraidGate (i + 1) * cliffordBraidGate i =
      cliffordBraidGate (i + 1) * cliffordBraidGate i * cliffordBraidGate (i + 1) := by
  simp [cliffordBraidGate]

/-- Separated Artin commutation under the local two-atom parity representation. -/
theorem clifford_separated_artin (i j : ℕ) :
    cliffordBraidGate i * cliffordBraidGate j = cliffordBraidGate j * cliffordBraidGate i := by
  simp [cliffordBraidGate]

/-- Finite-stage inclusion into the infinite braid boundary. -/
def finiteToInfinite {n : ℕ} (i : Fin n) : ℕ := i.1

/-- Successor inclusion preserves the infinite boundary generator. -/
theorem finiteToInfinite_castSucc {n : ℕ} (i : Fin n) :
    finiteToInfinite (Fin.castSucc i) = finiteToInfinite i := by
  rfl

/-- The finite Majorana braid matrix used as the first nondegenerate adjacent generator. -/
def majoranaGate12 : InfoGeometry.GrandUnification.MajoranaBraidGroup.M8Z :=
  InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12

/-- The finite Majorana braid matrix used as the second nondegenerate adjacent generator. -/
def majoranaGate23 : InfoGeometry.GrandUnification.MajoranaBraidGroup.M8Z :=
  InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23

/-- Nondegenerate adjacent Majorana generators satisfy the Artin braid relation. -/
theorem majorana_adjacent_artin_bridge :
    majoranaGate12 * majoranaGate23 * majoranaGate12 =
      majoranaGate23 * majoranaGate12 * majoranaGate23 := by
  exact InfoGeometry.GrandUnification.MajoranaBraidGroup.majorana_adjacent_artin

/-- Unlike the uniform two-atom parity channel, the Majorana adjacent generators do not commute. -/
theorem majorana_adjacent_noncommuting_bridge :
    majoranaGate12 * majoranaGate23 ≠ majoranaGate23 * majoranaGate12 := by
  decide

/-- The imported Majorana finite theorem strengthens the braid--Clifford bridge. -/
theorem braid_clifford_majorana_strengthening :
    majoranaGate12 * majoranaGate23 * majoranaGate12 =
      majoranaGate23 * majoranaGate12 * majoranaGate23 ∧
    majoranaGate12 * majoranaGate23 ≠ majoranaGate23 * majoranaGate12 := by
  exact ⟨majorana_adjacent_artin_bridge, majorana_adjacent_noncommuting_bridge⟩

end InfoGeometry.GrandUnification.BraidCliffordIntegration

namespace InfoGeometry.GrandUnification.BraidIntegration

open Complex

/-- Complex `2 × 2` matrices for the finite local braid gate model. -/
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- A finite braid word at stage `n`, represented by a list of Artin generator indices. -/
def BraidWord (n : ℕ) := List (Fin n)

/-- Elementary finite-stage Artin moves, plus transitive closure. -/
inductive ArtinMove {n : ℕ} : BraidWord n → BraidWord n → Prop
  | adjacent (i : Fin n) (h : i.val + 1 < n) :
      ArtinMove [i, ⟨i.val + 1, h⟩, i] [⟨i.val + 1, h⟩, i, ⟨i.val + 1, h⟩]
  | separated (i j : Fin n) (h : i.val + 2 ≤ j.val) :
      ArtinMove [i, j] [j, i]
  | trans (w1 w2 w3 : BraidWord n) :
      ArtinMove w1 w2 → ArtinMove w2 w3 → ArtinMove w1 w3

/-- Artin moves preserve word length. -/
theorem ArtinMove.length_eq {n : ℕ} {w1 w2 : BraidWord n} (h : ArtinMove w1 w2) :
    w1.length = w2.length := by
  induction h with
  | adjacent i h => rfl
  | separated i j h => rfl
  | trans w1 w2 w3 h1 h2 ih1 ih2 => rw [ih1, ih2]

/-- Uniform Clifford flow amplitude `q^|w|`. -/
def uniformCliffordAmplitude (q : ℂ) {n : ℕ} (w : BraidWord n) : ℂ :=
  q ^ w.length

/-- Thermodynamic Witten weight of a braid word, using the complexified atom weight. -/
def braidWordWittenWeight (α : ℂ) {n : ℕ} (w : BraidWord n) : ℂ :=
  (2 * sinh α) ^ w.length

/-- Artin translations preserve uniform length-only Clifford amplitudes. -/
theorem artinMove_preserves_uniformCliffordAmplitude
    (q : ℂ) {n : ℕ} {w1 w2 : BraidWord n} (h : ArtinMove w1 w2) :
    uniformCliffordAmplitude q w1 = uniformCliffordAmplitude q w2 := by
  simp [uniformCliffordAmplitude, h.length_eq]

/-- Artin translations preserve the Witten weight of the vacuum word. -/
theorem artinMove_preserves_braidWordWittenWeight
    (α : ℂ) {n : ℕ} {w1 w2 : BraidWord n} (h : ArtinMove w1 w2) :
    braidWordWittenWeight α w1 = braidWordWittenWeight α w2 := by
  simp [braidWordWittenWeight, h.length_eq]

/-- Complex chiral grading. -/
def sigma3 : M2C := !![1, 0; 0, -1]

/-- Real-form representative of `iσ₂` over `ℂ`; its square is `-I`. -/
def iSigma2 : M2C := !![0, 1; -1, 0]

/-- Local Pauli parity channel `σ₃ · iσ₂`.  This is `σ₁` in real matrix form. -/
def twoAtomParity : M2C := sigma3 * iSigma2

/-- Uniform Clifford braid gate for a generator index. -/
def cliffordBraidGate (_i : ℕ) : M2C := twoAtomParity

/-- `iσ₂` has square `-I`; hence it is the projective/cyclic braid phase channel. -/
theorem iSigma2_sq : iSigma2 * iSigma2 = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [iSigma2]

/-- The parity channel has square `+I`. -/
theorem twoAtomParity_sq : twoAtomParity * twoAtomParity = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [twoAtomParity, sigma3, iSigma2]

/-- The projective phase channel satisfies the cubic relation `G³ = -G`. -/
theorem iSigma2_cubed_neg : iSigma2 * iSigma2 * iSigma2 = -iSigma2 := by
  calc
    iSigma2 * iSigma2 * iSigma2 = (iSigma2 * iSigma2) * iSigma2 := by simp [mul_assoc]
    _ = (-(1 : M2C)) * iSigma2 := by rw [iSigma2_sq]
    _ = -iSigma2 := by
          rw [neg_mul, one_mul]

/-- The parity braid gate is tripotent: `G³ = G`.

The literal formula `G³ = -G` applies to `iSigma2`; for `σ₃ iσ₂` the square is `+I`,
so the theorem-honest closure is the tripotent one below. -/
theorem cliffordBraidGate_cubed (i : ℕ) :
    cliffordBraidGate i * cliffordBraidGate i * cliffordBraidGate i = cliffordBraidGate i := by
  calc
    cliffordBraidGate i * cliffordBraidGate i * cliffordBraidGate i
        = (cliffordBraidGate i * cliffordBraidGate i) * cliffordBraidGate i := by simp [mul_assoc]
    _ = (1 : M2C) * cliffordBraidGate i := by
          rw [show cliffordBraidGate i * cliffordBraidGate i = (1 : M2C) by
            simp [cliffordBraidGate, twoAtomParity_sq]]
    _ = cliffordBraidGate i := by
          rw [one_mul]

/-- Adjacent Artin relation in the uniform local Clifford representation. -/
theorem clifford_adjacent_artin (i : ℕ) :
    cliffordBraidGate i * cliffordBraidGate (i+1) * cliffordBraidGate i =
    cliffordBraidGate (i+1) * cliffordBraidGate i * cliffordBraidGate (i+1) := by
  simp [cliffordBraidGate]

/-- Separated Artin commutation in the uniform local Clifford representation. -/
theorem clifford_separated_artin (i j : ℕ) (_h : i + 2 ≤ j) :
    cliffordBraidGate i * cliffordBraidGate j = cliffordBraidGate j * cliffordBraidGate i := by
  simp [cliffordBraidGate]

/-- Stage-successor embedding of a finite braid word. -/
def finiteToInfinite {n : ℕ} : BraidWord n → BraidWord (n + 1)
  | [] => []
  | i :: ws => ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩ :: finiteToInfinite ws

/-- The successor embedding preserves length. -/
theorem finiteToInfinite_length {n : ℕ} (w : BraidWord n) :
    (finiteToInfinite w).length = w.length := by
  induction w with
  | nil => rfl
  | cons i ws ih => simp [finiteToInfinite, ih]

/-- Singleton embedding is the expected `Fin.castSucc`-style inclusion. -/
theorem finiteToInfinite_castSucc {n : ℕ} (i : Fin n) :
    finiteToInfinite [i] = [⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩] := rfl

/-- Adjacent finite Artin moves embed into the successor stage. -/
theorem finite_adjacent_to_infinite {n : ℕ} (i : Fin n) (h : i.val + 1 < n) :
    ArtinMove (finiteToInfinite [i, ⟨i.val + 1, h⟩, i])
      (finiteToInfinite [⟨i.val + 1, h⟩, i, ⟨i.val + 1, h⟩]) := by
  dsimp [finiteToInfinite]
  have h_plus : i.val + 1 < n + 1 := Nat.lt_trans h (Nat.lt_succ_self n)
  exact ArtinMove.adjacent ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩ h_plus

/-! ### 6. Abstract nondegenerate Majorana/Yang--Baxter algebra -/

/-- Abstract exchange operator generated by two Majorana/Clifford modes.  In concrete
matrix models this is proportional to `exp(π/4 · γᵢγⱼ)`.  The scalar normalization
cancels from the adjacent Artin relation, so the unnormalized form is enough. -/
def majoranaExchange {R : Type*} [Ring R] (γᵢ γⱼ : R) : R :=
  1 + γᵢ * γⱼ

/-- Algebraic Yang--Baxter/adjacent Artin relation for three anticommuting Majorana
modes.  This is the theorem-level Lean counterpart of the `8 × 8` SymPy computation. -/
theorem majorana_adjacent_artin
    {R : Type*} [Ring R] (γ₁ γ₂ γ₃ : R)
    (h12 : γ₁ * γ₂ = -(γ₂ * γ₁))
    (h23 : γ₂ * γ₃ = -(γ₃ * γ₂))
    (_h13 : γ₁ * γ₃ = -(γ₃ * γ₁))
    (h1 : γ₁ * γ₁ = 1) (h2 : γ₂ * γ₂ = 1) (h3 : γ₃ * γ₃ = 1) :
    majoranaExchange γ₁ γ₂ * majoranaExchange γ₂ γ₃ * majoranaExchange γ₁ γ₂ =
      majoranaExchange γ₂ γ₃ * majoranaExchange γ₁ γ₂ * majoranaExchange γ₂ γ₃ := by
  let A : R := γ₁ * γ₂
  let B : R := γ₂ * γ₃
  have hA : A * A = -1 := by
    dsimp [A]
    calc
      (γ₁ * γ₂) * (γ₁ * γ₂) = γ₁ * (γ₂ * γ₁) * γ₂ := by noncomm_ring
      _ = γ₁ * (-(γ₁ * γ₂)) * γ₂ := by
            have h21 : γ₂ * γ₁ = -(γ₁ * γ₂) := by rw [h12]; abel
            rw [h21]
      _ = -(γ₁ * γ₁) * (γ₂ * γ₂) := by noncomm_ring
      _ = -1 := by rw [h1, h2]; noncomm_ring
  have hB : B * B = -1 := by
    dsimp [B]
    calc
      (γ₂ * γ₃) * (γ₂ * γ₃) = γ₂ * (γ₃ * γ₂) * γ₃ := by noncomm_ring
      _ = γ₂ * (-(γ₂ * γ₃)) * γ₃ := by
            have h32 : γ₃ * γ₂ = -(γ₂ * γ₃) := by rw [h23]; abel
            rw [h32]
      _ = -(γ₂ * γ₂) * (γ₃ * γ₃) := by noncomm_ring
      _ = -1 := by rw [h2, h3]; noncomm_ring
  have hAB : A * B = -(B * A) := by
    dsimp [A, B]
    have hAB_left : (γ₁ * γ₂) * (γ₂ * γ₃) = γ₁ * γ₃ := by
      calc
        (γ₁ * γ₂) * (γ₂ * γ₃) = γ₁ * (γ₂ * γ₂) * γ₃ := by noncomm_ring
        _ = γ₁ * 1 * γ₃ := by rw [h2]
        _ = γ₁ * γ₃ := by noncomm_ring
    have hBA_calc : (γ₂ * γ₃) * (γ₁ * γ₂) = -(γ₁ * γ₃) := by
      calc
        (γ₂ * γ₃) * (γ₁ * γ₂) = γ₂ * (γ₃ * γ₁) * γ₂ := by noncomm_ring
        _ = γ₂ * (-(γ₁ * γ₃)) * γ₂ := by
              have h31 : γ₃ * γ₁ = -(γ₁ * γ₃) := by rw [_h13]; abel
              rw [h31]
        _ = -(γ₂ * γ₁) * (γ₃ * γ₂) := by noncomm_ring
        _ = - (-(γ₁ * γ₂)) * (-(γ₂ * γ₃)) := by
              have h21 : γ₂ * γ₁ = -(γ₁ * γ₂) := by rw [h12]; abel
              have h32 : γ₃ * γ₂ = -(γ₂ * γ₃) := by rw [h23]; abel
              rw [h21, h32]
        _ = -(γ₁ * γ₃) := by
              calc
                - (-(γ₁ * γ₂)) * (-(γ₂ * γ₃)) = -((γ₁ * γ₂) * (γ₂ * γ₃)) := by noncomm_ring
                _ = -(γ₁ * γ₃) := by rw [hAB_left]
    calc
      (γ₁ * γ₂) * (γ₂ * γ₃) = γ₁ * γ₃ := hAB_left
      _ = -(-(γ₁ * γ₃)) := by rw [neg_neg]
      _ = -((γ₂ * γ₃) * (γ₁ * γ₂)) := by rw [hBA_calc]
  have hBA : B * A = -(A * B) := by rw [hAB]; abel
  have hABA : A * B * A = B := by
    calc
      A * B * A = -(B * A) * A := by rw [hAB]
      _ = -(B * (A * A)) := by simp [mul_assoc]
      _ = -(B * (-1)) := by rw [hA]
      _ = B := by noncomm_ring
  have hBAB : B * A * B = A := by
    calc
      B * A * B = -(A * B) * B := by rw [hBA]
      _ = -(A * (B * B)) := by simp [mul_assoc]
      _ = -(A * (-1)) := by rw [hB]
      _ = A := by noncomm_ring
  change (1 + A) * (1 + B) * (1 + A) = (1 + B) * (1 + A) * (1 + B)
  calc
    (1 + A) * (1 + B) * (1 + A)
        = 1 + B + A + A*B + A + B*A + A*A + A*B*A := by noncomm_ring
    _ = 1 + B + A + A*B + A + (-(A*B)) + (-1) + B := by rw [hBA, hA, hABA]
    _ = 2*A + 2*B := by noncomm_ring
    _ = 1 + A + B + B*A + B + A*B + B*B + B*A*B := by rw [hBAB, hBA, hB]; noncomm_ring
    _ = (1 + B) * (1 + A) * (1 + B) := by noncomm_ring

/-- After embedding to the successor boundary, Artin moves still
preserve the thermodynamic Witten weight. -/
theorem braid_clifford_finiteToInfinite_weight_relation
    {n : ℕ} (w1 w2 : BraidWord n) (h_move : ArtinMove w1 w2) (α : ℂ) :
    braidWordWittenWeight α (finiteToInfinite w1) = braidWordWittenWeight α (finiteToInfinite w2) := by
  simp [braidWordWittenWeight, finiteToInfinite_length, h_move.length_eq]

end InfoGeometry.GrandUnification.BraidIntegration
