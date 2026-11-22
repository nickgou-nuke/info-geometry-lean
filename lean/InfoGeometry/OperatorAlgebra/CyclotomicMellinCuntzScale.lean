/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis

/-!
# Mellin scale intertwiners of the `Φ₂₄` clock and Cuntz scale hopping in operator rings

Builds on the existing owners `CyclotomicExplicitMatrixRealizations.phi24Companion` (the
integer companion clock of `Φ₂₄ = X⁸ - X⁴ + 1`) and
`CyclotomicGaloisNilpotentSylvesterSynthesis.opPhi24` (`Φ₂₄` on an operator in an arbitrary
ring, with `X¹² = -1`, `X²⁴ = 1`, coprime Galois powers).

* **Mellin intertwiners.**  The Galois scale `ζ ↦ ζᵘ` (`u ∈ (ℤ/24)ˣ`) acts on the clock module
  by explicit integer matrices `mellin u` with `(mellin u)² = 1`,
  `mellin u * C * mellin u = Cᵘ`, `mellin 5 * mellin 7 = mellin 11`; every statement is
  transported to `8 × 8` matrices over an **arbitrary operator ring** `B`
  (`opClock`, `opMellin`), and `(opClock : Matrix (Fin 8) (Fin 8) B)` is a `Φ₂₄`-root in the owner sense.  The
  intertwiners do not commute with the clock (`mellin5_clock_ne`).
* **Cuntz trace obstruction.**  In any ring with an additive cyclic functional `τ`, a Cuntz
  family `S_i* S_i = 1`, `Σ S_i S_i* = 1` with `N` members forces `N • τ 1 = τ 1`.
* **Cuntz endomorphism.**  For any Cuntz family in any ring,
  `ρ(X) = Σ S_i X S_i*` is a unital multiplicative map.
* **Dyadic scale hopping.**  On `ℤ`-indexed signals with values in any additive group, the
  decimation/interpolation operators form a Cuntz `𝒪₂` family inside the noncommutative
  endomorphism ring `AddMonoid.End (ℤ → M)`, so that ring admits no cyclic additive
  functional with `τ 1 ≠ 0` into a torsion-free target.

## Scope

Not proved: `ℤ[ζ₂₄] ≅ E₈` as a lattice, the Turyn / Golay gluing, or any Leech-lattice
statement (kissing number, unimodularity).  Golay codes have separate owners in
`InfoGeometry.Combinatorics`.
-/

namespace InfoGeometry.OperatorAlgebra.CyclotomicMellinCuntzScale

open Matrix
open InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations (phi24Companion)
open InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis
  (opPhi24)

/-! ### Integer Mellin intertwiners (columns: `ζ^{u k mod 24}` in the basis `1, ζ, …, ζ⁷`) -/

def mellin5 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, -1;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

def mellin7 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 1;
     0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, 1, 0, 0, 0, 1, 0, 0]

def mellin13 : Matrix (Fin 8) (Fin 8) ℤ := Matrix.diagonal ![1, -1, 1, -1, 1, -1, 1, -1]

/-- `mellin 11 = mellin 5 * mellin 7` (`5 · 7 ≡ 11 mod 24`). -/
def mellin11 : Matrix (Fin 8) (Fin 8) ℤ := mellin5 * mellin7

theorem mellin_involutions :
    mellin5 * mellin5 = 1 ∧ mellin7 * mellin7 = 1 ∧ mellin13 * mellin13 = 1 ∧
      mellin5 * mellin7 = mellin7 * mellin5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Clock–scale intertwining `M_u C M_u = Cᵘ`. -/
theorem mellin_intertwining :
    mellin5 * phi24Companion * mellin5 = phi24Companion ^ 5 ∧
      mellin7 * phi24Companion * mellin7 = phi24Companion ^ 7 ∧
      mellin11 * phi24Companion * mellin11 = phi24Companion ^ 11 ∧
      mellin13 * phi24Companion * mellin13 = phi24Companion ^ 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The `Φ₂₄` clock as an integer matrix of this module. -/
def clock24 : Matrix (Fin 8) (Fin 8) ℤ := phi24Companion

/-- The scale intertwiner does not commute with the clock. -/
theorem mellin5_clock_ne : mellin5 * clock24 ≠ clock24 * mellin5 := by decide

/-- Integer inverse of the clock: `C (C³ - C⁷) = 1`. -/
theorem clock_inverse : phi24Companion * (phi24Companion ^ 3 - phi24Companion ^ 7) = 1 := by
  decide

/-! ### Transport to `8 × 8` matrices over an arbitrary operator ring -/

section Operator

variable {B : Type*} [Ring B]

/-- The `Φ₂₄` clock with entries in the operator ring `B`. -/
def opClock : Matrix (Fin 8) (Fin 8) B := (Int.castRingHom B).mapMatrix phi24Companion

/-- Mellin intertwiners with entries in `B`. -/
def opMellin5 : Matrix (Fin 8) (Fin 8) B := (Int.castRingHom B).mapMatrix mellin5
def opMellin7 : Matrix (Fin 8) (Fin 8) B := (Int.castRingHom B).mapMatrix mellin7
def opMellin13 : Matrix (Fin 8) (Fin 8) B := (Int.castRingHom B).mapMatrix mellin13

/-- The operator clock is a root of `Φ₂₄` in the owner sense, so the owner's Galois-orbit
results (`X¹² = -1`, `X²⁴ = 1`, coprime powers) apply to it. -/
theorem opPhi24_opClock : opPhi24 ((opClock : Matrix (Fin 8) (Fin 8) B)) = 0 := by
  have h := InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations.phi24Companion_polynomial
  unfold opPhi24 opClock
  rw [← map_pow, ← map_pow, ← map_sub, ← map_one ((Int.castRingHom B).mapMatrix), ← map_add, h,
    map_zero]

theorem opMellin_intertwining :
    (opMellin5 : Matrix (Fin 8) (Fin 8) B) * (opMellin5 : Matrix (Fin 8) (Fin 8) B) = 1 ∧ (opMellin7 : Matrix (Fin 8) (Fin 8) B) * (opMellin7 : Matrix (Fin 8) (Fin 8) B) = 1 ∧
      (opMellin13 : Matrix (Fin 8) (Fin 8) B) * (opMellin13 : Matrix (Fin 8) (Fin 8) B) = 1 ∧
      (opMellin5 : Matrix (Fin 8) (Fin 8) B) * (opClock : Matrix (Fin 8) (Fin 8) B) * (opMellin5 : Matrix (Fin 8) (Fin 8) B) = (opClock : Matrix (Fin 8) (Fin 8) B) ^ 5 ∧
      (opMellin7 : Matrix (Fin 8) (Fin 8) B) * (opClock : Matrix (Fin 8) (Fin 8) B) * (opMellin7 : Matrix (Fin 8) (Fin 8) B) = (opClock : Matrix (Fin 8) (Fin 8) B) ^ 7 ∧
      (opMellin13 : Matrix (Fin 8) (Fin 8) B) * (opClock : Matrix (Fin 8) (Fin 8) B) * (opMellin13 : Matrix (Fin 8) (Fin 8) B) = (opClock : Matrix (Fin 8) (Fin 8) B) ^ 13 := by
  obtain ⟨i5, i7, i13, -⟩ := mellin_involutions
  obtain ⟨t5, t7, -, t13⟩ := mellin_intertwining
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [opMellin5, opMellin7, opMellin13, opClock, ← map_mul, ← map_pow, i5, i7, i13, t5,
      t7, t13, map_one]

/-- Noncommutativity witness on the operator carrier (any characteristic-zero ring). -/
theorem opMellin5_clock_ne {C : Type*} [Ring C] [CharZero C] :
    (opMellin5 : Matrix (Fin 8) (Fin 8) C) * opClock ≠ opClock * opMellin5 := by
  intro h
  apply mellin5_clock_ne
  unfold clock24
  have hinj : Function.Injective ((Int.castRingHom C).mapMatrix :
      Matrix (Fin 8) (Fin 8) ℤ → Matrix (Fin 8) (Fin 8) C) :=
    Matrix.map_injective Int.cast_injective
  apply hinj
  simpa only [opMellin5, opClock, map_mul] using h

end Operator

/-! ### Cuntz families in an arbitrary ring -/

section Cuntz

variable {A : Type*} [Ring A] {N : ℕ}

/-- **Trace obstruction.**  For a Cuntz family (`S_i* S_i = 1`, `Σ S_i S_i* = 1`) and an
additive cyclic functional `τ`, `N • τ 1 = τ 1`. -/
theorem cuntz_trace_obstruction {G : Type*} [AddCommGroup G] (τ : A →+ G)
    (hcyc : ∀ x y : A, τ (x * y) = τ (y * x)) (S Sstar : Fin N → A)
    (hiso : ∀ i, Sstar i * S i = 1) (hsum : ∑ i, S i * Sstar i = 1) :
    N • τ 1 = τ 1 := by
  calc N • τ 1 = ∑ _i : Fin N, τ 1 := by simp
    _ = ∑ i, τ (Sstar i * S i) := by simp [hiso]
    _ = ∑ i, τ (S i * Sstar i) := by simp [hcyc]
    _ = τ (∑ i, S i * Sstar i) := (map_sum τ _ _).symm
    _ = τ 1 := by rw [hsum]

/-- With two members, `τ 1 = 0`. -/
theorem cuntz2_trace_zero {G : Type*} [AddCommGroup G] (τ : A →+ G)
    (hcyc : ∀ x y : A, τ (x * y) = τ (y * x)) (S Sstar : Fin 2 → A)
    (hiso : ∀ i, Sstar i * S i = 1) (hsum : ∑ i, S i * Sstar i = 1) : τ 1 = 0 := by
  have h := cuntz_trace_obstruction τ hcyc S Sstar hiso hsum
  rw [two_nsmul] at h
  simpa using h

/-- **Cuntz endomorphism** `ρ(X) = Σ S_i X S_i*` is unital and multiplicative. -/
theorem cuntz_endomorphism (S Sstar : Fin N → A)
    (horth : ∀ i j, Sstar i * S j = if i = j then 1 else 0) (hsum : ∑ i, S i * Sstar i = 1)
    (X Y : A) :
    (∑ i, S i * 1 * Sstar i) = 1 ∧
      (∑ i, S i * X * Sstar i) * (∑ j, S j * Y * Sstar j) = ∑ i, S i * (X * Y) * Sstar i := by
  refine ⟨by simpa using hsum, ?_⟩
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · calc S i * X * Sstar i * (S i * Y * Sstar i)
        = S i * X * (Sstar i * S i) * Y * Sstar i := by simp only [mul_assoc]
      _ = S i * (X * Y) * Sstar i := by rw [horth]; simp [mul_assoc]
  · intro j _ hji
    calc S i * X * Sstar i * (S j * Y * Sstar j)
        = S i * X * (Sstar i * S j) * Y * Sstar j := by simp only [mul_assoc]
      _ = 0 := by rw [horth]; simp [Ne.symm hji]
  · simp

/-- **Cuntz composition** `𝒪_N → 𝒪_{N·N}`: the words `S_i S_j` again form a Cuntz family. -/
theorem cuntz_compose (S Sstar : Fin N → A)
    (horth : ∀ i j, Sstar i * S j = if i = j then 1 else 0) (hsum : ∑ i, S i * Sstar i = 1) :
    (∀ p q : Fin N × Fin N, (Sstar p.2 * Sstar p.1) * (S q.1 * S q.2) = if p = q then 1 else 0) ∧
      ∑ p : Fin N × Fin N, (S p.1 * S p.2) * (Sstar p.2 * Sstar p.1) = 1 := by
  constructor
  · rintro ⟨i, j⟩ ⟨k, l⟩
    have e : (Sstar j * Sstar i) * (S k * S l) = Sstar j * (Sstar i * S k) * S l := by
      simp only [mul_assoc]
    rw [e, horth]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, mul_one, horth]
      by_cases hjl : j = l
      · subst hjl; simp
      · simp [hjl]
    · simp [hik]
  · rw [Fintype.sum_prod_type]
    calc ∑ i, ∑ j, S i * S j * (Sstar j * Sstar i)
        = ∑ i, S i * (∑ j, S j * Sstar j) * Sstar i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [mul_assoc]
      _ = 1 := by simp only [hsum, mul_one]

/-- Scale intertwining propagates to all clock powers: `M Cᵏ M = C^(u k)`. -/
theorem intertwine_pow {M C : A} {u : ℕ} (hM : M * M = 1) (hMC : M * C * M = C ^ u) (k : ℕ) :
    M * C ^ k * M = C ^ (u * k) := by
  induction k with
  | zero => simp [hM]
  | succ k ih =>
    calc M * C ^ (k + 1) * M = (M * C ^ k * M) * (M * C * M) := by
          rw [pow_succ]
          calc M * (C ^ k * C) * M = M * C ^ k * 1 * C * M := by simp only [mul_assoc, one_mul]
            _ = M * C ^ k * (M * M) * C * M := by rw [hM]
            _ = (M * C ^ k * M) * (M * C * M) := by simp only [mul_assoc]
      _ = C ^ (u * (k + 1)) := by rw [ih, hMC, ← pow_add, mul_add, mul_one]

end Cuntz

/-! ### Dyadic scale hopping in `AddMonoid.End (ℤ → M)` -/

section Dyadic

variable (M : Type*) [AddCommGroup M]

/-- Interpolation into even slots: `(S₀ f)(n) = f(n/2)` for even `n`, else `0`. -/
def hopS0 : AddMonoid.End (ℤ → M) where
  toFun f n := if 2 ∣ n then f (n / 2) else 0
  map_zero' := by funext n; simp
  map_add' f g := by funext n; by_cases h : 2 ∣ n <;> simp [h]

/-- Interpolation into odd slots: `(S₁ f)(n) = f((n-1)/2)` for odd `n`, else `0`. -/
def hopS1 : AddMonoid.End (ℤ → M) where
  toFun f n := if 2 ∣ n then 0 else f ((n - 1) / 2)
  map_zero' := by funext n; simp
  map_add' f g := by funext n; by_cases h : 2 ∣ n <;> simp [h]

/-- Even decimation `(S₀* f)(k) = f(2k)`. -/
def hopS0star : AddMonoid.End (ℤ → M) where
  toFun f k := f (2 * k)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Odd decimation `(S₁* f)(k) = f(2k+1)`. -/
def hopS1star : AddMonoid.End (ℤ → M) where
  toFun f k := f (2 * k + 1)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The dyadic Cuntz `𝒪₂` relations in the noncommutative ring `AddMonoid.End (ℤ → M)`. -/
theorem dyadic_cuntz_relations :
    hopS0star M * hopS0 M = 1 ∧ hopS1star M * hopS1 M = 1 ∧
      hopS0star M * hopS1 M = 0 ∧ hopS1star M * hopS0 M = 0 ∧
      hopS0 M * hopS0star M + hopS1 M * hopS1star M = 1 := by
  have odd : ∀ n : ℤ, ¬ (2 ∣ 2 * n + 1) := fun n h => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext f n
  · change (if 2 ∣ 2 * n then f (2 * n / 2) else 0) = f n
    simp
  · change (if 2 ∣ 2 * n + 1 then 0 else f ((2 * n + 1 - 1) / 2)) = f n
    simp only [odd n, ↓reduceIte]; congr 1; omega
  · change (if 2 ∣ 2 * n then 0 else f ((2 * n - 1) / 2)) = 0
    simp
  · change (if 2 ∣ 2 * n + 1 then f ((2 * n + 1) / 2) else 0) = 0
    simp only [odd n, ↓reduceIte]
  · change (if 2 ∣ n then f (2 * (n / 2)) else 0) +
        (if 2 ∣ n then 0 else f (2 * ((n - 1) / 2) + 1)) = f n
    by_cases h : 2 ∣ n
    · simp only [h, ↓reduceIte, add_zero]; congr 1; omega
    · simp only [h, ↓reduceIte, zero_add]; congr 1; omega

/-- The signal endomorphism ring carries no cyclic additive functional `τ` with `τ 1 ≠ 0`
into a torsion-free group: dyadic scale hopping is genuinely infinite. -/
theorem dyadic_no_cyclic_trace {G : Type*} [AddCommGroup G] (τ : AddMonoid.End (ℤ → M) →+ G)
    (hcyc : ∀ x y, τ (x * y) = τ (y * x)) : τ 1 = 0 := by
  obtain ⟨h00, h11, -, -, hsum⟩ := dyadic_cuntz_relations M
  refine cuntz2_trace_zero τ hcyc ![hopS0 M, hopS1 M] ![hopS0star M, hopS1star M] ?_ ?_
  · intro i; fin_cases i <;> simpa
  · simpa [Fin.sum_univ_two] using hsum

end Dyadic

end InfoGeometry.OperatorAlgebra.CyclotomicMellinCuntzScale
