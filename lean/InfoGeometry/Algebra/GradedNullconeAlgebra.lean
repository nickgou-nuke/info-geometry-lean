/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# $\mathbb{Z}/2$-Graded Differential Operator Algebra Over Dual Isotropic Nullcones

This module formalizes the five irreducible algebraic axioms of the $\mathbb{Z}/2$-graded
differential operator algebra `(V = N₊ ⊕ N₋, Γ, J, D)` over dual isotropic nullcones:

1. **Axiom 1 (`axiom1_dual_isotropic_nullcones`)**: Complementary isotropic nullspaces
   `nullPlus` and `nullMinus` with trivial self-pairings `η(N₊, N₊) = 0`, `η(N₋, N₋) = 0`,
   direct-sum decomposition, and cross-pairing heredity of symmetry and nondegeneracy.
2. **Axiom 2 (`axiom2_cut_vs_mirror_law`)**: Distinct involutions `cutOp` (`Γ`) and
   `mirrorOp` (`J`), `{Γ, J} = 0`, ghost collapse `η(x, Γ x) = 0`, intertwined positive
   norm `η(x, J x)`, and Krein `(n, n)` split signature on the diagonal/skew sectors.
3. **Axiom 3 (`axiom3_peirce_zorn_operator_algebra`)**: Noncommutative `2 × 2` Peirce–Zorn
   block operators `[T, Y; X, G]` over an arbitrary ring `E`, grading anticommutation
   `{Γ, F} = 0`, symmetric mass `{X_op, Y_op} = F^2`, chiral commutator
   `[Y_op, X_op] = Γ * F^2`, idempotent Socratic defect, and unilateral nilpotent limit.
4. **Axiom 4 (`axiom4_derivation_and_soldering_laws`)**: Constructive `RingDeriv`
   derivations (`Inhabited` via `innerRingDeriv`), unit/inverse identities, logarithmic
   soldering `logSoldering D g = g⁻¹ * D g`, the noncommutative Cartan cocycle and
   Maurer–Cartan curvature identity `D₁ θ₂ - D₂ θ₁ + [θ₁, θ₂] = g⁻¹ ([D₁, D₂] g)`, and
   gauge/soldering Peirce splitting.
5. **Axiom 5 (`axiom5_parity_soldered_clifford_tower`)**: The `Cl(1,1) ≅ M₂(ℝ)` atom
   (`gammaCut2`, `gammaMir2`, `gammaSkew2`) and the Jordan–Wigner / Koszul Kronecker tower
   `M_{2^k}(ℝ)` of dimension `4^k` with faithful split CAR and `(k, k)` Clifford relations.
-/

namespace InfoGeometry.Algebra.GradedNullconeAlgebra

open scoped Kronecker Matrix

/-! ## Axiom 1 & Axiom 2: Dual Isotropic Nullcones, Cut `Γ`, and Mirror `J` -/

/-- Canonical carrier for the dual nullcone direct sum `N₊ ⊕ N₋`. -/
abbrev NullconeCarrier (H : Type*) := H × H

section NullconeSpace

variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]

/-- Injection into the `+` isotropic nullcone `N₊`. -/
def nullPlus (u : H) : NullconeCarrier H := (u, 0)

/-- Injection into the `-` isotropic nullcone `N₋`. -/
def nullMinus (v : H) : NullconeCarrier H := (0, v)

@[simp]
theorem nullPlus_apply (u : H) : nullPlus u = (u, (0 : H)) := rfl

@[simp]
theorem nullMinus_apply (v : H) : nullMinus v = ((0 : H), v) := rfl

/-- The indefinite Krein cross-pairing on `N₊ ⊕ N₋` induced by `b : H →ₗ[R] H →ₗ[R] R`. -/
def nullKreinPairing (b : H →ₗ[R] H →ₗ[R] R) (x y : NullconeCarrier H) : R :=
  b x.1 y.2 + b x.2 y.1

/-- Perspectival $\mathbb{Z}/2$-grading cut `Γ`: `+1` on `N₊` and `-1` on `N₋`. -/
def cutOp : NullconeCarrier H →ₗ[R] NullconeCarrier H where
  toFun x := (x.1, -x.2)
  map_add' x y := by
    ext
    · rfl
    · simp only [Prod.snd_add]; abel
  map_smul' r x := by simp [smul_neg]

/-- Mirror reciprocity involution `J : N₊ ↔ N₋`. -/
def mirrorOp : NullconeCarrier H →ₗ[R] NullconeCarrier H where
  toFun x := (x.2, x.1)
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp]
theorem cutOp_apply (x : NullconeCarrier H) :
    (cutOp : NullconeCarrier H →ₗ[R] NullconeCarrier H) x = (x.1, -x.2) := rfl

@[simp]
theorem mirrorOp_apply (x : NullconeCarrier H) :
    (mirrorOp : NullconeCarrier H →ₗ[R] NullconeCarrier H) x = (x.2, x.1) := rfl

/-- Axiom 1: Both half-spaces `N₊` and `N₋` are identically isotropic under `nullKreinPairing`,
every carrier splits uniquely as `nullPlus x.1 + nullMinus x.2`, and nondegeneracy/symmetry of
the cross-pairing pass to `N₊ ⊕ N₋`. -/
theorem axiom1_dual_isotropic_nullcones (b : H →ₗ[R] H →ₗ[R] R) :
    (∀ u₁ u₂ : H, nullKreinPairing b (nullPlus u₁) (nullPlus u₂) = 0) ∧
    (∀ v₁ v₂ : H, nullKreinPairing b (nullMinus v₁) (nullMinus v₂) = 0) ∧
    (∀ u v : H, nullKreinPairing b (nullPlus u) (nullMinus v) = b u v) ∧
    (∀ x : NullconeCarrier H, nullPlus x.1 + nullMinus x.2 = x) ∧
    ((∀ u v : H, b u v = b v u) →
      ∀ x y : NullconeCarrier H, nullKreinPairing b x y = nullKreinPairing b y x) ∧
    ((∀ u : H, (∀ v : H, b u v = 0) → u = 0) →
      ∀ x : NullconeCarrier H, (∀ y : NullconeCarrier H, nullKreinPairing b x y = 0) →
        x = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u₁ u₂
    simp [nullKreinPairing]
  · intro v₁ v₂
    simp [nullKreinPairing]
  · intro u v
    simp [nullKreinPairing]
  · intro x
    ext <;> simp
  · intro hsym x y
    simp only [nullKreinPairing]
    rw [hsym x.1 y.2, hsym x.2 y.1, add_comm]
  · intro hnd x hx
    have hx1 : x.1 = 0 := hnd x.1 fun v => by
      have h := hx (nullMinus v)
      simpa [nullKreinPairing] using h
    have hx2 : x.2 = 0 := hnd x.2 fun u => by
      have h := hx (nullPlus u)
      simpa [nullKreinPairing] using h
    ext <;> simp [hx1, hx2]

/-- Axiom 2: `cutOp` (`Γ`) and `mirrorOp` (`J`) are anticommuting involutions (`{Γ, J} = 0`),
never equal when `H` is nontrivial, preserving/reversing `η` respectively, while confusing
`J` with `Γ` inside `η` causes ghost collapse `η(x, Γ x) = 0` and preserving `J` produces
the intertwined symmetric metric `b x.1 x.1 + b x.2 x.2` alongside `(n, n)` split signature. -/
theorem axiom2_cut_vs_mirror_law (b : H →ₗ[R] H →ₗ[R] R)
    (hsym : ∀ u v : H, b u v = b v u) :
    ((cutOp : NullconeCarrier H →ₗ[R] NullconeCarrier H).comp cutOp = LinearMap.id) ∧
    ((mirrorOp : NullconeCarrier H →ₗ[R] NullconeCarrier H).comp mirrorOp = LinearMap.id) ∧
    ((cutOp : NullconeCarrier H →ₗ[R] NullconeCarrier H).comp mirrorOp +
      (mirrorOp : NullconeCarrier H →ₗ[R] NullconeCarrier H).comp cutOp = 0) ∧
    (∀ u : H, u ≠ 0 →
      (cutOp : NullconeCarrier H →ₗ[R] NullconeCarrier H) (nullPlus u) ≠
        (mirrorOp : NullconeCarrier H →ₗ[R] NullconeCarrier H) (nullPlus u)) ∧
    (∀ x : NullconeCarrier H, nullKreinPairing b x (cutOp (R := R) x) = 0) ∧
    (∀ x : NullconeCarrier H, nullKreinPairing b x (mirrorOp (R := R) x) = b x.1 x.1 + b x.2 x.2) ∧
    (∀ x y : NullconeCarrier H,
      nullKreinPairing b (mirrorOp (R := R) x) (mirrorOp (R := R) y) = nullKreinPairing b x y) ∧
    (∀ x y : NullconeCarrier H,
      nullKreinPairing b (cutOp (R := R) x) (cutOp (R := R) y) = - nullKreinPairing b x y) ∧
    (∀ u : H,
      nullKreinPairing b (u, u) (u, u) = (2 : R) * b u u ∧
      nullKreinPairing b (u, -u) (u, -u) = - ((2 : R) * b u u)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x <;> simp
  · ext x <;> simp
  · ext x <;> simp
  · intro u hu hEq
    have hfst : u = 0 := congrArg Prod.fst hEq
    exact hu hfst
  · intro x
    simp only [nullKreinPairing, cutOp_apply, map_neg]
    rw [hsym x.2 x.1]
    ring
  · intro x
    simp [nullKreinPairing]
  · intro x y
    simp only [nullKreinPairing, mirrorOp_apply]
    ring
  · intro x y
    simp only [nullKreinPairing, cutOp_apply, map_neg, LinearMap.neg_apply]
    ring
  · intro u
    constructor
    · simp only [nullKreinPairing]
      ring
    · simp only [nullKreinPairing, map_neg, LinearMap.neg_apply]
      ring

end NullconeSpace

/-! ## Axiom 3: The `2 × 2` Peirce–Zorn Operator Matrix -/

section PeirceZornBlock

variable {E : Type*} [Ring E]

/-- `2 × 2` grading matrix `diag(1, -1)` over an arbitrary ring `E`. -/
def peirceGamma : Matrix (Fin 2) (Fin 2) E := !![1, 0; 0, -1]

/-- Pure lower-left bridge `N₊ → N₋` in `M₂(E)`. -/
def peirceX (X : E) : Matrix (Fin 2) (Fin 2) E := !![0, 0; X, 0]

/-- Pure upper-right bridge `N₋ → N₊` in `M₂(E)`. -/
def peirceY (Y : E) : Matrix (Fin 2) (Fin 2) E := !![0, Y; 0, 0]

/-- General Peirce–Zorn `2 × 2` block operator `[T, Y; X, G]` over `E`. -/
def peirceOperator (T X Y G : E) : Matrix (Fin 2) (Fin 2) E := !![T, Y; X, G]

/-- Witness of noncommutativity for `Matrix (Fin 2) (Fin 2) E` when `E` is nontrivial. -/
theorem peirce_block_mul_noncommutative [Nontrivial E] :
    ∃ A B : Matrix (Fin 2) (Fin 2) E, A * B ≠ B * A := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], ?_⟩
  intro hEq
  have h01 := congrFun (congrFun hEq 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Axiom 3: Over any ring `E`, the `2 × 2` Peirce–Zorn operator algebra has nilpotent
bridges `X_op^2 = Y_op^2 = 0`, odd grading `{Γ, F} = 0` for `F = X_op + Y_op`, symmetric
mass `{X_op, Y_op} = F^2`, chiral commutator `[Y_op, X_op] = Γ * F^2`, idempotent
Socratic defect `diag(T - T^2, G - G^2) = F^2`, and unilateral Jordan block `F ≠ 0, F^2 = 0`. -/
theorem axiom3_peirce_zorn_operator_algebra (T X Y G : E) :
    let Γ : Matrix (Fin 2) (Fin 2) E := peirceGamma
    let Xop : Matrix (Fin 2) (Fin 2) E := peirceX X
    let Yop : Matrix (Fin 2) (Fin 2) E := peirceY Y
    let F : Matrix (Fin 2) (Fin 2) E := Xop + Yop
    let Ω : Matrix (Fin 2) (Fin 2) E := peirceOperator T X Y G
    (Γ * Γ = 1) ∧
    (Xop * Xop = 0) ∧
    (Yop * Yop = 0) ∧
    (Γ * F + F * Γ = 0) ∧
    (Xop * Yop + Yop * Xop = F * F) ∧
    (Yop * Xop - Xop * Yop = Γ * (F * F)) ∧
    (Ω * Ω = Ω → !![T - T * T, 0; 0, G - G * G] = F * F) ∧
    (Y ≠ 0 → peirceX (0 : E) + peirceY Y ≠ 0 ∧
      (peirceX (0 : E) + peirceY Y) * (peirceX (0 : E) + peirceY Y) = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [peirceGamma, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [peirceX, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [peirceY, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [peirceGamma, peirceX, peirceY]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceX, peirceY, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceGamma, peirceX, peirceY, Matrix.mul_apply, Fin.sum_univ_two]
  · intro hidem
    have h00 := congrFun (congrFun hidem 0) 0
    have h11 := congrFun (congrFun hidem 1) 1
    simp only [peirceOperator, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
    have hT : T - T * T = Y * X := by
      calc
        T - T * T = (T * T + Y * X) - T * T := by rw [h00]
        _ = Y * X := by noncomm_ring
    have hG : G - G * G = X * Y := by
      calc
        G - G * G = (X * Y + G * G) - G * G := by rw [h11]
        _ = X * Y := by noncomm_ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceX, peirceY, Matrix.mul_apply, Fin.sum_univ_two, hT, hG]
  · intro hY
    constructor
    · intro hZero
      have h01 := congrFun (congrFun hZero 0) 1
      simp [peirceX, peirceY] at h01
      exact hY h01
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [peirceX, peirceY, Matrix.mul_apply, Fin.sum_univ_two]

end PeirceZornBlock

/-! ## Axiom 4: Leibniz Derivation and Soldering Connection `θ = g⁻¹ D g` -/

/-- Additive Leibniz derivation `D(x * y) = x * D y + D x * y` on an associative ring `E`. -/
structure RingDeriv (E : Type*) [Ring E] where
  /-- Underlying map of the derivation. -/
  toFun : E → E
  /-- Additivity law. -/
  map_add' : ∀ x y : E, toFun (x + y) = toFun x + toFun y
  /-- Leibniz product rule. -/
  map_mul' : ∀ x y : E, toFun (x * y) = x * toFun y + toFun x * y

instance {E : Type*} [Ring E] : CoeFun (RingDeriv E) (fun _ => E → E) where
  coe := RingDeriv.toFun

/-- Inner commutator derivation `ad_A(x) = A * x - x * A`. -/
def innerRingDeriv {E : Type*} [Ring E] (A : E) : RingDeriv E where
  toFun x := A * x - x * A
  map_add' x y := by noncomm_ring
  map_mul' x y := by noncomm_ring

instance {E : Type*} [Ring E] : Inhabited (RingDeriv E) :=
  ⟨innerRingDeriv 0⟩

namespace RingDeriv

variable {E : Type*} [Ring E]

theorem map_add (D : RingDeriv E) (x y : E) : D (x + y) = D x + D y :=
  D.map_add' x y

theorem map_mul (D : RingDeriv E) (x y : E) : D (x * y) = x * D y + D x * y :=
  D.map_mul' x y

theorem map_one (D : RingDeriv E) : D 1 = 0 := by
  have h : D 1 = D (1 * 1) := by rw [one_mul]
  rw [D.map_mul 1 1, one_mul, mul_one] at h
  calc
    D 1 = (D 1 + D 1) - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self _

theorem map_inv (D : RingDeriv E) (g : Eˣ) :
    D ((g⁻¹ : Eˣ) : E) = - (((g⁻¹ : Eˣ) : E) * D g * ((g⁻¹ : Eˣ) : E)) := by
  have h : D ((g : E) * ((g⁻¹ : Eˣ) : E)) = 0 := by
    rw [Units.mul_inv, D.map_one]
  rw [D.map_mul] at h
  have hmul := congrArg (fun z => ((g⁻¹ : Eˣ) : E) * z) h
  rw [mul_zero, mul_add, ← mul_assoc, Units.inv_mul, one_mul] at hmul
  exact eq_neg_of_add_eq_zero_left (by simpa [mul_assoc] using hmul)

end RingDeriv

/-- Logarithmic Maurer–Cartan soldering form `θ_L(g) = g⁻¹ * D g`. -/
def logSoldering {E : Type*} [Ring E] (D : RingDeriv E) (g : Eˣ) : E :=
  ((g⁻¹ : Eˣ) : E) * D g

/-- Axiom 4: Unit normalization, noncommutative Cartan cocycle law, centralizer additive
reduction, inverse formula, Maurer–Cartan curvature from `[D₁, D₂]`, inner gauge transport,
and diagonal/off-diagonal Peirce decomposition for block soldering forms. -/
theorem axiom4_derivation_and_soldering_laws {E : Type*} [Ring E]
    (D D₁ D₂ : RingDeriv E) (g h : Eˣ) (A : E) :
    (logSoldering D 1 = 0) ∧
    (logSoldering D (g * h) =
      ((h⁻¹ : Eˣ) : E) * logSoldering D g * (h : E) + logSoldering D h) ∧
    (((h : E) * logSoldering D g = logSoldering D g * (h : E)) →
      logSoldering D (g * h) = logSoldering D g + logSoldering D h) ∧
    (logSoldering D g⁻¹ = - ((g : E) * logSoldering D g * ((g⁻¹ : Eˣ) : E))) ∧
    (D₁ (logSoldering D₂ g) - D₂ (logSoldering D₁ g) +
        (logSoldering D₁ g * logSoldering D₂ g - logSoldering D₂ g * logSoldering D₁ g) =
      ((g⁻¹ : Eˣ) : E) * (D₁ (D₂ g) - D₂ (D₁ g))) ∧
    (logSoldering (innerRingDeriv A) g = ((g⁻¹ : Eˣ) : E) * A * (g : E) - A) ∧
    (∀ θ : Matrix (Fin 2) (Fin 2) E,
      let P : Matrix (Fin 2) (Fin 2) E := !![1, 0; 0, 0]
      let Q : Matrix (Fin 2) (Fin 2) E := !![0, 0; 0, 1]
      let Γ : Matrix (Fin 2) (Fin 2) E := peirceGamma
      let θDiag := P * θ * P + Q * θ * Q
      let θOff := P * θ * Q + Q * θ * P
      θ = θDiag + θOff ∧ Γ * θDiag = θDiag * Γ ∧ Γ * θOff + θOff * Γ = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [logSoldering, RingDeriv.map_one]
  · simp only [logSoldering, Units.val_mul, mul_inv_rev, RingDeriv.map_mul]
    rw [mul_add, mul_assoc ((h⁻¹ : Eˣ) : E) ((g⁻¹ : Eˣ) : E),
      ← mul_assoc ((g⁻¹ : Eˣ) : E) (g : E), Units.inv_mul, one_mul]
    simp [mul_assoc, add_comm]
  · intro hcomm
    calc
      logSoldering D (g * h)
          = ((h⁻¹ : Eˣ) : E) * logSoldering D g * (h : E) + logSoldering D h := by
              simp only [logSoldering, Units.val_mul, mul_inv_rev, RingDeriv.map_mul]
              rw [mul_add, mul_assoc ((h⁻¹ : Eˣ) : E) ((g⁻¹ : Eˣ) : E),
                ← mul_assoc ((g⁻¹ : Eˣ) : E) (g : E), Units.inv_mul, one_mul]
              simp [mul_assoc, add_comm]
      _ = ((h⁻¹ : Eˣ) : E) * ((h : E) * logSoldering D g) + logSoldering D h := by
            rw [mul_assoc, hcomm]
      _ = logSoldering D g + logSoldering D h := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
  · simp only [logSoldering, inv_inv]
    rw [RingDeriv.map_inv]
    noncomm_ring
  · have h12 : D₁ (logSoldering D₂ g) =
        - (logSoldering D₁ g * logSoldering D₂ g) + ((g⁻¹ : Eˣ) : E) * D₁ (D₂ g) := by
      simp only [logSoldering]
      rw [D₁.map_mul, D₁.map_inv]
      noncomm_ring
    have h21 : D₂ (logSoldering D₁ g) =
        - (logSoldering D₂ g * logSoldering D₁ g) + ((g⁻¹ : Eˣ) : E) * D₂ (D₁ g) := by
      simp only [logSoldering]
      rw [D₂.map_mul, D₂.map_inv]
      noncomm_ring
    rw [h12, h21]
    noncomm_ring
  · simp only [logSoldering, innerRingDeriv]
    rw [mul_sub, ← mul_assoc, ← mul_assoc ((g⁻¹ : Eˣ) : E) (g : E) A, Units.inv_mul, one_mul,
      mul_assoc]
  · intro θ
    dsimp only
    have hmul (A B : Matrix (Fin 2) (Fin 2) E) (i j : Fin 2) :
        (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    have htwo : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      rcases htwo i with rfl | rfl <;> rcases htwo j with rfl | rfl <;>
        simp only [Matrix.add_apply, hmul, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;>
        noncomm_ring
    · ext i j
      rcases htwo i with rfl | rfl <;> rcases htwo j with rfl | rfl <;>
        simp only [peirceGamma, Matrix.add_apply, hmul, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;>
        noncomm_ring
    · ext i j
      rcases htwo i with rfl | rfl <;> rcases htwo j with rfl | rfl <;>
        simp only [peirceGamma, Matrix.zero_apply, Matrix.add_apply, hmul, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        noncomm_ring

/-! ## Axiom 5: The `Cl(1,1) ≅ M₂(ℝ)` Atom and Jordan–Wigner Kronecker Tower -/

/-- `2 × 2` grading matrix `Γ = diag(1, -1)` over `ℝ`. -/
def gammaCut2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- `2 × 2` mirror matrix `J = [[0, 1], [1, 0]]` over `ℝ`. -/
def gammaMir2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- `2 × 2` chiral product `Γ * J = [[0, 1], [-1, 0]]` over `ℝ`. -/
def gammaSkew2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Explicit noncommutativity of `gammaCut2` and `gammaMir2` in `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem gammaCut2_mul_gammaMir2_ne :
    gammaCut2 * gammaMir2 ≠ gammaMir2 * gammaCut2 := by
  intro hEq
  have h01 := congrFun (congrFun hEq 0) 1
  simp [gammaCut2, gammaMir2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  linarith

/-- Explicit Trap T16 noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem mat2R_mul_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨gammaCut2, gammaMir2, gammaCut2_mul_gammaMir2_ne⟩

/-- Complete structural laws of the `k = 1` atom `Cl(1,1) ≅ M₂(ℝ)`. -/
theorem cl11_atom_laws :
    (gammaCut2 * gammaCut2 = 1) ∧
    (gammaMir2 * gammaMir2 = 1) ∧
    (gammaCut2 * gammaMir2 + gammaMir2 * gammaCut2 = 0) ∧
    (gammaCut2 * gammaMir2 = gammaSkew2) ∧
    (gammaSkew2 * gammaSkew2 = -1) ∧
    (gammaCut2.trace = 0 ∧ gammaMir2.trace = 0 ∧ gammaSkew2.trace = 0) ∧
    (∀ M : Matrix (Fin 2) (Fin 2) ℝ,
      let a := (M 0 0 + M 1 1) / 2
      let b := (M 0 0 - M 1 1) / 2
      let c := (M 0 1 + M 1 0) / 2
      let d := (M 0 1 - M 1 0) / 2
      M = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) + b • gammaCut2 +
        c • gammaMir2 + d • gammaSkew2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gammaCut2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gammaMir2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gammaCut2, gammaMir2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gammaCut2, gammaMir2, gammaSkew2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gammaSkew2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [gammaCut2, Matrix.trace, Fin.sum_univ_two]
  · simp [gammaMir2, Matrix.trace, Fin.sum_univ_two]
  · simp [gammaSkew2, Matrix.trace, Fin.sum_univ_two]
  · intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gammaCut2, gammaMir2, gammaSkew2] <;> ring

/-- Recursive index set of cardinality `2^k` for the `k`-fold parity-soldered tower. -/
@[reducible] def TowerIdx : ℕ → Type
  | 0 => Unit
  | k + 1 => TowerIdx k × Fin 2

instance instFintypeTowerIdx : ∀ k, Fintype (TowerIdx k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeProd (TowerIdx k) (Fin 2) (instFintypeTowerIdx k) inferInstance

instance instDecidableEqTowerIdx : ∀ k, DecidableEq (TowerIdx k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => @instDecidableEqProd (TowerIdx k) (Fin 2) (instDecidableEqTowerIdx k) inferInstance

instance instInhabitedTowerIdx : ∀ k, Inhabited (TowerIdx k)
  | 0 => ⟨()⟩
  | k + 1 => ⟨(@default (TowerIdx k) (instInhabitedTowerIdx k), 0)⟩

@[simp]
theorem card_towerIdx (k : ℕ) : Fintype.card (TowerIdx k) = 2 ^ k := by
  induction k with
  | zero =>
    change Fintype.card Unit = 1
    exact Fintype.card_unit
  | succ k ih =>
    change Fintype.card (TowerIdx k × Fin 2) = 2 ^ (k + 1)
    rw [Fintype.card_prod, ih, Fintype.card_fin, pow_succ]

theorem finrank_clTower (k : ℕ) :
    Module.finrank ℝ (Matrix (TowerIdx k) (TowerIdx k) ℝ) = 4 ^ k := by
  rw [Module.finrank_matrix, card_towerIdx, Module.finrank_self, mul_one,
    show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]

/-- Lower-left raising atom `a_+ = [[0, 0], [1, 0]]` in `M₂(ℝ)`. -/
private def atomPos2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- Upper-right lowering atom `a_- = [[0, 1], [0, 0]]` in `M₂(ℝ)`. -/
private def atomNeg2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

private theorem atom_car_relations :
    (atomPos2 * atomPos2 = 0) ∧
    (atomNeg2 * atomNeg2 = 0) ∧
    (atomPos2 * atomNeg2 + atomNeg2 * atomPos2 = 1) ∧
    (atomPos2 * gammaCut2 + gammaCut2 * atomPos2 = 0) ∧
    (atomNeg2 * gammaCut2 + gammaCut2 * atomNeg2 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [atomPos2, atomNeg2, gammaCut2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem kronecker_one_one {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    ((1 : Matrix m m ℝ) ⊗ₖ (1 : Matrix n n ℝ)) = (1 : Matrix (m × n) (m × n) ℝ) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h1, h2]

/-- Total $\mathbb{Z}/2$-grading operator `Γ^(k)` on `M_{2^k}(ℝ)`. -/
def towerGamma : ∀ k : ℕ, Matrix (TowerIdx k) (TowerIdx k) ℝ
  | 0 => 1
  | k + 1 => towerGamma k ⊗ₖ gammaCut2

/-- Jordan–Wigner parity-soldered creation/raising operators `e_i^+` on `M_{2^k}(ℝ)`. -/
def jwPos : ∀ (k : ℕ), Fin k → Matrix (TowerIdx k) (TowerIdx k) ℝ
  | 0 => Fin.elim0
  | k + 1 => Fin.lastCases (towerGamma k ⊗ₖ atomPos2) (fun i => jwPos k i ⊗ₖ 1)

/-- Jordan–Wigner parity-soldered annihilation/lowering operators `e_i^-` on `M_{2^k}(ℝ)`. -/
def jwNeg : ∀ (k : ℕ), Fin k → Matrix (TowerIdx k) (TowerIdx k) ℝ
  | 0 => Fin.elim0
  | k + 1 => Fin.lastCases (towerGamma k ⊗ₖ atomNeg2) (fun i => jwNeg k i ⊗ₖ 1)

private theorem towerGamma_succ (k : ℕ) :
    towerGamma (k + 1) = towerGamma k ⊗ₖ gammaCut2 := rfl

private theorem jwPos_last (k : ℕ) :
    jwPos (k + 1) (Fin.last k) = towerGamma k ⊗ₖ atomPos2 := by
  simp only [jwPos, Fin.lastCases_last]

private theorem jwPos_castSucc (k : ℕ) (i : Fin k) :
    jwPos (k + 1) i.castSucc = jwPos k i ⊗ₖ 1 := by
  simp only [jwPos, Fin.lastCases_castSucc]

private theorem jwNeg_last (k : ℕ) :
    jwNeg (k + 1) (Fin.last k) = towerGamma k ⊗ₖ atomNeg2 := by
  simp only [jwNeg, Fin.lastCases_last]

private theorem jwNeg_castSucc (k : ℕ) (i : Fin k) :
    jwNeg (k + 1) i.castSucc = jwNeg k i ⊗ₖ 1 := by
  simp only [jwNeg, Fin.lastCases_castSucc]

private theorem towerGamma_sq (k : ℕ) : towerGamma k * towerGamma k = 1 := by
  induction k with
  | zero => simp [towerGamma]
  | succ k ih =>
    rw [towerGamma_succ, ← Matrix.mul_kronecker_mul, ih, cl11_atom_laws.1, kronecker_one_one]

private theorem jwPos_anticomm_gamma (k : ℕ) (i : Fin k) :
    jwPos k i * towerGamma k + towerGamma k * jwPos k i = 0 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ ?_ i
    · rw [jwPos_last, towerGamma_succ, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, towerGamma_sq, ← Matrix.kronecker_add,
        atom_car_relations.2.2.2.1, Matrix.kronecker_zero]
    · intro j
      rw [jwPos_castSucc, towerGamma_succ, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, one_mul, mul_one, ← Matrix.add_kronecker, ih j,
        Matrix.zero_kronecker]

private theorem jwNeg_anticomm_gamma (k : ℕ) (i : Fin k) :
    jwNeg k i * towerGamma k + towerGamma k * jwNeg k i = 0 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ ?_ i
    · rw [jwNeg_last, towerGamma_succ, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, towerGamma_sq, ← Matrix.kronecker_add,
        atom_car_relations.2.2.2.2, Matrix.kronecker_zero]
    · intro j
      rw [jwNeg_castSucc, towerGamma_succ, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, one_mul, mul_one, ← Matrix.add_kronecker, ih j,
        Matrix.zero_kronecker]

private theorem jwPos_anticomm (k : ℕ) (i j : Fin k) :
    jwPos k i * jwPos k j + jwPos k j * jwPos k i = 0 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        rw [jwPos_last, ← Matrix.mul_kronecker_mul, towerGamma_sq, atom_car_relations.1,
          Matrix.kronecker_zero, add_zero]
      | cast j' =>
        rw [jwPos_last, jwPos_castSucc, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, mul_one, one_mul, ← Matrix.add_kronecker]
        exact (congrArg (fun M : Matrix (TowerIdx k) (TowerIdx k) ℝ => M ⊗ₖ atomPos2)
          (by rw [add_comm]; exact jwPos_anticomm_gamma k j')).trans (Matrix.zero_kronecker _)
    | cast i' =>
      induction j using Fin.lastCases with
      | last =>
        rw [jwPos_castSucc, jwPos_last, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, one_mul, mul_one, ← Matrix.add_kronecker,
          jwPos_anticomm_gamma k i', Matrix.zero_kronecker]
      | cast j' =>
        rw [jwPos_castSucc, jwPos_castSucc, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, one_mul, ← Matrix.add_kronecker, ih i' j',
          Matrix.zero_kronecker]

private theorem jwNeg_anticomm (k : ℕ) (i j : Fin k) :
    jwNeg k i * jwNeg k j + jwNeg k j * jwNeg k i = 0 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        rw [jwNeg_last, ← Matrix.mul_kronecker_mul, towerGamma_sq, atom_car_relations.2.1,
          Matrix.kronecker_zero, add_zero]
      | cast j' =>
        rw [jwNeg_last, jwNeg_castSucc, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, mul_one, one_mul, ← Matrix.add_kronecker]
        exact (congrArg (fun M : Matrix (TowerIdx k) (TowerIdx k) ℝ => M ⊗ₖ atomNeg2)
          (by rw [add_comm]; exact jwNeg_anticomm_gamma k j')).trans (Matrix.zero_kronecker _)
    | cast i' =>
      induction j using Fin.lastCases with
      | last =>
        rw [jwNeg_castSucc, jwNeg_last, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, one_mul, mul_one, ← Matrix.add_kronecker,
          jwNeg_anticomm_gamma k i', Matrix.zero_kronecker]
      | cast j' =>
        rw [jwNeg_castSucc, jwNeg_castSucc, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, one_mul, ← Matrix.add_kronecker, ih i' j',
          Matrix.zero_kronecker]

private theorem jwPos_jwNeg_car (k : ℕ) (i j : Fin k) :
    jwPos k i * jwNeg k j + jwNeg k j * jwPos k i = if i = j then 1 else 0 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [ite_true]
        rw [jwPos_last, jwNeg_last, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          towerGamma_sq, ← Matrix.kronecker_add, atom_car_relations.2.2.1, kronecker_one_one]
      | cast j' =>
        have hne : (Fin.last k : Fin (k + 1)) ≠ j'.castSucc := (Fin.castSucc_lt_last j').ne'
        simp only [hne, ite_false]
        rw [jwPos_last, jwNeg_castSucc, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          mul_one, one_mul, ← Matrix.add_kronecker]
        exact (congrArg (fun M : Matrix (TowerIdx k) (TowerIdx k) ℝ => M ⊗ₖ atomPos2)
          (by rw [add_comm]; exact jwNeg_anticomm_gamma k j')).trans (Matrix.zero_kronecker _)
    | cast i' =>
      induction j using Fin.lastCases with
      | last =>
        have hne : i'.castSucc ≠ Fin.last k := (Fin.castSucc_lt_last i').ne
        simp only [hne, ite_false]
        rw [jwPos_castSucc, jwNeg_last, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          one_mul, mul_one, ← Matrix.add_kronecker, jwPos_anticomm_gamma k i',
          Matrix.zero_kronecker]
      | cast j' =>
        simp only [Fin.castSucc_inj]
        rw [jwPos_castSucc, jwNeg_castSucc, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, one_mul, ← Matrix.add_kronecker, ih i' j']
        split_ifs with h
        · exact kronecker_one_one
        · exact Matrix.zero_kronecker _

/-- Explicit Trap T16 noncommutativity witness for `Matrix (TowerIdx k) (TowerIdx k) ℝ`
whenever `1 ≤ k`. -/
theorem towerMatrix_mul_noncommutative (k : ℕ) (hk : 1 ≤ k) :
    ∃ A B : Matrix (TowerIdx k) (TowerIdx k) ℝ, A * B ≠ B * A := by
  let i0 : Fin k := ⟨0, hk⟩
  refine ⟨jwPos k i0, towerGamma k, ?_⟩
  intro hEq
  have hzero := jwPos_anticomm_gamma k i0
  rw [← hEq] at hzero
  have h2 : (2 : ℝ) • (jwPos k i0 * towerGamma k) = 0 := by
    rw [two_smul]
    exact hzero
  have hprod0 : jwPos k i0 * towerGamma k = 0 :=
    (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hpos0 : jwPos k i0 = 0 := by
    calc
      jwPos k i0 = jwPos k i0 * (towerGamma k * towerGamma k) := by rw [towerGamma_sq, mul_one]
      _ = (jwPos k i0 * towerGamma k) * towerGamma k := by rw [mul_assoc]
      _ = 0 := by rw [hprod0, zero_mul]
  have hcar := jwPos_jwNeg_car k i0 i0
  rw [hpos0, zero_mul, mul_zero, add_zero] at hcar
  simp only [ite_true] at hcar
  have h00 := congrFun (congrFun hcar default) default
  simp at h00

/-- Axiom 5: The parity-soldered Kronecker tower `M_{2^k}(ℝ)` has dimension `4^k` and supports
faithful split CAR generators `{e_i^+, e_j^-} = δ_{ij} 1`, `{e_i^±, e_j^±} = 0`,
`{e_i^±, Γ^(k)} = 0`, together with split `(k, k)` Clifford generators
`m_i^+ = e_i^+ + e_i^-` (`(m_i^+)^2 = 1`) and `m_i^- = e_i^+ - e_i^-` (`(m_i^-)^2 = -1`). -/
theorem axiom5_parity_soldered_clifford_tower (k : ℕ) :
    (Module.finrank ℝ (Matrix (TowerIdx k) (TowerIdx k) ℝ) = 4 ^ k) ∧
    (towerGamma k * towerGamma k = 1) ∧
    (∀ i : Fin k, jwPos k i * towerGamma k + towerGamma k * jwPos k i = 0) ∧
    (∀ i : Fin k, jwNeg k i * towerGamma k + towerGamma k * jwNeg k i = 0) ∧
    (∀ i j : Fin k, jwPos k i * jwPos k j + jwPos k j * jwPos k i = 0) ∧
    (∀ i j : Fin k, jwNeg k i * jwNeg k j + jwNeg k j * jwNeg k i = 0) ∧
    (∀ i j : Fin k,
      jwPos k i * jwNeg k j + jwNeg k j * jwPos k i = if i = j then 1 else 0) ∧
    (∀ i : Fin k,
      (jwPos k i + jwNeg k i) * (jwPos k i + jwNeg k i) = 1 ∧
      (jwPos k i - jwNeg k i) * (jwPos k i - jwNeg k i) = -1) := by
  refine ⟨finrank_clTower k, towerGamma_sq k, jwPos_anticomm_gamma k, jwNeg_anticomm_gamma k,
    jwPos_anticomm k, jwNeg_anticomm k, jwPos_jwNeg_car k, ?_⟩
  intro i
  have hpp := jwPos_anticomm k i i
  have hp2 : jwPos k i * jwPos k i = 0 := by
    have h2 : (2 : ℝ) • (jwPos k i * jwPos k i) = 0 := by rwa [two_smul]
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hnn := jwNeg_anticomm k i i
  have hn2 : jwNeg k i * jwNeg k i = 0 := by
    have h2 : (2 : ℝ) • (jwNeg k i * jwNeg k i) = 0 := by rwa [two_smul]
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hpn : jwPos k i * jwNeg k i + jwNeg k i * jwPos k i = 1 := by
    simpa using jwPos_jwNeg_car k i i
  constructor
  · calc
      (jwPos k i + jwNeg k i) * (jwPos k i + jwNeg k i)
          = jwPos k i * jwPos k i + (jwPos k i * jwNeg k i + jwNeg k i * jwPos k i) +
              jwNeg k i * jwNeg k i := by noncomm_ring
      _ = 1 := by rw [hp2, hn2, hpn, zero_add, add_zero]
  · calc
      (jwPos k i - jwNeg k i) * (jwPos k i - jwNeg k i)
          = jwPos k i * jwPos k i - (jwPos k i * jwNeg k i + jwNeg k i * jwPos k i) +
              jwNeg k i * jwNeg k i := by noncomm_ring
      _ = -1 := by rw [hp2, hn2, hpn, zero_sub, add_zero]

end InfoGeometry.Algebra.GradedNullconeAlgebra
