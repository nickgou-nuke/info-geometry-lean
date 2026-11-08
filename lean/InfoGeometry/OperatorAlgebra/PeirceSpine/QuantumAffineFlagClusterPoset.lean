/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.PositroidClusterTwistPoset

/-!
# Stage `D₂₇` (Archetypes `Q₁ → Q₅`): Peirce Power Modes, Ring Factorizations,
# Square-Root Identities & Nested-Idempotent Corners

This module formalizes five families of identities in an associative Peirce operator ring
(`[Ring B]`). Their names are motivated by quantum-affine, representation-theoretic, cluster, and
flag constructions, but this file does **not** construct a quantum-affine algebra representation,
Kirillov–Reshetikhin modules, a dual canonical basis, an analytic four-mass-box letter, or a flag
variety as a geometric space. It proves only the displayed ring identities and idempotent-corner
facts (`Q₁ → Q₅`, Stage `D₂₇`):

1. **Archetype `Q₁` (`drinfeldXPlus`, `drinfeldXMinus`, `drinfeldPhiPlus`, `drinfeldPhiMinus`,
   `drinfeld_new_presentation_loop_relations`, `drinfeld_cartan_grading_conjugation`):**
   Given an idempotent `P` (`P * P = P`), define Peirce power modes
   `X_{+,n} = V^n N_+(A)` and `X_{-,m} = V^m N_-(C)`. The file proves the selected products and
   parity identities below for all `n, m : ℕ`; these are not the full Drinfeld new presentation
   or a representation of a quantum-affine algebra:
   - Cartan grading conjugation: `invS P * X_{±,n} * invS P = -X_{±,n}`,
   - Same-sector nilpotency: `X_{+,n} * X_{+,m} = 0` and `X_{-,n} * X_{-,m} = 0`,
   - Loop products: `X_{+,n} * X_{-,m} = Φ_{+,n+m}` and `X_{-,m} * X_{+,n} = Φ_{-,n+m}`,
   - Loop commutator & anticommutator:
     `[X_{+,n}, X_{-,m}] = Φ_{+,n+m} - Φ_{-,n+m}` and `{X_{+,n}, X_{-,m}} = V^{n+m+1}`.

2. **Archetype `Q₂` (`krModulePlus`, `krModuleMinus`, `krFrozenPlus`, `krFrozenMinus`,
   `kirillov_reshetikhin_t_system_exchange`):**
   The defined ring elements `1 ± Φ(A, C)` and `1 - Q_±(A, C)` satisfy the displayed factorization
   identity. This is a local bilinear identity, not a construction of KR modules or the general
   Kirillov–Reshetikhin `T`-system:
   `T_KR^+ * T_KR^- = Δ_+ * Δ_- = zetaFactor P A C = 1 - V(A, C) = T_KR^- * T_KR^+`.

3. **Archetype `Q₃` & `Q₄` (`dualCanonicalCh`, `dualCanonicalUnion`, `imaginaryModuleDefect`,
   `fourMassBoxDisc`, `fourMassBoxSqrt`, `algSymbolFactorPlus`, `algSymbolFactorMinus`,
   `imaginary_module_and_four_mass_box_letter`, `algSymbolFactor_rationalization_of_comm`):**
   For the explicitly defined ring elements `P + Φ` and `P + Φ + 2 • V`, the square-excess
   expression is `-V`; the defined expression `1 - 4 • B_im` equals `1 + 4 • V`; and the defined
   ring element `invS P + 2 • Φ` squares to it. These names do not assert module-character or
   analytic-letter interpretations. Rationalization is proved only under the explicit commutation
   hypotheses in `algSymbolFactor_rationalization_of_comm`.

4. **Archetype `Q₅` (`flagStratumIdem`, `flagEmbeddedCorner`,
   `partial_flag_to_grassmannian_embedding`):**
   For any nested partial flag of idempotents `P₁ ⊂ P₂` (`P₁² = P₁`, `P₂² = P₂`,
   `P₁ P₂ = P₂ P₁ = P₁`), the relative stratum `E₂ = P₂ - P₁` is an idempotent orthogonal to both
   `P₁` and `1 - P₂` (`P₁ + (P₂ - P₁) + (1 - P₂) = 1`), and the partial flag corner embeds
   into the top Grassmannian corner:
   `flagEmbeddedCorner P₁ P₂ A = conePlus P₁ A * (1 - P₂) = P₁ * A * (1 - P₂) = conePlus P₂ (P₁ * A)`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### 1. Causal Poset of Quantum Affine, Dual Canonical & Flag Cluster Archetypes (`Q₁ → Q₅`) -/

/-- The 5 stages of the non-commutative quantum affine, dual canonical & flag cluster poset
(`Stage D₂₇`). -/
inductive QuantumAffineFlagStage : Type
  | Q1_drinfeld_loop_currents
  | Q2_kirillov_reshetikhin_t_system
  | Q3_imaginary_module_defect
  | Q4_four_mass_box_symbol_letter
  | Q5_partial_flag_grassmannian_embedding
  deriving DecidableEq, Repr

/-- Alias for `QuantumAffineFlagStage`. -/
abbrev QuantumAffineFlagClusterStage := QuantumAffineFlagStage

namespace QuantumAffineFlagStage

/-- Strict topological rank of each stage `Q₁ → Q₅`. -/
def rank : QuantumAffineFlagStage → ℕ
  | .Q1_drinfeld_loop_currents => 1
  | .Q2_kirillov_reshetikhin_t_system => 2
  | .Q3_imaginary_module_defect => 3
  | .Q4_four_mass_box_symbol_letter => 4
  | .Q5_partial_flag_grassmannian_embedding => 5

/-- Directed causal edges of the 5-stage quantum affine & flag cluster poset (`Q₁ → Q₅`). -/
def causalEdge : QuantumAffineFlagStage → QuantumAffineFlagStage → Prop
  | .Q1_drinfeld_loop_currents, .Q2_kirillov_reshetikhin_t_system => True
  | .Q1_drinfeld_loop_currents, .Q3_imaginary_module_defect => True
  | .Q2_kirillov_reshetikhin_t_system, .Q4_four_mass_box_symbol_letter => True
  | .Q3_imaginary_module_defect, .Q4_four_mass_box_symbol_letter => True
  | .Q3_imaginary_module_defect, .Q5_partial_flag_grassmannian_embedding => True
  | .Q4_four_mass_box_symbol_letter, .Q5_partial_flag_grassmannian_embedding => True
  | _, _ => False

/-- `rank` is injective on `QuantumAffineFlagStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> cases h <;> rfl

instance : LinearOrder QuantumAffineFlagStage :=
  LinearOrder.lift' rank rank_injective

/-- Every directed causal edge in `QuantumAffineFlagStage` strictly increases `rank`. -/
theorem causalEdge_strict_rank_mono {x y : QuantumAffineFlagStage}
    (h : causalEdge x y) : rank x < rank y := by
  cases x <;> cases y <;> simp [causalEdge, rank] at h ⊢

/-- The causal poset `QuantumAffineFlagStage` has no self-loops. -/
theorem causalEdge_irrefl (x : QuantumAffineFlagStage) : ¬ causalEdge x x := by
  intro h
  exact Nat.lt_irrefl (rank x) (causalEdge_strict_rank_mono h)

end QuantumAffineFlagStage

/-! ### 2. Core Drinfeld Loop, Dual Canonical & Partial Flag Primitives -/

section Primitives

variable {B : Type*} [Ring B]

/-- Recursive right-associated operator power `opPow n X = X^n`. -/
def opPow : ℕ → B → B
  | 0, _ => 1
  | n + 1, X => opPow n X * X

@[simp]
theorem opPow_zero (X : B) : opPow 0 X = 1 := rfl

@[simp]
theorem opPow_succ (n : ℕ) (X : B) : opPow (n + 1) X = opPow n X * X := rfl

/-- `opPow n X` coincides with the standard monoid power `X ^ n`. -/
theorem opPow_eq_pow (n : ℕ) (X : B) : opPow n X = X ^ n := by
  induction n with
  | zero => simp [opPow, pow_zero]
  | succ k ih => rw [opPow_succ, ih, pow_succ]

/-- Multiplicativity of `opPow` under addition of exponents:
`opPow (n + m) X = opPow n X * opPow m X`. -/
theorem opPow_add (n m : ℕ) (X : B) : opPow (n + m) X = opPow n X * opPow m X := by
  rw [opPow_eq_pow, opPow_eq_pow, opPow_eq_pow, pow_add]

/-- `X` commutes with `opPow n X` for all `n : ℕ`. -/
theorem mul_opPow_comm (n : ℕ) (X : B) : X * opPow n X = opPow n X * X := by
  rw [opPow_eq_pow, ← pow_succ', ← pow_succ]

/-- If an operator power vanishes, multiplication by the generator annihilates
the preceding power on both sides.  This is the ring-theoretic top-mode
consequence of nilpotence; it requires no commutativity assumption. -/
theorem nilpotent_predecessor_power_annihilated (n : ℕ) (X : B)
    (hX : opPow (n + 1) X = 0) :
    X * opPow n X = 0 ∧ opPow n X * X = 0 := by
  constructor
  · calc
      X * opPow n X = opPow n X * X := mul_opPow_comm n X
      _ = opPow (n + 1) X := by rw [opPow_succ]
      _ = 0 := hX
  · calc
      opPow n X * X = opPow (n + 1) X := by rw [opPow_succ]
      _ = 0 := hX

/-- **Archetype `Q₁` (`drinfeldXPlus`, `drinfeldXMinus`, `drinfeldPhiPlus`, `drinfeldPhiMinus`):**
Drinfeld new presentation affine loop currents and Chari–Pressley chiral weight modes:
- `drinfeldXPlus n P A C = (V^n) * N_+(A)`,
- `drinfeldXMinus n P A C = (V^n) * N_-(C)`,
- `drinfeldPhiPlus r P A C = (V^r) * Q_+(A, C)`,
- `drinfeldPhiMinus r P A C = (V^r) * Q_-(A, C)`. -/
def drinfeldXPlus (n : ℕ) (P A C : B) : B :=
  opPow n (genV P A C) * conePlus P A

def drinfeldXMinus (n : ℕ) (P A C : B) : B :=
  opPow n (genV P A C) * coneMinus P C

def drinfeldPhiPlus (r : ℕ) (P A C : B) : B :=
  opPow r (genV P A C) * qgtPlus P A C

def drinfeldPhiMinus (r : ℕ) (P A C : B) : B :=
  opPow r (genV P A C) * qgtMinus P A C

/-- **Archetype `Q₂` (`krModulePlus`, `krModuleMinus`, `krFrozenPlus`, `krFrozenMinus`):**
Kirillov–Reshetikhin `T`-system transfer operators `1 ± Φ(A, C)` and frozen Grassmannian
boundary modules `1 - Q_±(A, C)`. -/
def krModulePlus (P A C : B) : B := 1 + genPhi P A C
def krModuleMinus (P A C : B) : B := 1 - genPhi P A C
def krFrozenPlus (P A C : B) : B := 1 - qgtPlus P A C
def krFrozenMinus (P A C : B) : B := 1 - qgtMinus P A C

/-- **Archetype `Q₃` & `Q₄` (`dualCanonicalCh`, `dualCanonicalUnion`, `imaginaryModuleDefect`,
`fourMassBoxDisc`, `fourMassBoxSqrt`, `algSymbolFactorPlus`, `algSymbolFactorMinus`):**
- `dualCanonicalCh P A C = P + Φ(A, C)`,
- `dualCanonicalUnion P A C = P + Φ(A, C) + 2 • V(A, C)`,
- `imaginaryModuleDefect P A C = ch(T)² - ch(T ∪ T)`,
- `fourMassBoxDisc P A C = 1 - 4 • imaginaryModuleDefect P A C`,
- `fourMassBoxSqrt P A C = invS P + 2 • Φ(A, C)`,
- `algSymbolFactorPlus P A C Z₀ B_z = Z₀ + B_z * fourMassBoxSqrt P A C`,
- `algSymbolFactorMinus P A C Z₀ B_z = Z₀ - B_z * fourMassBoxSqrt P A C`. -/
def dualCanonicalCh (P A C : B) : B := P + genPhi P A C
def dualCanonicalUnion (P A C : B) : B := P + genPhi P A C + (2 : ℤ) • genV P A C

def imaginaryModuleDefect (P A C : B) : B :=
  dualCanonicalCh P A C * dualCanonicalCh P A C - dualCanonicalUnion P A C

def fourMassBoxDisc (P A C : B) : B :=
  1 - (4 : ℤ) • imaginaryModuleDefect P A C

def fourMassBoxSqrt (P A C : B) : B :=
  invS P + (2 : ℤ) • genPhi P A C

def algSymbolFactorPlus (P A C Z₀ B_z : B) : B :=
  Z₀ + B_z * fourMassBoxSqrt P A C

def algSymbolFactorMinus (P A C Z₀ B_z : B) : B :=
  Z₀ - B_z * fourMassBoxSqrt P A C

/-- **Archetype `Q₅` (`flagStratumIdem`, `flagEmbeddedCorner`, `flagStepCorner`):**
- `flagStratumIdem P₁ P₂ = P₂ - P₁` (relative stratum projector of the nested partial flag `P₁ ⊂ P₂`),
- `flagEmbeddedCorner P₁ P₂ A = conePlus P₁ A * (1 - P₂)` (partial flag corner embedded into the
  top Grassmannian corner `conePlus P₂ (P₁ * A)`),
- `flagStepCorner E_src E_dst A = E_src * A * E_dst` (block-parabolic step generator between
  relative flag strata `E_src` and `E_dst`). -/
def flagStratumIdem (P₁ P₂ : B) : B := P₂ - P₁
def flagEmbeddedCorner (P₁ P₂ A : B) : B := conePlus P₁ A * (1 - P₂)
def flagStepCorner (E_src E_dst A : B) : B := E_src * A * E_dst

end Primitives

/-! ### 3. Individual Lemmas & Theorems for Archetypes `Q₁ → Q₅` -/

section Theorems

variable {B : Type*} [Ring B]

/-- **Lemma `Q₁.0` (`opPow_genV_comm_invS_and_cones`):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and any loop mode `n : ℕ`, the power
`opPow n (genV P A C)` commutes with the Cartan grading reflection `invS P` and with both
Peirce nilpotent cones `conePlus P A` and `coneMinus P C`. -/
theorem opPow_genV_comm_invS_and_cones {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    invS P * opPow n (genV P A C) = opPow n (genV P A C) * invS P ∧
    conePlus P A * opPow n (genV P A C) = opPow n (genV P A C) * conePlus P A ∧
    coneMinus P C * opPow n (genV P A C) = opPow n (genV P A C) * coneMinus P C := by
  induction n with
  | zero =>
    simp [opPow]
  | succ k ih =>
    rcases ih with ⟨ihS, ihP, ihM⟩
    have hVS : invS P * genV P A C = genV P A C * invS P := by peirce_nf hP
    have hVP : conePlus P A * genV P A C = genV P A C * conePlus P A := by peirce_nf hP
    have hVM : coneMinus P C * genV P A C = genV P A C * coneMinus P C := by peirce_nf hP
    refine ⟨?_, ?_, ?_⟩
    · calc invS P * (opPow k (genV P A C) * genV P A C)
        _ = (invS P * opPow k (genV P A C)) * genV P A C := by rw [mul_assoc]
        _ = opPow k (genV P A C) * (invS P * genV P A C) := by rw [ihS, mul_assoc]
        _ = (opPow k (genV P A C) * genV P A C) * invS P := by rw [hVS, ← mul_assoc]
    · calc conePlus P A * (opPow k (genV P A C) * genV P A C)
        _ = (conePlus P A * opPow k (genV P A C)) * genV P A C := by rw [mul_assoc]
        _ = opPow k (genV P A C) * (conePlus P A * genV P A C) := by rw [ihP, mul_assoc]
        _ = (opPow k (genV P A C) * genV P A C) * conePlus P A := by rw [hVP, ← mul_assoc]
    · calc coneMinus P C * (opPow k (genV P A C) * genV P A C)
        _ = (coneMinus P C * opPow k (genV P A C)) * genV P A C := by rw [mul_assoc]
        _ = opPow k (genV P A C) * (coneMinus P C * genV P A C) := by rw [ihM, mul_assoc]
        _ = (opPow k (genV P A C) * genV P A C) * coneMinus P C := by rw [hVM, ← mul_assoc]

/-- `invS P` commutes with `opPow n (genV P A C)` for every loop mode `n : ℕ`. -/
theorem invS_comm_opPow_genV {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    invS P * opPow n (genV P A C) = opPow n (genV P A C) * invS P :=
  (opPow_genV_comm_invS_and_cones hP A C n).1

/-- **Lemma `Q₁.2` (`drinfeld_cartan_grading_conjugation`):**
Under the Peirce–Drinfeld Cartan grading involution `K_P = invS P`, the loop current generators
`drinfeldXPlus n P A C` and `drinfeldXMinus n P A C` are odd (`K_P X_{±,n} K_P = -X_{±,n}`) for
every mode `n : ℕ`. -/
theorem drinfeld_cartan_grading_conjugation {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    invS P * drinfeldXPlus n P A C * invS P = -drinfeldXPlus n P A C ∧
    invS P * drinfeldXMinus n P A C * invS P = -drinfeldXMinus n P A C := by
  have hSn := invS_comm_opPow_genV hP A C n
  have hSP : invS P * conePlus P A * invS P = -conePlus P A := by peirce_nf hP
  have hSM : invS P * coneMinus P C * invS P = -coneMinus P C := by peirce_nf hP
  refine ⟨?_, ?_⟩
  · unfold drinfeldXPlus
    calc invS P * (opPow n (genV P A C) * conePlus P A) * invS P
      _ = (invS P * opPow n (genV P A C)) * conePlus P A * invS P := by simp only [mul_assoc]
      _ = opPow n (genV P A C) * (invS P * conePlus P A * invS P) := by
          rw [hSn]; simp only [mul_assoc]
      _ = -(opPow n (genV P A C) * conePlus P A) := by rw [hSP, mul_neg]
  · unfold drinfeldXMinus
    calc invS P * (opPow n (genV P A C) * coneMinus P C) * invS P
      _ = (invS P * opPow n (genV P A C)) * coneMinus P C * invS P := by simp only [mul_assoc]
      _ = opPow n (genV P A C) * (invS P * coneMinus P C * invS P) := by
          rw [hSn]; simp only [mul_assoc]
      _ = -(opPow n (genV P A C) * coneMinus P C) := by rw [hSM, mul_neg]

/-- **Theorem `Q₁.1` (`drinfeld_new_presentation_loop_relations`):**
Selected identities for Peirce power modes. Despite the legacy theorem name, this is not a full
Drinfeld presentation and does not construct a quantum-affine algebra representation.
For any idempotent `P` (`P * P = P`), any `A, C : B`, and any loop modes `n, m : ℕ`:
1. **Cartan Grading Conjugation (`K_P X_{±,n} K_P = -X_{±,n}`):**
   `invS P * drinfeldXPlus n P A C * invS P = -drinfeldXPlus n P A C` and
   `invS P * drinfeldXMinus n P A C * invS P = -drinfeldXMinus n P A C`.
2. **Same-Sector Nilpotency (`X_{+,n} * N_+ = 0`, `X_{+,n} * X_{+,m} = 0`):**
   `drinfeldXPlus n P A C * conePlus P A = 0`, `drinfeldXMinus n P A C * coneMinus P C = 0`,
   `drinfeldXPlus n P A C * drinfeldXPlus m P A C = 0`, and
   `drinfeldXMinus n P A C * drinfeldXMinus m P A C = 0`.
3. **Single-Mode & Two-Mode Drinfeld Loop Current Products, Commutators & Anticommutators:**
   - `drinfeldXPlus n P A C * coneMinus P C = drinfeldPhiPlus n P A C`,
   - `drinfeldXMinus n P A C * conePlus P A = drinfeldPhiMinus n P A C`,
   - `drinfeldXPlus n P A C * coneMinus P C - drinfeldXMinus n P A C * conePlus P A =`
     `drinfeldPhiPlus n P A C - drinfeldPhiMinus n P A C`,
   - `drinfeldXPlus n P A C * coneMinus P C + drinfeldXMinus n P A C * conePlus P A =`
     `opPow (n + 1) (genV P A C)`,
   - `comm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) =`
     `drinfeldPhiPlus (n + m) P A C - drinfeldPhiMinus (n + m) P A C`,
   - `anticomm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) =`
     `opPow (n + m + 1) (genV P A C)`. -/
theorem drinfeld_new_presentation_loop_relations {P : B} (hP : P * P = P) (A C : B) (n m : ℕ) :
    invS P * drinfeldXPlus n P A C * invS P = -drinfeldXPlus n P A C ∧
    invS P * drinfeldXMinus n P A C * invS P = -drinfeldXMinus n P A C ∧
    drinfeldXPlus n P A C * conePlus P A = 0 ∧
    drinfeldXMinus n P A C * coneMinus P C = 0 ∧
    drinfeldXPlus n P A C * coneMinus P C = drinfeldPhiPlus n P A C ∧
    drinfeldXMinus n P A C * conePlus P A = drinfeldPhiMinus n P A C ∧
    drinfeldXPlus n P A C * coneMinus P C - drinfeldXMinus n P A C * conePlus P A =
      drinfeldPhiPlus n P A C - drinfeldPhiMinus n P A C ∧
    drinfeldXPlus n P A C * coneMinus P C + drinfeldXMinus n P A C * conePlus P A =
      opPow (n + 1) (genV P A C) ∧
    drinfeldXPlus n P A C * drinfeldXPlus m P A C = 0 ∧
    drinfeldXMinus n P A C * drinfeldXMinus m P A C = 0 ∧
    comm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) =
      drinfeldPhiPlus (n + m) P A C - drinfeldPhiMinus (n + m) P A C ∧
    anticomm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) =
      opPow (n + m + 1) (genV P A C) := by
  rcases opPow_genV_comm_invS_and_cones hP A C n with ⟨_, _, hMn⟩
  rcases opPow_genV_comm_invS_and_cones hP A C m with ⟨_, hPm, hMm⟩
  rcases drinfeld_cartan_grading_conjugation hP A C n with ⟨hCartanP, hCartanM⟩
  have hNpSq : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hNmSq : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  have hProdPM :
      drinfeldXPlus n P A C * drinfeldXMinus m P A C = drinfeldPhiPlus (n + m) P A C := by
    unfold drinfeldXPlus drinfeldXMinus drinfeldPhiPlus qgtPlus
    calc (opPow n (genV P A C) * conePlus P A) * (opPow m (genV P A C) * coneMinus P C)
      _ = opPow n (genV P A C) * (conePlus P A * opPow m (genV P A C)) * coneMinus P C := by
          simp only [mul_assoc]
      _ = (opPow n (genV P A C) * opPow m (genV P A C)) * (conePlus P A * coneMinus P C) := by
          rw [hPm]; simp only [mul_assoc]
      _ = opPow (n + m) (genV P A C) * (conePlus P A * coneMinus P C) := by
          rw [← opPow_add]
  have hProdMP :
      drinfeldXMinus m P A C * drinfeldXPlus n P A C = drinfeldPhiMinus (n + m) P A C := by
    unfold drinfeldXPlus drinfeldXMinus drinfeldPhiMinus qgtMinus
    calc (opPow m (genV P A C) * coneMinus P C) * (opPow n (genV P A C) * conePlus P A)
      _ = opPow m (genV P A C) * (coneMinus P C * opPow n (genV P A C)) * conePlus P A := by
          simp only [mul_assoc]
      _ = (opPow m (genV P A C) * opPow n (genV P A C)) * (coneMinus P C * conePlus P A) := by
          rw [hMn]; simp only [mul_assoc]
      _ = opPow (n + m) (genV P A C) * (coneMinus P C * conePlus P A) := by
          rw [← opPow_add, Nat.add_comm]
  refine ⟨hCartanP, hCartanM,
    by unfold drinfeldXPlus; rw [mul_assoc, hNpSq, mul_zero],
    by unfold drinfeldXMinus; rw [mul_assoc, hNmSq, mul_zero],
    by unfold drinfeldXPlus drinfeldPhiPlus qgtPlus; rw [mul_assoc],
    by unfold drinfeldXMinus drinfeldPhiMinus qgtMinus; rw [mul_assoc],
    by unfold drinfeldXPlus drinfeldXMinus drinfeldPhiPlus drinfeldPhiMinus qgtPlus qgtMinus
       rw [mul_assoc, mul_assoc],
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold drinfeldXPlus drinfeldXMinus
    rw [opPow_succ, mul_assoc, mul_assoc, ← mul_add]
    rfl
  · unfold drinfeldXPlus
    calc (opPow n (genV P A C) * conePlus P A) * (opPow m (genV P A C) * conePlus P A)
      _ = opPow n (genV P A C) * (conePlus P A * opPow m (genV P A C)) * conePlus P A := by
          simp only [mul_assoc]
      _ = (opPow n (genV P A C) * opPow m (genV P A C)) * (conePlus P A * conePlus P A) := by
          rw [hPm]; simp only [mul_assoc]
      _ = 0 := by rw [hNpSq, mul_zero]
  · unfold drinfeldXMinus
    calc (opPow n (genV P A C) * coneMinus P C) * (opPow m (genV P A C) * coneMinus P C)
      _ = opPow n (genV P A C) * (coneMinus P C * opPow m (genV P A C)) * coneMinus P C := by
          simp only [mul_assoc]
      _ = (opPow n (genV P A C) * opPow m (genV P A C)) * (coneMinus P C * coneMinus P C) := by
          rw [hMm]; simp only [mul_assoc]
      _ = 0 := by rw [hNmSq, mul_zero]
  · unfold comm
    rw [hProdPM, hProdMP]
  · unfold anticomm
    rw [hProdPM, hProdMP]
    unfold drinfeldPhiPlus drinfeldPhiMinus
    rw [opPow_succ, ← mul_add]
    rfl

/-- **Theorem `Q₂.1` (`kirillov_reshetikhin_t_system_exchange`):**
This proves the stated local factorization for defined ring elements; it does not construct
Kirillov–Reshetikhin modules or prove the general `T`-system.
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. `krModulePlus P A C * krModuleMinus P A C = krFrozenPlus P A C * krFrozenMinus P A C`.
2. Both sides equal `zetaFactor P A C = 1 - genV P A C` and commute strictly:
   `krModulePlus P A C * krModuleMinus P A C = krModuleMinus P A C * krModulePlus P A C`. -/
theorem kirillov_reshetikhin_t_system_exchange {P : B} (hP : P * P = P) (A C : B) :
    krModulePlus P A C * krModuleMinus P A C =
      krFrozenPlus P A C * krFrozenMinus P A C ∧
    krModulePlus P A C * krModuleMinus P A C = 1 - genV P A C ∧
    krModulePlus P A C * krModuleMinus P A C =
      krModuleMinus P A C * krModulePlus P A C := by
  refine ⟨by unfold krModulePlus krModuleMinus krFrozenPlus krFrozenMinus qgtPlus qgtMinus; peirce_nf hP,
          by unfold krModulePlus krModuleMinus; peirce_nf hP,
          by unfold krModulePlus krModuleMinus; peirce_nf hP⟩

/-- **Theorem `Q₃.1` & `Q₄.1` (`imaginary_module_and_four_mass_box_letter`):**
The names below denote formal ring expressions, not module characters or analytic letters.
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Imaginary Square-Excess Defect (`B = ch(T)² - ch(T ∪ T) = -V`):**
   `imaginaryModuleDefect P A C = -genV P A C`.
2. **Four-Mass-Box Discriminant & Square-Root Identification (`Δ = 1 + 4V = (√Δ)²`):**
   - `fourMassBoxDisc P A C = 1 + (4 : ℤ) • genV P A C`,
   - `fourMassBoxSqrt P A C = radicalLetterPlus P A C`,
   - `fourMassBoxSqrt P A C * fourMassBoxSqrt P A C = fourMassBoxDisc P A C`.
3. **Dual Canonical Algebraic Symbol Letter Rationalization:**
   - `algSymbolFactorPlus P A C 1 1 * algSymbolFactorMinus P A C 1 1 = -(4 : ℤ) • genV P A C`,
   - `algSymbolFactorPlus P A C (genV P A C) 1 * algSymbolFactorMinus P A C (genV P A C) 1 =`
     `genV P A C * genV P A C - fourMassBoxDisc P A C`. -/
theorem imaginary_module_and_four_mass_box_letter {P : B} (hP : P * P = P) (A C : B) :
    imaginaryModuleDefect P A C = -genV P A C ∧
    fourMassBoxDisc P A C = 1 + (4 : ℤ) • genV P A C ∧
    fourMassBoxSqrt P A C = radicalLetterPlus P A C ∧
    fourMassBoxSqrt P A C * fourMassBoxSqrt P A C = fourMassBoxDisc P A C ∧
    algSymbolFactorPlus P A C 1 1 * algSymbolFactorMinus P A C 1 1 =
      -(4 : ℤ) • genV P A C ∧
    algSymbolFactorPlus P A C (genV P A C) 1 *
      algSymbolFactorMinus P A C (genV P A C) 1 =
      genV P A C * genV P A C - fourMassBoxDisc P A C := by
  refine ⟨
    by unfold imaginaryModuleDefect dualCanonicalCh dualCanonicalUnion; peirce_nf hP,
    by unfold fourMassBoxDisc imaginaryModuleDefect dualCanonicalCh dualCanonicalUnion; peirce_nf hP,
    by unfold fourMassBoxSqrt radicalLetterPlus peirceTransfer; peirce_nf hP,
    by unfold fourMassBoxSqrt fourMassBoxDisc imaginaryModuleDefect dualCanonicalCh dualCanonicalUnion
       peirce_nf hP,
    by unfold algSymbolFactorPlus algSymbolFactorMinus fourMassBoxSqrt
       peirce_nf hP,
    by unfold algSymbolFactorPlus algSymbolFactorMinus fourMassBoxSqrt fourMassBoxDisc
              imaginaryModuleDefect dualCanonicalCh dualCanonicalUnion
       peirce_nf hP⟩

/-- **Theorem `Q₄.2` (`algSymbolFactor_rationalization_of_comm`):**
General non-commutative symbol letter rationalization: for any `Z₀, B_z : B` that commute with
each other (`Z₀ * B_z = B_z * Z₀`) and with `fourMassBoxSqrt P A C`,
`algSymbolFactorPlus P A C Z₀ B_z * algSymbolFactorMinus P A C Z₀ B_z =`
`Z₀ * Z₀ - B_z * B_z * fourMassBoxDisc P A C`. -/
theorem algSymbolFactor_rationalization_of_comm
    {P : B} (hP : P * P = P) (A C Z₀ B_z : B)
    (hZB : Z₀ * B_z = B_z * Z₀)
    (hZSqrt : Z₀ * fourMassBoxSqrt P A C = fourMassBoxSqrt P A C * Z₀)
    (hBSqrt : B_z * fourMassBoxSqrt P A C = fourMassBoxSqrt P A C * B_z) :
    algSymbolFactorPlus P A C Z₀ B_z * algSymbolFactorMinus P A C Z₀ B_z =
      Z₀ * Z₀ - B_z * B_z * fourMassBoxDisc P A C := by
  have hSq : fourMassBoxSqrt P A C * fourMassBoxSqrt P A C = fourMassBoxDisc P A C :=
    (imaginary_module_and_four_mass_box_letter hP A C).2.2.2.1
  unfold algSymbolFactorPlus algSymbolFactorMinus
  have hCross :
      (B_z * fourMassBoxSqrt P A C) * Z₀ = Z₀ * (B_z * fourMassBoxSqrt P A C) := by
    calc (B_z * fourMassBoxSqrt P A C) * Z₀
      _ = B_z * (fourMassBoxSqrt P A C * Z₀) := by rw [mul_assoc]
      _ = (B_z * Z₀) * fourMassBoxSqrt P A C := by rw [← hZSqrt, ← mul_assoc]
      _ = Z₀ * (B_z * fourMassBoxSqrt P A C) := by rw [← hZB, mul_assoc]
  have hProd :
      (B_z * fourMassBoxSqrt P A C) * (B_z * fourMassBoxSqrt P A C) =
        B_z * B_z * fourMassBoxDisc P A C := by
    calc (B_z * fourMassBoxSqrt P A C) * (B_z * fourMassBoxSqrt P A C)
      _ = B_z * (fourMassBoxSqrt P A C * B_z) * fourMassBoxSqrt P A C := by simp only [mul_assoc]
      _ = B_z * B_z * (fourMassBoxSqrt P A C * fourMassBoxSqrt P A C) := by
          rw [← hBSqrt]; simp only [mul_assoc]
      _ = B_z * B_z * fourMassBoxDisc P A C := by rw [hSq]
  calc (Z₀ + B_z * fourMassBoxSqrt P A C) * (Z₀ - B_z * fourMassBoxSqrt P A C)
    _ = Z₀ * Z₀ - Z₀ * (B_z * fourMassBoxSqrt P A C) +
        (B_z * fourMassBoxSqrt P A C) * Z₀ -
        (B_z * fourMassBoxSqrt P A C) * (B_z * fourMassBoxSqrt P A C) := by
        noncomm_ring
    _ = Z₀ * Z₀ - B_z * B_z * fourMassBoxDisc P A C := by
        rw [hCross, hProd]
        abel

/-- **Theorem `Q₅.1` (`partial_flag_to_grassmannian_embedding`):**
Let `P₁, P₂ : B` be nested idempotents (`h1 : P₁ * P₁ = P₁`, `h2 : P₂ * P₂ = P₂`,
`h12 : P₁ * P₂ = P₁`, `h21 : P₂ * P₁ = P₁`, modeling `0 ⊂ V₁ ⊂ V₂`). Then:
1. **Relative Flag Stratum Idempotency, Mutual Orthogonality & Partition of Unity (`P₂ - P₁`):**
   - `flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂`,
   - `P₁ * flagStratumIdem P₁ P₂ = 0` and `flagStratumIdem P₁ P₂ * P₁ = 0`,
   - `flagStratumIdem P₁ P₂ * (1 - P₂) = 0` and `(1 - P₂) * flagStratumIdem P₁ P₂ = 0`,
   - `P₁ + flagStratumIdem P₁ P₂ + (1 - P₂) = 1`.
2. **Exact Embedding of the Partial Flag Corner into the Top Grassmannian Corner:**
   - `flagEmbeddedCorner P₁ P₂ A = P₁ * A * (1 - P₂)`,
   - `flagEmbeddedCorner P₁ P₂ A = conePlus P₂ (P₁ * A)`. -/
theorem partial_flag_to_grassmannian_embedding
    {P₁ P₂ : B} (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = P₁) (h21 : P₂ * P₁ = P₁) (A : B) :
    flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂ ∧
    P₁ * flagStratumIdem P₁ P₂ = 0 ∧
    flagStratumIdem P₁ P₂ * P₁ = 0 ∧
    flagStratumIdem P₁ P₂ * (1 - P₂) = 0 ∧
    (1 - P₂) * flagStratumIdem P₁ P₂ = 0 ∧
    P₁ + flagStratumIdem P₁ P₂ + (1 - P₂) = 1 ∧
    flagEmbeddedCorner P₁ P₂ A = P₁ * A * (1 - P₂) ∧
    flagEmbeddedCorner P₁ P₂ A = conePlus P₂ (P₁ * A) := by
  have h21_assoc : ∀ X : B, P₂ * (P₁ * X) = P₁ * X := by intro X; rw [← mul_assoc, h21]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold flagStratumIdem
    simp only [sub_mul, mul_sub, h1, h2, h12, h21]
    abel
  · unfold flagStratumIdem
    rw [mul_sub, h12, h1, sub_self]
  · unfold flagStratumIdem
    rw [sub_mul, h21, h1, sub_self]
  · unfold flagStratumIdem
    simp only [sub_mul, mul_sub, mul_one, h2, h12, sub_self]
  · unfold flagStratumIdem
    simp only [sub_mul, mul_sub, one_mul, h2, h21, sub_self]
  · unfold flagStratumIdem
    abel
  · unfold flagEmbeddedCorner conePlus
    calc (P₁ * A * (1 - P₁)) * (1 - P₂)
      _ = P₁ * A * ((1 - P₁) * (1 - P₂)) := by simp only [mul_assoc]
      _ = P₁ * A * (1 - P₂) := by
          have hSub : (1 - P₁) * (1 - P₂) = 1 - P₂ := by
            simp only [sub_mul, mul_sub, one_mul, mul_one, h12]
            abel
          rw [hSub]
  · unfold flagEmbeddedCorner conePlus
    calc (P₁ * A * (1 - P₁)) * (1 - P₂)
      _ = P₁ * A * ((1 - P₁) * (1 - P₂)) := by simp only [mul_assoc]
      _ = P₁ * A * (1 - P₂) := by
          have hSub : (1 - P₁) * (1 - P₂) = 1 - P₂ := by
            simp only [sub_mul, mul_sub, one_mul, mul_one, h12]
            abel
          rw [hSub]
      _ = P₂ * (P₁ * A) * (1 - P₂) := by rw [h21_assoc]

/-! ### 4. Master Theorem `D₂₇` (`Q₁ → Q₅`): Quantum Affine, Dual Canonical & Flag Cluster Poset -/

/-- **Master Theorem `D₂₇` (`stage_D27_quantum_affine_dual_canonical_and_partial_flag_master_synthesis`):**
Complete synthesis of the 5-stage quantum affine, dual canonical & partial flag cluster poset
(`Q₁ → Q₅`):
1. **`Q₁` (Drinfeld New Presentation Loop Currents & Chiral Weight Modes):**
   - `invS P * drinfeldXPlus n P A C * invS P = -drinfeldXPlus n P A C`,
   - `invS P * drinfeldXMinus n P A C * invS P = -drinfeldXMinus n P A C`,
   - `drinfeldXPlus n P A C * coneMinus P C - drinfeldXMinus n P A C * conePlus P A =`
     `drinfeldPhiPlus n P A C - drinfeldPhiMinus n P A C`,
   - `drinfeldXPlus n P A C * coneMinus P C + drinfeldXMinus n P A C * conePlus P A =`
     `opPow (n + 1) (genV P A C)`,
   - `comm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) =`
     `drinfeldPhiPlus (n + m) P A C - drinfeldPhiMinus (n + m) P A C`,
   - `anticomm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) = opPow (n + m + 1) (genV P A C)`;
2. **`Q₂` (Kirillov–Reshetikhin `T`-System Bilinear Exchange Identity):**
   - `krModulePlus P A C * krModuleMinus P A C = krFrozenPlus P A C * krFrozenMinus P A C`,
   - `krModulePlus P A C * krModuleMinus P A C = 1 - genV P A C`;
3. **`Q₃` & `Q₄` (Imaginary Prime Module Defect & Four-Mass-Box Square-Root Letter):**
   - `imaginaryModuleDefect P A C = -genV P A C`,
   - `fourMassBoxSqrt P A C * fourMassBoxSqrt P A C = fourMassBoxDisc P A C`,
   - `algSymbolFactorPlus P A C (genV P A C) 1 * algSymbolFactorMinus P A C (genV P A C) 1 =`
     `genV P A C * genV P A C - fourMassBoxDisc P A C`;
4. **`Q₅` (Nested Partial Flag Variety Stratum Orthogonality & Grassmannian Corner Embedding):**
   - `flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂`,
   - `P₁ + flagStratumIdem P₁ P₂ + (1 - P₂) = 1`,
   - `flagEmbeddedCorner P₁ P₂ A = P₁ * A * (1 - P₂)`,
   - `flagEmbeddedCorner P₁ P₂ A = conePlus P₂ (P₁ * A)`. -/
theorem stage_D27_quantum_affine_dual_canonical_and_partial_flag_master_synthesis
    {P P₁ P₂ A C : B}
    (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = P₁) (h21 : P₂ * P₁ = P₁) (n m : ℕ) :
    -- 1. Drinfeld New Presentation Loop Currents (Q₁):
    invS P * drinfeldXPlus n P A C * invS P = -drinfeldXPlus n P A C ∧
    invS P * drinfeldXMinus n P A C * invS P = -drinfeldXMinus n P A C ∧
    drinfeldXPlus n P A C * coneMinus P C - drinfeldXMinus n P A C * conePlus P A =
      drinfeldPhiPlus n P A C - drinfeldPhiMinus n P A C ∧
    drinfeldXPlus n P A C * coneMinus P C + drinfeldXMinus n P A C * conePlus P A =
      opPow (n + 1) (genV P A C) ∧
    comm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) =
      drinfeldPhiPlus (n + m) P A C - drinfeldPhiMinus (n + m) P A C ∧
    anticomm (drinfeldXPlus n P A C) (drinfeldXMinus m P A C) =
      opPow (n + m + 1) (genV P A C) ∧
    -- 2. Kirillov–Reshetikhin `T`-System Bilinear Exchange Identity (Q₂):
    krModulePlus P A C * krModuleMinus P A C =
      krFrozenPlus P A C * krFrozenMinus P A C ∧
    krModulePlus P A C * krModuleMinus P A C = 1 - genV P A C ∧
    -- 3. Imaginary Prime Module Defect & Four-Mass-Box Square-Root Letter (Q₃ & Q₄):
    imaginaryModuleDefect P A C = -genV P A C ∧
    fourMassBoxSqrt P A C * fourMassBoxSqrt P A C = fourMassBoxDisc P A C ∧
    algSymbolFactorPlus P A C (genV P A C) 1 *
      algSymbolFactorMinus P A C (genV P A C) 1 =
      genV P A C * genV P A C - fourMassBoxDisc P A C ∧
    -- 4. Partial Flag Variety Stratum Orthogonality & Grassmannian Corner Embedding (Q₅):
    flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂ ∧
    P₁ + flagStratumIdem P₁ P₂ + (1 - P₂) = 1 ∧
    flagEmbeddedCorner P₁ P₂ A = P₁ * A * (1 - P₂) ∧
    flagEmbeddedCorner P₁ P₂ A = conePlus P₂ (P₁ * A) := by
  rcases drinfeld_new_presentation_loop_relations hP A C n m with
    ⟨hD1, hD2, _, _, _, _, hD5, hD6, _, _, hD9, hD10⟩
  rcases kirillov_reshetikhin_t_system_exchange hP A C with ⟨hK1, hK2, _⟩
  rcases imaginary_module_and_four_mass_box_letter hP A C with ⟨hI1, _, _, hI4, _, hI6⟩
  rcases partial_flag_to_grassmannian_embedding h1 h2 h12 h21 A with
    ⟨hF1, _, _, _, _, hF6, hF7, hF8⟩
  exact ⟨hD1, hD2, hD5, hD6, hD9, hD10, hK1, hK2, hI1, hI4, hI6, hF1, hF6, hF7, hF8⟩

/-! ### 5. Stage `D₃₀`: Length-3 Partial Flag Variety Filtration (`P₁ ⊂ P₂ ⊂ P₃`), Parabolic Radical & Top-Grassmannian Embedding -/

/-- **Master Theorem `D₃₀` (`stage_D30_three_step_partial_flag_and_parabolic_radical_bridge`):**
For a length-3 nested partial flag `P₁ ⊂ P₂ ⊂ P₃` (`P_i² = P_i` and `P_i P_j = P_j P_i = P_{min(i,j)}`):
1. **Four-Stratum Partition of Unity & Mutual Orthogonality (`P₁`, `P₂ - P₁`, `P₃ - P₂`, `1 - P₃`):**
   - `flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂`,
   - `flagStratumIdem P₂ P₃ * flagStratumIdem P₂ P₃ = flagStratumIdem P₂ P₃`,
   - `flagStratumIdem P₁ P₂ * flagStratumIdem P₂ P₃ = 0` and
     `flagStratumIdem P₂ P₃ * flagStratumIdem P₁ P₂ = 0`,
   - `P₁ + flagStratumIdem P₁ P₂ + flagStratumIdem P₂ P₃ + (1 - P₃) = 1`;
2. **Parabolic Upper-Triangular Step Radical Composition & Reverse Annihilation:**
   - `flagStepCorner P₁ (flagStratumIdem P₁ P₂) A * flagStepCorner (flagStratumIdem P₁ P₂) (flagStratumIdem P₂ P₃) C =`
     `flagStepCorner P₁ (flagStratumIdem P₂ P₃) (A * flagStratumIdem P₁ P₂ * C)`,
   - `flagStepCorner (flagStratumIdem P₁ P₂) (flagStratumIdem P₂ P₃) C * flagStepCorner P₁ (flagStratumIdem P₁ P₂) A = 0`;
3. **Iterated Flag-to-Top-Grassmannian Corner Embedding (`Fℓ_{d₁,d₂,d₃;n} ↪ Gr(d₃, N)`):**
   - `flagEmbeddedCorner P₁ P₂ A * (1 - P₃) = flagEmbeddedCorner P₁ P₃ A`,
   - `flagEmbeddedCorner P₁ P₃ A = conePlus P₃ (P₁ * A)`,
   - `flagEmbeddedCorner P₂ P₃ A = conePlus P₃ (P₂ * A)`. -/
theorem stage_D30_three_step_partial_flag_and_parabolic_radical_bridge
    {P₁ P₂ P₃ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h3 : P₃ * P₃ = P₃)
    (h12 : P₁ * P₂ = P₁) (h21 : P₂ * P₁ = P₁)
    (h23 : P₂ * P₃ = P₂) (h32 : P₃ * P₂ = P₂)
    (h13 : P₁ * P₃ = P₁) (h31 : P₃ * P₁ = P₁)
    (A C : B) :
    flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂ ∧
    flagStratumIdem P₂ P₃ * flagStratumIdem P₂ P₃ = flagStratumIdem P₂ P₃ ∧
    flagStratumIdem P₁ P₂ * flagStratumIdem P₂ P₃ = 0 ∧
    flagStratumIdem P₂ P₃ * flagStratumIdem P₁ P₂ = 0 ∧
    P₁ + flagStratumIdem P₁ P₂ + flagStratumIdem P₂ P₃ + (1 - P₃) = 1 ∧
    flagStepCorner P₁ (flagStratumIdem P₁ P₂) A *
        flagStepCorner (flagStratumIdem P₁ P₂) (flagStratumIdem P₂ P₃) C =
      flagStepCorner P₁ (flagStratumIdem P₂ P₃) (A * flagStratumIdem P₁ P₂ * C) ∧
    flagStepCorner (flagStratumIdem P₁ P₂) (flagStratumIdem P₂ P₃) C *
        flagStepCorner P₁ (flagStratumIdem P₁ P₂) A = 0 ∧
    flagEmbeddedCorner P₁ P₂ A * (1 - P₃) = flagEmbeddedCorner P₁ P₃ A ∧
    flagEmbeddedCorner P₁ P₃ A = conePlus P₃ (P₁ * A) ∧
    flagEmbeddedCorner P₂ P₃ A = conePlus P₃ (P₂ * A) := by
  rcases partial_flag_to_grassmannian_embedding h1 h2 h12 h21 A with
    ⟨hIdem12, _, hOrth12P1, _, _, _, hEmb12, _⟩
  rcases partial_flag_to_grassmannian_embedding h2 h3 h23 h32 A with
    ⟨hIdem23, hOrthP2_23, hOrth23_P2, _, _, _, _, hEmb23Top⟩
  rcases partial_flag_to_grassmannian_embedding h1 h3 h13 h31 A with
    ⟨_, _, _, _, _, _, hEmb13, hEmb13Top⟩
  have hOrth12_23 : flagStratumIdem P₁ P₂ * flagStratumIdem P₂ P₃ = 0 := by
    unfold flagStratumIdem
    simp only [sub_mul, mul_sub, h2, h23, h12, h13]
    abel
  have hOrth23_12 : flagStratumIdem P₂ P₃ * flagStratumIdem P₁ P₂ = 0 := by
    unfold flagStratumIdem
    simp only [sub_mul, mul_sub, h2, h32, h21, h31]
    abel
  have hOrth23_P1 : flagStratumIdem P₂ P₃ * P₁ = 0 := by
    unfold flagStratumIdem
    rw [sub_mul, h31, h21, sub_self]
  refine ⟨hIdem12, hIdem23, hOrth12_23, hOrth23_12, ?_, ?_, ?_, ?_, hEmb13Top, hEmb23Top⟩
  · unfold flagStratumIdem
    abel
  · unfold flagStepCorner
    calc (P₁ * A * flagStratumIdem P₁ P₂) *
          (flagStratumIdem P₁ P₂ * C * flagStratumIdem P₂ P₃)
      _ = P₁ * A * (flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂) * C *
          flagStratumIdem P₂ P₃ := by simp only [mul_assoc]
      _ = P₁ * (A * flagStratumIdem P₁ P₂ * C) * flagStratumIdem P₂ P₃ := by
          rw [hIdem12]; simp only [mul_assoc]
  · unfold flagStepCorner
    calc (flagStratumIdem P₁ P₂ * C * flagStratumIdem P₂ P₃) *
          (P₁ * A * flagStratumIdem P₁ P₂)
      _ = flagStratumIdem P₁ P₂ * C * (flagStratumIdem P₂ P₃ * P₁) * A *
          flagStratumIdem P₁ P₂ := by simp only [mul_assoc]
      _ = 0 := by rw [hOrth23_P1, mul_zero, zero_mul, zero_mul]
  · rw [hEmb12, hEmb13]
    calc (P₁ * A * (1 - P₂)) * (1 - P₃)
      _ = P₁ * A * ((1 - P₂) * (1 - P₃)) := by rw [mul_assoc]
      _ = P₁ * A * (1 - P₃) := by
          have hSub23 : (1 - P₂) * (1 - P₃) = 1 - P₃ := by
            simp only [sub_mul, mul_sub, one_mul, mul_one, h23]
            abel
          rw [hSub23]

end Theorems

end InfoGeometry.OperatorAlgebra.PeirceSpine
