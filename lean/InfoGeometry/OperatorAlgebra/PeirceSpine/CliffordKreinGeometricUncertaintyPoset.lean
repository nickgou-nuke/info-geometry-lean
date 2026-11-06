/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Clifford–Krein Geometric Uncertainty Poset and Native `CliffordAlgebra` Reversion Bridge

This module formalizes the 6-stage Clifford–Krein Geometric Uncertainty Poset (`p₀ ≺ ⋯ ≺ p₅`)
over arbitrary associative rings `[Ring B]` and native Mathlib `CliffordAlgebra Q`:

1. **`CliffordKreinUncertaintyStage` (`p₀ ≺ p₁ ≺ p₂ ≺ p₃ ≺ p₄ ≺ p₅`)**:
   Strict acyclic causal poset ordering the indefinite Krein metric and bivector rotor (`p₀`),
   Hestenes geometric product (`p₁`), spinor reversion and Krein adjoint (`p₂`), mixed-grade
   geometric tensor `Q = g + K` (`p₃`), non-commutative vs. commuting Clifford–Krein reversion
   modulus (`p₄`), and signature-dependent Elliptic (`I² = -1`) vs. Hyperbolic (`I² = +1`)
   modulus factorization (`p₅`).
2. **`cliffordKreinModulus_noncommutative` & `cliffordKreinModulus`**:
   Exact non-commutative expansion `(g + K) * (g - K) = g * g - K * K - (g * K - K * g)` and
   commuting reduction `(g + K) * (g - K) = g * g - K * K`.
3. **`cliffordKrein_bivector_rotor_signature_dichotomy`**:
   When `g, Ω, I : B` pairwise commute and `K = I * Ω`:
   - General rotor modulus: `(g + I * Ω) * (g - I * Ω) = g * g - (I * I) * (Ω * Ω)`
   - Elliptic / space-like bivector (`I * I = -1`): `(g + I * Ω) * (g - I * Ω) = g * g + Ω * Ω`
   - Hyperbolic / time-like bivector (`I * I = 1`): `(g + I * Ω) * (g - I * Ω) = g * g - Ω * Ω = (g - Ω) * (g + Ω)`
   - Peirce para-Kähler lightcone annihilation (`hP : P * P = P`):
     `geometricTensor (genV P A C) (genSig P A C) * geometricTensorReverse (genV P A C) (genSig P A C) = 0`.
4. **`native_cliffordAlgebra_bivector_reverse_and_modulus`**:
   In native Mathlib `CliffordAlgebra Q` over `[CommRing R] [AddCommGroup M] [Module R M]`, for any
   orthogonal vectors `u v : M` (`ι Q u * ι Q v + ι Q v * ι Q u = 0`), the bivector
   `B_uv = ι Q u * ι Q v` satisfies `CliffordAlgebra.reverse B_uv = -B_uv`, so
   `CliffordAlgebra.reverse (algebraMap R _ g + B_uv) = geometricTensorReverse (algebraMap R _ g) B_uv`
   and `(algebraMap R _ g + B_uv) * CliffordAlgebra.reverse (algebraMap R _ g + B_uv) =
   algebraMap R _ (g * g) - B_uv * B_uv`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.CliffordKreinGeometricUncertaintyPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The 6-stage Clifford–Krein Geometric Uncertainty Poset (`p₀ ≺ p₁ ≺ p₂ ≺ p₃ ≺ p₄ ≺ p₅`). -/
inductive CliffordKreinUncertaintyStage : Type
  | p0_KreinMetricAndBivectorRotor
  | p1_HestenesGeometricProduct
  | p2_SpinorReversionAndKreinAdjoint
  | p3_MixedGradeGeometricTensor
  | p4_CliffordKreinReversionModulus
  | p5_SignatureDependentCausalUncertainty
  deriving DecidableEq, Repr, Inhabited

namespace CliffordKreinUncertaintyStage

/-- Strict topological rank of each stage in `CliffordKreinUncertaintyStage`. -/
def rk : CliffordKreinUncertaintyStage → ℕ
  | .p0_KreinMetricAndBivectorRotor => 0
  | .p1_HestenesGeometricProduct => 1
  | .p2_SpinorReversionAndKreinAdjoint => 2
  | .p3_MixedGradeGeometricTensor => 3
  | .p4_CliffordKreinReversionModulus => 4
  | .p5_SignatureDependentCausalUncertainty => 5

/-- Directed causal edge `s₁ → s₂` in `CliffordKreinUncertaintyStage`. -/
def causalEdge : CliffordKreinUncertaintyStage → CliffordKreinUncertaintyStage → Prop
  | .p0_KreinMetricAndBivectorRotor, .p1_HestenesGeometricProduct => True
  | .p1_HestenesGeometricProduct, .p2_SpinorReversionAndKreinAdjoint => True
  | .p2_SpinorReversionAndKreinAdjoint, .p3_MixedGradeGeometricTensor => True
  | .p3_MixedGradeGeometricTensor, .p4_CliffordKreinReversionModulus => True
  | .p4_CliffordKreinReversionModulus, .p5_SignatureDependentCausalUncertainty => True
  | _, _ => False

theorem rk_strict_mono {s₁ s₂ : CliffordKreinUncertaintyStage}
    (h : causalEdge s₁ s₂) : s₁.rk < s₂.rk := by
  cases s₁ <;> cases s₂ <;> simp [causalEdge, rk] at h ⊢

theorem transGen_rk_lt {s₁ s₂ : CliffordKreinUncertaintyStage}
    (h : Relation.TransGen causalEdge s₁ s₂) : s₁.rk < s₂.rk := by
  induction h with
  | single he => exact rk_strict_mono he
  | tail _ he ih => exact Nat.lt_trans ih (rk_strict_mono he)

/-- Strict acyclicity of `CliffordKreinUncertaintyStage`. -/
theorem cliffordKrein_poset_strict_acyclicity (s : CliffordKreinUncertaintyStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl s.rk (transGen_rk_lt h)

end CliffordKreinUncertaintyStage

/-- The two-term geometric tensor `g + K`. -/
def geometricTensor (g K : B) : B := g + K

/-- Reversal of the two-term tensor, fixing `g` and negating `K`. -/
def geometricTensorReverse (g K : B) : B := g - K

/-- Exact non-commutative expansion of the Clifford–Krein modulus product:
`geometricTensor g K * geometricTensorReverse g K = g * g - K * K - (g * K - K * g)`. -/
theorem cliffordKreinModulus_noncommutative (g K : B) :
    geometricTensor g K * geometricTensorReverse g K =
      g * g - K * K - (g * K - K * g) := by
  dsimp [geometricTensor, geometricTensorReverse]
  noncomm_ring

/-- Clifford–Krein modulus for commuting scalar-like and bivector-like parts. -/
theorem cliffordKreinModulus (g K : B) (hComm : g * K = K * g) :
    geometricTensor g K * geometricTensorReverse g K = g * g - K * K := by
  dsimp [geometricTensor, geometricTensorReverse]
  calc
    (g + K) * (g - K) = g * g + K * g - g * K - K * K := by noncomm_ring
    _ = g * g - K * K := by rw [hComm]; abel

/-- **Signature-Dependent Bivector Rotor Modulus Dichotomy (`I² = -1` vs. `I² = +1`) &
Peirce Para-Kähler Lightcone Annihilation**:
1. When `g, Ω, I : B` pairwise commute (`g * I = I * g`, `g * Ω = Ω * g`, `I * Ω = Ω * I`),
   `geometricTensor g (I * Ω) * geometricTensorReverse g (I * Ω) = g * g - (I * I) * (Ω * Ω)`.
2. **Elliptic / Space-like Bivector (`I * I = -1`)**:
   `geometricTensor g (I * Ω) * geometricTensorReverse g (I * Ω) = g * g + Ω * Ω`.
3. **Hyperbolic / Time-like Bivector (`I * I = 1`)**:
   `geometricTensor g (I * Ω) * geometricTensorReverse g (I * Ω) = g * g - Ω * Ω = (g - Ω) * (g + Ω)`.
4. **Peirce Para-Kähler Lightcone Factorization (`P * P = P`)**:
   For `V = genV P A C` and `Σ = genSig P A C` (`2 N_+ N_- = V + Σ`, `2 N_- N_+ = V - Σ`),
   `geometricTensor (genV P A C) (genSig P A C) * geometricTensorReverse (genV P A C) (genSig P A C) = 0`. -/
theorem cliffordKrein_bivector_rotor_signature_dichotomy
    {P : B} (hP : P * P = P) (A C g Ω I : B)
    (hComm_gI : g * I = I * g) (hComm_gΩ : g * Ω = Ω * g) (hComm_IΩ : I * Ω = Ω * I) :
    geometricTensor g (I * Ω) * geometricTensorReverse g (I * Ω) =
      g * g - (I * I) * (Ω * Ω) ∧
    (I * I = -1 →
      geometricTensor g (I * Ω) * geometricTensorReverse g (I * Ω) =
        g * g + Ω * Ω) ∧
    (I * I = 1 →
      geometricTensor g (I * Ω) * geometricTensorReverse g (I * Ω) =
        g * g - Ω * Ω ∧
      g * g - Ω * Ω = (g - Ω) * (g + Ω)) ∧
    geometricTensor (genV P A C) (genSig P A C) *
      geometricTensorReverse (genV P A C) (genSig P A C) = 0 := by
  have hComm_gK : g * (I * Ω) = (I * Ω) * g := by
    calc
      g * (I * Ω) = (g * I) * Ω := (mul_assoc g I Ω).symm
      _ = (I * g) * Ω := by rw [hComm_gI]
      _ = I * (g * Ω) := mul_assoc I g Ω
      _ = I * (Ω * g) := by rw [hComm_gΩ]
      _ = (I * Ω) * g := (mul_assoc I Ω g).symm
  have hK2 : (I * Ω) * (I * Ω) = (I * I) * (Ω * Ω) := by
    calc
      (I * Ω) * (I * Ω) = I * (Ω * I) * Ω := by noncomm_ring
      _ = I * (I * Ω) * Ω := by rw [← hComm_IΩ]
      _ = (I * I) * (Ω * Ω) := by noncomm_ring
  have hGen :
      geometricTensor g (I * Ω) * geometricTensorReverse g (I * Ω) =
        g * g - (I * I) * (Ω * Ω) := by
    rw [cliffordKreinModulus g (I * Ω) hComm_gK, hK2]
  refine ⟨hGen, ?_, ?_, ?_⟩
  · intro hEll
    rw [hGen, hEll]
    noncomm_ring
  · intro hHyp
    refine ⟨by rw [hGen, hHyp, one_mul], ?_⟩
    calc
      g * g - Ω * Ω = g * g + g * Ω - Ω * g - Ω * Ω := by rw [hComm_gΩ]; abel
      _ = (g - Ω) * (g + Ω) := by noncomm_ring
  · dsimp [geometricTensor, geometricTensorReverse]
    peirce_nf hP

/-- **Native Mathlib `CliffordAlgebra Q` Reversion & Modulus Bridge**:
In native Mathlib `CliffordAlgebra Q` over `[CommRing R] [AddCommGroup M] [Module R M]`,
for any two vectors `u v : M` that anticommute in `CliffordAlgebra Q`
(`ι Q u * ι Q v + ι Q v * ι Q u = 0`), the bivector `B_uv = ι Q u * ι Q v` satisfies:
1. `CliffordAlgebra.reverse B_uv = -B_uv`,
2. `CliffordAlgebra.reverse (geometricTensor (algebraMap R (CliffordAlgebra Q) g) B_uv) =
   geometricTensorReverse (algebraMap R (CliffordAlgebra Q) g) B_uv`,
3. `geometricTensor (algebraMap R (CliffordAlgebra Q) g) B_uv *
   CliffordAlgebra.reverse (geometricTensor (algebraMap R (CliffordAlgebra Q) g) B_uv) =
   algebraMap R (CliffordAlgebra Q) (g * g) - B_uv * B_uv`. -/
theorem native_cliffordAlgebra_bivector_reverse_and_modulus
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (g : R) (u v : M)
    (h_anticomm : CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v +
      CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u = 0) :
    let B_uv : CliffordAlgebra Q := CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v
    let g_alg : CliffordAlgebra Q := algebraMap R (CliffordAlgebra Q) g
    CliffordAlgebra.reverse B_uv = -B_uv ∧
    CliffordAlgebra.reverse (geometricTensor g_alg B_uv) =
      geometricTensorReverse g_alg B_uv ∧
    geometricTensor g_alg B_uv * CliffordAlgebra.reverse (geometricTensor g_alg B_uv) =
      algebraMap R (CliffordAlgebra Q) (g * g) - B_uv * B_uv := by
  dsimp only
  have hRevB :
      CliffordAlgebra.reverse (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
        -(CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) := by
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_ι]
    exact eq_neg_of_add_eq_zero_right h_anticomm
  have hRevG :
      CliffordAlgebra.reverse (algebraMap R (CliffordAlgebra Q) g) =
        algebraMap R (CliffordAlgebra Q) g :=
    CliffordAlgebra.reverse.commutes g
  have hRevTensor :
      CliffordAlgebra.reverse
        (geometricTensor (algebraMap R (CliffordAlgebra Q) g)
          (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) =
      geometricTensorReverse (algebraMap R (CliffordAlgebra Q) g)
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) := by
    dsimp [geometricTensor, geometricTensorReverse]
    rw [map_add, hRevG, hRevB, sub_eq_add_neg]
  have hMod :
      geometricTensor (algebraMap R (CliffordAlgebra Q) g)
          (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
        CliffordAlgebra.reverse
          (geometricTensor (algebraMap R (CliffordAlgebra Q) g)
            (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) =
      algebraMap R (CliffordAlgebra Q) (g * g) -
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
          (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) := by
    rw [hRevTensor]
    rw [cliffordKreinModulus (algebraMap R (CliffordAlgebra Q) g)
      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)
      (Algebra.commutes g (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v))]
    rw [← map_mul]
  exact ⟨hRevB, hRevTensor, hMod⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.CliffordKreinGeometricUncertaintyPoset
