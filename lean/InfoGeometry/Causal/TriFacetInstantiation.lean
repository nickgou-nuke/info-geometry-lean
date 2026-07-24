import Mathlib
import InfoGeometry.Foundations.AxiomaticDependencyGraph
import InfoGeometry.Causal.CausalAlgebra

open Matrix
open LinearMap

/-!
# TriFacetInstantiation — Abstract Hodge–Krein on the Causal 2×2 Model

This file instantiates the abstract tri-facet decomposition from
`AxiomaticDependencyGraph` (`namespace Audit`) on the concrete 2×2
causal algebra over ℝ from `CausalAlgebra.lean`.

## Key Result

In this model the **harmonic projector is identically zero**:

    P_harmonic = 0

Therefore the tri-facet resolution reduces to P_exact + P_coexact = I,
where:

    P_exact = dℝ   (future / forward cone)
    P_coexact = δℝ (past / backward cone)

This unifies the graph-theoretic (partial order / causal cone) and
operator-algebraic (d, δ) pictures under a single abstract framework.
-/

namespace InfoGeometry.Causal.TriFacetInstantiation

open InfoGeometry.Causal.Algebra
open Audit

/-! ## Section 1: Vector Space — the Carrier -/

/--
The carrier for the 2×2 causal model is the space of functions from
`Fin 2` to ℝ, i.e. ℝ². Linear maps act via 2×2 matrix multiplication.
-/
@[reducible]
noncomputable def V : Type _ := (Fin 2) → ℝ

instance : AddCommGroup V := by
  delta V; infer_instance

noncomputable instance : Module ℝ V := by
  delta V; infer_instance

/-! ## Section 2: Krein Space — Frobenius Inner Product with O-Involution -/

/--
The Frobenius (dot) inner product on ℝ²: B(v,w) = v₀·w₀ + v₁·w₁.
-/
def B (v w : V) : ℝ := v 0 * w 0 + v 1 * w 1

lemma B_add_left (x y z : V) : B (x + y) z = B x z + B y z := by
  simp [B, add_mul, add_add_add_comm]

lemma B_smul_left (c : ℝ) (x y : V) : B (c • x) y = c * B x y := by
  simp [B, smul_eq_mul, mul_add]
  ring

lemma B_comm (x y : V) : B x y = B y x := by
  simp [B, mul_comm]

/-- Computes the 0-entry of Oℝ.mulVec x. -/
lemma O_mulVec_0 (x : V) : (Oℝ.mulVec x) 0 = x 1 := by
  have : Matrix.mulVec Oℝ x = fun i => ∑ j : Fin 2, Oℝ i j * x j := rfl
  calc
    (Oℝ.mulVec x) 0 = (∑ j : Fin 2, Oℝ 0 j * x j) := rfl
    _ = Oℝ 0 0 * x 0 + Oℝ 0 1 * x 1 := by simp [Fin.sum_univ_two]
    _ = (0 : ℝ) * x 0 + (1 : ℝ) * x 1 := by simp [Oℝ]
    _ = x 1 := by ring

/-- Computes the 1-entry of Oℝ.mulVec x. -/
lemma O_mulVec_1 (x : V) : (Oℝ.mulVec x) 1 = x 0 := by
  calc
    (Oℝ.mulVec x) 1 = (∑ j : Fin 2, Oℝ 1 j * x j) := rfl
    _ = Oℝ 1 0 * x 0 + Oℝ 1 1 * x 1 := by simp [Fin.sum_univ_two]
    _ = (1 : ℝ) * x 0 + (0 : ℝ) * x 1 := by simp [Oℝ]
    _ = x 0 := by ring

/--
The Krein involution J is the causal orientation Oℝ acting by matrix
multiplication on column vectors.
-/
noncomputable def J : V →ₗ[ℝ] V :=
  Matrix.toLin' Oℝ

lemma J_sq (x : V) : J (J x) = x := by
  calc
    J (J x) = (Matrix.toLin' (Oℝ * Oℝ)) x := by
      simp [J]
    _ = (Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) ℝ)) x := by rw [Oℝ_mul_Oℝ]
    _ = x := by simp

lemma J_adj (x y : V) : B (J x) y = B x (J y) := by
  unfold J B
  calc
    ((Oℝ.mulVec x) 0) * y 0 + ((Oℝ.mulVec x) 1) * y 1 = (x 1) * y 0 + (x 0) * y 1 := by
      simp [O_mulVec_0, O_mulVec_1]
    _ = x 0 * y 1 + x 1 * y 0 := by ring
    _ = x 0 * ((Oℝ.mulVec y) 0) + x 1 * ((Oℝ.mulVec y) 1) := by
      simp [O_mulVec_0, O_mulVec_1]

/-- The Krein-space instance on V (Audit.Node0_KreinSpace). -/
noncomputable instance : Audit.Node0_KreinSpace V where
  B := B
  B_add_left := B_add_left
  B_smul_left := B_smul_left
  B_comm := B_comm
  J := J
  J_sq := J_sq
  J_adj := J_adj

/-! ## Section 3: Tri-Facet Operator — Oℝ on ℝ² -/

/--
The tri-facet operator O = σ₁ acting on ℝ² via matrix multiplication.
For Oℝ = [[0,1],[1,0]] we have O² = I and therefore O³ = O.
-/
noncomputable def O_op : V →ₗ[ℝ] V :=
  Matrix.toLin' Oℝ

lemma O_sq_eq_id (x : V) : O_op (O_op x) = x :=
  J_sq x

lemma O_cubed (x : V) : O_op (O_op (O_op x)) = O_op x := by
  rw [O_sq_eq_id]

lemma O_adj (x y : V) : B (O_op x) y = B x (O_op y) :=
  J_adj x y

/-- The tri-facet operator instance on V (Audit.Node1_TriFacetOperator). -/
noncomputable instance : Audit.Node1_TriFacetOperator V where
  O := O_op
  O_cubed := O_cubed
  O_adj := O_adj

/-! ## Section 4: Instantiating the Three Projectors -/

/--
The abstract **exact projector** (future cone) equals the concrete
causal forward projector dℝ on ℝ².
-/
theorem exact_projector_eq_dℝ (x : V) :
    Audit.exact_projector (V := V) x = dℝ.mulVec x := by
  unfold Audit.exact_projector
  have h_sq : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) = x := by
    simpa using O_sq_eq_id x
  rw [h_sq]
  have h_O : Node1_TriFacetOperator.O x = Oℝ.mulVec x := by
    simp [Node1_TriFacetOperator.O, O_op, Matrix.toLin'_apply]
  rw [h_O]
  calc
    (1/2 : ℝ) • (x + Oℝ.mulVec x) = (1/2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + Oℝ).mulVec x := by
      simp [Matrix.add_mulVec, Matrix.one_mulVec]
    _ = dℝ.mulVec x := by
      ext i
      fin_cases i <;>
        simp [dℝ, Oℝ, Matrix.mulVec, vecHead, vecTail]
      all_goals ring

/--
The abstract **coexact projector** (past cone) equals the concrete
causal backward projector δℝ on ℝ².
-/
theorem coexact_projector_eq_δℝ (x : V) :
    Audit.coexact_projector (V := V) x = δℝ.mulVec x := by
  unfold Audit.coexact_projector
  have h_sq : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) = x := by
    simpa using O_sq_eq_id x
  rw [h_sq]
  have h_O : Node1_TriFacetOperator.O x = Oℝ.mulVec x := by
    simp [Node1_TriFacetOperator.O, O_op, Matrix.toLin'_apply]
  rw [h_O]
  calc
    (1/2 : ℝ) • (x - Oℝ.mulVec x) = (1/2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) - Oℝ).mulVec x := by
      simp [Matrix.sub_mulVec, Matrix.one_mulVec]
    _ = δℝ.mulVec x := by
      ext i
      fin_cases i <;>
        simp [δℝ, Oℝ, Matrix.mulVec, vecHead, vecTail]
      all_goals ring

/--
The abstract **harmonic projector** is identically zero on the 2×2
causal model. Proof: Since O² = I, we have O(O(x)) = x, so x - O(O(x)) = 0.
-/
theorem harmonic_projector_zero (x : V) :
    Audit.harmonic_projector (V := V) x = 0 := by
  unfold Audit.harmonic_projector
  have h_sq : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) = x := by
    simpa using O_sq_eq_id x
  rw [h_sq, sub_self]

/--
**Corollary**: The tri-facet resolution on the 2×2 causal model reduces
to `dℝ + δℝ = I`, i.e. every edge is oriented.
-/
theorem tri_facet_resolution_simplifies (x : V) :
    Audit.exact_projector (V := V) x + Audit.coexact_projector (V := V) x = x := by
  rw [exact_projector_eq_dℝ, coexact_projector_eq_δℝ, ← Matrix.add_mulVec,
    dℝ_add_δℝ_eq_one, Matrix.one_mulVec]

/-! ## Section 5: Nilpotent Shear — The Zero Shear -/

/-- The zero nilpotent shear on the 2×2 causal model. -/
noncomputable instance : Audit.Node3_NilpotentShear V :=
  Audit.nilpotentShearZero (V := V)

/-! ## Section 6: Summary Theorem — Full Unification -/

/--
**Full unification**: On the 2×2 causal model over ℝ:

  - P_exact = dℝ  (forward cone — proved dependencies)
  - P_coexact = δℝ (backward cone — certificate holes)
  - P_harmonic = 0 (no harmonic component)
-/
theorem tri_facet_causal_unification :
    (∀ x : V, Audit.exact_projector (V := V) x = dℝ.mulVec x) ∧
    (∀ x : V, Audit.coexact_projector (V := V) x = δℝ.mulVec x) ∧
    (∀ x : V, Audit.harmonic_projector (V := V) x = 0) :=
  ⟨exact_projector_eq_dℝ, coexact_projector_eq_δℝ, harmonic_projector_zero⟩

/--
The abstract coexact projector and the causal backward projector δℝ
agree as linear maps on ℝ².
-/
theorem abstract_δ_eq_causal_δ :
    (Audit.coexact_projector_lin (V := V) : V →ₗ[ℝ] V) = Matrix.toLin' δℝ := by
  ext x; simp [Audit.coexact_projector_lin, coexact_projector_eq_δℝ, Matrix.toLin'_apply]

end InfoGeometry.Causal.TriFacetInstantiation
