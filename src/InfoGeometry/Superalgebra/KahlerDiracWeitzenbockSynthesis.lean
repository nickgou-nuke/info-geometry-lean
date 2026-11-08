import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# Exterior CAR, Chevalley Action, and Finite Operator Identities

This module proves algebraic exterior-algebra CAR and Chevalley-action
identities, conditional identities for endomorphisms satisfying square-zero
hypotheses, a two-generator operator expansion, and finite-index contraction
identities. The operator results do not construct a manifold, differential
forms, a metric connection, scalar curvature, a Bismut connection, or a Ricci
flow. In particular, the two-generator expansion is not the geometric
Lichnerowicz formula, and the final matrix-valued formula is not a derived
Bismut–Perelman tensor.

## Main Definitions and Theorems

1. **Archetype I (Exterior Wedge & Interior Contraction CAR Algebra)**:
   * `exteriorWedge`, `exteriorContract`
   * `exteriorWedge_sq`, `exteriorContract_sq`
   * `exteriorWedge_anticomm`, `exteriorContract_anticomm`
   * `exteriorContract_wedge_apply`, `exterior_cartan_homotopy_car`
2. **Archetype II (Chevalley Cliffordization of the Exterior Bundle)**:
   * `chevalleyAction`
   * `chevalleyAction_one`, `chevalleyAction_iota`
   * `chevalleyAction_sq`, `chevalleyAction_anticomm`
3. **Archetype III (Square-Zero Endomorphisms and Their Laplacian Identity)**:
   * `kahlerDirac`, `cliffordDiracSub`, `hodgeLaplacian`
   * `kahlerDirac_sq_expansion`, `kahlerDirac_sq_eq_hodgeLaplacian`,
     `cliffordDiracSub_sq_eq_neg_hodgeLaplacian`
   * `hodgeLaplacian_comm_d`, `hodgeLaplacian_comm_delta`,
     `kahlerDirac_comm_hodgeLaplacian`, `kahlerDirac_harmonic_imp_hodge_harmonic`
4. **Archetype IV (Two-Generator Endomorphism Expansion)**:
   * `diracOperator`, `bochnerLaplacian₂`, `curvatureCommutator`, `diracOperator₂`
   * `diracOperator₂_sq_weitzenbock`, `dirac_sq_remainder_decomposition`,
     `dirac_sq_scalar_remainder_apply`
5. **Archetype V (Finite Quadratic Contraction and Weighted Matrix Formula)**:
   * `finiteQuadraticTensorContraction`, `weightedRicciHessianTensor`
   * `finiteQuadraticTensorContraction_symm`, `finiteQuadraticTensorContraction_diag_nonneg`
   * `weightedRicciHessianTensor_isSymm`, `weightedRicciHessianTensor_zero_corrections`
-/

noncomputable section

namespace InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis

variable (R : Type*) [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Ω : Type*} [AddCommGroup Ω] [Module R Ω]

/-!
## Archetype I: Exterior Wedge & Interior Contraction CAR Algebra on `ExteriorAlgebra R M`
-/

/-- Exterior wedge creation operator `v ∧ -` on `ExteriorAlgebra R M`. -/
def exteriorWedge (v : M) : Module.End R (ExteriorAlgebra R M) :=
  Algebra.lmul R (ExteriorAlgebra R M) (ExteriorAlgebra.ι R v)

/-- Interior contraction annihilation operator `φ ⌟ -` on `ExteriorAlgebra R M`,
realized via left contraction on `CliffordAlgebra (0 : QuadraticForm R M)`. -/
def exteriorContract {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) : Module.End R (ExteriorAlgebra R M) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ

@[simp]
theorem exteriorWedge_apply (v : M) (ω : ExteriorAlgebra R M) :
    exteriorWedge R v ω = ExteriorAlgebra.ι R v * ω := rfl

@[simp]
theorem exteriorContract_one {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) :
    exteriorContract φ 1 = 0 :=
  CliffordAlgebra.contractLeft_one (0 : QuadraticForm R M) φ

/-- Nilpotency of the exterior wedge operator: `(v ∧ -)² = 0`. -/
@[simp]
theorem exteriorWedge_sq (v : M) :
    exteriorWedge R v * exteriorWedge R v = 0 := by
  apply LinearMap.ext
  intro ω
  change ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R v * ω) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- Nilpotency of the interior contraction operator: `(φ ⌟ -)² = 0`. -/
@[simp]
theorem exteriorContract_sq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) :
    exteriorContract φ * exteriorContract φ = 0 := by
  apply LinearMap.ext
  intro ω
  exact CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm R M)) φ ω

/-- Exterior wedge operators anticommute: `e_v e_u + e_u e_v = 0`. -/
theorem exteriorWedge_anticomm (v u : M) :
    exteriorWedge R v * exteriorWedge R u + exteriorWedge R u * exteriorWedge R v = 0 := by
  apply LinearMap.ext
  intro ω
  change ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R u * ω) +
      ExteriorAlgebra.ι R u * (ExteriorAlgebra.ι R v * ω) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

/-- Interior contraction operators anticommute: `i_φ i_ψ + i_ψ i_φ = 0`. -/
theorem exteriorContract_anticomm {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (φ ψ : Module.Dual R M) :
    exteriorContract φ * exteriorContract ψ + exteriorContract ψ * exteriorContract φ = 0 := by
  apply LinearMap.ext
  intro ω
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) ψ ω) +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) ψ
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ ω) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

/-- Graded Leibniz rule for interior contraction across an exterior wedge product. -/
@[simp]
theorem exteriorContract_wedge_apply {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) (v : M) (ω : ExteriorAlgebra R M) :
    exteriorContract φ (exteriorWedge R v ω) =
      φ v • ω - exteriorWedge R v (exteriorContract φ ω) := by
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
      (ExteriorAlgebra.ι R v * ω) = _
  rw [CliffordAlgebra.contractLeft_ι_mul]
  rfl

/-- Interior contraction of a 1-form `ι R u` evaluates the covector `φ` on `u`. -/
@[simp]
theorem exteriorContract_iota {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) (u : M) :
    exteriorContract φ (ExteriorAlgebra.ι R u) = (φ u) • (1 : ExteriorAlgebra R M) := by
  have h : ExteriorAlgebra.ι R u = exteriorWedge R u 1 := (mul_one _).symm
  rw [h, exteriorContract_wedge_apply, exteriorContract_one, map_zero, sub_zero]

/-- Canonical Anticommutation Relation (Cartan homotopy formula for wedge and contraction):
`i_φ e_v + e_v i_φ = φ(v) • 1`. -/
theorem exterior_cartan_homotopy_car {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) (v : M) :
    exteriorContract φ * exteriorWedge R v + exteriorWedge R v * exteriorContract φ =
      (φ v) • (1 : Module.End R (ExteriorAlgebra R M)) := by
  apply LinearMap.ext
  intro ω
  change exteriorContract φ (exteriorWedge R v ω) + exteriorWedge R v (exteriorContract φ ω) =
    φ v • ω
  rw [exteriorContract_wedge_apply, sub_add_cancel]

/-- Concrete creation operator used in the noncommutativity witness. -/
noncomputable def exteriorCreationWitnessOperator :
    Module.End ℝ (ExteriorAlgebra ℝ ℝ) := exteriorWedge ℝ (1 : ℝ)

/-- Concrete contraction operator used in the noncommutativity witness. -/
noncomputable def exteriorContractionWitnessOperator :
    Module.End ℝ (ExteriorAlgebra ℝ ℝ) :=
  exteriorContract (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

/-- A concrete noncommutativity witness for the exterior creation and
contraction operators. Evaluating the two compositions on the unit separates
them, so the operator carrier is not being treated as a scalar surrogate. -/
theorem exteriorContract_wedge_noncommute_witness :
    exteriorContractionWitnessOperator * exteriorCreationWitnessOperator ≠
      exteriorCreationWitnessOperator * exteriorContractionWitnessOperator := by
  intro h
  simp only [exteriorContractionWitnessOperator, exteriorCreationWitnessOperator] at h
  have hEval := congrArg
    (fun f : Module.End ℝ (ExteriorAlgebra ℝ ℝ) => f 1) h
  simp [Module.End.mul_apply, exteriorWedge_apply,
    exteriorContract_iota, exteriorContract_one] at hEval

/-!
## Archetype II: Chevalley Cliffordization of the Exterior Bundle (`u v = u ∧ v + u ⌟ v`)
-/

/-- The Chevalley Clifford action of a vector-covector pair `(v, φ)` on `ExteriorAlgebra R M`,
combining exterior creation and interior annihilation: `c(v, φ) = (v ∧ -) + (φ ⌟ -)`. -/
def chevalleyAction {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (v : M) (φ : Module.Dual R M) : Module.End R (ExteriorAlgebra R M) :=
  exteriorWedge R v + exteriorContract φ

/-- Acting with the Chevalley Clifford operator on the vacuum `1` creates the 1-form `ι R v`. -/
@[simp]
theorem chevalleyAction_one {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (v : M) (φ : Module.Dual R M) :
    chevalleyAction v φ 1 = ExteriorAlgebra.ι R v := by
  change exteriorWedge R v 1 + exteriorContract φ 1 = ExteriorAlgebra.ι R v
  rw [exteriorWedge_apply, mul_one, exteriorContract_one, add_zero]

/-- Acting with the Chevalley Clifford operator on a 1-form `ι R u` decomposes into the
exterior bivector `v ∧ u` plus the scalar contraction `φ(u) • 1` (`u v = u ∧ v + u ⋅ v`). -/
theorem chevalleyAction_iota {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (v u : M) (φ : Module.Dual R M) :
    chevalleyAction v φ (ExteriorAlgebra.ι R u) =
      ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u + (φ u) • (1 : ExteriorAlgebra R M) := by
  change exteriorWedge R v (ExteriorAlgebra.ι R u) + exteriorContract φ (ExteriorAlgebra.ι R u) = _
  rw [exteriorWedge_apply, exteriorContract_iota]

/-- The Chevalley Clifford square law: `c(v, φ)² = φ(v) • 1`. -/
theorem chevalleyAction_sq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (v : M) (φ : Module.Dual R M) :
    chevalleyAction v φ * chevalleyAction v φ =
      (φ v) • (1 : Module.End R (ExteriorAlgebra R M)) := by
  calc
    chevalleyAction v φ * chevalleyAction v φ =
        exteriorWedge R v * exteriorWedge R v +
          (exteriorContract φ * exteriorWedge R v + exteriorWedge R v * exteriorContract φ) +
          exteriorContract φ * exteriorContract φ := by
      simp only [chevalleyAction, add_mul, mul_add]
      abel
    _ = (φ v) • (1 : Module.End R (ExteriorAlgebra R M)) := by
      rw [exteriorWedge_sq, exteriorContract_sq, exterior_cartan_homotopy_car, zero_add, add_zero]

/-- Polarized two-direction Chevalley Clifford anticommutator:
`c(v, φ) c(u, ψ) + c(u, ψ) c(v, φ) = (φ(u) + ψ(v)) • 1`. -/
theorem chevalleyAction_anticomm {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (v u : M) (φ ψ : Module.Dual R M) :
    chevalleyAction v φ * chevalleyAction u ψ + chevalleyAction u ψ * chevalleyAction v φ =
      (φ u + ψ v) • (1 : Module.End R (ExteriorAlgebra R M)) := by
  calc
    chevalleyAction v φ * chevalleyAction u ψ + chevalleyAction u ψ * chevalleyAction v φ =
        (exteriorWedge R v * exteriorWedge R u + exteriorWedge R u * exteriorWedge R v) +
        (exteriorContract φ * exteriorWedge R u + exteriorWedge R u * exteriorContract φ) +
        (exteriorContract ψ * exteriorWedge R v + exteriorWedge R v * exteriorContract ψ) +
        (exteriorContract φ * exteriorContract ψ + exteriorContract ψ * exteriorContract φ) := by
      simp only [chevalleyAction, add_mul, mul_add]
      abel
    _ = (φ u + ψ v) • (1 : Module.End R (ExteriorAlgebra R M)) := by
      rw [exteriorWedge_anticomm, exteriorContract_anticomm,
        exterior_cartan_homotopy_car φ u, exterior_cartan_homotopy_car ψ v,
        zero_add, add_zero, add_smul]

/-!
## Archetype III: Kähler–Dirac Operator `D = d + δ` and Hodge Laplacian `Δ = (d + δ)²`
-/

variable {R}

/-- The Kähler–Dirac operator `D = d + δ` built from coboundary `d` and codifferential `δ`. -/
def kahlerDirac (d δ : Module.End R Ω) : Module.End R Ω :=
  d + δ

/-- The skew-adjoint Clifford–Dirac operator `D_- = d - δ`. -/
def cliffordDiracSub (d δ : Module.End R Ω) : Module.End R Ω :=
  d - δ

/-- The Hodge Laplacian `Δ = d δ + δ d` (anticommutator of `d` and `δ`). -/
def hodgeLaplacian (d δ : Module.End R Ω) : Module.End R Ω :=
  d * δ + δ * d

/-- Full operator expansion of `(d + δ)²` prior to imposing nilpotency of `d` and `δ`. -/
theorem kahlerDirac_sq_expansion (d δ : Module.End R Ω) :
    kahlerDirac d δ * kahlerDirac d δ = d * d + hodgeLaplacian d δ + δ * δ := by
  simp only [kahlerDirac, hodgeLaplacian, add_mul, mul_add]
  abel

/-- When `d² = 0` and `δ² = 0`, the square of the Kähler–Dirac operator `D = d + δ` is
identically the Hodge Laplacian `Δ = d δ + δ d`. -/
theorem kahlerDirac_sq_eq_hodgeLaplacian (d δ : Module.End R Ω)
    (hd : d * d = 0) (hδ : δ * δ = 0) :
    kahlerDirac d δ * kahlerDirac d δ = hodgeLaplacian d δ := by
  rw [kahlerDirac_sq_expansion, hd, hδ, zero_add, add_zero]

/-- When `d² = 0` and `δ² = 0`, the square of `d - δ` is `-Δ = -(d δ + δ d)`. -/
theorem cliffordDiracSub_sq_eq_neg_hodgeLaplacian (d δ : Module.End R Ω)
    (hd : d * d = 0) (hδ : δ * δ = 0) :
    cliffordDiracSub d δ * cliffordDiracSub d δ = - hodgeLaplacian d δ := by
  calc
    cliffordDiracSub d δ * cliffordDiracSub d δ =
        d * d - (d * δ + δ * d) + δ * δ := by
      simp only [cliffordDiracSub, sub_mul, mul_sub]
      abel
    _ = - hodgeLaplacian d δ := by
      rw [hd, hδ, zero_sub, add_zero, hodgeLaplacian]

/-- The Hodge Laplacian commutes with the exterior derivative `d` whenever `d² = 0`. -/
theorem hodgeLaplacian_comm_d (d δ : Module.End R Ω) (hd : d * d = 0) :
    hodgeLaplacian d δ * d = d * hodgeLaplacian d δ := by
  calc
    hodgeLaplacian d δ * d = d * δ * d + δ * (d * d) := by
      simp only [hodgeLaplacian, add_mul, mul_assoc]
    _ = (d * d) * δ + d * (δ * d) := by
      rw [hd, mul_zero, zero_mul, add_zero, zero_add, mul_assoc]
    _ = d * hodgeLaplacian d δ := by
      simp only [hodgeLaplacian, mul_add, mul_assoc]

/-- The Hodge Laplacian commutes with the codifferential `δ` whenever `δ² = 0`. -/
theorem hodgeLaplacian_comm_delta (d δ : Module.End R Ω) (hδ : δ * δ = 0) :
    hodgeLaplacian d δ * δ = δ * hodgeLaplacian d δ := by
  calc
    hodgeLaplacian d δ * δ = d * (δ * δ) + δ * d * δ := by
      simp only [hodgeLaplacian, add_mul, mul_assoc]
    _ = δ * (d * δ) + (δ * δ) * d := by
      rw [hδ, mul_zero, zero_mul, zero_add, add_zero, mul_assoc]
    _ = δ * hodgeLaplacian d δ := by
      simp only [hodgeLaplacian, mul_add, mul_assoc]

/-- The Kähler–Dirac operator commutes with the Hodge Laplacian. -/
theorem kahlerDirac_comm_hodgeLaplacian (d δ : Module.End R Ω)
    (hd : d * d = 0) (hδ : δ * δ = 0) :
    kahlerDirac d δ * hodgeLaplacian d δ = hodgeLaplacian d δ * kahlerDirac d δ := by
  simp only [kahlerDirac, add_mul, mul_add,
    ← hodgeLaplacian_comm_d d δ hd, ← hodgeLaplacian_comm_delta d δ hδ]

/-- Every Kähler–Dirac harmonic form (`(d + δ) ω = 0`) is Hodge harmonic (`Δ ω = 0`). -/
theorem kahlerDirac_harmonic_imp_hodge_harmonic (d δ : Module.End R Ω)
    (hd : d * d = 0) (hδ : δ * δ = 0) (ω : Ω) (hω : kahlerDirac d δ ω = 0) :
    hodgeLaplacian d δ ω = 0 := by
  rw [← kahlerDirac_sq_eq_hodgeLaplacian d δ hd hδ, Module.End.mul_apply, hω, map_zero]

/-!
## Archetype IV: Two-Generator Endomorphism Expansion
-/

/-- Finite sum of products in an endomorphism algebra. No geometric frame is
part of this definition. -/
def diracOperator {ι : Type*} [Fintype ι] (γ covDeriv : ι → Module.End R Ω) : Module.End R Ω :=
  ∑ i : ι, γ i * covDeriv i

/-- Two-direction Bochner rough Laplacian `∇₁² + ∇₂²`. -/
def bochnerLaplacian₂ (covDeriv₁ covDeriv₂ : Module.End R Ω) : Module.End R Ω :=
  covDeriv₁ * covDeriv₁ + covDeriv₂ * covDeriv₂

/-- Covariant curvature commutator `R₁₂ = [∇₁, ∇₂] = ∇₁ ∇₂ - ∇₂ ∇₁`. -/
def curvatureCommutator (covDeriv₁ covDeriv₂ : Module.End R Ω) : Module.End R Ω :=
  covDeriv₁ * covDeriv₂ - covDeriv₂ * covDeriv₁

/-- Two-term endomorphism expression `D₂ = γ₁ A₁ + γ₂ A₂`. -/
def diracOperator₂ (γ₁ γ₂ covDeriv₁ covDeriv₂ : Module.End R Ω) : Module.End R Ω :=
  γ₁ * covDeriv₁ + γ₂ * covDeriv₂

/-- Two-generator endomorphism identity under the stated square, anticommutation,
and commutation hypotheses. Its commutator term is an algebraic rearrangement;
this theorem does not assert the geometric Lichnerowicz formula. -/
theorem diracOperator₂_sq_weitzenbock (γ₁ γ₂ covDeriv₁ covDeriv₂ : Module.End R Ω)
    (hγ1 : γ₁ * γ₁ = 1) (hγ2 : γ₂ * γ₂ = 1)
    (hanticomm : γ₁ * γ₂ + γ₂ * γ₁ = 0)
    (hcomm11 : covDeriv₁ * γ₁ = γ₁ * covDeriv₁) (hcomm12 : covDeriv₁ * γ₂ = γ₂ * covDeriv₁)
    (hcomm21 : covDeriv₂ * γ₁ = γ₁ * covDeriv₂) (hcomm22 : covDeriv₂ * γ₂ = γ₂ * covDeriv₂) :
    diracOperator₂ γ₁ γ₂ covDeriv₁ covDeriv₂ * diracOperator₂ γ₁ γ₂ covDeriv₁ covDeriv₂ =
      bochnerLaplacian₂ covDeriv₁ covDeriv₂ + (γ₁ * γ₂) * curvatureCommutator covDeriv₁ covDeriv₂ := by
  have hγ21 : γ₂ * γ₁ = -(γ₁ * γ₂) := by
    calc
      γ₂ * γ₁ = (γ₁ * γ₂ + γ₂ * γ₁) - γ₁ * γ₂ := by abel
      _ = -(γ₁ * γ₂) := by rw [hanticomm, zero_sub]
  have h11 : (γ₁ * covDeriv₁) * (γ₁ * covDeriv₁) = covDeriv₁ * covDeriv₁ := by
    calc
      (γ₁ * covDeriv₁) * (γ₁ * covDeriv₁) = γ₁ * (covDeriv₁ * γ₁) * covDeriv₁ := by simp only [mul_assoc]
      _ = (γ₁ * γ₁) * (covDeriv₁ * covDeriv₁) := by rw [hcomm11]; simp only [mul_assoc]
      _ = covDeriv₁ * covDeriv₁ := by rw [hγ1, one_mul]
  have h22 : (γ₂ * covDeriv₂) * (γ₂ * covDeriv₂) = covDeriv₂ * covDeriv₂ := by
    calc
      (γ₂ * covDeriv₂) * (γ₂ * covDeriv₂) = γ₂ * (covDeriv₂ * γ₂) * covDeriv₂ := by simp only [mul_assoc]
      _ = (γ₂ * γ₂) * (covDeriv₂ * covDeriv₂) := by rw [hcomm22]; simp only [mul_assoc]
      _ = covDeriv₂ * covDeriv₂ := by rw [hγ2, one_mul]
  have h12 : (γ₁ * covDeriv₁) * (γ₂ * covDeriv₂) = (γ₁ * γ₂) * (covDeriv₁ * covDeriv₂) := by
    calc
      (γ₁ * covDeriv₁) * (γ₂ * covDeriv₂) = γ₁ * (covDeriv₁ * γ₂) * covDeriv₂ := by simp only [mul_assoc]
      _ = (γ₁ * γ₂) * (covDeriv₁ * covDeriv₂) := by rw [hcomm12]; simp only [mul_assoc]
  have h21 : (γ₂ * covDeriv₂) * (γ₁ * covDeriv₁) = -((γ₁ * γ₂) * (covDeriv₂ * covDeriv₁)) := by
    calc
      (γ₂ * covDeriv₂) * (γ₁ * covDeriv₁) = γ₂ * (covDeriv₂ * γ₁) * covDeriv₁ := by simp only [mul_assoc]
      _ = (γ₂ * γ₁) * (covDeriv₂ * covDeriv₁) := by rw [hcomm21]; simp only [mul_assoc]
      _ = -((γ₁ * γ₂) * (covDeriv₂ * covDeriv₁)) := by rw [hγ21, neg_mul]
  calc
    diracOperator₂ γ₁ γ₂ covDeriv₁ covDeriv₂ * diracOperator₂ γ₁ γ₂ covDeriv₁ covDeriv₂ =
        (γ₁ * covDeriv₁) * (γ₁ * covDeriv₁) + (γ₂ * covDeriv₂) * (γ₂ * covDeriv₂) +
          ((γ₁ * covDeriv₁) * (γ₂ * covDeriv₂) + (γ₂ * covDeriv₂) * (γ₁ * covDeriv₁)) := by
      simp only [diracOperator₂, add_mul, mul_add]
      abel
    _ = bochnerLaplacian₂ covDeriv₁ covDeriv₂ + (γ₁ * γ₂) * curvatureCommutator covDeriv₁ covDeriv₂ := by
      rw [h11, h22, h12, h21, bochnerLaplacian₂, curvatureCommutator, mul_sub, sub_eq_add_neg]

/-- Decompose any endomorphism square into a chosen summand and its remainder. -/
theorem dirac_sq_remainder_decomposition (D bochnerLaplacian : Module.End R Ω) :
    D * D = bochnerLaplacian + (D * D - bochnerLaplacian) :=
  (add_sub_cancel bochnerLaplacian (D * D)).symm

/-- If the remainder is assumed to be a scalar multiple of the identity, its
action is multiplication by that scalar. This assumes the scalar identification
rather than deriving curvature from geometric data. -/
theorem dirac_sq_scalar_remainder_apply (D bochnerLaplacian : Module.End R Ω) (κ : R)
    (hκ : D * D - bochnerLaplacian = κ • (1 : Module.End R Ω)) (ψ : Ω) :
    (D * D) ψ = bochnerLaplacian ψ + κ • ψ := by
  have hD : D * D = bochnerLaplacian + κ • (1 : Module.End R Ω) := by
    rw [dirac_sq_remainder_decomposition D bochnerLaplacian, hκ]
  rw [hD, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]

/-!
## Archetype V: Finite Quadratic Contraction and Weighted Matrix Formula
-/

/-- Finite-index quadratic contraction `Cᵢⱼ = ∑ₖₗ Hᵢₖₗ Hⱼₖₗ` of an arbitrary
three-index function. No differential-form or metric structure is assumed. -/
def finiteQuadraticTensorContraction {n : Type*} [Fintype n]
    (H : n → n → n → R) (i j : n) : R :=
  ∑ k : n, ∑ l : n, H i k l * H j k l

/-- The finite quadratic contraction is symmetric in its two free indices. -/
theorem finiteQuadraticTensorContraction_symm {n : Type*} [Fintype n]
    (H : n → n → n → R) (i j : n) :
    finiteQuadraticTensorContraction H i j = finiteQuadraticTensorContraction H j i := by
  unfold finiteQuadraticTensorContraction
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  exact mul_comm (H i k l) (H j k l)

/-- Over a linearly ordered commutative ring, diagonal entries of this
contraction are nonnegative sums of squares. -/
theorem finiteQuadraticTensorContraction_diag_nonneg {S : Type*}
    [CommRing S] [LinearOrder S]
    [IsStrictOrderedRing S] {n : Type*} [Fintype n] (H : n → n → n → S) (i : n) :
    0 ≤ finiteQuadraticTensorContraction H i i := by
  unfold finiteQuadraticTensorContraction
  refine Finset.sum_nonneg fun k _ => ?_
  refine Finset.sum_nonneg fun l _ => ?_
  exact mul_self_nonneg (H i k l)

/-- A componentwise weighted combination of an input matrix, the finite
quadratic contraction, and a second input matrix. -/
def weightedRicciHessianTensor {n : Type*} [Fintype n]
    (ricci hessPhi : Matrix n n R) (H : n → n → n → R) (cH cPhi : R) : Matrix n n R :=
  fun i j => ricci i j - cH * finiteQuadraticTensorContraction H i j + cPhi * hessPhi i j

/-- If the input matrices are symmetric, their weighted combination with the
finite quadratic contraction is symmetric. -/
theorem weightedRicciHessianTensor_isSymm {n : Type*} [Fintype n]
    (ricci hessPhi : Matrix n n R) (H : n → n → n → R) (cH cPhi : R)
    (hRic : ricci.IsSymm) (hHess : hessPhi.IsSymm) :
    (weightedRicciHessianTensor ricci hessPhi H cH cPhi).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [weightedRicciHessianTensor, hRic.apply i j, hHess.apply i j,
    finiteQuadraticTensorContraction_symm H j i]

/-- If both correction inputs vanish, the weighted matrix formula reduces to
the first input matrix. -/
@[simp]
theorem weightedRicciHessianTensor_zero_corrections {n : Type*} [Fintype n]
    (ricci : Matrix n n R) (cH cPhi : R) :
    weightedRicciHessianTensor ricci 0 (fun _ _ _ => (0 : R)) cH cPhi = ricci := by
  ext i j
  simp [weightedRicciHessianTensor, finiteQuadraticTensorContraction]

end InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
