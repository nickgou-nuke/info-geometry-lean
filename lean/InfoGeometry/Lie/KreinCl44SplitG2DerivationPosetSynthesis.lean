/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Lie.SplitG2RealFormCapstone
import InfoGeometry.Lie.KantorTKKFiveGrading
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.Clifford
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Tactic

/-!
# Double-Real Krein `Cl(4,4)`, Explicit Split `g_{2(2)}` Stabilizer, Matrix Lie Group $G_{2(2)} \le \mathrm{GL}_{16}(\mathbb{R})$, Genuine `FreeLieAlgebra` 294-Lyndon Basis & 15-Node Causal Poset

Formalizes the complete algebraic, Clifford–Krein, Cartan-triality, split exceptional Lie algebra,
matrix Lie group exponential, genuine Mathlib `FreeLieAlgebra ℝ (Fin 4)` 294-element Shirshov–Lyndon
pigeonhole, and causal-poset spine in complete, Mathlib-rooted Lean 4 code:

1. **Section 1 — Universal First-Order Derivation Algebra, Second-Order Leibniz Defect & Jacobi Ceiling**:
   - Proves Lie bracket closure `[D₁, D₂]` of product derivations over arbitrary bilinear products `B`
     (including non-associative ones);
   - Computes the exact Jordan anticommutator defect `leibnizDefect B (D₁.comp D₂ + D₂.comp D₁)` and
     derivation-square defect `leibnizDefect B (D.comp D) x y = (2 : R) • B (D x) (D y)`;
   - Exhibits a concrete `Matrix (Fin 2) (Fin 2) ℝ` witness `innerDerivationWitness` where `D ∈ der`
     but `D² ∉ der`;
   - Proves `ax4_associative_jacobi_ceiling`: associative matrix commutators satisfy the Jacobi
     identity identically.

2. **Section 2 — Double-Real Krein Spinor Module `Krein16Idx`, `Cl(4,4)`, `Γ_{4,4}`, `kreinMetric88` & Orthogonal Bivector Shear**:
   - Constructs `Cl(4,4)` inside `Matrix Krein16Idx Krein16Idx ℝ` (`finrank = 256`) via 4-factor
     Jordan–Wigner Kronecker products `tensor4` of `2 × 2` real blocks;
   - Establishes `Γ_{4,4}` (`gamma44^2 = 1`, `trace = 0`, anticommuting with all 8 generators) and
     the double-real Krein metric `kreinMetric88` (`ᵀ = id`, `^2 = 1`, `trace = 0`, `[kreinMetric88, gamma44] = 0`);
   - Proves all 8 vector generators are Krein-symmetric and all 28 bivectors are chiral-even and
     Krein-skew, plus the orthogonal shear law between the Lie commutator and Jordan anticommutator.

3. **Section 3 — Cartan `S₃` Triality on `ℝ⁴` & 2D Fixed Split Cartan**:
   - Realizes the Hadamard swap `trialitySwapVS` and spinor swap `trialitySwapSpin` generating `S₃`
     on `Fin 4 → ℝ` and proves the fixed Cartan subspace `{v | v 3 = 0 ∧ v 0 = v 1 + v 2}` has `finrank = 2`.

4. **Section 4 — Explicit 14-Dimensional Split `g_{2(2)}` Subalgebra, Faithful `so(4,4)` `LieHom`, & Matrix Lie Group `SplitG2MatrixGroup ≤ GL₁₆(ℝ)`**:
   - Constructs the extremal Majorana–Weyl spinor `majoranaRefSpinor` (`<ψ₊, kreinMetric88 ψ₊> = 2`),
     exhibits all 14 integer-entry basis matrices `g2Basis : Fin 14 → Matrix Krein16Idx Krein16Idx ℝ`,
     verifies `IsSplitG2Stabilizer`, the 5-grading `[-2, -1, 0, +1, +2]`, the Cartan ratio `3`
     (`[X₃, X₄] = 3 • Z_{+2}` vs. `[X₁, X₂] = Z_{+2}`), all 5 Serre syzygies, the vertical Jordan
     jump `{X₁, X₂} ∉ g2Submodule`, linear independence via 14 unique pivot entries (`finrank = 14`),
     compatibility with `InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations`, full
     91-pair Lie bracket closure, and triviality of the center (`g2Submodule_center_trivial`);
   -Packages `g2LieSubalgebra : LieSubalgebra ℝ M₁₆(ℝ)` and injective `g2RhoVec8LieHom`, constructs the
     matrix Lie group `SplitG2MatrixGroup : Subgroup (Matrix.GeneralLinearGroup Krein16Idx ℝ)`,
     integrates `expMat16GL Z t ∈ SplitG2MatrixGroup` via `NormedSpace.exp`, proves global Clifford-to-`SO(4,4)`
     adjoint exponential intertwining, recovers the tangent Lie algebra via `HasDerivAt` at `t = 0`,
     and bridges to `SplitG2RealFormCapstone.split_g2_derivation_exponential_is_real_automorphism`.

5. **Section 5 — Witt Free Lie Dimension Formula, Genuine `FreeLieAlgebra ℝ (Fin 4)` 294-Element Shirshov–Lyndon Basis & Universal `FreeLieAlgebra.lift` Syzygies**:
   - Computes `wittFreeLieDim 4 n` for `n = 1..5` (`[4, 6, 20, 60, 204]`, sum `= 294`) using Mathlib's
     `ArithmeticFunction.moebius` (`μ`);
   - Realizes all `4 + 6 + 20 + 60 + 204 = 294` explicit Shirshov–Lyndon elements `lyndonFreeLie4 : Fin 294 → FreeLieAlgebra ℝ (Fin 4)`,
     proves `LinearIndependent ℝ lyndonFreeLie4` via the Magnus/prepend-endomorphism functional
     `FreeLieAlgebra.lift ℝ prependWordOp`, proves no `FreeLieAlgebra.lift ℝ f : FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ M₁₆(ℝ)`
     can be injective (`ker ≠ ⊥` and 5-step syzygy `finrank ≥ 38` universally), and proves exact 5-step
     syzygy `finrank = 289` on the Chevalley generator assignment `![g2X1, g2X2, g2X3, g2X4]` (including
     the explicit nonzero Serre relation `3 • ⁅x₀, x₁⁆ - ⁅x₂, x₃⁆ ∈ ker`).

6. **Section 6 — 15-Element Graded Acyclic Causal Poset & Master `Ξ_⊤` Coagulation**:
   - Formalizes `KreinG2CausalNode` with 15 nodes across grades `0..6`, proves strict grade monotonicity,
     minimal Hasse covering (`covers_transitively_reduced`), verified antichains, boundedness, and
     `IsLUB {H, E} Xi_top`, then registers and audits all QMS `TypedArchetype`s (`[propext, Classical.choice, Quot.sound]`).

Scope barrier: This module formalizes finite-dimensional Clifford/Krein spinors, the matrix Lie subgroup
`SplitG2MatrixGroup ≤ GL₁₆(ℝ)` with its 1-parameter `NormedSpace.exp` subgroup and `HasDerivAt` tangent recovery,
and the cumulative 5-step `294`-element Shirshov–Lyndon subspace inside `FreeLieAlgebra ℝ (Fin 4)`; it does not
equip `SplitG2MatrixGroup` with an abstract `Manifold`/`LieGroup` atlas or classify infinite-dimensional Kac–Moody Quotients.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

open BigOperators Matrix
open InfoGeometry.MetaCompiler

/-! ## Section 1: Universal First-Order Derivation Algebra, Second-Order Leibniz Defect & Jacobi Ceiling -/

section DerivationsAndJacobi

/-- A linear map `D : V →ₗ[R] V` is a product derivation with respect to a bilinear product
`B : V →ₗ[R] V →ₗ[R] V` (not assumed associative) iff it satisfies the Leibniz rule. -/
def IsProductDerivation {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] V) (D : V →ₗ[R] V) : Prop :=
  ∀ x y : V, D (B x y) = B (D x) y + B x (D y)

/-- The bilinear Leibniz defect `δ(T)(x, y) := T(B(x, y)) - B(T x, y) - B(x, T y)` measuring
the failure of a linear endomorphism `T` to act as a first-order derivation. -/
def leibnizDefect {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] V) (T : V →ₗ[R] V) (x y : V) : V :=
  T (B x y) - B (T x) y - B x (T y)

/-- `T` is a product derivation iff its Leibniz defect vanishes identically. -/
theorem isProductDerivation_iff_leibnizDefect_zero {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (B : V →ₗ[R] V →ₗ[R] V) (T : V →ₗ[R] V) :
    IsProductDerivation B T ↔ ∀ x y : V, leibnizDefect B T x y = 0 := by
  unfold IsProductDerivation leibnizDefect
  constructor
  · intro hT x y
    rw [hT x y, add_sub_cancel_left, sub_self]
  · intro hdef x y
    have h0 : T (B x y) - B (T x) y - B x (T y) = 0 := hdef x y
    have h1 : T (B x y) - B (T x) y = B x (T y) := sub_eq_zero.mp h0
    have h2 : T (B x y) = B (T x) y + B x (T y) := eq_add_of_sub_eq' h1
    exact h2

/-- Universal Lie-bracket closure of `der(V, B)`: the commutator `[D₁, D₂]` of two product
derivations is again a product derivation (holds for any bilinear algebra, even non-associative). -/
theorem derivation_commutator_closure {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {B : V →ₗ[R] V →ₗ[R] V} {D₁ D₂ : V →ₗ[R] V}
    (hD₁ : IsProductDerivation B D₁) (hD₂ : IsProductDerivation B D₂) :
    IsProductDerivation B (D₁.comp D₂ - D₂.comp D₁) := by
  intro x y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hD₂ x y, hD₁ x y, map_add, map_add]
  rw [hD₁ (D₂ x) y, hD₁ x (D₂ y), hD₂ (D₁ x) y, hD₂ x (D₁ y)]
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- Exact Leibniz defect of the Jordan anticommutator `D₁ ∘ D₂ + D₂ ∘ D₁` of two derivations. -/
theorem leibnizDefect_jordan_anticomm {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {B : V →ₗ[R] V →ₗ[R] V} {D₁ D₂ : V →ₗ[R] V}
    (hD₁ : IsProductDerivation B D₁) (hD₂ : IsProductDerivation B D₂) (x y : V) :
    leibnizDefect B (D₁.comp D₂ + D₂.comp D₁) x y =
      (2 : R) • (B (D₁ x) (D₂ y) + B (D₂ x) (D₁ y)) := by
  unfold leibnizDefect
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [hD₂ x y, hD₁ x y, map_add, map_add]
  rw [hD₁ (D₂ x) y, hD₁ x (D₂ y), hD₂ (D₁ x) y, hD₂ x (D₁ y)]
  simp only [map_add, LinearMap.add_apply, smul_add, two_smul]
  abel

/-- Corollary: `leibnizDefect B (D²) x y = 2 • B (D x) (D y)` for any product derivation `D`. -/
theorem leibnizDefect_sq_derivation {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {B : V →ₗ[R] V →ₗ[R] V} {D : V →ₗ[R] V} (hD : IsProductDerivation B D) (x y : V) :
    leibnizDefect B (D.comp D) x y = (2 : R) • B (D x) (D y) := by
  unfold leibnizDefect
  simp only [LinearMap.comp_apply]
  rw [hD x y, map_add, hD (D x) y, hD x (D y), two_smul]
  abel

/-- Matrix multiplication packaged as an `ℝ`-bilinear map on `Matrix (Fin 2) (Fin 2) ℝ`. -/
def matMulBilin2 :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.mul ℝ (Matrix (Fin 2) (Fin 2) ℝ)

/-- Concrete inner derivation `D(X) = [diag(1, -1), X]` on `M₂(ℝ)`. -/
def innerDerivationWitness : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun X := !![(1 : ℝ), 0; 0, -1] * X - X * !![(1 : ℝ), 0; 0, -1]
  map_add' X Y := by
    rw [mul_add, add_mul]
    abel
  map_smul' r X := by
    simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Concrete separation witness: `innerDerivationWitness` is a product derivation, whereas its
operator square `D²` has nonzero Leibniz defect `-8 E₀₀` on `(E₀₁, E₁₀)` and hence `D² ∉ der`. -/
theorem innerDerivationWitness_sq_not_derivation :
    IsProductDerivation matMulBilin2 innerDerivationWitness ∧
    leibnizDefect matMulBilin2 (innerDerivationWitness.comp innerDerivationWitness)
      !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] = !![(-8 : ℝ), 0; 0, 0] ∧
    ¬ IsProductDerivation matMulBilin2 (innerDerivationWitness.comp innerDerivationWitness) := by
  have hD : IsProductDerivation matMulBilin2 innerDerivationWitness := by
    intro X Y
    change innerDerivationWitness (X * Y) =
      innerDerivationWitness X * Y + X * innerDerivationWitness Y
    simp only [innerDerivationWitness, LinearMap.coe_mk, AddHom.coe_mk]
    noncomm_ring
  have hdef : leibnizDefect matMulBilin2 (innerDerivationWitness.comp innerDerivationWitness)
      !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] = !![(-8 : ℝ), 0; 0, 0] := by
    rw [leibnizDefect_sq_derivation hD]
    change (2 : ℝ) •
      (innerDerivationWitness !![(0 : ℝ), 1; 0, 0] *
        innerDerivationWitness !![(0 : ℝ), 0; 1, 0]) = !![(-8 : ℝ), 0; 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [innerDerivationWitness]; try norm_num)
  have hnot : ¬ IsProductDerivation matMulBilin2
      (innerDerivationWitness.comp innerDerivationWitness) := by
    intro hsq
    have hz := (isProductDerivation_iff_leibnizDefect_zero matMulBilin2 _).mp hsq
      !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0]
    rw [hdef] at hz
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hz
    norm_num at h00
  exact ⟨hD, hdef, hnot⟩

/-- Explicit OpenGauss `T16` non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem mat2_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![(0 : ℝ), 1; 1, 0], !![(1 : ℝ), 0; 0, -1], ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h01
  norm_num at h01

/-- Associative ring commutator `[X, Y] = X Y - Y X`. -/
def assocComm {A : Type*} [Ring A] (X Y : A) : A := X * Y - Y * X

/-- **Ax.4 — Universal Associative Jacobi Ceiling**: in any associative ring `A`, the commutator
bracket satisfies the Jacobi identity identically, forbidding any non-associative Jacobi anomaly. -/
theorem ax4_associative_jacobi_ceiling {A : Type*} [Ring A] (X Y Z : A) :
    assocComm X (assocComm Y Z) + assocComm Y (assocComm Z X) +
      assocComm Z (assocComm X Y) = 0 := by
  unfold assocComm
  noncomm_ring

/-- Non-unital non-associative second-order Leibniz defect identity `(D²)(x * y) - (D² x) * y - x * (D² y) = 2 (D x * D y)`,
valid over any `[NonUnitalNonAssocRing A]` (associative algebras, Lie algebras, and split-octonions). -/
theorem derivation_sq_leibniz_defect_nonAssocRing {A : Type*} [NonUnitalNonAssocRing A]
    (D : A →+ A) (hD : ∀ x y : A, D (x * y) = D x * y + x * D y) (x y : A) :
    D (D (x * y)) - D (D x) * y - x * D (D y) = D x * D y + D x * D y := by
  rw [hD x y, map_add, hD (D x) y, hD x (D y)]
  abel

end DerivationsAndJacobi

/-! ## Section 2: Double-Real Krein Spinor Module `Krein16Idx`, `tensor4` Engine, `Cl(4,4)`, `Γ_{4,4}`, `kreinMetric88` & Orthogonal Bivector Shear -/

section KreinCl44AndBivectorShear

/-- 16-dimensional double-real Krein spinor basis indexed by 4 qubit slots `(b₀, b₁, b₂, b₃)`. -/
abbrev Krein16Idx : Type := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- Cardinality of `Krein16Idx` is `16`. -/
theorem card_krein16Idx : Fintype.card Krein16Idx = 16 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]

/-- `Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) = 256` (`16² = 256`). -/
theorem finrank_mat16 :
    Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) = 256 := by
  rw [Module.finrank_matrix, card_krein16Idx, Module.finrank_self]

/-- 4-factor Kronecker tensor product on `Matrix Krein16Idx Krein16Idx ℝ`. -/
def tensor4 (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix Krein16Idx Krein16Idx ℝ :=
  fun i j => A₀ i.1 j.1 * A₁ i.2.1 j.2.1 * A₂ i.2.2.1 j.2.2.1 * A₃ i.2.2.2 j.2.2.2

/-- 4-factor Kronecker tensor spinor vector on `Krein16Idx → ℝ`. -/
def vec4 (v₀ v₁ v₂ v₃ : Fin 2 → ℝ) : Krein16Idx → ℝ :=
  fun i => v₀ i.1 * v₁ i.2.1 * v₂ i.2.2.1 * v₃ i.2.2.2

/-- Mixed-product law `(A₀ ⊗ A₁ ⊗ A₂ ⊗ A₃) * (B₀ ⊗ B₁ ⊗ B₂ ⊗ B₃) = (A₀B₀) ⊗ (A₁B₁) ⊗ (A₂B₂) ⊗ (A₃B₃)`. -/
theorem tensor4_mul (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ A₂ A₃ * tensor4 B₀ B₁ B₂ B₃ =
      tensor4 (A₀ * B₀) (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.mul_apply, Krein16Idx, Fintype.sum_prod_type, Fin.sum_univ_two, tensor4]
  ring

/-- `1 ⊗ 1 ⊗ 1 ⊗ 1 = (1 : Matrix Krein16Idx Krein16Idx ℝ)`. -/
theorem tensor4_one :
    tensor4 (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 1 =
      (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [tensor4]
  by_cases h₀ : i₀ = j₀ <;> by_cases h₁ : i₁ = j₁ <;>
    by_cases h₂ : i₂ = j₂ <;> by_cases h₃ : i₃ = j₃ <;>
    simp [Matrix.one_apply, h₀, h₁, h₂, h₃]

/-- Transpose distributes factorwise over `tensor4`. -/
theorem tensor4_transpose (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    (tensor4 A₀ A₁ A₂ A₃)ᵀ = tensor4 A₀ᵀ A₁ᵀ A₂ᵀ A₃ᵀ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.transpose_apply, tensor4]

/-- Trace multiplies factorwise across `tensor4`. -/
theorem tensor4_trace (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (tensor4 A₀ A₁ A₂ A₃) =
      Matrix.trace A₀ * Matrix.trace A₁ * Matrix.trace A₂ * Matrix.trace A₃ := by
  unfold Matrix.trace Matrix.diag tensor4
  simp only [Krein16Idx, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Matrix-vector action factorizes over `tensor4` and `vec4`. -/
theorem tensor4_mulVec (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) (v₀ v₁ v₂ v₃ : Fin 2 → ℝ) :
    (tensor4 A₀ A₁ A₂ A₃).mulVec (vec4 v₀ v₁ v₂ v₃) =
      vec4 (A₀.mulVec v₀) (A₁.mulVec v₁) (A₂.mulVec v₂) (A₃.mulVec v₃) := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Matrix.mulVec, dotProduct, Krein16Idx, Fintype.sum_prod_type, Fin.sum_univ_two,
    tensor4, vec4]
  ring

theorem tensor4_smul_all (r : ℝ) (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    r • tensor4 A₀ A₁ A₂ A₃ = tensor4 (r • A₀) A₁ A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.smul_apply, smul_eq_mul, tensor4, mul_assoc]

theorem tensor4_neg_0 (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 (-A₀) A₁ A₂ A₃ = -tensor4 A₀ A₁ A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.neg_apply, tensor4, neg_mul]

theorem tensor4_neg_1 (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ (-A₁) A₂ A₃ = -tensor4 A₀ A₁ A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.neg_apply, tensor4, mul_neg, neg_mul]

theorem tensor4_neg_2 (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ (-A₂) A₃ = -tensor4 A₀ A₁ A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.neg_apply, tensor4, mul_neg, neg_mul]

theorem tensor4_neg_3 (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ A₂ (-A₃) = -tensor4 A₀ A₁ A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.neg_apply, tensor4, mul_neg]

theorem tensor4_zero_0 (A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 0 A₁ A₂ A₃ = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.zero_apply, tensor4, zero_mul]

theorem tensor4_zero_1 (A₀ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ 0 A₂ A₃ = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.zero_apply, tensor4, mul_zero, zero_mul]

theorem tensor4_zero_2 (A₀ A₁ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ 0 A₃ = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.zero_apply, tensor4, mul_zero, zero_mul]

theorem tensor4_zero_3 (A₀ A₁ A₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ A₂ 0 = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.zero_apply, tensor4, mul_zero]

theorem tensor4_add_0 (A₀ A₀' A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 (A₀ + A₀') A₁ A₂ A₃ = tensor4 A₀ A₁ A₂ A₃ + tensor4 A₀' A₁ A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.add_apply, tensor4]
  ring

theorem tensor4_add_1 (A₀ A₁ A₁' A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ (A₁ + A₁') A₂ A₃ = tensor4 A₀ A₁ A₂ A₃ + tensor4 A₀ A₁' A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.add_apply, tensor4]
  ring

theorem tensor4_add_2 (A₀ A₁ A₂ A₂' A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ (A₂ + A₂') A₃ = tensor4 A₀ A₁ A₂ A₃ + tensor4 A₀ A₁ A₂' A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.add_apply, tensor4]
  ring

theorem tensor4_add_3 (A₀ A₁ A₂ A₃ A₃' : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ A₂ (A₃ + A₃') = tensor4 A₀ A₁ A₂ A₃ + tensor4 A₀ A₁ A₂ A₃' := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.add_apply, tensor4]
  ring

theorem tensor4_sub_0 (A₀ A₀' A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 (A₀ - A₀') A₁ A₂ A₃ = tensor4 A₀ A₁ A₂ A₃ - tensor4 A₀' A₁ A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.sub_apply, tensor4]
  ring

theorem tensor4_sub_1 (A₀ A₁ A₁' A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ (A₁ - A₁') A₂ A₃ = tensor4 A₀ A₁ A₂ A₃ - tensor4 A₀ A₁' A₂ A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.sub_apply, tensor4]
  ring

theorem tensor4_sub_2 (A₀ A₁ A₂ A₂' A₃ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ (A₂ - A₂') A₃ = tensor4 A₀ A₁ A₂ A₃ - tensor4 A₀ A₁ A₂' A₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.sub_apply, tensor4]
  ring

theorem tensor4_sub_3 (A₀ A₁ A₂ A₃ A₃' : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₀ A₁ A₂ (A₃ - A₃') = tensor4 A₀ A₁ A₂ A₃ - tensor4 A₀ A₁ A₂ A₃' := by
  ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
  simp only [Matrix.sub_apply, tensor4]
  ring

theorem vec4_zero_0 (v₁ v₂ v₃ : Fin 2 → ℝ) : vec4 0 v₁ v₂ v₃ = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.zero_apply, vec4, zero_mul]

theorem vec4_zero_1 (v₀ v₂ v₃ : Fin 2 → ℝ) : vec4 v₀ 0 v₂ v₃ = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.zero_apply, vec4, mul_zero, zero_mul]

theorem vec4_zero_2 (v₀ v₁ v₃ : Fin 2 → ℝ) : vec4 v₀ v₁ 0 v₃ = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.zero_apply, vec4, mul_zero, zero_mul]

theorem vec4_zero_3 (v₀ v₁ v₂ : Fin 2 → ℝ) : vec4 v₀ v₁ v₂ 0 = 0 := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.zero_apply, vec4, mul_zero]

theorem vec4_neg_0 (v₀ v₁ v₂ v₃ : Fin 2 → ℝ) : vec4 (-v₀) v₁ v₂ v₃ = -vec4 v₀ v₁ v₂ v₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.neg_apply, vec4, neg_mul]

theorem vec4_neg_1 (v₀ v₁ v₂ v₃ : Fin 2 → ℝ) : vec4 v₀ (-v₁) v₂ v₃ = -vec4 v₀ v₁ v₂ v₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.neg_apply, vec4, mul_neg, neg_mul]

theorem vec4_neg_2 (v₀ v₁ v₂ v₃ : Fin 2 → ℝ) : vec4 v₀ v₁ (-v₂) v₃ = -vec4 v₀ v₁ v₂ v₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.neg_apply, vec4, mul_neg, neg_mul]

theorem vec4_neg_3 (v₀ v₁ v₂ v₃ : Fin 2 → ℝ) : vec4 v₀ v₁ v₂ (-v₃) = -vec4 v₀ v₁ v₂ v₃ := by
  ext ⟨i₀, i₁, i₂, i₃⟩
  simp only [Pi.neg_apply, vec4, mul_neg]

/-! ### `2 × 2` Real `Cl(1,1)` Building Blocks -/

/-- Positive `Cl(1,1)` generator `[[0, 1], [1, 0]]` (`γ₊² = 1`). -/
def cl11Pos : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Negative `Cl(1,1)` generator `[[0, -1], [1, 0]]` (`γ₋² = -1`). -/
def cl11Neg : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- `Cl(1,1)` chiral grading `[[1, 0], [0, -1]]` (`σ² = 1`). -/
def cl11Grad : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Raising operator `E₀₁ = [[0, 1], [0, 0]] = (γ₊ - γ₋)/2`. -/
def cl11Up : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Lowering operator `E₁₀ = [[0, 0], [1, 0]] = (γ₊ + γ₋)/2`. -/
def cl11Down : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- Projector `E₀₀ = [[1, 0], [0, 0]]`. -/
def cl11P0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Projector `E₁₁ = [[0, 0], [0, 1]]`. -/
def cl11P1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- Basis spinor `|0⟩ = ![1, 0]`. -/
def ket0 : Fin 2 → ℝ := ![1, 0]

/-- Basis spinor `|1⟩ = ![0, 1]`. -/
def ket1 : Fin 2 → ℝ := ![0, 1]

section Cl11Lemmas

theorem cl11Pos_sq : cl11Pos * cl11Pos = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, Matrix.mul_apply]

theorem cl11Neg_sq : cl11Neg * cl11Neg = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, Matrix.mul_apply]

theorem cl11Grad_sq : cl11Grad * cl11Grad = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, Matrix.mul_apply]

theorem cl11Pos_mul_cl11Neg : cl11Pos * cl11Neg = cl11Grad := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Neg, cl11Grad, Matrix.mul_apply]

theorem cl11Neg_mul_cl11Pos : cl11Neg * cl11Pos = -cl11Grad := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Neg, cl11Grad, Matrix.mul_apply]

theorem cl11Neg_mul_cl11Grad : cl11Neg * cl11Grad = cl11Pos := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Neg, cl11Grad, Matrix.mul_apply]

theorem cl11Grad_mul_cl11Neg : cl11Grad * cl11Neg = -cl11Pos := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Neg, cl11Grad, Matrix.mul_apply]

theorem cl11Pos_mul_cl11Grad : cl11Pos * cl11Grad = cl11Neg := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Neg, cl11Grad, Matrix.mul_apply]

theorem cl11Grad_mul_cl11Pos : cl11Grad * cl11Pos = -cl11Neg := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Neg, cl11Grad, Matrix.mul_apply]

theorem cl11Pos_transpose : cl11Posᵀ = cl11Pos := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos]

theorem cl11Neg_transpose : cl11Negᵀ = -cl11Neg := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg]

theorem cl11Grad_transpose : cl11Gradᵀ = cl11Grad := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad]

theorem cl11Grad_trace : Matrix.trace cl11Grad = 0 := by
  unfold Matrix.trace cl11Grad
  rw [Fin.sum_univ_two]
  norm_num

theorem cl11Pos_trace : Matrix.trace cl11Pos = 0 := by
  unfold Matrix.trace cl11Pos
  rw [Fin.sum_univ_two]
  norm_num

theorem cl11Up_mul_cl11Up : cl11Up * cl11Up = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Up, Matrix.mul_apply]

theorem cl11Down_mul_cl11Down : cl11Down * cl11Down = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Down, Matrix.mul_apply]

theorem cl11Up_mul_cl11Down : cl11Up * cl11Down = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Up, cl11Down, cl11P0, Matrix.mul_apply]

theorem cl11Down_mul_cl11Up : cl11Down * cl11Up = cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Up, cl11Down, cl11P1, Matrix.mul_apply]

theorem cl11P0_mul_cl11P0 : cl11P0 * cl11P0 = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P0, Matrix.mul_apply]

theorem cl11P1_mul_cl11P1 : cl11P1 * cl11P1 = cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P1, Matrix.mul_apply]

theorem cl11P0_mul_cl11P1 : cl11P0 * cl11P1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P0, cl11P1, Matrix.mul_apply]

theorem cl11P1_mul_cl11P0 : cl11P1 * cl11P0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P0, cl11P1, Matrix.mul_apply]

theorem cl11Grad_mul_cl11Up : cl11Grad * cl11Up = cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11Up, Matrix.mul_apply]

theorem cl11Up_mul_cl11Grad : cl11Up * cl11Grad = -cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11Up, Matrix.mul_apply]

theorem cl11Grad_mul_cl11Down : cl11Grad * cl11Down = -cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11Down, Matrix.mul_apply]

theorem cl11Down_mul_cl11Grad : cl11Down * cl11Grad = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11Down, Matrix.mul_apply]

theorem cl11Grad_mul_cl11P0 : cl11Grad * cl11P0 = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11P0, Matrix.mul_apply]

theorem cl11P0_mul_cl11Grad : cl11P0 * cl11Grad = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11P0, Matrix.mul_apply]

theorem cl11Grad_mul_cl11P1 : cl11Grad * cl11P1 = -cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11P1, Matrix.mul_apply]

theorem cl11P1_mul_cl11Grad : cl11P1 * cl11Grad = -cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11P1, Matrix.mul_apply]

theorem cl11P0_mul_cl11Up : cl11P0 * cl11Up = cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P0, cl11Up, Matrix.mul_apply]

theorem cl11P1_mul_cl11Up : cl11P1 * cl11Up = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P1, cl11Up, Matrix.mul_apply]

theorem cl11Up_mul_cl11P0 : cl11Up * cl11P0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Up, cl11P0, Matrix.mul_apply]

theorem cl11Up_mul_cl11P1 : cl11Up * cl11P1 = cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Up, cl11P1, Matrix.mul_apply]

theorem cl11P0_mul_cl11Down : cl11P0 * cl11Down = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P0, cl11Down, Matrix.mul_apply]

theorem cl11P1_mul_cl11Down : cl11P1 * cl11Down = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P1, cl11Down, Matrix.mul_apply]

theorem cl11Down_mul_cl11P0 : cl11Down * cl11P0 = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Down, cl11P0, Matrix.mul_apply]

theorem cl11Down_mul_cl11P1 : cl11Down * cl11P1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Down, cl11P1, Matrix.mul_apply]

theorem cl11Pos_mul_cl11P0 : cl11Pos * cl11P0 = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11P0, cl11Down, Matrix.mul_apply]

theorem cl11P0_mul_cl11Pos : cl11P0 * cl11Pos = cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11P0, cl11Up, Matrix.mul_apply]

theorem cl11Pos_mul_cl11P1 : cl11Pos * cl11P1 = cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11P1, cl11Up, Matrix.mul_apply]

theorem cl11P1_mul_cl11Pos : cl11P1 * cl11Pos = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11P1, cl11Down, Matrix.mul_apply]

theorem cl11Neg_mul_cl11P0 : cl11Neg * cl11P0 = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11P0, cl11Down, Matrix.mul_apply]

theorem cl11P0_mul_cl11Neg : cl11P0 * cl11Neg = -cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11P0, cl11Up, Matrix.mul_apply]

theorem cl11Neg_mul_cl11P1 : cl11Neg * cl11P1 = -cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11P1, cl11Up, Matrix.mul_apply]

theorem cl11P1_mul_cl11Neg : cl11P1 * cl11Neg = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11P1, cl11Down, Matrix.mul_apply]

theorem cl11Pos_mul_cl11Up : cl11Pos * cl11Up = cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Up, cl11P1, Matrix.mul_apply]

theorem cl11Up_mul_cl11Pos : cl11Up * cl11Pos = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Up, cl11P0, Matrix.mul_apply]

theorem cl11Pos_mul_cl11Down : cl11Pos * cl11Down = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Down, cl11P0, Matrix.mul_apply]

theorem cl11Down_mul_cl11Pos : cl11Down * cl11Pos = cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Down, cl11P1, Matrix.mul_apply]

theorem cl11Neg_mul_cl11Up : cl11Neg * cl11Up = cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11Up, cl11P1, Matrix.mul_apply]

theorem cl11Up_mul_cl11Neg : cl11Up * cl11Neg = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11Up, cl11P0, Matrix.mul_apply]

theorem cl11Neg_mul_cl11Down : cl11Neg * cl11Down = -cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11Down, cl11P0, Matrix.mul_apply]

theorem cl11Down_mul_cl11Neg : cl11Down * cl11Neg = -cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11Down, cl11P1, Matrix.mul_apply]

theorem cl11Up_transpose : cl11Upᵀ = cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Up, cl11Down]

theorem cl11Down_transpose : cl11Downᵀ = cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Up, cl11Down]

theorem cl11P0_transpose : cl11P0ᵀ = cl11P0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P0]

theorem cl11P1_transpose : cl11P1ᵀ = cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P1]

theorem cl11One_eq_P0_add_P1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) = cl11P0 + cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11P0, cl11P1]

theorem cl11Grad_eq_P0_sub_P1 : cl11Grad = cl11P0 - cl11P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Grad, cl11P0, cl11P1]

theorem cl11Pos_eq_Up_add_Down : cl11Pos = cl11Up + cl11Down := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Pos, cl11Up, cl11Down]

theorem cl11Neg_eq_Down_sub_Up : cl11Neg = cl11Down - cl11Up := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11Neg, cl11Up, cl11Down]

theorem one_mulVec2 (v : Fin 2 → ℝ) : (1 : Matrix (Fin 2) (Fin 2) ℝ).mulVec v = v :=
  Matrix.one_mulVec v

theorem cl11Grad_mulVec_ket0 : cl11Grad.mulVec ket0 = ket0 := by
  ext i; fin_cases i <;> simp [cl11Grad, ket0, Matrix.mulVec, dotProduct]

theorem cl11Grad_mulVec_ket1 : cl11Grad.mulVec ket1 = -ket1 := by
  ext i; fin_cases i <;> simp [cl11Grad, ket1, Matrix.mulVec, dotProduct]

theorem cl11Pos_mulVec_ket0 : cl11Pos.mulVec ket0 = ket1 := by
  ext i; fin_cases i <;> simp [cl11Pos, ket0, ket1, Matrix.mulVec, dotProduct]

theorem cl11Pos_mulVec_ket1 : cl11Pos.mulVec ket1 = ket0 := by
  ext i; fin_cases i <;> simp [cl11Pos, ket0, ket1, Matrix.mulVec, dotProduct]

theorem cl11Neg_mulVec_ket0 : cl11Neg.mulVec ket0 = ket1 := by
  ext i; fin_cases i <;> simp [cl11Neg, ket0, ket1, Matrix.mulVec, dotProduct]

theorem cl11Neg_mulVec_ket1 : cl11Neg.mulVec ket1 = -ket0 := by
  ext i; fin_cases i <;> simp [cl11Neg, ket0, ket1, Matrix.mulVec, dotProduct]

theorem cl11Up_mulVec_ket0 : cl11Up.mulVec ket0 = 0 := by
  ext i; fin_cases i <;> simp [cl11Up, ket0, Matrix.mulVec, dotProduct]

theorem cl11Up_mulVec_ket1 : cl11Up.mulVec ket1 = ket0 := by
  ext i; fin_cases i <;> simp [cl11Up, ket0, ket1, Matrix.mulVec, dotProduct]

theorem cl11Down_mulVec_ket0 : cl11Down.mulVec ket0 = ket1 := by
  ext i; fin_cases i <;> simp [cl11Down, ket0, ket1, Matrix.mulVec, dotProduct]

theorem cl11Down_mulVec_ket1 : cl11Down.mulVec ket1 = 0 := by
  ext i; fin_cases i <;> simp [cl11Down, ket1, Matrix.mulVec, dotProduct]

theorem cl11P0_mulVec_ket0 : cl11P0.mulVec ket0 = ket0 := by
  ext i; fin_cases i <;> simp [cl11P0, ket0, Matrix.mulVec, dotProduct]

theorem cl11P0_mulVec_ket1 : cl11P0.mulVec ket1 = 0 := by
  ext i; fin_cases i <;> simp [cl11P0, ket1, Matrix.mulVec, dotProduct]

theorem cl11P1_mulVec_ket0 : cl11P1.mulVec ket0 = 0 := by
  ext i; fin_cases i <;> simp [cl11P1, ket0, Matrix.mulVec, dotProduct]

theorem cl11P1_mulVec_ket1 : cl11P1.mulVec ket1 = ket1 := by
  ext i; fin_cases i <;> simp [cl11P1, ket1, Matrix.mulVec, dotProduct]

end Cl11Lemmas

attribute [local simp]
  tensor4_mul tensor4_one
  tensor4_zero_0 tensor4_zero_1 tensor4_zero_2 tensor4_zero_3
  tensor4_neg_0 tensor4_neg_1 tensor4_neg_2 tensor4_neg_3
  add_mul mul_add sub_mul mul_sub neg_mul mul_neg
  mul_assoc one_mul mul_one zero_mul mul_zero
  cl11Pos_sq cl11Neg_sq cl11Grad_sq
  cl11Pos_mul_cl11Neg cl11Neg_mul_cl11Pos
  cl11Neg_mul_cl11Grad cl11Grad_mul_cl11Neg
  cl11Pos_mul_cl11Grad cl11Grad_mul_cl11Pos
  cl11Up_mul_cl11Up cl11Down_mul_cl11Down cl11Up_mul_cl11Down cl11Down_mul_cl11Up
  cl11P0_mul_cl11P0 cl11P1_mul_cl11P1 cl11P0_mul_cl11P1 cl11P1_mul_cl11P0
  cl11Grad_mul_cl11Up cl11Up_mul_cl11Grad cl11Grad_mul_cl11Down cl11Down_mul_cl11Grad
  cl11Grad_mul_cl11P0 cl11P0_mul_cl11Grad cl11Grad_mul_cl11P1 cl11P1_mul_cl11Grad
  cl11P0_mul_cl11Up cl11P1_mul_cl11Up cl11Up_mul_cl11P0 cl11Up_mul_cl11P1
  cl11P0_mul_cl11Down cl11P1_mul_cl11Down cl11Down_mul_cl11P0 cl11Down_mul_cl11P1
  cl11Pos_mul_cl11P0 cl11P0_mul_cl11Pos cl11Pos_mul_cl11P1 cl11P1_mul_cl11Pos
  cl11Neg_mul_cl11P0 cl11P0_mul_cl11Neg cl11Neg_mul_cl11P1 cl11P1_mul_cl11Neg
  cl11Pos_mul_cl11Up cl11Up_mul_cl11Pos cl11Pos_mul_cl11Down cl11Down_mul_cl11Pos
  cl11Neg_mul_cl11Up cl11Up_mul_cl11Neg cl11Neg_mul_cl11Down cl11Down_mul_cl11Neg

/-- Explicit OpenGauss `T16` non-commutativity witness on `Matrix Krein16Idx Krein16Idx ℝ`. -/
theorem krein16_matrix_noncommutative :
    ∃ A B : Matrix Krein16Idx Krein16Idx ℝ, A * B ≠ B * A := by
  refine ⟨tensor4 cl11Pos 1 1 1, tensor4 cl11Neg 1 1 1, ?_⟩
  intro h
  have h1 : tensor4 cl11Grad 1 1 1 = tensor4 (-cl11Grad) 1 1 1 := by
    simpa [cl11Pos_mul_cl11Neg, cl11Neg_mul_cl11Pos] using h
  have h00 := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ =>
    M (0, 0, 0, 0) (0, 0, 0, 0)) h1
  unfold tensor4 at h00
  simp only [Matrix.neg_apply, cl11Grad, Matrix.one_apply, Matrix.of_apply,
    Matrix.cons_val_zero] at h00
  norm_num at h00

/-! ### Explicit 8 Generators of `Cl(4,4)`, `Γ_{4,4}`, `kreinMetric88` & Bivector Shear -/

/-- Jordan–Wigner representation of the 8 generators of `Cl(4,4)` inside `M₁₆(ℝ)`:
- `0..3`: `e₀..e₃` with `e_k² = +1`;
- `4..7`: `ẽ₀..ẽ₃` with `ẽ_k² = -1`. -/
def cl44Gen : Fin 8 → Matrix Krein16Idx Krein16Idx ℝ
  | 0 => tensor4 cl11Pos 1 1 1
  | 1 => tensor4 cl11Grad cl11Pos 1 1
  | 2 => tensor4 cl11Grad cl11Grad cl11Pos 1
  | 3 => tensor4 cl11Grad cl11Grad cl11Grad cl11Pos
  | 4 => tensor4 cl11Neg 1 1 1
  | 5 => tensor4 cl11Grad cl11Neg 1 1
  | 6 => tensor4 cl11Grad cl11Grad cl11Neg 1
  | 7 => tensor4 cl11Grad cl11Grad cl11Grad cl11Neg

/-- Majorana–Weyl chiral grading operator `Γ_{4,4} = σ ⊗ σ ⊗ σ ⊗ σ`. -/
def gamma44 : Matrix Krein16Idx Krein16Idx ℝ :=
  tensor4 cl11Grad cl11Grad cl11Grad cl11Grad

/-- Double-real Krein metric `η̂_{8,8} = ẽ₀ ẽ₁ ẽ₂ ẽ₃ = γ₊ ⊗ γ₋ ⊗ γ₊ ⊗ γ₋`. -/
def kreinMetric88 : Matrix Krein16Idx Krein16Idx ℝ :=
  tensor4 cl11Pos cl11Neg cl11Pos cl11Neg

/-- Clifford bivector generator `B_{ab} := γ_a γ_b`. -/
def cl44Bivector (a b : Fin 8) : Matrix Krein16Idx Krein16Idx ℝ :=
  cl44Gen a * cl44Gen b

/-- Signature squares `e_k² = +1` (`k < 4`) and `ẽ_k² = -1` (`k ≥ 4`). -/
theorem cl44Gen_sq (a : Fin 8) :
    cl44Gen a * cl44Gen a = if a.val < 4 then 1 else -1 := by
  fin_cases a <;> simp [cl44Gen]

/-- Clifford anticommutation `{γ_a, γ_b} = 0` for all distinct `a ≠ b : Fin 8`. -/
theorem cl44Gen_anticomm {a b : Fin 8} (hab : a ≠ b) :
    cl44Gen a * cl44Gen b + cl44Gen b * cl44Gen a = 0 := by
  fin_cases a <;> fin_cases b
  all_goals first | exact absurd rfl hab | (simp [cl44Gen]; try abel)

/-- Exact volume-element identity, involution, trace zero, and odd chiral anticommutation of `Γ_{4,4}`. -/
theorem gamma44_properties :
    cl44Gen 0 * cl44Gen 4 * cl44Gen 1 * cl44Gen 5 *
        cl44Gen 2 * cl44Gen 6 * cl44Gen 3 * cl44Gen 7 = gamma44 ∧
    gamma44 * gamma44 = 1 ∧
    Matrix.trace gamma44 = 0 ∧
    (∀ a : Fin 8, cl44Gen a * gamma44 + gamma44 * cl44Gen a = 0) := by
  have hprod :
      cl44Gen 0 * cl44Gen 4 * cl44Gen 1 * cl44Gen 5 *
        cl44Gen 2 * cl44Gen 6 * cl44Gen 3 * cl44Gen 7 = gamma44 := by
    simp [cl44Gen, gamma44]
  have hsq : gamma44 * gamma44 = 1 := by
    simp [gamma44]
  have htr : Matrix.trace gamma44 = 0 := by
    unfold gamma44
    rw [tensor4_trace, cl11Grad_trace, zero_mul, zero_mul, zero_mul]
  refine ⟨hprod, hsq, htr, ?_⟩
  intro a
  fin_cases a <;> simp [cl44Gen, gamma44]

/-- Explicit symmetry, involution, trace zero (8×`+1`, 8×`-1` spectrum), and chiral compatibility
of `kreinMetric88`. -/
theorem kreinMetric88_properties :
    cl44Gen 4 * cl44Gen 5 * cl44Gen 6 * cl44Gen 7 = kreinMetric88 ∧
    kreinMetric88ᵀ = kreinMetric88 ∧
    kreinMetric88 * kreinMetric88 = 1 ∧
    Matrix.trace kreinMetric88 = 0 ∧
    kreinMetric88 * gamma44 = gamma44 * kreinMetric88 := by
  have hprod : cl44Gen 4 * cl44Gen 5 * cl44Gen 6 * cl44Gen 7 = kreinMetric88 := by
    simp [cl44Gen, kreinMetric88]
  have hsymm : kreinMetric88ᵀ = kreinMetric88 := by
    unfold kreinMetric88
    rw [tensor4_transpose, cl11Pos_transpose, cl11Neg_transpose]
    rw [tensor4_neg_1, tensor4_neg_3, neg_neg]
  have hsq : kreinMetric88 * kreinMetric88 = 1 := by
    simp [kreinMetric88]
  have htr : Matrix.trace kreinMetric88 = 0 := by
    unfold kreinMetric88
    rw [tensor4_trace, cl11Pos_trace, zero_mul, zero_mul, zero_mul]
  have hcomm : kreinMetric88 * gamma44 = gamma44 * kreinMetric88 := by
    simp [kreinMetric88, gamma44]
  exact ⟨hprod, hsymm, hsq, htr, hcomm⟩

/-- Every vector generator `γ_a` (`a : Fin 8`) is Krein-symmetric: `γ_aᵀ * η̂ = η̂ * γ_a`. -/
theorem cl44Gen_krein_symm (a : Fin 8) :
    (cl44Gen a)ᵀ * kreinMetric88 = kreinMetric88 * cl44Gen a := by
  fin_cases a
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Pos_transpose, Matrix.transpose_one]
    simp
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Grad_transpose, cl11Pos_transpose, Matrix.transpose_one]
    simp
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Grad_transpose, cl11Pos_transpose, Matrix.transpose_one]
    simp
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Grad_transpose, cl11Pos_transpose]
    simp
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Neg_transpose, Matrix.transpose_one]
    simp
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Grad_transpose, cl11Neg_transpose, Matrix.transpose_one]
    simp
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Grad_transpose, cl11Neg_transpose, Matrix.transpose_one]
    simp
  · unfold cl44Gen kreinMetric88
    rw [tensor4_transpose, cl11Grad_transpose, cl11Neg_transpose]
    simp

/-- Every Clifford bivector `B_{ab}` (`a ≠ b`) is automatically chiral-even (`[B_{ab}, Γ_{4,4}] = 0`)
and Krein-skew (`B_{ab}ᵀ η̂ + η̂ B_{ab} = 0`). -/
theorem cl44Bivector_chiral_even_and_krein_skew {a b : Fin 8} (hab : a ≠ b) :
    cl44Bivector a b * gamma44 = gamma44 * cl44Bivector a b ∧
    (cl44Bivector a b)ᵀ * kreinMetric88 + kreinMetric88 * cl44Bivector a b = 0 := by
  have ha_gam := gamma44_properties.2.2.2 a
  have hb_gam := gamma44_properties.2.2.2 b
  have ha_g : cl44Gen a * gamma44 = -(gamma44 * cl44Gen a) := eq_neg_of_add_eq_zero_left ha_gam
  have hb_g : cl44Gen b * gamma44 = -(gamma44 * cl44Gen b) := eq_neg_of_add_eq_zero_left hb_gam
  have hchiral : cl44Bivector a b * gamma44 = gamma44 * cl44Bivector a b := by
    unfold cl44Bivector
    calc
      (cl44Gen a * cl44Gen b) * gamma44
          = cl44Gen a * (cl44Gen b * gamma44) := by rw [Matrix.mul_assoc]
      _ = cl44Gen a * (-(gamma44 * cl44Gen b)) := by rw [hb_g]
      _ = -((cl44Gen a * gamma44) * cl44Gen b) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = -((-(gamma44 * cl44Gen a)) * cl44Gen b) := by rw [ha_g]
      _ = gamma44 * (cl44Gen a * cl44Gen b) := by rw [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hab_anti : cl44Gen b * cl44Gen a = -(cl44Gen a * cl44Gen b) :=
    eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab)
  have hskew : (cl44Bivector a b)ᵀ * kreinMetric88 + kreinMetric88 * cl44Bivector a b = 0 := by
    unfold cl44Bivector
    rw [Matrix.transpose_mul, Matrix.mul_assoc, cl44Gen_krein_symm a]
    rw [← Matrix.mul_assoc, cl44Gen_krein_symm b, Matrix.mul_assoc, hab_anti]
    rw [Matrix.mul_neg, neg_add_cancel]
  exact ⟨hchiral, hskew⟩

/-- **Orthogonal Shear Law of Bivector Commutators vs. Jordan Anticommutators in `Cl(4,4)`**:
1. `[B_{ab}, γ_c] = 0` when `c ∉ {a, b}`, while `[B_{ab}, γ_b] = 2 (γ_b²) γ_a`;
2. Overlapping bivectors `(a, b)` and `(b, c)` (`a, b, c` distinct) close horizontally in `Cl⁽²⁾(4,4)`
   (`[B_{ab}, B_{bc}] = 2 (γ_b²) B_{ac}`) while their Jordan anticommutator vanishes (`{B_{ab}, B_{bc}} = 0`);
3. Disjoint bivectors `(a, b)` and `(c, d)` (`a, b, c, d` pairwise distinct) have zero Lie commutator
   (`[B_{ab}, B_{cd}] = 0`) while their Jordan anticommutator jumps vertically into `Cl⁽⁴⁾(4,4)`. -/
theorem cl44Bivector_orthogonal_shear :
    (∀ {a b c : Fin 8}, c ≠ a → c ≠ b →
      cl44Bivector a b * cl44Gen c - cl44Gen c * cl44Bivector a b = 0) ∧
    (∀ {a b : Fin 8}, a ≠ b →
      cl44Bivector a b * cl44Gen b - cl44Gen b * cl44Bivector a b =
        (2 : ℝ) • ((if b.val < 4 then (1 : ℝ) else -1) • cl44Gen a)) ∧
    (∀ {a b c : Fin 8}, a ≠ b → b ≠ c → a ≠ c →
      cl44Bivector a b * cl44Bivector b c - cl44Bivector b c * cl44Bivector a b =
        (2 : ℝ) • ((if b.val < 4 then (1 : ℝ) else -1) • cl44Bivector a c) ∧
      cl44Bivector a b * cl44Bivector b c + cl44Bivector b c * cl44Bivector a b = 0) ∧
    (∀ {a b c d : Fin 8}, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      cl44Bivector a b * cl44Bivector c d - cl44Bivector c d * cl44Bivector a b = 0 ∧
      cl44Bivector a b * cl44Bivector c d + cl44Bivector c d * cl44Bivector a b =
        (2 : ℝ) • (cl44Gen a * cl44Gen b * cl44Gen c * cl44Gen d)) := by
  have h1 : ∀ {a b c : Fin 8}, c ≠ a → c ≠ b →
      cl44Bivector a b * cl44Gen c - cl44Gen c * cl44Bivector a b = 0 := by
    intro a b c hca hcb
    have hbc : cl44Gen b * cl44Gen c = -(cl44Gen c * cl44Gen b) :=
      eq_neg_of_add_eq_zero_left (cl44Gen_anticomm hcb.symm)
    have hac : cl44Gen a * cl44Gen c = -(cl44Gen c * cl44Gen a) :=
      eq_neg_of_add_eq_zero_left (cl44Gen_anticomm hca.symm)
    unfold cl44Bivector
    rw [Matrix.mul_assoc, hbc, Matrix.mul_neg, ← Matrix.mul_assoc, hac]
    rw [Matrix.neg_mul, neg_neg, Matrix.mul_assoc, sub_self]
  have h2 : ∀ {a b : Fin 8}, a ≠ b →
      cl44Bivector a b * cl44Gen b - cl44Gen b * cl44Bivector a b =
        (2 : ℝ) • ((if b.val < 4 then (1 : ℝ) else -1) • cl44Gen a) := by
    intro a b hab
    have hba : cl44Gen b * cl44Gen a = -(cl44Gen a * cl44Gen b) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab)
    have hsq : cl44Gen b * cl44Gen b = (if b.val < 4 then (1 : ℝ) else -1) • (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
      rw [cl44Gen_sq b]
      split_ifs <;> simp only [one_smul, neg_smul]
    unfold cl44Bivector
    calc
      cl44Gen a * cl44Gen b * cl44Gen b - cl44Gen b * (cl44Gen a * cl44Gen b)
          = cl44Gen a * (cl44Gen b * cl44Gen b) - (cl44Gen b * cl44Gen a) * cl44Gen b := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = cl44Gen a * (cl44Gen b * cl44Gen b) + cl44Gen a * (cl44Gen b * cl44Gen b) := by
              rw [hba, Matrix.neg_mul, sub_neg_eq_add, Matrix.mul_assoc]
      _ = (2 : ℝ) • (cl44Gen a * (cl44Gen b * cl44Gen b)) := (two_smul ℝ _).symm
      _ = (2 : ℝ) • ((if b.val < 4 then (1 : ℝ) else -1) • cl44Gen a) := by
              rw [hsq, Matrix.mul_smul, Matrix.mul_one]
  have h3 : ∀ {a b c : Fin 8}, a ≠ b → b ≠ c → a ≠ c →
      cl44Bivector a b * cl44Bivector b c - cl44Bivector b c * cl44Bivector a b =
        (2 : ℝ) • ((if b.val < 4 then (1 : ℝ) else -1) • cl44Bivector a c) ∧
      cl44Bivector a b * cl44Bivector b c + cl44Bivector b c * cl44Bivector a b = 0 := by
    intro a b c hab hbc hac
    have hca : cl44Gen c * cl44Gen a = -(cl44Gen a * cl44Gen c) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hac)
    have hba : cl44Gen b * cl44Gen a = -(cl44Gen a * cl44Gen b) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab)
    have hcb : cl44Gen c * cl44Gen b = -(cl44Gen b * cl44Gen c) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hbc)
    have hsq : cl44Gen b * cl44Gen b = (if b.val < 4 then (1 : ℝ) else -1) • (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
      rw [cl44Gen_sq b]
      split_ifs <;> simp only [one_smul, neg_smul]
    have hswap : cl44Bivector b c * cl44Bivector a b = -(cl44Bivector a b * cl44Bivector b c) := by
      unfold cl44Bivector
      calc
        (cl44Gen b * cl44Gen c) * (cl44Gen a * cl44Gen b)
            = cl44Gen b * ((cl44Gen c * cl44Gen a) * cl44Gen b) := by
                simp only [Matrix.mul_assoc]
        _ = cl44Gen b * ((-(cl44Gen a * cl44Gen c)) * cl44Gen b) := by rw [hca]
        _ = -((cl44Gen b * cl44Gen a) * (cl44Gen c * cl44Gen b)) := by
                simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
        _ = -((-(cl44Gen a * cl44Gen b)) * (-(cl44Gen b * cl44Gen c))) := by
                rw [hba, hcb]
        _ = -((cl44Gen a * cl44Gen b) * (cl44Gen b * cl44Gen c)) := by
                rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have hmul_ab_bc : cl44Bivector a b * cl44Bivector b c =
        (if b.val < 4 then (1 : ℝ) else -1) • cl44Bivector a c := by
      unfold cl44Bivector
      calc
        (cl44Gen a * cl44Gen b) * (cl44Gen b * cl44Gen c)
            = cl44Gen a * (cl44Gen b * cl44Gen b) * cl44Gen c := by
                simp only [Matrix.mul_assoc]
        _ = (if b.val < 4 then (1 : ℝ) else -1) • (cl44Gen a * cl44Gen c) := by
                rw [hsq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · rw [hswap, sub_neg_eq_add, hmul_ab_bc, two_smul]
    · rw [hswap, add_neg_cancel]
  have h4 : ∀ {a b c d : Fin 8}, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      cl44Bivector a b * cl44Bivector c d - cl44Bivector c d * cl44Bivector a b = 0 ∧
      cl44Bivector a b * cl44Bivector c d + cl44Bivector c d * cl44Bivector a b =
        (2 : ℝ) • (cl44Gen a * cl44Gen b * cl44Gen c * cl44Gen d) := by
    intro a b c d hac had hbc hbd
    have hca : cl44Gen c * cl44Gen a = -(cl44Gen a * cl44Gen c) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hac)
    have hcb : cl44Gen c * cl44Gen b = -(cl44Gen b * cl44Gen c) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hbc)
    have hda : cl44Gen d * cl44Gen a = -(cl44Gen a * cl44Gen d) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm had)
    have hdb : cl44Gen d * cl44Gen b = -(cl44Gen b * cl44Gen d) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hbd)
    have hcomm : cl44Bivector c d * cl44Bivector a b = cl44Bivector a b * cl44Bivector c d := by
      unfold cl44Bivector
      calc
        (cl44Gen c * cl44Gen d) * (cl44Gen a * cl44Gen b)
            = cl44Gen c * ((cl44Gen d * cl44Gen a) * cl44Gen b) := by
                simp only [Matrix.mul_assoc]
        _ = -(cl44Gen c * (cl44Gen a * (cl44Gen d * cl44Gen b))) := by
                rw [hda]
                simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
        _ = cl44Gen c * (cl44Gen a * (cl44Gen b * cl44Gen d)) := by
                rw [hdb, Matrix.mul_neg, Matrix.mul_neg, neg_neg]
        _ = -(cl44Gen a * ((cl44Gen c * cl44Gen b) * cl44Gen d)) := by
                calc
                  cl44Gen c * (cl44Gen a * (cl44Gen b * cl44Gen d))
                      = (cl44Gen c * cl44Gen a) * (cl44Gen b * cl44Gen d) := by
                          simp only [Matrix.mul_assoc]
                  _ = -(cl44Gen a * ((cl44Gen c * cl44Gen b) * cl44Gen d)) := by
                          rw [hca]
                          simp only [Matrix.neg_mul, Matrix.mul_assoc]
        _ = (cl44Gen a * cl44Gen b) * (cl44Gen c * cl44Gen d) := by
                rw [hcb]
                simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    refine ⟨?_, ?_⟩
    · rw [hcomm, sub_self]
    · rw [hcomm, ← two_smul ℝ]
      unfold cl44Bivector
      simp only [Matrix.mul_assoc]
  exact ⟨@h1, @h2, @h3, @h4⟩

/-! ### Intrinsic D₄ root-vector soldering in the Clifford bivector carrier

These definitions construct null vectors from the existing split Clifford
generators. Their products are actual bivectors, and the Cartan weights below
are calculated by ambient matrix commutators. -/

def d4Cartan0 : Matrix Krein16Idx Krein16Idx ℝ := cl44Bivector 0 4
def d4Cartan1 : Matrix Krein16Idx Krein16Idx ℝ := cl44Bivector 1 5
def d4Cartan2 : Matrix Krein16Idx Krein16Idx ℝ := cl44Bivector 2 6
def d4Cartan3 : Matrix Krein16Idx Krein16Idx ℝ := cl44Bivector 3 7
def d4NullPlus0 : Matrix Krein16Idx Krein16Idx ℝ := cl44Gen 0 + cl44Gen 4
def d4NullPlus1 : Matrix Krein16Idx Krein16Idx ℝ := cl44Gen 1 + cl44Gen 5
def d4RootVectorPlusPlus : Matrix Krein16Idx Krein16Idx ℝ := d4NullPlus0 * d4NullPlus1

private lemma d4Cartan0_nullPlus0_weight :
    d4Cartan0 * d4NullPlus0 - d4NullPlus0 * d4Cartan0 = (-2 : ℝ) • d4NullPlus0 := by
  have h0 : d4Cartan0 * cl44Gen 0 - cl44Gen 0 * d4Cartan0 =
      (-2 : ℝ) • cl44Gen 4 := by
    rcases cl44Bivector_orthogonal_shear with ⟨_, hsecond, _, _⟩
    have h := hsecond
      (a := (4 : Fin 8)) (b := (0 : Fin 8)) (by decide)
    have hs : cl44Bivector 4 0 = -cl44Bivector 0 4 := by
      unfold cl44Bivector
      exact eq_neg_of_add_eq_zero_right (cl44Gen_anticomm (by decide))
    calc
      d4Cartan0 * cl44Gen 0 - cl44Gen 0 * d4Cartan0 =
          -(cl44Bivector 4 0 * cl44Gen 0 - cl44Gen 0 * cl44Bivector 4 0) := by
            dsimp [d4Cartan0]
            rw [hs]
            noncomm_ring
      _ = -((2 : ℝ) • cl44Gen 4) := by rw [h]; norm_num
      _ = (-2 : ℝ) • cl44Gen 4 := by rw [neg_smul]
  have h4 : d4Cartan0 * cl44Gen 4 - cl44Gen 4 * d4Cartan0 =
      (-2 : ℝ) • cl44Gen 0 := by
    rcases cl44Bivector_orthogonal_shear with ⟨_, hsecond, _, _⟩
    have h := hsecond
      (a := (0 : Fin 8)) (b := (4 : Fin 8)) (by decide)
    simpa [d4Cartan0] using h
  dsimp [d4NullPlus0]
  calc
    d4Cartan0 * (cl44Gen 0 + cl44Gen 4) - (cl44Gen 0 + cl44Gen 4) * d4Cartan0 =
        (d4Cartan0 * cl44Gen 0 - cl44Gen 0 * d4Cartan0) +
          (d4Cartan0 * cl44Gen 4 - cl44Gen 4 * d4Cartan0) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = (-2 : ℝ) • (cl44Gen 0 + cl44Gen 4) := by
      rw [h0, h4, smul_add]
      abel

private lemma d4Cartan0_nullPlus1_fixed :
    d4Cartan0 * d4NullPlus1 - d4NullPlus1 * d4Cartan0 = 0 := by
  change cl44Bivector 0 4 * (cl44Gen 1 + cl44Gen 5) -
    (cl44Gen 1 + cl44Gen 5) * cl44Bivector 0 4 = 0
  rcases cl44Bivector_orthogonal_shear with ⟨hfirst, _, _, _⟩
  have h1 := hfirst
    (a := (0 : Fin 8)) (b := (4 : Fin 8)) (c := (1 : Fin 8)) (by decide) (by decide)
  have h5 := hfirst
    (a := (0 : Fin 8)) (b := (4 : Fin 8)) (c := (5 : Fin 8)) (by decide) (by decide)
  calc
    cl44Bivector 0 4 * (cl44Gen 1 + cl44Gen 5) -
        (cl44Gen 1 + cl44Gen 5) * cl44Bivector 0 4 =
        (cl44Bivector 0 4 * cl44Gen 1 - cl44Gen 1 * cl44Bivector 0 4) +
          (cl44Bivector 0 4 * cl44Gen 5 - cl44Gen 5 * cl44Bivector 0 4) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = 0 := by rw [h1, h5]; abel

private lemma d4Cartan1_nullPlus1_weight :
    d4Cartan1 * d4NullPlus1 - d4NullPlus1 * d4Cartan1 = (-2 : ℝ) • d4NullPlus1 := by
  have h1 : d4Cartan1 * cl44Gen 1 - cl44Gen 1 * d4Cartan1 =
      (-2 : ℝ) • cl44Gen 5 := by
    rcases cl44Bivector_orthogonal_shear with ⟨_, hsecond, _, _⟩
    have h := hsecond
      (a := (5 : Fin 8)) (b := (1 : Fin 8)) (by decide)
    have hs : cl44Bivector 5 1 = -cl44Bivector 1 5 := by
      unfold cl44Bivector
      exact eq_neg_of_add_eq_zero_right (cl44Gen_anticomm (by decide))
    calc
      d4Cartan1 * cl44Gen 1 - cl44Gen 1 * d4Cartan1 =
          -(cl44Bivector 5 1 * cl44Gen 1 - cl44Gen 1 * cl44Bivector 5 1) := by
            dsimp [d4Cartan1]
            rw [hs]
            noncomm_ring
      _ = -((2 : ℝ) • cl44Gen 5) := by rw [h]; norm_num
      _ = (-2 : ℝ) • cl44Gen 5 := by rw [neg_smul]
  have h5 : d4Cartan1 * cl44Gen 5 - cl44Gen 5 * d4Cartan1 =
      (-2 : ℝ) • cl44Gen 1 := by
    rcases cl44Bivector_orthogonal_shear with ⟨_, hsecond, _, _⟩
    have h := hsecond
      (a := (1 : Fin 8)) (b := (5 : Fin 8)) (by decide)
    simpa [d4Cartan1] using h
  dsimp [d4NullPlus1]
  calc
    d4Cartan1 * (cl44Gen 1 + cl44Gen 5) - (cl44Gen 1 + cl44Gen 5) * d4Cartan1 =
        (d4Cartan1 * cl44Gen 1 - cl44Gen 1 * d4Cartan1) +
          (d4Cartan1 * cl44Gen 5 - cl44Gen 5 * d4Cartan1) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = (-2 : ℝ) • (cl44Gen 1 + cl44Gen 5) := by
      rw [h1, h5, smul_add]
      abel

private lemma d4Cartan1_nullPlus0_fixed :
    d4Cartan1 * d4NullPlus0 - d4NullPlus0 * d4Cartan1 = 0 := by
  change cl44Bivector 1 5 * (cl44Gen 0 + cl44Gen 4) -
    (cl44Gen 0 + cl44Gen 4) * cl44Bivector 1 5 = 0
  rcases cl44Bivector_orthogonal_shear with ⟨hfirst, _, _, _⟩
  have h0 := hfirst
    (a := (1 : Fin 8)) (b := (5 : Fin 8)) (c := (0 : Fin 8)) (by decide) (by decide)
  have h4 := hfirst
    (a := (1 : Fin 8)) (b := (5 : Fin 8)) (c := (4 : Fin 8)) (by decide) (by decide)
  calc
    cl44Bivector 1 5 * (cl44Gen 0 + cl44Gen 4) -
        (cl44Gen 0 + cl44Gen 4) * cl44Bivector 1 5 =
        (cl44Bivector 1 5 * cl44Gen 0 - cl44Gen 0 * cl44Bivector 1 5) +
          (cl44Bivector 1 5 * cl44Gen 4 - cl44Gen 4 * cl44Bivector 1 5) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = 0 := by rw [h0, h4]; abel

private lemma d4Cartan2_nullPlus0_fixed :
    d4Cartan2 * d4NullPlus0 - d4NullPlus0 * d4Cartan2 = 0 := by
  change cl44Bivector 2 6 * (cl44Gen 0 + cl44Gen 4) -
    (cl44Gen 0 + cl44Gen 4) * cl44Bivector 2 6 = 0
  rcases cl44Bivector_orthogonal_shear with ⟨hfirst, _, _, _⟩
  have h0 := hfirst (a := (2 : Fin 8)) (b := (6 : Fin 8)) (c := (0 : Fin 8))
    (by decide) (by decide)
  have h4 := hfirst (a := (2 : Fin 8)) (b := (6 : Fin 8)) (c := (4 : Fin 8))
    (by decide) (by decide)
  calc
    cl44Bivector 2 6 * (cl44Gen 0 + cl44Gen 4) -
        (cl44Gen 0 + cl44Gen 4) * cl44Bivector 2 6 =
        (cl44Bivector 2 6 * cl44Gen 0 - cl44Gen 0 * cl44Bivector 2 6) +
          (cl44Bivector 2 6 * cl44Gen 4 - cl44Gen 4 * cl44Bivector 2 6) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = 0 := by rw [h0, h4]; abel

private lemma d4Cartan2_nullPlus1_fixed :
    d4Cartan2 * d4NullPlus1 - d4NullPlus1 * d4Cartan2 = 0 := by
  change cl44Bivector 2 6 * (cl44Gen 1 + cl44Gen 5) -
    (cl44Gen 1 + cl44Gen 5) * cl44Bivector 2 6 = 0
  rcases cl44Bivector_orthogonal_shear with ⟨hfirst, _, _, _⟩
  have h1 := hfirst (a := (2 : Fin 8)) (b := (6 : Fin 8)) (c := (1 : Fin 8))
    (by decide) (by decide)
  have h5 := hfirst (a := (2 : Fin 8)) (b := (6 : Fin 8)) (c := (5 : Fin 8))
    (by decide) (by decide)
  calc
    cl44Bivector 2 6 * (cl44Gen 1 + cl44Gen 5) -
        (cl44Gen 1 + cl44Gen 5) * cl44Bivector 2 6 =
        (cl44Bivector 2 6 * cl44Gen 1 - cl44Gen 1 * cl44Bivector 2 6) +
          (cl44Bivector 2 6 * cl44Gen 5 - cl44Gen 5 * cl44Bivector 2 6) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = 0 := by rw [h1, h5]; abel

private lemma d4Cartan3_nullPlus0_fixed :
    d4Cartan3 * d4NullPlus0 - d4NullPlus0 * d4Cartan3 = 0 := by
  change cl44Bivector 3 7 * (cl44Gen 0 + cl44Gen 4) -
    (cl44Gen 0 + cl44Gen 4) * cl44Bivector 3 7 = 0
  rcases cl44Bivector_orthogonal_shear with ⟨hfirst, _, _, _⟩
  have h0 := hfirst (a := (3 : Fin 8)) (b := (7 : Fin 8)) (c := (0 : Fin 8))
    (by decide) (by decide)
  have h4 := hfirst (a := (3 : Fin 8)) (b := (7 : Fin 8)) (c := (4 : Fin 8))
    (by decide) (by decide)
  calc
    cl44Bivector 3 7 * (cl44Gen 0 + cl44Gen 4) -
        (cl44Gen 0 + cl44Gen 4) * cl44Bivector 3 7 =
        (cl44Bivector 3 7 * cl44Gen 0 - cl44Gen 0 * cl44Bivector 3 7) +
          (cl44Bivector 3 7 * cl44Gen 4 - cl44Gen 4 * cl44Bivector 3 7) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = 0 := by rw [h0, h4]; abel

private lemma d4Cartan3_nullPlus1_fixed :
    d4Cartan3 * d4NullPlus1 - d4NullPlus1 * d4Cartan3 = 0 := by
  change cl44Bivector 3 7 * (cl44Gen 1 + cl44Gen 5) -
    (cl44Gen 1 + cl44Gen 5) * cl44Bivector 3 7 = 0
  rcases cl44Bivector_orthogonal_shear with ⟨hfirst, _, _, _⟩
  have h1 := hfirst (a := (3 : Fin 8)) (b := (7 : Fin 8)) (c := (1 : Fin 8))
    (by decide) (by decide)
  have h5 := hfirst (a := (3 : Fin 8)) (b := (7 : Fin 8)) (c := (5 : Fin 8))
    (by decide) (by decide)
  calc
    cl44Bivector 3 7 * (cl44Gen 1 + cl44Gen 5) -
        (cl44Gen 1 + cl44Gen 5) * cl44Bivector 3 7 =
        (cl44Bivector 3 7 * cl44Gen 1 - cl44Gen 1 * cl44Bivector 3 7) +
          (cl44Bivector 3 7 * cl44Gen 5 - cl44Gen 5 * cl44Bivector 3 7) := by
            rw [Matrix.mul_add, Matrix.add_mul]
            abel
    _ = 0 := by rw [h1, h5]; abel

private lemma commutator_mul_left {R : Type*} [Ring R] (H U V : R) :
    H * (U * V) - (U * V) * H = (H * U - U * H) * V + U * (H * V - V * H) := by
  noncomm_ring

/-- A concrete Clifford root vector has weight `(-2,-2)` for the first two
split-Cartan bivectors. This verifies the soldering in the real 16-dimensional
matrix representation, without transporting the bracket from the `g₂` carrier. -/
theorem d4_rootVectorPlusPlus_cartan_weights :
    d4Cartan0 * d4RootVectorPlusPlus - d4RootVectorPlusPlus * d4Cartan0 =
        (-2 : ℝ) • d4RootVectorPlusPlus ∧
    d4Cartan1 * d4RootVectorPlusPlus - d4RootVectorPlusPlus * d4Cartan1 =
        (-2 : ℝ) • d4RootVectorPlusPlus := by
  constructor
  · change d4Cartan0 * (d4NullPlus0 * d4NullPlus1) -
      (d4NullPlus0 * d4NullPlus1) * d4Cartan0 =
      (-2 : ℝ) • (d4NullPlus0 * d4NullPlus1)
    rw [commutator_mul_left, d4Cartan0_nullPlus0_weight, d4Cartan0_nullPlus1_fixed]
    simp
  · change d4Cartan1 * (d4NullPlus0 * d4NullPlus1) -
      (d4NullPlus0 * d4NullPlus1) * d4Cartan1 =
      (-2 : ℝ) • (d4NullPlus0 * d4NullPlus1)
    rw [commutator_mul_left, d4Cartan1_nullPlus0_fixed, d4Cartan1_nullPlus1_weight]
    simp

/-- Grade-1 vector subspace `Cl⁽¹⁾(4,4) = span{γ₀, …, γ₇} ⊂ M₁₆(ℝ)`. -/
def cl44Vec1Submodule : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ (Set.range cl44Gen)

/-- Canonical 4-vector `F₄ = e₀ e₁ e₂ e₃ ∈ Cl⁽⁴⁾(4,4)`. -/
def cl44FourVec : Matrix Krein16Idx Krein16Idx ℝ :=
  cl44Gen 0 * cl44Gen 1 * cl44Gen 2 * cl44Gen 3

theorem cl11Neg_trace : Matrix.trace cl11Neg = 0 := by
  unfold Matrix.trace cl11Neg
  rw [Fin.sum_univ_two]
  norm_num

/-- Hilbert–Schmidt trace orthogonality of the 8 generators of `Cl(4,4)`:
`Tr(γ_a γ_b) = ±16` when `a = b` and `0` when `a ≠ b`. -/
theorem trace_cl44Gen_mul (a b : Fin 8) :
    Matrix.trace (cl44Gen a * cl44Gen b) =
      if a = b then (if a.val < 4 then 16 else -16) else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [cl44Gen_sq]
    simp only [↓reduceIte]
    split_ifs <;> simp
  · have hcomm := Matrix.trace_mul_comm (cl44Gen a) (cl44Gen b)
    have hanti : cl44Gen b * cl44Gen a = -(cl44Gen a * cl44Gen b) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab)
    rw [hanti, Matrix.trace_neg] at hcomm
    simp only [hab, ↓reduceIte]
    linarith

/-- Linear independence of all 8 Clifford vector generators `cl44Gen : Fin 8 → M₁₆(ℝ)`. -/
theorem cl44Gen_linearIndependent : LinearIndependent ℝ cl44Gen := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hmul := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => cl44Gen a * M) hc
  rw [Matrix.mul_zero, Matrix.mul_sum] at hmul
  have htr := congrArg Matrix.trace hmul
  rw [Matrix.trace_zero, Matrix.trace_sum] at htr
  have hsum : (∑ b : Fin 8, Matrix.trace (cl44Gen a * (c b • cl44Gen b))) =
      c a * (if a.val < 4 then 16 else -16) := by
    rw [Finset.sum_eq_single a]
    · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_cl44Gen_mul]
      simp only [↓reduceIte]
    · intro b _ hb
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_cl44Gen_mul]
      simp only [hb.symm, ↓reduceIte, mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [hsum] at htr
  rcases mul_eq_zero.mp htr with hc0 | hsig
  · exact hc0
  · split_ifs at hsig <;> norm_num at hsig

/-- `Module.finrank ℝ cl44Vec1Submodule = 8`. -/
theorem finrank_cl44Vec1Submodule : Module.finrank ℝ cl44Vec1Submodule = 8 := by
  unfold cl44Vec1Submodule
  rw [finrank_span_eq_card cl44Gen_linearIndependent, Fintype.card_fin]

/-- Every bivector `B_{ab}` (`a ≠ b`) normalizes `Cl⁽¹⁾(4,4)`: `[B_{ab}, X] ∈ cl44Vec1Submodule`. -/
theorem cl44Bivector_normalizes_vec1 {a b : Fin 8} (hab : a ≠ b)
    {X : Matrix Krein16Idx Krein16Idx ℝ} (hX : X ∈ cl44Vec1Submodule) :
    cl44Bivector a b * X - X * cl44Bivector a b ∈ cl44Vec1Submodule := by
  have hmem : ∀ k : Fin 8, cl44Gen k ∈ cl44Vec1Submodule :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  have heq : ∀ x y : Matrix Krein16Idx Krein16Idx ℝ,
      cl44Bivector a b * (x + y) - (x + y) * cl44Bivector a b =
        (cl44Bivector a b * x - x * cl44Bivector a b) +
          (cl44Bivector a b * y - y * cl44Bivector a b) := by
    intro x y
    rw [Matrix.mul_add, Matrix.add_mul]
    abel
  refine Submodule.span_induction (hx := hX) ?_ ?_ ?_ ?_
  · rintro _ ⟨c, rfl⟩
    by_cases hca : c = a
    · subst hca
      have hba : cl44Bivector c b = -(cl44Bivector b c) := by
        unfold cl44Bivector
        exact eq_neg_of_add_eq_zero_left (cl44Gen_anticomm hab)
      have hneg_eq : cl44Bivector c b * cl44Gen c - cl44Gen c * cl44Bivector c b =
          -(cl44Bivector b c * cl44Gen c - cl44Gen c * cl44Bivector b c) := by
        rw [hba, Matrix.neg_mul, Matrix.mul_neg]
        abel
      rw [hneg_eq, cl44Bivector_orthogonal_shear.2.1 hab.symm]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hmem b)))
    · by_cases hcb : c = b
      · subst hcb
        rw [cl44Bivector_orthogonal_shear.2.1 hab]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hmem a))
      · rw [cl44Bivector_orthogonal_shear.1 hca hcb]
        exact Submodule.zero_mem _
  · rw [Matrix.mul_zero, Matrix.zero_mul, sub_self]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [heq]
    exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
    exact Submodule.smul_mem _ r hx

/-- Any matrix `W ∈ cl44Vec1Submodule` orthogonal to all 8 generators under Hilbert–Schmidt
trace vanishes identically. -/
theorem vec1_eq_zero_of_trace_orthogonal {W : Matrix Krein16Idx Krein16Idx ℝ}
    (hW : W ∈ cl44Vec1Submodule) (htr : ∀ a : Fin 8, Matrix.trace (cl44Gen a * W) = 0) :
    W = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hW
  have hc0 : ∀ a : Fin 8, c a = 0 := by
    intro a
    have ha := htr a
    rw [← hc, Matrix.mul_sum, Matrix.trace_sum] at ha
    have hsum : (∑ b : Fin 8, Matrix.trace (cl44Gen a * (c b • cl44Gen b))) =
        c a * (if a.val < 4 then 16 else -16) := by
      rw [Finset.sum_eq_single a]
      · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_cl44Gen_mul]
        simp only [↓reduceIte]
      · intro b _ hb
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_cl44Gen_mul]
        simp only [hb.symm, ↓reduceIte, mul_zero]
      · intro ha'
        exact absurd (Finset.mem_univ a) ha'
    rw [hsum] at ha
    rcases mul_eq_zero.mp ha with hc0' | hsig
    · exact hc0'
    · split_ifs at hsig <;> norm_num at hsig
  rw [← hc]
  simp only [hc0, zero_smul, Finset.sum_const_zero]

/-- **4-Vector Normalizer Escape Theorem**: `[F₄, e₀] = -2 e₁ e₂ e₃ ≠ 0` is trace-orthogonal
to every vector generator `γ_a`, and therefore `∉ cl44Vec1Submodule`. -/
theorem cl44FourVec_exits_vec1_normalizer :
    cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec =
      (-2 : ℝ) • (cl44Gen 1 * cl44Gen 2 * cl44Gen 3) ∧
    cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec ≠ 0 ∧
    (∀ a : Fin 8,
      Matrix.trace (cl44Gen a * (cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec)) = 0) ∧
    cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec ∉ cl44Vec1Submodule := by
  have h123 : cl44Gen 1 * cl44Gen 2 * cl44Gen 3 =
      tensor4 cl11Grad cl11Pos cl11Neg cl11Pos := by
    simp [cl44Gen]
  have hbr : cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec =
      (-2 : ℝ) • (cl44Gen 1 * cl44Gen 2 * cl44Gen 3) := by
    have hl : cl44FourVec * cl44Gen 0 = -tensor4 cl11Grad cl11Pos cl11Neg cl11Pos := by
      simp [cl44FourVec, cl44Gen]
    have hr : cl44Gen 0 * cl44FourVec = tensor4 cl11Grad cl11Pos cl11Neg cl11Pos := by
      simp [cl44FourVec, cl44Gen]
    rw [hl, hr, h123, neg_smul, two_smul]
    abel
  have hnz : cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec ≠ 0 := by
    intro h0
    rw [hbr, h123] at h0
    have hpt := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ =>
      M (0, 0, 0, 0) (0, 1, 1, 1)) h0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, tensor4, cl11Grad, cl11Pos,
      cl11Neg, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hpt
    norm_num at hpt
  have htr : ∀ a : Fin 8,
      Matrix.trace (cl44Gen a * (cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec)) = 0 := by
    intro a
    rw [hbr, h123, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have htz : Matrix.trace (cl44Gen a * tensor4 cl11Grad cl11Pos cl11Neg cl11Pos) = 0 := by
      fin_cases a <;>
        (unfold cl44Gen; rw [tensor4_mul, tensor4_trace];
         simp [cl11Pos_trace, cl11Neg_trace, cl11Grad_trace])
    rw [htz, mul_zero]
  have hnot : cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec ∉ cl44Vec1Submodule := by
    intro hmem
    exact hnz (vec1_eq_zero_of_trace_orthogonal hmem htr)
  exact ⟨hbr, hnz, htr, hnot⟩

end KreinCl44AndBivectorShear

/-! ## Section 3: Cartan `S₃` Triality on `ℝ⁴` & Reduction to 2D Split Cartan -/

section CartanS3Triality

/-- Vector–Spinor Hadamard swap `σ_{VS} = ½ H₄` on `ℝ⁴`. -/
def trialitySwapVS : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

/-- Spinor chirality reflection `σ_{±} = diag(1, 1, 1, -1)` on `ℝ⁴`. -/
def trialitySwapSpin : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- Order-3 Cartan triality cycle `τ = σ_{VS} σ_{±}` on `ℝ⁴`. -/
def trialityCycle3 : Matrix (Fin 4) (Fin 4) ℝ :=
  trialitySwapVS * trialitySwapSpin

/-- Exact `S₃` Coxeter/Weyl presentation of Cartan triality on `ℝ⁴`:
`σ_{VS}² = 1`, `σ_{±}² = 1`, `τ³ = 1`, `τ ≠ 1`, and `σ_{±} τ σ_{±} = τ²`. -/
theorem cartan_s3_triality_presentation :
    trialitySwapVS * trialitySwapVS = 1 ∧
    trialitySwapSpin * trialitySwapSpin = 1 ∧
    trialityCycle3 ^ 3 = 1 ∧
    trialityCycle3 ≠ 1 ∧
    trialitySwapSpin * trialityCycle3 * trialitySwapSpin = trialityCycle3 ^ 2 := by
  have hvs : trialitySwapVS * trialitySwapVS = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapVS, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  have hsp : trialitySwapSpin * trialitySwapSpin = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapSpin, Matrix.mul_apply, Fin.sum_univ_four]
  have htau3 : trialityCycle3 ^ 3 = 1 := by
    unfold trialityCycle3
    rw [pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapVS, trialitySwapSpin, Matrix.mul_apply,
        Fin.sum_univ_four] <;> norm_num
  have hne : trialityCycle3 ≠ 1 := by
    intro h
    have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
    unfold trialityCycle3 trialitySwapVS trialitySwapSpin at h00
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00
    norm_num at h00
  have hconj : trialitySwapSpin * trialityCycle3 * trialitySwapSpin = trialityCycle3 ^ 2 := by
    unfold trialityCycle3
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapVS, trialitySwapSpin, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  exact ⟨hvs, hsp, htau3, hne, hconj⟩

/-- Explicit OpenGauss `T16` non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem triality_mat4_noncommutative :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨trialitySwapVS, trialitySwapSpin, ?_⟩
  intro h
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 3) h
  unfold trialitySwapVS trialitySwapSpin at h03
  simp only [Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at h03
  norm_num at h03

/-- Explicit `S₃`-fixed Cartan submodule of `Fin 4 → ℝ` under `trialitySwapVS` and `trialitySwapSpin`. -/
def s3FixedCartanSubmodule : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {v | trialitySwapVS.mulVec v = v ∧ trialitySwapSpin.mulVec v = v}
  zero_mem' := ⟨Matrix.mulVec_zero _, Matrix.mulVec_zero _⟩
  add_mem' {u v} hu hv :=
    ⟨by rw [Matrix.mulVec_add, hu.1, hv.1], by rw [Matrix.mulVec_add, hu.2, hv.2]⟩
  smul_mem' r v hv :=
    ⟨by rw [Matrix.mulVec_smul, hv.1], by rw [Matrix.mulVec_smul, hv.2]⟩

/-- Characterization of the `S₃`-fixed Cartan locus: `(v 3 = 0 ∧ v 0 = v 1 + v 2)`. -/
theorem cartan_s3_fixed_subspace_iff (v : Fin 4 → ℝ) :
    v ∈ s3FixedCartanSubmodule ↔ (v 3 = 0 ∧ v 0 = v 1 + v 2) := by
  change (trialitySwapVS.mulVec v = v ∧ trialitySwapSpin.mulVec v = v) ↔ (v 3 = 0 ∧ v 0 = v 1 + v 2)
  constructor
  · rintro ⟨hvs, hsp⟩
    have h3 : (trialitySwapSpin.mulVec v) 3 = v 3 := congrFun hsp 3
    have h0 : (trialitySwapVS.mulVec v) 0 = v 0 := congrFun hvs 0
    simp only [trialitySwapSpin, trialitySwapVS, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Matrix.of_apply] at h3 h0
    norm_num at h3 h0
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hv3, hv0⟩
    constructor
    · ext i
      fin_cases i <;>
        simp [trialitySwapVS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv3, hv0] <;>
        linarith
    · ext i
      fin_cases i <;>
        simp [trialitySwapSpin, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv3]

/-- Explicit `ℝ`-linear equivalence `(Fin 2 → ℝ) ≃ₗ[ℝ] s3FixedCartanSubmodule`. -/
def s3FixedCartanEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] s3FixedCartanSubmodule where
  toFun p := ⟨![p 0 + p 1, p 0, p 1, 0],
    (cartan_s3_fixed_subspace_iff _).mpr ⟨rfl, rfl⟩⟩
  invFun v := ![v.1 1, v.1 2]
  left_inv p := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    apply Subtype.ext
    have hv := (cartan_s3_fixed_subspace_iff v.1).mp v.2
    ext i
    fin_cases i <;> simp [hv.1, hv.2]
  map_add' p q := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' r p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [mul_add]

/-- The `S₃` triality symmetry cuts the 4D `D₄` Cartan subalgebra down to exact dimension `2`. -/
theorem finrank_s3FixedCartanSubmodule :
    Module.finrank ℝ s3FixedCartanSubmodule = 2 := by
  have h := s3FixedCartanEquiv.finrank_eq
  rw [Module.finrank_fin_fun] at h
  exact h.symm

/-- Integer-valued 24 roots `(±1, ±1)` of `D₄` inside `Fin 4 → ℤ` for fast decidable permutation verification. -/
private def d4RootZ : Fin 24 → Fin 4 → ℤ :=
  ![ ![1, 1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 0],
     ![1, 0, 1, 0], ![1, 0, -1, 0], ![-1, 0, 1, 0], ![-1, 0, -1, 0],
     ![1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 0, 0, 1], ![-1, 0, 0, -1],
     ![0, 1, 1, 0], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, -1, 0],
     ![0, 1, 0, 1], ![0, 1, 0, -1], ![0, -1, 0, 1], ![0, -1, 0, -1],
     ![0, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, -1] ]

private def hadamard4Z : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

private def spinRefl4Z : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- Explicit enumeration of all 24 roots `(±1, ±1)` of `D₄` inside `Fin 4 → ℝ`. -/
def d4Root (k : Fin 24) (i : Fin 4) : ℝ :=
  (d4RootZ k i : ℝ)

/-! ### Uniform support/sign data for the 24 concrete D₄ roots

The root table is arranged in six blocks of four sign choices. This map
records the two occupied Cartan coordinates of each block; `d4Root` remains
the authoritative signed coordinate vector. -/

private def d4RootSupport (k : Fin 24) : Fin 4 × Fin 4 :=
  match k.val / 4 with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | _ => (2, 3)

private lemma d4RootSupport_lt (k : Fin 24) :
    (d4RootSupport k).1 < (d4RootSupport k).2 := by
  fin_cases k <;> norm_num [d4RootSupport]

private lemma d4RootSupport_coordinates (k : Fin 24) :
    d4Root k (d4RootSupport k).1 ≠ 0 ∧
    d4Root k (d4RootSupport k).2 ≠ 0 ∧
    (∀ i : Fin 4, i ≠ (d4RootSupport k).1 →
      i ≠ (d4RootSupport k).2 → d4Root k i = 0) := by
  fin_cases k <;> norm_num [d4Root, d4RootZ, d4RootSupport] <;>
    intro i <;> fin_cases i <;> norm_num

private def d4SignedNullVector (i : Fin 4) (ε : ℝ) :
    Matrix Krein16Idx Krein16Idx ℝ :=
  cl44Gen (Fin.castAdd 4 i) + ε • cl44Gen (Fin.natAdd 4 i)

/-- For each of the 24 listed D₄ roots, select the two split-Clifford null
vectors in its support, with signs read from the actual root coordinates.
Their product is a concrete matrix in `M₁₆(ℝ)`, not merely a coordinate label. -/
def d4CliffordRootOperator (k : Fin 24) :
    Matrix Krein16Idx Krein16Idx ℝ :=
  let i := (d4RootSupport k).1
  let j := (d4RootSupport k).2
  d4SignedNullVector i (-d4Root k i) * d4SignedNullVector j (-d4Root k j)

/-- The uniform root construction specializes to the previously checked
`(-1,-1,0,0)` Clifford root vector. -/
theorem d4CliffordRootOperator_three_eq :
    d4CliffordRootOperator 3 = d4RootVectorPlusPlus := by
  norm_num [d4CliffordRootOperator, d4RootSupport, d4SignedNullVector,
    d4Root, d4RootZ, d4RootVectorPlusPlus, d4NullPlus0, d4NullPlus1]

/-- The Clifford null-vector product `d4RootVectorPlusPlus` is an operator
realization of the listed D₄ root `(-1,-1,0,0)`: its four Cartan commutators
are exactly twice the corresponding root coordinates. -/
theorem d4_rootVectorPlusPlus_matches_d4Root3 :
    (d4Cartan0 * d4RootVectorPlusPlus - d4RootVectorPlusPlus * d4Cartan0 =
        (2 * d4Root 3 0) • d4RootVectorPlusPlus) ∧
    (d4Cartan1 * d4RootVectorPlusPlus - d4RootVectorPlusPlus * d4Cartan1 =
        (2 * d4Root 3 1) • d4RootVectorPlusPlus) ∧
    (d4Cartan2 * d4RootVectorPlusPlus - d4RootVectorPlusPlus * d4Cartan2 =
        (2 * d4Root 3 2) • d4RootVectorPlusPlus) ∧
    (d4Cartan3 * d4RootVectorPlusPlus - d4RootVectorPlusPlus * d4Cartan3 =
        (2 * d4Root 3 3) • d4RootVectorPlusPlus) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [d4Root, d4RootZ] using d4_rootVectorPlusPlus_cartan_weights.1
  · simpa [d4Root, d4RootZ] using d4_rootVectorPlusPlus_cartan_weights.2
  · have hcoord : 2 * d4Root 3 2 = 0 := by norm_num [d4Root, d4RootZ]
    rw [hcoord, zero_smul]
    change d4Cartan2 * (d4NullPlus0 * d4NullPlus1) -
      (d4NullPlus0 * d4NullPlus1) * d4Cartan2 = 0
    rw [commutator_mul_left, d4Cartan2_nullPlus0_fixed, d4Cartan2_nullPlus1_fixed]
    simp
  · have hcoord : 2 * d4Root 3 3 = 0 := by norm_num [d4Root, d4RootZ]
    rw [hcoord, zero_smul]
    change d4Cartan3 * (d4NullPlus0 * d4NullPlus1) -
      (d4NullPlus0 * d4NullPlus1) * d4Cartan3 = 0
    rw [commutator_mul_left, d4Cartan3_nullPlus0_fixed, d4Cartan3_nullPlus1_fixed]
    simp

/-- Permutation induced on the 24 `D₄` roots by Hadamard reflection `trialitySwapVS`. -/
def d4PermVS : Fin 24 → Fin 24 :=
  ![0, 20, 23, 3, 4, 16, 19, 7, 8, 12, 15, 11, 9, 13, 14, 10, 5, 17, 18, 6, 1, 21, 22, 2]

/-- Permutation induced on the 24 `D₄` roots by chirality reflection `trialitySwapSpin`. -/
def d4PermSpin : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 12, 13, 14, 15, 17, 16, 19, 18, 21, 20, 23, 22]

/-- The root permutation induced by the order-three Cartan triality operator
`trialityCycle3 = trialitySwapVS * trialitySwapSpin`. Function composition follows the
matrix action convention: first apply the spin reflection, then the VS swap. -/
def d4TrialityCycle : Fin 24 → Fin 24 := d4PermVS ∘ d4PermSpin

/-- The `S₃` Coxeter relations for the listed triality permutations on the 24-root index type. -/
def d4TrialityRootPermutationPresentation : Prop :=
    (∀ k : Fin 24, d4PermVS (d4PermVS k) = k) ∧
    (∀ k : Fin 24, d4PermSpin (d4PermSpin k) = k) ∧
    (∀ k : Fin 24, d4TrialityCycle (d4TrialityCycle (d4TrialityCycle k)) = k) ∧
    d4TrialityCycle ≠ id ∧
    (∀ k : Fin 24,
      d4PermSpin (d4TrialityCycle (d4PermSpin k)) =
        d4TrialityCycle (d4TrialityCycle k))

/-- The listed root permutations satisfy the `S₃` Coxeter presentation: both generators are
involutions, their product has order three, and conjugating the product by the spin reflection
inverts it. This verifies the group relations on the enumerated root set, independently of any
Lie-bracket claim. -/
theorem d4_triality_root_permutation_presentation : d4TrialityRootPermutationPresentation := by
  change (∀ k : Fin 24, d4PermVS (d4PermVS k) = k) ∧
    (∀ k : Fin 24, d4PermSpin (d4PermSpin k) = k) ∧
    (∀ k : Fin 24, d4TrialityCycle (d4TrialityCycle (d4TrialityCycle k)) = k) ∧
    d4TrialityCycle ≠ id ∧
    (∀ k : Fin 24,
      d4PermSpin (d4TrialityCycle (d4PermSpin k)) =
        d4TrialityCycle (d4TrialityCycle k))
  decide

/-- The D₄ roots lying in the common fixed Cartan plane are exactly the six long-root
indices. The geometric condition is the previously established fixed-plane equation
`v 3 = 0 ∧ v 0 = v 1 + v 2`, evaluated on the explicit root list. -/
theorem d4Root_mem_fixedCartan_iff_longRootIndex (k : Fin 24) :
    d4Root k ∈ s3FixedCartanSubmodule ↔
      k ∈ ({0, 3, 4, 7, 13, 14} : Finset (Fin 24)) := by
  rw [cartan_s3_fixed_subspace_iff]
  fin_cases k <;> norm_num [d4Root, d4RootZ]

/-- Assignment of each of the 24 `D₄` roots to one of the 12 `S₃`-triality orbits
(`6` singleton long-root orbits and `6` three-element short-root orbits). -/
def d4OrbitId : Fin 24 → Fin 12 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9, 8, 10, 11, 9, 5, 5, 6, 6, 1, 1, 2, 2]

/-- Canonical representative index in `Fin 24` for each of the 12 `S₃` orbits. -/
def d4OrbitRep : Fin 12 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 13, 14]

/-- Explicit root-index fibers of the twelve triality orbits. -/
def d4OrbitFiber (o : Fin 12) : Finset (Fin 24) :=
  ![{0}, {1, 20, 21}, {2, 22, 23}, {3}, {4}, {5, 16, 17},
    {6, 18, 19}, {7}, {8, 9, 12}, {10, 11, 15}, {13}, {14}] o

/-- The displayed fibers agree with the orbit labels on all 24 roots. -/
theorem d4OrbitFiber_eq_filter (o : Fin 12) :
    d4OrbitFiber o = Finset.univ.filter (fun k : Fin 24 => d4OrbitId k = o) := by
  fin_cases o <;> decide

/-- The mean of the D₄ roots in one listed triality orbit, viewed in the Cartan coordinate
space `Fin 4 → ℝ`. This is the Reynolds average of that finite orbit. -/
noncomputable def d4OrbitMean (o : Fin 12) : Fin 4 → ℝ :=
  fun i => ((d4OrbitFiber o).card : ℝ)⁻¹ * ∑ k ∈ d4OrbitFiber o, d4Root k i

/-- Explicit coordinates of the twelve Reynolds means, used to keep the matrix checks local. -/
def d4OrbitMeanTable : Fin 12 → Fin 4 → ℝ :=
  ![![1, 1, 0, 0], ![1 / 3, -1 / 3, 2 / 3, 0],
    ![-1 / 3, 1 / 3, -2 / 3, 0], ![-1, -1, 0, 0],
    ![1, 0, 1, 0], ![1 / 3, 2 / 3, -1 / 3, 0],
    ![-1 / 3, -2 / 3, 1 / 3, 0], ![-1, 0, -1, 0],
    ![2 / 3, 1 / 3, 1 / 3, 0], ![-2 / 3, -1 / 3, -1 / 3, 0],
    ![0, 1, -1, 0], ![0, -1, 1, 0]]

/-- The Reynolds-average definition agrees coordinatewise with the explicit orbit-mean table. -/
theorem d4OrbitMean_eq_table : d4OrbitMean = d4OrbitMeanTable := by
  funext o
  fin_cases o <;> funext i <;> fin_cases i <;>
    norm_num [d4OrbitMean, d4OrbitFiber, d4OrbitMeanTable, d4Root, d4RootZ]

/-- The twelve orbit means are fixed by both generating triality reflections, and their squared
lengths are `2` for the six singleton orbits and `2/3` for the six three-root orbits. Hence the
folded root system has the long-to-short squared-length ratio `3`. This is a root-system statement;
it does not identify the folded root brackets with the separately constructed matrix subalgebra. -/
theorem d4_triality_folded_root_means :
    (∀ o : Fin 12,
      trialitySwapVS.mulVec (d4OrbitMean o) = d4OrbitMean o ∧
      trialitySwapSpin.mulVec (d4OrbitMean o) = d4OrbitMean o) ∧
    (∀ o : Fin 12,
      (∑ i : Fin 4, d4OrbitMean o i ^ 2) =
        if o.val = 0 ∨ o.val = 3 ∨ o.val = 4 ∨ o.val = 7 ∨ o.val = 10 ∨ o.val = 11
        then 2 else (2 : ℝ) / 3) := by
  rw [d4OrbitMean_eq_table]
  constructor
  · intro o
    fin_cases o <;> constructor <;> ext i <;> fin_cases i <;>
      norm_num [d4OrbitMeanTable, trialitySwapVS, trialitySwapSpin,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · intro o
    fin_cases o <;> norm_num [d4OrbitMeanTable, Fin.sum_univ_four]

/-- Explicit verification that `trialitySwapVS` and `trialitySwapSpin` permute the 24 `D₄` roots
according to `d4PermVS` and `d4PermSpin`. -/
theorem d4_triality_permutes_roots (k : Fin 24) :
    trialitySwapVS.mulVec (d4Root k) = d4Root (d4PermVS k) ∧
    trialitySwapSpin.mulVec (d4Root k) = d4Root (d4PermSpin k) := by
  have hVSentry : ∀ i j : Fin 4, (2 : ℝ) * trialitySwapVS i j = ((hadamard4Z i j : ℤ) : ℝ) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [trialitySwapVS, hadamard4Z]
  have hSPentry : ∀ i j : Fin 4, trialitySwapSpin i j = ((spinRefl4Z i j : ℤ) : ℝ) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [trialitySwapSpin, spinRefl4Z]
  have hVSz : ∀ (m : Fin 24) (i : Fin 4),
      ∑ j : Fin 4, hadamard4Z i j * d4RootZ m j = 2 * d4RootZ (d4PermVS m) i := by
    decide
  have hSPz : ∀ (m : Fin 24) (i : Fin 4),
      ∑ j : Fin 4, spinRefl4Z i j * d4RootZ m j = d4RootZ (d4PermSpin m) i := by
    decide
  constructor
  · ext i
    simp only [Matrix.mulVec, dotProduct]
    have hmul : (2 : ℝ) * ∑ j : Fin 4, trialitySwapVS i j * d4Root k j =
        (2 : ℝ) * d4Root (d4PermVS k) i := by
      rw [Finset.mul_sum]
      calc ∑ j : Fin 4, (2 : ℝ) * (trialitySwapVS i j * d4Root k j)
          = ∑ j : Fin 4, ((hadamard4Z i j : ℝ) * (d4RootZ k j : ℝ)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← mul_assoc, hVSentry i j, d4Root]
        _ = ((∑ j : Fin 4, hadamard4Z i j * d4RootZ k j : ℤ) : ℝ) := by
              push_cast; rfl
        _ = (((2 * d4RootZ (d4PermVS k) i : ℤ) : ℝ)) := by rw [hVSz k i]
        _ = (2 : ℝ) * d4Root (d4PermVS k) i := by push_cast; rfl
    linarith
  · ext i
    simp only [Matrix.mulVec, dotProduct]
    calc ∑ j : Fin 4, trialitySwapSpin i j * d4Root k j
        = ∑ j : Fin 4, ((spinRefl4Z i j : ℝ) * (d4RootZ k j : ℝ)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hSPentry i j, d4Root]
      _ = ((∑ j : Fin 4, spinRefl4Z i j * d4RootZ k j : ℤ) : ℝ) := by
            push_cast; rfl
      _ = ((d4RootZ (d4PermSpin k) i : ℤ) : ℝ) := by rw [hSPz k i]
      _ = d4Root (d4PermSpin k) i := rfl

/-- A root index is fixed by both permutations exactly when its root vector lies in the common
fixed Cartan plane. The permutation-to-vector direction uses the proved action formula; the
reverse direction reduces geometrically to the six roots in that plane. -/
theorem d4Root_fixedCartan_iff_common_fixed_index (k : Fin 24) :
    d4Root k ∈ s3FixedCartanSubmodule ↔
      d4PermVS k = k ∧ d4PermSpin k = k := by
  constructor
  · intro hk
    have hlong := (d4Root_mem_fixedCartan_iff_longRootIndex k).mp hk
    fin_cases k <;> simp_all [d4PermVS, d4PermSpin]
  · intro hk
    rcases d4_triality_permutes_roots k with ⟨hvs, hspin⟩
    change trialitySwapVS.mulVec (d4Root k) = d4Root k ∧
      trialitySwapSpin.mulVec (d4Root k) = d4Root k
    rw [hk.1] at hvs
    rw [hk.2] at hspin
    exact ⟨hvs, hspin⟩

/-- The roots fixed by both triality generators are exactly the six singleton-orbit indices.
This follows by identifying common-fixed roots with the fixed Cartan plane and then applying its
root-coordinate classification. -/
theorem d4_triality_common_fixed_roots :
    Finset.univ.filter (fun k : Fin 24 => d4PermVS k = k ∧ d4PermSpin k = k) =
      ({0, 3, 4, 7, 13, 14} : Finset (Fin 24)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← d4Root_fixedCartan_iff_common_fixed_index,
    d4Root_mem_fixedCartan_iff_longRootIndex]

/-- The order-three matrix triality operator acts on each enumerated root by the composite
permutation `d4TrialityCycle`. This is the matrix-to-root-coordinate compatibility law needed
before lifting the action to a Lie algebra with a specified root-space bracket. -/
theorem d4_triality_cycle_permutes_roots (k : Fin 24) :
    trialityCycle3.mulVec (d4Root k) = d4Root (d4TrialityCycle k) := by
  change (trialitySwapVS * trialitySwapSpin).mulVec (d4Root k) =
    d4Root (d4PermVS (d4PermSpin k))
  rw [← Matrix.mulVec_mulVec]
  rw [(d4_triality_permutes_roots k).2]
  exact (d4_triality_permutes_roots (d4PermSpin k)).1

/-- A root-space vector `f : Fin 24 → ℝ` is invariant under both `d4PermVS` and `d4PermSpin`
iff it is constant on each of the 12 `S₃` orbits (`d4OrbitId`). -/
theorem d4_root_fixed_iff_orbit_const (f : Fin 24 → ℝ) :
    ((∀ k : Fin 24, f (d4PermVS k) = f k) ∧ (∀ k : Fin 24, f (d4PermSpin k) = f k)) ↔
    (∀ k : Fin 24, f k = f (d4OrbitRep (d4OrbitId k))) := by
  constructor
  · rintro ⟨hvs, hsp⟩ k
    have h1_20 : f 20 = f 1 := hvs 1
    have h20_21 : f 21 = f 20 := hsp 20
    have h2_23 : f 23 = f 2 := hvs 2
    have h23_22 : f 22 = f 23 := hsp 23
    have h5_16 : f 16 = f 5 := hvs 5
    have h16_17 : f 17 = f 16 := hsp 16
    have h6_19 : f 19 = f 6 := hvs 6
    have h19_18 : f 18 = f 19 := hsp 19
    have h8_9 : f 9 = f 8 := hsp 8
    have h9_12 : f 12 = f 9 := hvs 9
    have h10_11 : f 11 = f 10 := hsp 10
    have h10_15 : f 15 = f 10 := hvs 10
    fin_cases k <;> simp only [d4OrbitId, d4OrbitRep]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact h8_9
    · rfl
    · exact h10_11
    · exact h9_12.trans h8_9
    · rfl
    · rfl
    · exact h10_15
    · exact h5_16
    · exact h16_17.trans h5_16
    · exact h19_18.trans h6_19
    · exact h6_19
    · exact h1_20
    · exact h20_21.trans h1_20
    · exact h23_22.trans h2_23
    · exact h2_23
  · intro horb
    have hinv : ∀ k : Fin 24,
        d4OrbitId (d4PermVS k) = d4OrbitId k ∧ d4OrbitId (d4PermSpin k) = d4OrbitId k := by
      decide
    constructor
    · intro k
      rw [horb (d4PermVS k), horb k, (hinv k).1]
    · intro k
      rw [horb (d4PermSpin k), horb k, (hinv k).2]

/-- Full 28-dimensional `D₄` Cartan+root carrier `(Fin 4 → ℝ) × (Fin 24 → ℝ)` restricted
to the `S₃`-triality-fixed subspace (`2` fixed Cartan directions + `12` root orbits = `14`). -/
def s3FixedSpin44Submodule : Submodule ℝ ((Fin 4 → ℝ) × (Fin 24 → ℝ)) where
  carrier := {p | p.1 ∈ s3FixedCartanSubmodule ∧
    (∀ k : Fin 24, p.2 (d4PermVS k) = p.2 k) ∧
    (∀ k : Fin 24, p.2 (d4PermSpin k) = p.2 k)}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => rfl, fun _ => rfl⟩
  add_mem' {u v} hu hv :=
    ⟨Submodule.add_mem _ hu.1 hv.1,
     fun k => by simp only [Prod.snd_add, Pi.add_apply, hu.2.1 k, hv.2.1 k],
     fun k => by simp only [Prod.snd_add, Pi.add_apply, hu.2.2 k, hv.2.2 k]⟩
  smul_mem' r u hu :=
    ⟨Submodule.smul_mem _ r hu.1,
     fun k => by simp only [Prod.smul_snd, Pi.smul_apply, hu.2.1 k],
     fun k => by simp only [Prod.smul_snd, Pi.smul_apply, hu.2.2 k]⟩

/-- Explicit `ℝ`-linear isomorphism `(Fin 14 → ℝ) ≃ₗ[ℝ] s3FixedSpin44Submodule`. -/
def s3FixedSpin44Equiv : (Fin 14 → ℝ) ≃ₗ[ℝ] s3FixedSpin44Submodule where
  toFun c :=
    ⟨((s3FixedCartanEquiv ![c 0, c 1]).1,
      fun k => c ⟨2 + (d4OrbitId k).val, by have hk := (d4OrbitId k).isLt; omega⟩),
     ⟨(s3FixedCartanEquiv ![c 0, c 1]).2,
      (d4_root_fixed_iff_orbit_const _).mpr (fun k => by
        have hoid : d4OrbitId (d4OrbitRep (d4OrbitId k)) = d4OrbitId k := by
          have hall : ∀ m : Fin 12, d4OrbitId (d4OrbitRep m) = m := by decide
          exact hall (d4OrbitId k)
        simp only [hoid])⟩⟩
  invFun p m :=
    if hm : m.val < 2 then
      (if m.val = 0 then p.1.1 1 else p.1.1 2)
    else
      p.1.2 (d4OrbitRep ⟨m.val - 2, by omega⟩)
  left_inv c := by
    have hid_rep : ∀ j : Fin 12, d4OrbitId (d4OrbitRep j) = j := by decide
    ext m
    fin_cases m
    · simp [s3FixedCartanEquiv]
    · simp [s3FixedCartanEquiv]
    all_goals
      simp [hid_rep]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · have hv := (cartan_s3_fixed_subspace_iff p.1.1).mp p.2.1
      ext i
      fin_cases i <;> simp [s3FixedCartanEquiv, hv.1, hv.2]
    · have hf := (d4_root_fixed_iff_orbit_const p.1.2).mp p.2.2
      ext k
      dsimp
      split_ifs
      · exfalso; omega
      · exfalso; omega
      · have hsub : (⟨2 + (d4OrbitId k).val - 2,
            by have hk := (d4OrbitId k).isLt; omega⟩ : Fin 12) = d4OrbitId k := by
          ext
          simp
        rw [hsub, ← hf k]
  map_add' c₁ c₂ := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      (fin_cases i <;> simp [s3FixedCartanEquiv]); ring
    · ext k
      rfl
  map_smul' r c := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [s3FixedCartanEquiv, mul_add]
    · ext k
      rfl

/-- **Cartan Triality `28 → 14` Cutting Theorem**: `(Fin 4 → ℝ) × (Fin 24 → ℝ)` has dimension
`28 = dim so(4,4)`, and its `S₃`-triality-fixed submodule `s3FixedSpin44Submodule` has exact
dimension `14 = 2 (Cartan) + 12 (root orbits)`. -/
theorem finrank_spin44_triality_cutting_28_to_14 :
    Module.finrank ℝ ((Fin 4 → ℝ) × (Fin 24 → ℝ)) = 28 ∧
    Module.finrank ℝ s3FixedSpin44Submodule = 14 := by
  have h28 : Module.finrank ℝ ((Fin 4 → ℝ) × (Fin 24 → ℝ)) = 28 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
  have h14 : Module.finrank ℝ s3FixedSpin44Submodule = 14 := by
    have h := s3FixedSpin44Equiv.finrank_eq
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  exact ⟨h28, h14⟩

end CartanS3Triality

/-! ## Section 4: Explicit 14-Dimensional Split `g_{2(2)}` Subalgebra inside `Cl^(2)(4,4)`, 5-Grading, Serre Syzygies, Jordan Jump, `finrank = 14`, & Centerlessness -/

section ExplicitSplitG2InCl44

attribute [local simp]
  tensor4_mul tensor4_one tensor4_transpose
  tensor4_zero_0 tensor4_zero_1 tensor4_zero_2 tensor4_zero_3
  tensor4_neg_0 tensor4_neg_1 tensor4_neg_2 tensor4_neg_3
  add_mul mul_add sub_mul mul_sub neg_mul mul_neg
  mul_assoc one_mul mul_one zero_mul mul_zero
  Matrix.transpose_add Matrix.transpose_sub Matrix.transpose_neg Matrix.transpose_one
  Matrix.add_mulVec Matrix.sub_mulVec Matrix.neg_mulVec Matrix.mulVec_add
  tensor4_mulVec one_mulVec2
  vec4_zero_0 vec4_zero_1 vec4_zero_2 vec4_zero_3
  vec4_neg_0 vec4_neg_1 vec4_neg_2 vec4_neg_3
  cl11Pos_sq cl11Neg_sq cl11Grad_sq
  cl11Pos_transpose cl11Neg_transpose cl11Grad_transpose
  cl11Up_transpose cl11Down_transpose cl11P0_transpose cl11P1_transpose
  cl11Grad_mulVec_ket0 cl11Grad_mulVec_ket1
  cl11Pos_mulVec_ket0 cl11Pos_mulVec_ket1
  cl11Neg_mulVec_ket0 cl11Neg_mulVec_ket1
  cl11Up_mulVec_ket0 cl11Up_mulVec_ket1
  cl11Down_mulVec_ket0 cl11Down_mulVec_ket1
  cl11P0_mulVec_ket0 cl11P0_mulVec_ket1
  cl11P1_mulVec_ket0 cl11P1_mulVec_ket1
  cl11Pos_mul_cl11Neg cl11Neg_mul_cl11Pos
  cl11Neg_mul_cl11Grad cl11Grad_mul_cl11Neg
  cl11Pos_mul_cl11Grad cl11Grad_mul_cl11Pos
  cl11Up_mul_cl11Up cl11Down_mul_cl11Down cl11Up_mul_cl11Down cl11Down_mul_cl11Up
  cl11P0_mul_cl11P0 cl11P1_mul_cl11P1 cl11P0_mul_cl11P1 cl11P1_mul_cl11P0
  cl11Grad_mul_cl11Up cl11Up_mul_cl11Grad cl11Grad_mul_cl11Down cl11Down_mul_cl11Grad
  cl11Grad_mul_cl11P0 cl11P0_mul_cl11Grad cl11Grad_mul_cl11P1 cl11P1_mul_cl11Grad
  cl11P0_mul_cl11Up cl11P1_mul_cl11Up cl11Up_mul_cl11P0 cl11Up_mul_cl11P1
  cl11P0_mul_cl11Down cl11P1_mul_cl11Down cl11Down_mul_cl11P0 cl11Down_mul_cl11P1
  cl11Pos_mul_cl11P0 cl11P0_mul_cl11Pos cl11Pos_mul_cl11P1 cl11P1_mul_cl11Pos
  cl11Neg_mul_cl11P0 cl11P0_mul_cl11Neg cl11Neg_mul_cl11P1 cl11P1_mul_cl11Neg
  cl11Pos_mul_cl11Up cl11Up_mul_cl11Pos cl11Pos_mul_cl11Down cl11Down_mul_cl11Pos
  cl11Neg_mul_cl11Up cl11Up_mul_cl11Neg cl11Neg_mul_cl11Down cl11Down_mul_cl11Neg

/-- Extremal Majorana–Weyl spinor `ψ₊ = |0,0,0,0⟩ + |1,1,1,1⟩ ∈ S₊ ⊂ ℝ¹⁶`. -/
def majoranaRefSpinor : Krein16Idx → ℝ :=
  vec4 ket0 ket0 ket0 ket0 + vec4 ket1 ket1 ket1 ket1

/-- `ψ₊` is strictly chiral-even (`Γ_{4,4} ψ₊ = ψ₊`) and strictly Krein-positive (`⟨ψ₊, η̂ ψ₊⟩ = 2`). -/
theorem majoranaRefSpinor_chiral_and_krein_norm :
    gamma44.mulVec majoranaRefSpinor = majoranaRefSpinor ∧
    dotProduct majoranaRefSpinor (kreinMetric88.mulVec majoranaRefSpinor) = 2 := by
  have hgam : gamma44.mulVec majoranaRefSpinor = majoranaRefSpinor := by
    unfold majoranaRefSpinor gamma44
    rw [Matrix.mulVec_add, tensor4_mulVec, tensor4_mulVec]
    rw [cl11Grad_mulVec_ket0, cl11Grad_mulVec_ket1]
    simp only [vec4_neg_0, vec4_neg_1, vec4_neg_2, vec4_neg_3, neg_neg]
  have hneg_dot : dotProduct majoranaRefSpinor (kreinMetric88.mulVec majoranaRefSpinor) = 2 := by
    have hmul : kreinMetric88.mulVec majoranaRefSpinor =
        vec4 ket1 ket1 ket1 ket1 + vec4 ket0 ket0 ket0 ket0 := by
      unfold majoranaRefSpinor kreinMetric88
      rw [Matrix.mulVec_add, tensor4_mulVec, tensor4_mulVec]
      rw [cl11Pos_mulVec_ket0, cl11Neg_mulVec_ket0, cl11Pos_mulVec_ket1, cl11Neg_mulVec_ket1]
      rw [vec4_neg_1, vec4_neg_3, neg_neg]
    have hkrein_apply : ∀ a b c d : Fin 2 → ℝ, ∀ e f g h : Fin 2 → ℝ,
        dotProduct (vec4 a b c d) (vec4 e f g h) =
          dotProduct a e * dotProduct b f * dotProduct c g * dotProduct d h := by
      intro a b c d e f g h
      unfold vec4 dotProduct
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
      ring
    have hk00 : dotProduct ket0 ket0 = 1 := by simp [ket0, dotProduct, Fin.sum_univ_two]
    have hk11 : dotProduct ket1 ket1 = 1 := by simp [ket1, dotProduct, Fin.sum_univ_two]
    have hk01 : dotProduct ket0 ket1 = 0 := by simp [ket0, ket1, dotProduct, Fin.sum_univ_two]
    have hk10 : dotProduct ket1 ket0 = 0 := by simp [ket0, ket1, dotProduct, Fin.sum_univ_two]
    rw [hmul]
    unfold majoranaRefSpinor
    rw [dotProduct_add, add_dotProduct, add_dotProduct, hkrein_apply, hkrein_apply,
      hkrein_apply, hkrein_apply]
    rw [hk00, hk11, hk01, hk10]
    norm_num
  exact ⟨hgam, hneg_dot⟩

/-- Triality-stabilized Lie subalgebra predicate inside `M₁₆(ℝ)`: Krein-skew, chiral-even,
commuting with `e₀`, and annihilating the reference Majorana–Weyl spinor `ψ₊`. -/
def IsSplitG2Stabilizer (B : Matrix Krein16Idx Krein16Idx ℝ) : Prop :=
  Bᵀ * kreinMetric88 + kreinMetric88 * B = 0 ∧
  B * gamma44 = gamma44 * B ∧
  B * cl44Gen 0 = cl44Gen 0 * B ∧
  B.mulVec majoranaRefSpinor = 0

/-- Any `B` satisfying `IsSplitG2Stabilizer` annihilates `e₀ ψ₊`, and `IsSplitG2Stabilizer`
closes under the Lie commutator bracket. -/
theorem isSplitG2Stabilizer_commutator_closure :
    (∀ B, IsSplitG2Stabilizer B → B.mulVec ((cl44Gen 0).mulVec majoranaRefSpinor) = 0) ∧
    (∀ A B, IsSplitG2Stabilizer A → IsSplitG2Stabilizer B →
      IsSplitG2Stabilizer (A * B - B * A)) := by
  have hann : ∀ B, IsSplitG2Stabilizer B → B.mulVec ((cl44Gen 0).mulVec majoranaRefSpinor) = 0 := by
    intro B hB
    rw [Matrix.mulVec_mulVec, hB.2.2.1, ← Matrix.mulVec_mulVec, hB.2.2.2, Matrix.mulVec_zero]
  have hcomm : ∀ A B, IsSplitG2Stabilizer A → IsSplitG2Stabilizer B →
      IsSplitG2Stabilizer (A * B - B * A) := by
    intro A B hA hB
    have hAskew : Aᵀ * kreinMetric88 = -(kreinMetric88 * A) := eq_neg_of_add_eq_zero_left hA.1
    have hBskew : Bᵀ * kreinMetric88 = -(kreinMetric88 * B) := eq_neg_of_add_eq_zero_left hB.1
    have hk1 : (A * B - B * A)ᵀ * kreinMetric88 + kreinMetric88 * (A * B - B * A) = 0 := by
      have ht1 : (Bᵀ * Aᵀ) * kreinMetric88 = (kreinMetric88 * B) * A := by
        calc (Bᵀ * Aᵀ) * kreinMetric88
            = Bᵀ * (Aᵀ * kreinMetric88) := Matrix.mul_assoc _ _ _
          _ = Bᵀ * (-(kreinMetric88 * A)) := by rw [hAskew]
          _ = -(Bᵀ * (kreinMetric88 * A)) := Matrix.mul_neg _ _
          _ = -((Bᵀ * kreinMetric88) * A) := by rw [← Matrix.mul_assoc]
          _ = -(-(kreinMetric88 * B) * A) := by rw [hBskew]
          _ = (kreinMetric88 * B) * A := by simp only [Matrix.neg_mul, neg_neg]
      have ht2 : (Aᵀ * Bᵀ) * kreinMetric88 = (kreinMetric88 * A) * B := by
        calc (Aᵀ * Bᵀ) * kreinMetric88
            = Aᵀ * (Bᵀ * kreinMetric88) := Matrix.mul_assoc _ _ _
          _ = Aᵀ * (-(kreinMetric88 * B)) := by rw [hBskew]
          _ = -(Aᵀ * (kreinMetric88 * B)) := Matrix.mul_neg _ _
          _ = -((Aᵀ * kreinMetric88) * B) := by rw [← Matrix.mul_assoc]
          _ = -(-(kreinMetric88 * A) * B) := by rw [hAskew]
          _ = (kreinMetric88 * A) * B := by simp only [Matrix.neg_mul, neg_neg]
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.sub_mul,
        ht1, ht2, Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    have hk2 : (A * B - B * A) * gamma44 = gamma44 * (A * B - B * A) := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hB.2.1, hA.2.1]
      rw [← Matrix.mul_assoc A gamma44 B, ← Matrix.mul_assoc B gamma44 A, hA.2.1, hB.2.1]
      rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
    have hk3 : (A * B - B * A) * cl44Gen 0 = cl44Gen 0 * (A * B - B * A) := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hB.2.2.1, hA.2.2.1]
      rw [← Matrix.mul_assoc A (cl44Gen 0) B, ← Matrix.mul_assoc B (cl44Gen 0) A,
        hA.2.2.1, hB.2.2.1]
      rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
    have hk4 : (A * B - B * A).mulVec majoranaRefSpinor = 0 := by
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hB.2.2.2, hA.2.2.2, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_self]
    exact ⟨hk1, hk2, hk3, hk4⟩
  exact ⟨hann, hcomm⟩

/-! ### Integer-Entry Spinor Ladder Operators & Explicit 14D Split `g_{2(2)}` Basis -/

def et0Op : Matrix Krein16Idx Krein16Idx ℝ := tensor4 cl11Neg 1 1 1
def u1Op : Matrix Krein16Idx Krein16Idx ℝ := tensor4 cl11Grad cl11Up 1 1
def d1Op : Matrix Krein16Idx Krein16Idx ℝ := tensor4 cl11Grad cl11Down 1 1
def u2Op : Matrix Krein16Idx Krein16Idx ℝ := tensor4 cl11Grad cl11Grad cl11Up 1
def d2Op : Matrix Krein16Idx Krein16Idx ℝ := tensor4 cl11Grad cl11Grad cl11Down 1
def u3Op : Matrix Krein16Idx Krein16Idx ℝ := tensor4 cl11Grad cl11Grad cl11Grad cl11Up
def d3Op : Matrix Krein16Idx Krein16Idx ℝ := tensor4 cl11Grad cl11Grad cl11Grad cl11Down

/-- Exact identification of integer ladder operators `(u_k, d_k)` with `(e_k ∓ ẽ_k)/2`. -/
theorem ladder_ops_clifford_identities :
    (2 : ℝ) • u1Op = cl44Gen 1 - cl44Gen 5 ∧
    (2 : ℝ) • d1Op = cl44Gen 1 + cl44Gen 5 ∧
    (2 : ℝ) • u2Op = cl44Gen 2 - cl44Gen 6 ∧
    (2 : ℝ) • d2Op = cl44Gen 2 + cl44Gen 6 ∧
    (2 : ℝ) • u3Op = cl44Gen 3 - cl44Gen 7 ∧
    (2 : ℝ) • d3Op = cl44Gen 3 + cl44Gen 7 := by
  have hpos_neg : (2 : ℝ) • cl11Up = cl11Pos - cl11Neg := by
    ext i j; (fin_cases i <;> fin_cases j <;> simp [cl11Up, cl11Pos, cl11Neg]); norm_num
  have hpos_pos : (2 : ℝ) • cl11Down = cl11Pos + cl11Neg := by
    ext i j; (fin_cases i <;> fin_cases j <;> simp [cl11Down, cl11Pos, cl11Neg]); norm_num
  have hsmul_slot1 : ∀ A B C D : Matrix (Fin 2) (Fin 2) ℝ, (2 : ℝ) • tensor4 A B C D = tensor4 A ((2 : ℝ) • B) C D := by
    intro A B C D; ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
    simp only [Matrix.smul_apply, smul_eq_mul, tensor4]; ring
  have hsmul_slot2 : ∀ A B C D : Matrix (Fin 2) (Fin 2) ℝ, (2 : ℝ) • tensor4 A B C D = tensor4 A B ((2 : ℝ) • C) D := by
    intro A B C D; ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
    simp only [Matrix.smul_apply, smul_eq_mul, tensor4]; ring
  have hsmul_slot3 : ∀ A B C D : Matrix (Fin 2) (Fin 2) ℝ, (2 : ℝ) • tensor4 A B C D = tensor4 A B C ((2 : ℝ) • D) := by
    intro A B C D; ext ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩
    simp only [Matrix.smul_apply, smul_eq_mul, tensor4]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold u1Op cl44Gen; rw [hsmul_slot1, hpos_neg, tensor4_sub_1]
  · unfold d1Op cl44Gen; rw [hsmul_slot1, hpos_pos, tensor4_add_1]
  · unfold u2Op cl44Gen; rw [hsmul_slot2, hpos_neg, tensor4_sub_2]
  · unfold d2Op cl44Gen; rw [hsmul_slot2, hpos_pos, tensor4_add_2]
  · unfold u3Op cl44Gen; rw [hsmul_slot3, hpos_neg, tensor4_sub_3]
  · unfold d3Op cl44Gen; rw [hsmul_slot3, hpos_pos, tensor4_add_3]

def g2Zpos2 : Matrix Krein16Idx Krein16Idx ℝ := u1Op * d3Op
def g2X1 : Matrix Krein16Idx Krein16Idx ℝ := u1Op * d2Op
def g2X2 : Matrix Krein16Idx Krein16Idx ℝ := u2Op * d3Op
def g2X3 : Matrix Krein16Idx Krein16Idx ℝ := u1Op * u2Op + et0Op * d3Op
def g2X4 : Matrix Krein16Idx Krein16Idx ℝ := d2Op * d3Op - et0Op * u1Op
def g2E0 : Matrix Krein16Idx Krein16Idx ℝ := u3Op * u1Op + et0Op * d2Op
def g2F0 : Matrix Krein16Idx Krein16Idx ℝ := d3Op * d1Op - et0Op * u2Op
def g2Y1 : Matrix Krein16Idx Krein16Idx ℝ := u2Op * d1Op
def g2Y2 : Matrix Krein16Idx Krein16Idx ℝ := u3Op * d2Op
def g2Y3 : Matrix Krein16Idx Krein16Idx ℝ := u2Op * u3Op + et0Op * d1Op
def g2Y4 : Matrix Krein16Idx Krein16Idx ℝ := d1Op * d2Op - et0Op * u3Op
def g2Zneg2 : Matrix Krein16Idx Krein16Idx ℝ := u3Op * d1Op
def g2H1 : Matrix Krein16Idx Krein16Idx ℝ := u1Op * d1Op - u3Op * d3Op
def g2H2 : Matrix Krein16Idx Krein16Idx ℝ := u2Op * d2Op - u3Op * d3Op

/-- Simple-root Cartan element `H_α = H₁ - 2 H₂`. -/
def g2Halpha : Matrix Krein16Idx Krein16Idx ℝ := g2H1 - (2 : ℝ) • g2H2

/-- The 14 explicit basis matrices of the split real exceptional Lie algebra `g_{2(2)} ⊂ Cl⁽²⁾(4,4)`. -/
def g2Basis : Fin 14 → Matrix Krein16Idx Krein16Idx ℝ
  | 0 => g2Zpos2
  | 1 => g2X1
  | 2 => g2X2
  | 3 => g2X3
  | 4 => g2X4
  | 5 => g2E0
  | 6 => g2F0
  | 7 => g2Y1
  | 8 => g2Y2
  | 9 => g2Y3
  | 10 => g2Y4
  | 11 => g2Zneg2
  | 12 => g2H1
  | 13 => g2H2

/-- Real Lie subalgebra carrier `g_{2(2)}` spanned by the 14 integer basis matrices inside `M₁₆(ℝ)`. -/
def g2Submodule : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ (Set.range g2Basis)

private theorem g2Zpos2_nf : g2Zpos2 = -tensor4 1 cl11Up cl11Grad cl11Down := by
  unfold g2Zpos2 u1Op d3Op; simp
private theorem g2X1_nf : g2X1 = -tensor4 1 cl11Up cl11Down 1 := by
  unfold g2X1 u1Op d2Op; simp
private theorem g2X2_nf : g2X2 = -tensor4 1 1 cl11Up cl11Down := by
  unfold g2X2 u2Op d3Op; simp
private theorem g2X3_nf : g2X3 = -tensor4 1 cl11Up cl11Up 1 + tensor4 cl11Pos cl11Grad cl11Grad cl11Down := by
  unfold g2X3 u1Op u2Op et0Op d3Op; simp
private theorem g2X4_nf : g2X4 = tensor4 1 1 cl11Down cl11Down - tensor4 cl11Pos cl11Up 1 1 := by
  unfold g2X4 d2Op d3Op et0Op u1Op; simp
private theorem g2E0_nf : g2E0 = tensor4 1 cl11Up cl11Grad cl11Up + tensor4 cl11Pos cl11Grad cl11Down 1 := by
  unfold g2E0 u3Op u1Op et0Op d2Op; simp
private theorem g2F0_nf : g2F0 = -tensor4 1 cl11Down cl11Grad cl11Down - tensor4 cl11Pos cl11Grad cl11Up 1 := by
  unfold g2F0 d3Op d1Op et0Op u2Op; simp
private theorem g2Y1_nf : g2Y1 = -tensor4 1 cl11Down cl11Up 1 := by
  unfold g2Y1 u2Op d1Op; simp
private theorem g2Y2_nf : g2Y2 = -tensor4 1 1 cl11Down cl11Up := by
  unfold g2Y2 u3Op d2Op; simp
private theorem g2Y3_nf : g2Y3 = -tensor4 1 1 cl11Up cl11Up + tensor4 cl11Pos cl11Down 1 1 := by
  unfold g2Y3 u2Op u3Op et0Op d1Op; simp
private theorem g2Y4_nf : g2Y4 = tensor4 1 cl11Down cl11Down 1 - tensor4 cl11Pos cl11Grad cl11Grad cl11Up := by
  unfold g2Y4 d1Op d2Op et0Op u3Op; simp
private theorem g2Zneg2_nf : g2Zneg2 = -tensor4 1 cl11Down cl11Grad cl11Up := by
  unfold g2Zneg2 u3Op d1Op; simp
private theorem g2H1_nf : g2H1 = tensor4 1 cl11P0 1 1 - tensor4 1 1 1 cl11P0 := by
  unfold g2H1 u1Op d1Op u3Op d3Op; simp
private theorem g2H2_nf : g2H2 = tensor4 1 1 cl11P0 1 - tensor4 1 1 1 cl11P0 := by
  unfold g2H2 u2Op d2Op u3Op d3Op; simp

section MatrixUnitExpand

attribute [local simp]
  cl11One_eq_P0_add_P1 cl11Grad_eq_P0_sub_P1
  cl11Pos_eq_Up_add_Down cl11Neg_eq_Down_sub_Up
  tensor4_add_0 tensor4_add_1 tensor4_add_2 tensor4_add_3
  tensor4_sub_0 tensor4_sub_1 tensor4_sub_2 tensor4_sub_3

private theorem g2Basis_krein_skew_aux (m : Fin 14) :
    (g2Basis m)ᵀ * kreinMetric88 + kreinMetric88 * g2Basis m = 0 := by
  fin_cases m <;> simp only [g2Basis]
  all_goals (
    first
      | rw [g2Zpos2_nf] | rw [g2X1_nf] | rw [g2X2_nf] | rw [g2X3_nf]
      | rw [g2X4_nf] | rw [g2E0_nf] | rw [g2F0_nf] | rw [g2Y1_nf]
      | rw [g2Y2_nf] | rw [g2Y3_nf] | rw [g2Y4_nf] | rw [g2Zneg2_nf]
      | rw [g2H1_nf] | rw [g2H2_nf]
    unfold kreinMetric88
    simp
    abel)

private theorem g2_x12_comm_aux :
    g2X1 * g2X2 - g2X2 * g2X1 = g2Zpos2 := by
  rw [g2X1_nf, g2X2_nf, g2Zpos2_nf]
  simp
  module

private theorem g2_x34_comm_aux :
    g2X3 * g2X4 - g2X4 * g2X3 = (3 : ℝ) • g2Zpos2 := by
  rw [g2X3_nf, g2X4_nf, g2Zpos2_nf]
  simp
  module

private theorem g2_jordan_ksym_aux :
    (tensor4 1 cl11Up 1 cl11Down)ᵀ * kreinMetric88 =
      kreinMetric88 * tensor4 1 cl11Up 1 cl11Down := by
  unfold kreinMetric88
  simp
  abel

private theorem g2_zpos2_zneg2_aux : g2Zpos2 * g2Zneg2 - g2Zneg2 * g2Zpos2 = g2H1 := by
  rw [g2Zpos2_nf, g2Zneg2_nf, g2H1_nf]; simp; module

private theorem g2_x1_y1_aux : g2X1 * g2Y1 - g2Y1 * g2X1 = g2H1 - g2H2 := by
  rw [g2X1_nf, g2Y1_nf, g2H1_nf, g2H2_nf]; simp; module

private theorem g2_x2_y2_aux : g2X2 * g2Y2 - g2Y2 * g2X2 = g2H2 := by
  rw [g2X2_nf, g2Y2_nf, g2H2_nf]; simp; module

private theorem g2_x3_e0_aux : g2X3 * g2E0 - g2E0 * g2X3 = (-2 : ℝ) • g2X4 := by
  rw [g2X3_nf, g2E0_nf, g2X4_nf]; simp; module

private theorem g2_x3_f0_aux : g2X3 * g2F0 - g2F0 * g2X3 = (3 : ℝ) • g2X2 := by
  rw [g2X3_nf, g2F0_nf, g2X2_nf]; simp; module

private theorem g2_x3_y3_aux : g2X3 * g2Y3 - g2Y3 * g2X3 = (2 : ℝ) • g2F0 := by
  rw [g2X3_nf, g2Y3_nf, g2F0_nf]; simp; module

private theorem g2_x3_y4_aux : g2X3 * g2Y4 - g2Y4 * g2X3 = -(g2H1 + g2H2) := by
  rw [g2X3_nf, g2Y4_nf, g2H1_nf, g2H2_nf]; simp; module

private theorem g2_x4_e0_aux : g2X4 * g2E0 - g2E0 * g2X4 = (-3 : ℝ) • g2X1 := by
  rw [g2X4_nf, g2E0_nf, g2X1_nf]; simp; module

private theorem g2_x4_f0_aux : g2X4 * g2F0 - g2F0 * g2X4 = (2 : ℝ) • g2X3 := by
  rw [g2X4_nf, g2F0_nf, g2X3_nf]; simp; module

private theorem g2_x4_y3_aux : g2X4 * g2Y3 - g2Y3 * g2X4 = (-2 : ℝ) • g2H1 + g2H2 := by
  rw [g2X4_nf, g2Y3_nf, g2H1_nf, g2H2_nf]; simp; module

private theorem g2_x4_y4_aux : g2X4 * g2Y4 - g2Y4 * g2X4 = (-2 : ℝ) • g2E0 := by
  rw [g2X4_nf, g2Y4_nf, g2E0_nf]; simp; module

private theorem g2_e0_f0_aux : g2E0 * g2F0 - g2F0 * g2E0 = (2 : ℝ) • g2H2 - g2H1 := by
  rw [g2E0_nf, g2F0_nf, g2H1_nf, g2H2_nf]; simp; module

private theorem g2_e0_y3_aux : g2E0 * g2Y3 - g2Y3 * g2E0 = (-2 : ℝ) • g2Y4 := by
  rw [g2E0_nf, g2Y3_nf, g2Y4_nf]; simp; module

private theorem g2_e0_y4_aux : g2E0 * g2Y4 - g2Y4 * g2E0 = (3 : ℝ) • g2Y2 := by
  rw [g2E0_nf, g2Y4_nf, g2Y2_nf]; simp; module

private theorem g2_f0_y3_aux : g2F0 * g2Y3 - g2Y3 * g2F0 = (-3 : ℝ) • g2Y1 := by
  rw [g2F0_nf, g2Y3_nf, g2Y1_nf]; simp; module

private theorem g2_f0_y4_aux : g2F0 * g2Y4 - g2Y4 * g2F0 = (2 : ℝ) • g2Y3 := by
  rw [g2F0_nf, g2Y4_nf, g2Y3_nf]; simp; module

private theorem g2_y3_y4_aux : g2Y3 * g2Y4 - g2Y4 * g2Y3 = (3 : ℝ) • g2Zneg2 := by
  rw [g2Y3_nf, g2Y4_nf, g2Zneg2_nf]; simp; module

end MatrixUnitExpand

private theorem g2Basis_mem_stabilizer_aux (k : Fin 14) :
    IsSplitG2Stabilizer (g2Basis k) := by
  have hk_nf : ∀ m : Fin 14,
      (g2Basis m)ᵀ * kreinMetric88 + kreinMetric88 * g2Basis m = 0 ∧
      g2Basis m * gamma44 = gamma44 * g2Basis m ∧
      g2Basis m * cl44Gen 0 = cl44Gen 0 * g2Basis m := by
    intro m
    refine ⟨g2Basis_krein_skew_aux m, ?_, ?_⟩
    · fin_cases m <;> simp only [g2Basis]
      all_goals (
        first
          | rw [g2Zpos2_nf] | rw [g2X1_nf] | rw [g2X2_nf] | rw [g2X3_nf]
          | rw [g2X4_nf] | rw [g2E0_nf] | rw [g2F0_nf] | rw [g2Y1_nf]
          | rw [g2Y2_nf] | rw [g2Y3_nf] | rw [g2Y4_nf] | rw [g2Zneg2_nf]
          | rw [g2H1_nf] | rw [g2H2_nf]
        unfold gamma44
        simp
        try abel)
    · fin_cases m <;> simp only [g2Basis]
      all_goals (
        first
          | rw [g2Zpos2_nf] | rw [g2X1_nf] | rw [g2X2_nf] | rw [g2X3_nf]
          | rw [g2X4_nf] | rw [g2E0_nf] | rw [g2F0_nf] | rw [g2Y1_nf]
          | rw [g2Y2_nf] | rw [g2Y3_nf] | rw [g2Y4_nf] | rw [g2Zneg2_nf]
          | rw [g2H1_nf] | rw [g2H2_nf]
        unfold cl44Gen
        simp
        try abel)
  have hann : (g2Basis k).mulVec majoranaRefSpinor = 0 := by
    fin_cases k <;> simp only [g2Basis]
    all_goals (
      first
        | rw [g2Zpos2_nf] | rw [g2X1_nf] | rw [g2X2_nf] | rw [g2X3_nf]
        | rw [g2X4_nf] | rw [g2E0_nf] | rw [g2F0_nf] | rw [g2Y1_nf]
        | rw [g2Y2_nf] | rw [g2Y3_nf] | rw [g2Y4_nf] | rw [g2Zneg2_nf]
        | rw [g2H1_nf] | rw [g2H2_nf]
      unfold majoranaRefSpinor
      repeat (first
        | rw [Matrix.add_mulVec] | rw [Matrix.sub_mulVec] | rw [Matrix.neg_mulVec]
        | rw [Matrix.mulVec_add] | rw [tensor4_mulVec] | rw [one_mulVec2]
        | rw [cl11Grad_mulVec_ket0] | rw [cl11Grad_mulVec_ket1]
        | rw [cl11Pos_mulVec_ket0] | rw [cl11Pos_mulVec_ket1]
        | rw [cl11Neg_mulVec_ket0] | rw [cl11Neg_mulVec_ket1]
        | rw [cl11Up_mulVec_ket0] | rw [cl11Up_mulVec_ket1]
        | rw [cl11Down_mulVec_ket0] | rw [cl11Down_mulVec_ket1]
        | rw [cl11P0_mulVec_ket0] | rw [cl11P0_mulVec_ket1]
        | rw [vec4_zero_0] | rw [vec4_zero_1] | rw [vec4_zero_2] | rw [vec4_zero_3]
        | rw [vec4_neg_0] | rw [vec4_neg_1] | rw [vec4_neg_2] | rw [vec4_neg_3])
      try abel)
  exact ⟨(hk_nf k).1, (hk_nf k).2.1, (hk_nf k).2.2, hann⟩

/-- Every matrix in `g2Submodule` satisfies `IsSplitG2Stabilizer` (and is therefore Krein-skew,
chiral-even, commutes with `e₀`, and annihilates `majoranaRefSpinor`). -/
theorem g2Submodule_mem_stabilizer {B : Matrix Krein16Idx Krein16Idx ℝ} (hB : B ∈ g2Submodule) :
    IsSplitG2Stabilizer B := by
  refine Submodule.span_induction (hx := hB) ?_ ?_ ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact g2Basis_mem_stabilizer_aux k
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]
    · simp only [Matrix.zero_mul, Matrix.mul_zero]
    · simp only [Matrix.zero_mul, Matrix.mul_zero]
    · exact Matrix.zero_mulVec _
  · intro X Y _ _ hX hY
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
      calc (Xᵀ * kreinMetric88 + Yᵀ * kreinMetric88) + (kreinMetric88 * X + kreinMetric88 * Y)
          = (Xᵀ * kreinMetric88 + kreinMetric88 * X) + (Yᵀ * kreinMetric88 + kreinMetric88 * Y) := by abel
        _ = 0 := by rw [hX.1, hY.1, add_zero]
    · rw [Matrix.add_mul, Matrix.mul_add, hX.2.1, hY.2.1]
    · rw [Matrix.add_mul, Matrix.mul_add, hX.2.2.1, hY.2.2.1]
    · rw [Matrix.add_mulVec, hX.2.2.2, hY.2.2.2, add_zero]
  · intro r X _ hX
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX.1, smul_zero]
    · rw [Matrix.smul_mul, Matrix.mul_smul, hX.2.1]
    · rw [Matrix.smul_mul, Matrix.mul_smul, hX.2.2.1]
    · rw [Matrix.smul_mulVec, hX.2.2.2, smul_zero]

/-- Eigenvalues of `ad_{H_θ}` defining the exact 5-grading `[-2, -1, 0, +1, +2]` of `g_{2(2)}`. -/
def g2Grade : Fin 14 → ℤ :=
  ![2, 1, 1, 1, 1, 0, 0, -1, -1, -1, -1, -2, 0, 0]

/-- Eigenvalues of `ad_{H_α}` distinguishing all 12 nonzero roots alongside `g2Grade`. -/
def g2AlphaWeight : Fin 14 → ℤ :=
  ![0, 3, -3, -1, 1, 2, -2, -3, 3, -1, 1, 0, 0, 0]

/-- The two coordinates of a triality-fixed Cartan vector in the basis
`(1,1,0,0), (1,0,1,0)`. These are the evaluations of a D₄ root on that Cartan basis. -/
def d4FixedCartanCoordinates (v : Fin 4 → ℝ) : ℝ × ℝ :=
  (v 0 + v 1, v 0 + v 2)

/-- Convert the restricted D₄ root evaluations to the chosen G₂ simple-root coordinates.
The linear change `(a,b) ↦ (a, -a + 2b)` is fixed by the Cartan conventions used by
`g2Grade` and `g2AlphaWeight`. -/
def d4FoldedRootWeight (v : Fin 4 → ℝ) : ℝ × ℝ :=
  let c := d4FixedCartanCoordinates v
  (c.1, -c.1 + 2 * c.2)

/-- The root-space basis indices of `g2Basis`, in the same order as the twelve triality orbits.
The remaining basis indices `12,13` are the Cartan subalgebra. -/
def d4OrbitToG2RootIndex : Fin 12 → Fin 12 :=
  ![0, 5, 6, 11, 1, 3, 10, 7, 4, 9, 2, 8]

def d4OrbitToG2RootBasis (o : Fin 12) : Fin 14 :=
  ⟨(d4OrbitToG2RootIndex o).val, by
    fin_cases o <;> simp [d4OrbitToG2RootIndex]⟩

/-- The twelve folded D₄ orbit means have precisely the G₂ root weights recorded by the
explicit root-space basis of `g2Submodule`. This is a root-data compatibility theorem across
the coordinate Cartan model and the matrix model; it does not alone identify the corresponding
root vectors or prove bracket compatibility. -/
theorem d4_folded_root_weights_match_g2_basis :
    ∀ o : Fin 12,
      d4FoldedRootWeight (d4OrbitMean o) =
        ((g2Grade (d4OrbitToG2RootBasis o) : ℝ),
          (g2AlphaWeight (d4OrbitToG2RootBasis o) : ℝ)) := by
  intro o
  rw [d4OrbitMean_eq_table]
  fin_cases o <;> norm_num [d4FoldedRootWeight, d4FixedCartanCoordinates,
    d4OrbitMeanTable, d4OrbitToG2RootBasis, d4OrbitToG2RootIndex,
    g2Grade, g2AlphaWeight]

/-- Inverse indexing map from the twelve matrix root basis vectors to the twelve D₄ triality
orbits. -/
def g2RootBasisToD4Orbit : Fin 12 → Fin 12 :=
  ![0, 4, 10, 5, 8, 1, 2, 7, 11, 9, 6, 3]

/-- The explicit orbit/root index maps are mutually inverse. -/
theorem d4_orbit_g2_root_index_equiv :
    (∀ o : Fin 12, g2RootBasisToD4Orbit (d4OrbitToG2RootIndex o) = o) ∧
    (∀ k : Fin 12, d4OrbitToG2RootIndex (g2RootBasisToD4Orbit k) = k) := by
  constructor <;> intro x <;> fin_cases x <;>
    norm_num [d4OrbitToG2RootIndex, g2RootBasisToD4Orbit]

/-- Reorder the fixed-carrier coordinates into the matrix basis order and identify the two
Cartan coordinate conventions. Root coefficient slots are permuted by the orbit/root bijection;
the Cartan coefficients are sent by `(p₀,p₁) ↦ (p₀+p₁,-p₁)`. -/
def d4FixedToG2Coefficients : (Fin 14 → ℝ) →ₗ[ℝ] (Fin 14 → ℝ) where
  toFun c k :=
    if hk : k.val < 12 then
      c ⟨2 + (g2RootBasisToD4Orbit ⟨k.val, hk⟩).val, by
        have h := (g2RootBasisToD4Orbit ⟨k.val, hk⟩).isLt
        omega⟩
    else if hk : k.val = 12 then c 0 + c 1
    else -c 1
  map_add' c d := by
    funext k
    by_cases hk : k.val < 12
    · simp [hk]
    · by_cases hk12 : k.val = 12
      · simp [hk12]
        abel
      · have hk13 : k.val = 13 := by omega
        simp [hk13]
        abel
  map_smul' r c := by
    funext k
    by_cases hk : k.val < 12
    · simp [hk]
    · by_cases hk12 : k.val = 12
      · simp [hk12, mul_add]
      · have hk13 : k.val = 13 := by omega
        simp [hk13]

/-- The coordinate reorder and Cartan change are invertible. -/
theorem d4FixedToG2Coefficients_injective :
    Function.Injective d4FixedToG2Coefficients := by
  intro c d h
  have h12 : c 0 + c 1 = d 0 + d 1 := by
    have h := congrFun h (12 : Fin 14)
    change c 0 + c 1 = d 0 + d 1 at h
    exact h
  have h13 : -c 1 = -d 1 := by
    have h := congrFun h (13 : Fin 14)
    change -c 1 = -d 1 at h
    exact h
  have hc1 : c 1 = d 1 := by linarith
  have hc0 : c 0 = d 0 := by linarith
  have hroot : ∀ o : Fin 12,
      c ⟨2 + o.val, by have ho := o.isLt; omega⟩ =
        d ⟨2 + o.val, by have ho := o.isLt; omega⟩ := by
    intro o
    let k : Fin 14 := ⟨(d4OrbitToG2RootIndex o).val, by omega⟩
    have h := congrFun h k
    have hlt : k.val < 12 := (d4OrbitToG2RootIndex o).isLt
    have hinv := d4_orbit_g2_root_index_equiv.1 o
    simpa [d4FixedToG2Coefficients, k, hlt, hinv] using h
  have htail : ∀ m : Fin 14, 2 ≤ m.val → c m = d m := by
    intro m hm
    let o : Fin 12 := ⟨m.val - 2, by have hh := m.isLt; omega⟩
    have hr := hroot o
    have heq : (⟨2 + o.val, by have hh := o.isLt; omega⟩ : Fin 14) = m := by
      apply Fin.ext
      simp [o]
      omega
    rw [heq] at hr
    exact hr
  funext m
  by_cases hm0 : m = 0
  · simpa [hm0] using hc0
  · by_cases hm1 : m = 1
    · simpa [hm1] using hc1
    · exact htail m (by have hm := m.isLt; omega)

/-- Synthesize a matrix in the explicit G₂ carrier from its fourteen basis coefficients. -/
def g2CoefficientSynthesis : (Fin 14 → ℝ) →ₗ[ℝ]
    Matrix Krein16Idx Krein16Idx ℝ where
  toFun c := ∑ k : Fin 14, c k • g2Basis k
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

/-- The coefficient synthesis map lands in the span defining `g2Submodule`. -/
def g2CoefficientSynthesisToSubmodule : (Fin 14 → ℝ) →ₗ[ℝ] g2Submodule :=
  g2CoefficientSynthesis.codRestrict g2Submodule (by
    intro c
    unfold g2Submodule
    change (∑ k ∈ Finset.univ, c k • g2Basis k) ∈
      Submodule.span ℝ (Set.range g2Basis)
    refine Submodule.sum_mem
      (p := Submodule.span ℝ (Set.range g2Basis)) (t := Finset.univ)
      (f := fun k : Fin 14 => c k • g2Basis k) ?_
    intro k hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

private theorem g2H1_comm_basis (k : Fin 14) :
    g2H1 * g2Basis k - g2Basis k * g2H1 = (g2Grade k : ℝ) • g2Basis k := by
  fin_cases k <;> simp only [g2Basis]
  · rw [g2Zpos2_nf, g2H1_nf]; simp [g2Grade]; rw [two_smul]; abel
  · rw [g2X1_nf, g2H1_nf]; simp [g2Grade]
  · rw [g2X2_nf, g2H1_nf]; simp [g2Grade]
  · rw [g2X3_nf, g2H1_nf]; simp [g2Grade]; abel
  · rw [g2X4_nf, g2H1_nf]; simp [g2Grade]
  · rw [g2E0_nf, g2H1_nf]; simp [g2Grade]
  · rw [g2F0_nf, g2H1_nf]; simp [g2Grade]
  · rw [g2Y1_nf, g2H1_nf]; simp [g2Grade]
  · rw [g2Y2_nf, g2H1_nf]; simp [g2Grade]
  · rw [g2Y3_nf, g2H1_nf]; simp [g2Grade]; abel
  · rw [g2Y4_nf, g2H1_nf]; simp [g2Grade]; abel
  · rw [g2Zneg2_nf, g2H1_nf]; simp [g2Grade]; rw [two_smul]
  · rw [g2H1_nf]; simp [g2Grade]
  · rw [g2H2_nf, g2H1_nf]; simp [g2Grade]; abel

private theorem g2H2_comm_basis (k : Fin 14) :
    g2H2 * g2Basis k - g2Basis k * g2H2 =
      ((![(1 : ℤ), -1, 2, 1, 0, -1, 1, 1, -2, 0, -1, -1, 0, 0] k : ℝ)) • g2Basis k := by
  fin_cases k <;> simp only [g2Basis]
  · rw [g2Zpos2_nf, g2H2_nf]; simp
  · rw [g2X1_nf, g2H2_nf]; simp
  · rw [g2X2_nf, g2H2_nf]; simp; rw [two_smul]; abel
  · rw [g2X3_nf, g2H2_nf]; simp; abel
  · rw [g2X4_nf, g2H2_nf]; simp
  · rw [g2E0_nf, g2H2_nf]; simp; abel
  · rw [g2F0_nf, g2H2_nf]; simp
  · rw [g2Y1_nf, g2H2_nf]; simp
  · rw [g2Y2_nf, g2H2_nf]; simp; rw [two_smul]
  · rw [g2Y3_nf, g2H2_nf]; simp
  · rw [g2Y4_nf, g2H2_nf]; simp; abel
  · rw [g2Zneg2_nf, g2H2_nf]; simp
  · rw [g2H1_nf, g2H2_nf]; simp; abel
  · rw [g2H2_nf]; simp

/-! ### Cartan-weight part of the D₄-orbit to matrix soldering

The orbit means are vectors in the D₄ Cartan coordinate space.  Restricting a Cartan vector
to the triality-fixed plane and evaluating an orbit mean gives the same scalar as the adjoint
action of its image in the explicit matrix Cartan.  This proves compatibility of the Cartan
actions; it does not yet identify root vectors or prove root-root bracket compatibility. -/

/-- The triality-fixed Cartan vector associated to two coordinates. -/
def d4FixedCartanVector (p : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![p 0 + p 1, p 0, p 1, 0]

/-- Evaluation of a Reynolds-averaged D₄ root on a triality-fixed Cartan vector. -/
def d4OrbitCartanEvaluation (p : Fin 2 → ℝ) (o : Fin 12) : ℝ :=
  ∑ i : Fin 4, d4OrbitMean o i * d4FixedCartanVector p i

/-- Matrix Cartan element corresponding to the same two fixed-plane coordinates under the
existing coefficient map `(p₀,p₁) ↦ (p₀+p₁,-p₁)`. -/
def d4FixedCartanMatrix (p : Fin 2 → ℝ) : Matrix Krein16Idx Krein16Idx ℝ :=
  (p 0 + p 1) • g2H1 + (-p 1) • g2H2

/-- The D₄ orbit evaluation agrees with the matrix adjoint eigenvalue on the corresponding
G₂ root basis vector. This is the Cartan-action compatibility needed before checking brackets. -/
theorem d4_fixed_cartan_orbit_weight_matches_matrix (p : Fin 2 → ℝ) (o : Fin 12) :
    d4OrbitCartanEvaluation p o =
      (p 0 + p 1) * (g2Grade (d4OrbitToG2RootBasis o) : ℝ) -
        p 1 *
          ((![(1 : ℤ), -1, 2, 1, 0, -1, 1, 1, -2, 0, -1, -1, 0, 0]
            (d4OrbitToG2RootBasis o) : ℝ)) := by
  unfold d4OrbitCartanEvaluation
  rw [d4OrbitMean_eq_table]
  fin_cases o <;>
    norm_num [d4OrbitCartanEvaluation, d4FixedCartanVector, d4OrbitMeanTable,
      d4OrbitToG2RootBasis, d4OrbitToG2RootIndex, g2Grade, Fin.sum_univ_four] <;> ring

/-- The fixed-plane Cartan action on each folded root agrees with the explicit matrix
commutator action. This is a genuine intertwining law, not a bracket transported from the target. -/
theorem d4_fixed_cartan_action_matches_g2_basis (p : Fin 2 → ℝ) (o : Fin 12) :
    d4OrbitCartanEvaluation p o • g2Basis (d4OrbitToG2RootBasis o) =
      d4FixedCartanMatrix p * g2Basis (d4OrbitToG2RootBasis o) -
        g2Basis (d4OrbitToG2RootBasis o) * d4FixedCartanMatrix p := by
  let k := d4OrbitToG2RootBasis o
  have h1 := g2H1_comm_basis k
  have h2 := g2H2_comm_basis k
  have hweight := d4_fixed_cartan_orbit_weight_matches_matrix p o
  have hcomm : d4FixedCartanMatrix p * g2Basis k - g2Basis k * d4FixedCartanMatrix p =
      (p 0 + p 1) • (g2H1 * g2Basis k - g2Basis k * g2H1) +
        (-p 1) • (g2H2 * g2Basis k - g2Basis k * g2H2) := by
    apply Matrix.ext; intro i j
    simp [d4FixedCartanMatrix]
    ring
  rw [hcomm, h1, h2, hweight]
  module

/-- 5-grading, `(ad_{H_θ}, ad_{H_α})` root-weight decomposition, and Cartan commutativity. -/
theorem g2_five_grading_and_cartan :
    g2H1 * g2H2 - g2H2 * g2H1 = 0 ∧
    (∀ k : Fin 14, g2H1 * g2Basis k - g2Basis k * g2H1 = (g2Grade k : ℝ) • g2Basis k) ∧
    (∀ k : Fin 14, g2Halpha * g2Basis k - g2Basis k * g2Halpha = (g2AlphaWeight k : ℝ) • g2Basis k) := by
  refine ⟨by have h := g2H1_comm_basis 13; simp [g2Basis, g2Grade] at h; exact h,
    g2H1_comm_basis, ?_⟩
  intro k
  unfold g2Halpha
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  have h1 := g2H1_comm_basis k
  have h2 := g2H2_comm_basis k
  have hcomb : (g2H1 * g2Basis k - (2 : ℝ) • (g2H2 * g2Basis k)) -
      (g2Basis k * g2H1 - (2 : ℝ) • (g2Basis k * g2H2)) =
      (g2H1 * g2Basis k - g2Basis k * g2H1) -
        (2 : ℝ) • (g2H2 * g2Basis k - g2Basis k * g2H2) := by
    rw [smul_sub]
    abel
  rw [hcomb, h1, h2, ← smul_assoc, ← sub_smul]
  fin_cases k <;> simp [g2Grade, g2AlphaWeight] <;> norm_num

/-- The matrix commutator is a derivation in its second argument. -/
private theorem assocComm_derivation {A : Type*} [Ring A] (H X Y : A) :
    assocComm H (assocComm X Y) =
      assocComm (assocComm H X) Y + assocComm X (assocComm H Y) := by
  unfold assocComm
  noncomm_ring

/-- Scalar factors pass through either slot of the associative matrix commutator. -/
private theorem assocComm_smul_left (c : ℝ)
    (X Y : Matrix Krein16Idx Krein16Idx ℝ) :
    assocComm (c • X) Y = c • assocComm X Y := by
  unfold assocComm
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]

private theorem assocComm_smul_right (c : ℝ)
    (X Y : Matrix Krein16Idx Krein16Idx ℝ) :
    assocComm X (c • Y) = c • assocComm X Y := by
  unfold assocComm
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]

/-- The matrix root-space commutator has the sum of the two input weights under each
Cartan adjoint action. This is the bracket-side compatibility required by the folded-root
weight match; it is stronger than dimension or label agreement, while making no assertion
that a coordinate root orbit itself is a matrix. -/
theorem g2_basis_bracket_weights (i j : Fin 14) :
    g2H1 * (g2Basis i * g2Basis j - g2Basis j * g2Basis i) -
        (g2Basis i * g2Basis j - g2Basis j * g2Basis i) * g2H1 =
      ((g2Grade i + g2Grade j : ℤ) : ℝ) •
        (g2Basis i * g2Basis j - g2Basis j * g2Basis i) ∧
    g2Halpha * (g2Basis i * g2Basis j - g2Basis j * g2Basis i) -
        (g2Basis i * g2Basis j - g2Basis j * g2Basis i) * g2Halpha =
      ((g2AlphaWeight i + g2AlphaWeight j : ℤ) : ℝ) •
        (g2Basis i * g2Basis j - g2Basis j * g2Basis i) := by
  constructor
  · change assocComm g2H1 (assocComm (g2Basis i) (g2Basis j)) = _
    have hi := g2H1_comm_basis i
    have hj := g2H1_comm_basis j
    change assocComm g2H1 (g2Basis i) = _ at hi
    change assocComm g2H1 (g2Basis j) = _ at hj
    rw [assocComm_derivation, hi, hj,
      assocComm_smul_left, assocComm_smul_right, ← add_smul]
    change ((g2Grade i : ℝ) + (g2Grade j : ℝ)) •
      assocComm (g2Basis i) (g2Basis j) = _
    rw [Int.cast_add]
    rfl
  · change assocComm g2Halpha (assocComm (g2Basis i) (g2Basis j)) = _
    have hi := g2_five_grading_and_cartan.2.2 i
    have hj := g2_five_grading_and_cartan.2.2 j
    change assocComm g2Halpha (g2Basis i) = _ at hi
    change assocComm g2Halpha (g2Basis j) = _ at hj
    rw [assocComm_derivation, hi, hj,
      assocComm_smul_left, assocComm_smul_right, ← add_smul]
    change ((g2AlphaWeight i : ℝ) + (g2AlphaWeight j : ℝ)) •
      assocComm (g2Basis i) (g2Basis j) = _
    rw [Int.cast_add]
    rfl

/-- **Grade-+1 Contact Algebra, Cartan Ratio `3`, and Five Vanishing Serre Syzygies**:
`[X₁, X₂] = Z_{+2}`, `[X₃, X₄] = 3 • Z_{+2}`, the remaining four grade-`+1` brackets vanish,
and hence `3 • [X₁, X₂] - [X₃, X₄] = 0`. -/
theorem g2_grade1_contact_and_serre_syzygies :
    g2X1 * g2X2 - g2X2 * g2X1 = g2Zpos2 ∧
    g2X3 * g2X4 - g2X4 * g2X3 = (3 : ℝ) • g2Zpos2 ∧
    g2X1 * g2X3 - g2X3 * g2X1 = 0 ∧
    g2X1 * g2X4 - g2X4 * g2X1 = 0 ∧
    g2X2 * g2X3 - g2X3 * g2X2 = 0 ∧
    g2X2 * g2X4 - g2X4 * g2X2 = 0 ∧
    (3 : ℝ) • (g2X1 * g2X2 - g2X2 * g2X1) - (g2X3 * g2X4 - g2X4 * g2X3) = 0 := by
  have h12 : g2X1 * g2X2 - g2X2 * g2X1 = g2Zpos2 := g2_x12_comm_aux
  have h34 : g2X3 * g2X4 - g2X4 * g2X3 = (3 : ℝ) • g2Zpos2 := g2_x34_comm_aux
  have h13 : g2X1 * g2X3 - g2X3 * g2X1 = 0 := by
    rw [g2X1_nf, g2X3_nf]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg]
    simp
  have h14 : g2X1 * g2X4 - g2X4 * g2X1 = 0 := by
    rw [g2X1_nf, g2X4_nf]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg]
    simp
  have h23 : g2X2 * g2X3 - g2X3 * g2X2 = 0 := by
    rw [g2X2_nf, g2X3_nf]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg]
    simp
  have h24 : g2X2 * g2X4 - g2X4 * g2X2 = 0 := by
    rw [g2X2_nf, g2X4_nf]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg]
    simp
  have hsyz : (3 : ℝ) • (g2X1 * g2X2 - g2X2 * g2X1) - (g2X3 * g2X4 - g2X4 * g2X3) = 0 := by
    rw [h12, h34, sub_self]
  exact ⟨h12, h34, h13, h14, h23, h24, hsyz⟩

/-- Six coordinates of `Λ²` of the four grade-`+1` generators, ordered as
`(X₁,X₂), (X₁,X₃), (X₁,X₄), (X₂,X₃), (X₂,X₄), (X₃,X₄)`. -/
def g2ContactBracketCoefficient : (Fin 6 → ℝ) →ₗ[ℝ] ℝ where
  toFun c := c 0 + 3 * c 5
  map_add' c d := by simp; ring
  map_smul' a c := by simp; ring

/-- The actual bracket readout from the six basis vectors of `Λ² (grade +1)`
to the matrix carrier. -/
def g2ContactBracketMap : (Fin 6 → ℝ) →ₗ[ℝ]
    Matrix Krein16Idx Krein16Idx ℝ where
  toFun c := g2ContactBracketCoefficient c • g2Zpos2
  map_add' c d := by
    rw [map_add]
    exact add_smul _ _ _
  map_smul' a c := by
    rw [map_smul]
    exact mul_smul _ _ _

/-- The coordinate functional is read off from the actual matrix bracket table. -/
theorem g2ContactBracketCoefficient_matches_matrix_brackets (c : Fin 6 → ℝ) :
    c 0 • (g2X1 * g2X2 - g2X2 * g2X1) +
      c 1 • (g2X1 * g2X3 - g2X3 * g2X1) +
      c 2 • (g2X1 * g2X4 - g2X4 * g2X1) +
      c 3 • (g2X2 * g2X3 - g2X3 * g2X2) +
      c 4 • (g2X2 * g2X4 - g2X4 * g2X2) +
      c 5 • (g2X3 * g2X4 - g2X4 * g2X3) =
      g2ContactBracketCoefficient c • g2Zpos2 := by
  rcases g2_grade1_contact_and_serre_syzygies with
    ⟨h12, h34, h13, h14, h23, h24, _⟩
  simp [g2ContactBracketCoefficient, h12, h13, h14, h23, h24, h34]
  module

/-- The coordinate map agrees with the sum of the actual matrix brackets. -/
theorem g2ContactBracketMap_eq_matrix_bracket_sum (c : Fin 6 → ℝ) :
    g2ContactBracketMap c =
      c 0 • (g2X1 * g2X2 - g2X2 * g2X1) +
        c 1 • (g2X1 * g2X3 - g2X3 * g2X1) +
        c 2 • (g2X1 * g2X4 - g2X4 * g2X1) +
        c 3 • (g2X2 * g2X3 - g2X3 * g2X2) +
        c 4 • (g2X2 * g2X4 - g2X4 * g2X2) +
        c 5 • (g2X3 * g2X4 - g2X4 * g2X3) := by
  exact (g2ContactBracketCoefficient_matches_matrix_brackets c).symm

/-- The five-dimensional syzygy space of the grade-`+1` alternating bracket,
as the kernel of its coefficient functional (not just the arithmetic `6 - 1`). -/
theorem g2ContactBracketCoefficient_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker g2ContactBracketCoefficient) = 5 := by
  have hsurj : Function.Surjective g2ContactBracketCoefficient := by
    intro r
    refine ⟨fun i => if i = 0 then r else 0, ?_⟩
    simp [g2ContactBracketCoefficient]
  have hrange : LinearMap.range g2ContactBracketCoefficient = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdim := g2ContactBracketCoefficient.finrank_range_add_finrank_ker
  rw [hrange] at hdim
  simp only [finrank_top, CommSemiring.finrank_self, Module.finrank_fin_fun] at hdim
  omega

/-- Five explicit coordinate syzygies for the grade-`+1` contact bracket.
The first four are the pairs with zero bracket; the last is the relation
`3 (X₁ ∧ X₂) - (X₃ ∧ X₄)`. -/
def g2ContactSyzygy : Fin 5 → Fin 6 → ℝ
  | 0 => fun j => if j = 1 then 1 else 0
  | 1 => fun j => if j = 2 then 1 else 0
  | 2 => fun j => if j = 3 then 1 else 0
  | 3 => fun j => if j = 4 then 1 else 0
  | 4 => fun j => if j = 0 then 3 else if j = 5 then -1 else 0

/-- The displayed five vectors form a basis of the actual grade-`+1` bracket
kernel. This identifies the whole five-dimensional degree-`2` syzygy space,
not merely one nonzero Serre relation. -/
theorem g2ContactBracketCoefficient_kernel_eq_syzygy_span :
    LinearMap.ker g2ContactBracketCoefficient =
      Submodule.span ℝ (Set.range g2ContactSyzygy) := by
  have hmem (i : Fin 5) : g2ContactSyzygy i ∈ LinearMap.ker g2ContactBracketCoefficient := by
    change g2ContactBracketCoefficient (g2ContactSyzygy i) = 0
    fin_cases i <;> simp [g2ContactBracketCoefficient, g2ContactSyzygy]
  have hlin : LinearIndependent ℝ g2ContactSyzygy := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hcoord := congrArg (fun v : Fin 6 → ℝ => v (Fin.succ k)) hc
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hcoord
    have hsum : (∑ i : Fin 5, c i * g2ContactSyzygy i (Fin.succ k)) =
        c k * g2ContactSyzygy k (Fin.succ k) := by
      rw [Finset.sum_eq_single k]
      · intro i _ hik
        fin_cases i <;> fin_cases k <;> simp_all [g2ContactSyzygy]
      · fin_cases k <;> simp [g2ContactSyzygy]
    have hcoord' : (∑ i : Fin 5, c i * g2ContactSyzygy i (Fin.succ k)) = 0 := by
      simpa [smul_eq_mul] using hcoord
    rw [hsum] at hcoord'
    fin_cases k <;> simpa [g2ContactSyzygy] using hcoord'
  have hle : Submodule.span ℝ (Set.range g2ContactSyzygy) ≤
      LinearMap.ker g2ContactBracketCoefficient := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have heq : Submodule.span ℝ (Set.range g2ContactSyzygy) =
      LinearMap.ker g2ContactBracketCoefficient :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_eq_card hlin, Fintype.card_fin,
        g2ContactBracketCoefficient_kernel_finrank])
  exact heq.symm

/-- **Vertical Jordan Anticommutator Jump**: `{X₁, X₂}` is non-zero and Krein-symmetric (not
Krein-skew!), so it jumps vertically out of the Krein-skew Lie subalgebra `g2Submodule`. -/
theorem g2_jordan_anticomm_clifford_jump :
    (g2X1 * g2X2 + g2X2 * g2X1) ≠ 0 ∧
    (g2X1 * g2X2 + g2X2 * g2X1)ᵀ * kreinMetric88 =
      kreinMetric88 * (g2X1 * g2X2 + g2X2 * g2X1) ∧
    (g2X1 * g2X2 + g2X2 * g2X1) ∉ g2Submodule := by
  have hnf : g2X1 * g2X2 + g2X2 * g2X1 =
      tensor4 1 cl11Up cl11P0 cl11Down + tensor4 1 cl11Up cl11P1 cl11Down := by
    rw [g2X1_nf, g2X2_nf]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    simp
    rw [add_comm]
  have hnf_simple : g2X1 * g2X2 + g2X2 * g2X1 = tensor4 1 cl11Up 1 cl11Down := by
    rw [hnf, ← tensor4_add_2, ← cl11One_eq_P0_add_P1]
  have hnz : (g2X1 * g2X2 + g2X2 * g2X1) ≠ 0 := by
    intro h0
    rw [hnf_simple] at h0
    have hval := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ =>
      M (0, 0, 0, 1) (0, 1, 0, 0)) h0
    unfold tensor4 cl11Up cl11Down at hval
    simp only [Matrix.zero_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hval
    norm_num at hval
  have hksym : (g2X1 * g2X2 + g2X2 * g2X1)ᵀ * kreinMetric88 =
      kreinMetric88 * (g2X1 * g2X2 + g2X2 * g2X1) := by
    rw [hnf_simple]
    exact g2_jordan_ksym_aux
  have hnotmem : (g2X1 * g2X2 + g2X2 * g2X1) ∉ g2Submodule := by
    intro hmem
    have hskew := (g2Submodule_mem_stabilizer hmem).1
    rw [hksym, ← two_smul ℝ] at hskew
    have hmul := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => kreinMetric88 * M) hskew
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, kreinMetric88_properties.2.2.1, Matrix.one_mul,
      Matrix.mul_zero] at hmul
    have hzero : g2X1 * g2X2 + g2X2 * g2X1 = 0 := by
      have := smul_eq_zero.mp hmul
      exact this.resolve_left (by norm_num)
    exact hnz hzero
  exact ⟨hnz, hksym, hnotmem⟩

/-! ### Unique Pivot Entries, Linear Independence, `finrank = 14`, Centerlessness & Full Bracket Closure -/

/-- Unique separating matrix entry `(row, col)` for each of the 14 `g2Basis` generators. -/
def g2Pivot : Fin 14 → Krein16Idx × Krein16Idx
  | 0 => ((0, 0, 0, 1), (0, 1, 0, 0))
  | 1 => ((0, 0, 1, 0), (0, 1, 0, 0))
  | 2 => ((0, 0, 0, 1), (0, 0, 1, 0))
  | 3 => ((0, 0, 0, 0), (0, 1, 1, 0))
  | 4 => ((0, 0, 0, 0), (1, 1, 0, 0))
  | 5 => ((0, 0, 0, 0), (0, 1, 0, 1))
  | 6 => ((0, 0, 0, 0), (1, 0, 1, 0))
  | 7 => ((0, 1, 0, 0), (0, 0, 1, 0))
  | 8 => ((0, 0, 1, 0), (0, 0, 0, 1))
  | 9 => ((0, 0, 0, 0), (0, 0, 1, 1))
  | 10 => ((0, 0, 0, 0), (1, 0, 0, 1))
  | 11 => ((0, 1, 0, 0), (0, 0, 0, 1))
  | 12 => ((0, 0, 1, 1), (0, 0, 1, 1))
  | 13 => ((0, 0, 1, 0), (0, 0, 1, 0))

/-- Nonzero diagonal entry value at each `g2Pivot k`. -/
def g2PivotVal : Fin 14 → ℝ :=
  ![-1, -1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, -1]

private theorem g2Basis_eval_pivot (m k : Fin 14) :
    g2Basis m (g2Pivot k).1 (g2Pivot k).2 = if m = k then g2PivotVal k else 0 := by
  fin_cases m <;> simp only [g2Basis]
  · rw [g2Zpos2_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Up, cl11Grad, cl11Down]
  · rw [g2X1_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Up, cl11Down]
  · rw [g2X2_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Up, cl11Down]
  · rw [g2X3_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Up, cl11Pos, cl11Grad, cl11Down]
  · rw [g2X4_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Down, cl11Pos, cl11Up]
  · rw [g2E0_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Up, cl11Grad, cl11Pos, cl11Down]
  · rw [g2F0_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Down, cl11Grad, cl11Pos, cl11Up]
  · rw [g2Y1_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Down, cl11Up]
  · rw [g2Y2_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Down, cl11Up]
  · rw [g2Y3_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Up, cl11Pos, cl11Down]
  · rw [g2Y4_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Down, cl11Pos, cl11Grad, cl11Up]
  · rw [g2Zneg2_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11Down, cl11Grad, cl11Up]
  · rw [g2H1_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11P0]
  · rw [g2H2_nf]; fin_cases k <;> simp [g2Pivot, g2PivotVal, tensor4, cl11P0]

private theorem g2PivotVal_ne_zero (k : Fin 14) : g2PivotVal k ≠ 0 := by
  fin_cases k <;> simp [g2PivotVal]

/-- All 14 matrices in `g2Basis` are `ℝ`-linearly independent inside `M₁₆(ℝ)`. -/
theorem g2Basis_linearIndependent : LinearIndependent ℝ g2Basis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hpt := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (g2Pivot k).1 (g2Pivot k).2) hc
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hpt
  have hsum : (∑ m : Fin 14, c m * g2Basis m (g2Pivot k).1 (g2Pivot k).2) = c k * g2PivotVal k := by
    rw [Finset.sum_eq_single k]
    · simp only [g2Basis_eval_pivot, ↓reduceIte]
    · intro m _ hm
      simp only [g2Basis_eval_pivot, hm, ↓reduceIte, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hsum] at hpt
  exact (mul_eq_zero.mp hpt).resolve_right (g2PivotVal_ne_zero k)

/-- The central grade-`+2` bracket generator is nonzero, as the first member
of the linearly independent explicit `g2Basis`. -/
theorem g2Zpos2_ne_zero : g2Zpos2 ≠ 0 := by
  intro hzero
  have hB : g2Basis 0 = 0 := by simpa [g2Basis] using hzero
  exact (g2Basis_linearIndependent.ne_zero 0) hB

/-- The kernel of the actual matrix bracket readout is exactly the five
independent syzygies of the alternating bracket on the four grade-`+1` generators. -/
theorem g2ContactBracketMap_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker g2ContactBracketMap) = 5 := by
  have hker : LinearMap.ker g2ContactBracketMap =
      LinearMap.ker g2ContactBracketCoefficient := by
    ext c
    change g2ContactBracketCoefficient c • g2Zpos2 = 0 ↔
      g2ContactBracketCoefficient c = 0
    constructor
    · intro hz
      rcases smul_eq_zero.mp hz with hc | hZ
      · exact hc
      · exact (g2Zpos2_ne_zero hZ).elim
    · intro hc
      rw [hc]
      simp
  rw [hker]
  exact g2ContactBracketCoefficient_kernel_finrank

/-- The five explicit syzygies are exactly the kernel of the concrete
matrix-valued bracket readout, not only of its scalar coordinate functional. -/
theorem g2ContactBracketMap_kernel_eq_syzygy_span :
    LinearMap.ker g2ContactBracketMap =
      Submodule.span ℝ (Set.range g2ContactSyzygy) := by
  have hker : LinearMap.ker g2ContactBracketMap =
      LinearMap.ker g2ContactBracketCoefficient := by
    ext c
    change g2ContactBracketCoefficient c • g2Zpos2 = 0 ↔
      g2ContactBracketCoefficient c = 0
    constructor
    · intro hz
      rcases smul_eq_zero.mp hz with hc | hZ
      · exact hc
      · exact (g2Zpos2_ne_zero hZ).elim
    · intro hc
      rw [hc]
      simp
  rw [hker]
  exact g2ContactBracketCoefficient_kernel_eq_syzygy_span

/-- The image of the actual bracket readout is precisely the central
grade-`+2` line. -/
theorem g2ContactBracketMap_range_eq_centerLine :
    LinearMap.range g2ContactBracketMap =
      Submodule.span ℝ ({g2Zpos2} : Set (Matrix Krein16Idx Krein16Idx ℝ)) := by
  apply le_antisymm
  · rintro Y ⟨c, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.2
    intro Y hY
    simp only [Set.mem_singleton_iff] at hY
    subst Y
    refine ⟨fun i => if i = 0 then 1 else 0, ?_⟩
    simp [g2ContactBracketMap, g2ContactBracketCoefficient]

/-- Rank one of the image, so the six-dimensional coordinate bracket has a
one-dimensional central target and a five-dimensional kernel. -/
theorem g2ContactBracketMap_range_finrank :
    Module.finrank ℝ (LinearMap.range g2ContactBracketMap) = 1 := by
  rw [g2ContactBracketMap_range_eq_centerLine]
  exact finrank_span_singleton g2Zpos2_ne_zero

/-- Quotienting the six ordered-pair coordinates by the actual bracket kernel
identifies them with the central grade-`+2` line. -/
theorem g2ContactBracketMap_quotient_equiv_centerLine :
    Nonempty (((Fin 6 → ℝ) ⧸ LinearMap.ker g2ContactBracketMap) ≃ₗ[ℝ]
      Submodule.span ℝ ({g2Zpos2} : Set (Matrix Krein16Idx Krein16Idx ℝ))) := by
  exact ⟨g2ContactBracketMap.quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _ g2ContactBracketMap_range_eq_centerLine)⟩

/-- `Module.finrank ℝ g2Submodule = 14`, matching `SplitG2RealFormCapstone.parameter_model_is_fourteen_dimensional`. -/
theorem finrank_g2Submodule_and_owner_bridge :
    Module.finrank ℝ g2Submodule = 14 ∧
    Module.finrank ℝ g2Submodule =
      Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations := by
  have hfin : Module.finrank ℝ g2Submodule = 14 := by
    unfold g2Submodule
    rw [finrank_span_eq_card g2Basis_linearIndependent, Fintype.card_fin]
  have howner : Module.finrank ℝ g2Submodule =
      Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations := by
    rw [hfin, InfoGeometry.Lie.SplitG2RealFormCapstone.parameter_model_is_fourteen_dimensional]
  exact ⟨hfin, howner⟩

/-- Uniqueness of coordinates in the explicit matrix basis. -/
theorem g2CoefficientSynthesisToSubmodule_injective :
    Function.Injective g2CoefficientSynthesisToSubmodule := by
  intro c d h
  have hv := congrArg Subtype.val h
  change (∑ k : Fin 14, c k • g2Basis k) =
    (∑ k : Fin 14, d k • g2Basis k) at hv
  have hzero : ∑ k : Fin 14, (c k - d k) • g2Basis k = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hv, sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp g2Basis_linearIndependent
      (fun k => c k - d k) hzero
  apply funext
  intro k
  exact sub_eq_zero.mp (hcoeff k)

/-- Coefficient synthesis is a linear equivalence onto the concrete fourteen-dimensional
matrix submodule. -/
def g2CoefficientEquiv : (Fin 14 → ℝ) ≃ₗ[ℝ] g2Submodule :=
  LinearEquiv.ofInjectiveOfFinrankEq g2CoefficientSynthesisToSubmodule
    g2CoefficientSynthesisToSubmodule_injective (by
      rw [Module.finrank_fin_fun, finrank_g2Submodule_and_owner_bridge.1])

/-- The orbit reorder and Cartan change are an isomorphism of coordinate spaces. -/
def d4FixedToG2CoefficientEquiv : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ) :=
  LinearEquiv.ofInjectiveOfFinrankEq d4FixedToG2Coefficients
    d4FixedToG2Coefficients_injective (by rw [Module.finrank_fin_fun])

/-- The triality-fixed D₄ coordinate carrier and the explicit matrix G₂ carrier are linearly
equivalent. This map uses the orbit reindexing, Cartan coordinate change, and the actual
fourteen-matrix basis synthesis. -/
def s3FixedToG2CarrierEquiv : s3FixedSpin44Submodule ≃ₗ[ℝ] g2Submodule :=
  s3FixedSpin44Equiv.symm.trans
    (d4FixedToG2CoefficientEquiv.trans g2CoefficientEquiv)

/-- The coordinate basis vector for a triality orbit, using the source convention of two Cartan
slots followed by twelve orbit slots. -/
def d4TrialityOrbitCoordinate (o : Fin 12) : s3FixedSpin44Submodule :=
  s3FixedSpin44Equiv (Pi.single ⟨2 + o.val, by have ho := o.isLt; omega⟩ (1 : ℝ))

/-- The matrix realization of each triality-orbit coordinate is the corresponding explicit
G₂ root basis matrix. This makes the root reindexing in the carrier equivalence concrete on every
root direction, rather than only proving equality of carrier dimensions. -/
theorem d4TrialityOrbitCoordinate_maps_to_g2RootBasis (o : Fin 12) :
    (s3FixedToG2CarrierEquiv (d4TrialityOrbitCoordinate o)).1 =
      g2Basis (d4OrbitToG2RootBasis o) := by
  let j : Fin 14 := ⟨2 + o.val, by have ho := o.isLt; omega⟩
  let k := d4OrbitToG2RootBasis o
  have hcoord : d4FixedToG2Coefficients (Pi.single j (1 : ℝ)) = Pi.single k 1 := by
    ext i
    fin_cases o <;> fin_cases i <;>
      norm_num [d4FixedToG2Coefficients, d4OrbitToG2RootBasis,
        d4OrbitToG2RootIndex, g2RootBasisToD4Orbit, j, k]
  simp only [d4TrialityOrbitCoordinate, s3FixedToG2CarrierEquiv,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change (g2CoefficientEquiv (d4FixedToG2Coefficients (Pi.single j (1 : ℝ)))).1 = _
  rw [hcoord]
  change (g2CoefficientEquiv (Pi.single k (1 : ℝ))).1 = g2Basis k
  change (g2CoefficientSynthesisToSubmodule (Pi.single k (1 : ℝ))).1 = g2Basis k
  change (∑ i : Fin 14, (Pi.single k (1 : ℝ) : Fin 14 → ℝ) i • g2Basis i) = g2Basis k
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · simp

/-- The constructed carrier equivalence confirms equality of the two carrier dimensions. -/
theorem s3FixedToG2CarrierEquiv_finrank :
    Module.finrank ℝ s3FixedSpin44Submodule =
      Module.finrank ℝ g2Submodule :=
  s3FixedToG2CarrierEquiv.finrank_eq

section MatrixUnitExpand2

attribute [local simp]
  cl11One_eq_P0_add_P1 cl11Grad_eq_P0_sub_P1
  cl11Pos_eq_Up_add_Down cl11Neg_eq_Down_sub_Up
  tensor4_add_0 tensor4_add_1 tensor4_add_2 tensor4_add_3
  tensor4_sub_0 tensor4_sub_1 tensor4_sub_2 tensor4_sub_3

private theorem g2Bracket_row_lt4 (i j : Fin 14) (hi : i.val < 4) (hij : i < j) :
    g2Basis i * g2Basis j - g2Basis j * g2Basis i ∈ g2Submodule := by
  have hmem : ∀ k : Fin 14, g2Basis k ∈ g2Submodule :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  rw [Fin.lt_def] at hij
  fin_cases i <;> fin_cases j <;>
    dsimp only at hi hij <;>
    try (exfalso; have _ := hi; have _ := hij; omega)
  all_goals simp only [g2Basis]
  · have h : g2Zpos2 * g2X1 - g2X1 * g2Zpos2 = 0 := by rw [g2Zpos2_nf, g2X1_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Zpos2 * g2X2 - g2X2 * g2Zpos2 = 0 := by rw [g2Zpos2_nf, g2X2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Zpos2 * g2X3 - g2X3 * g2Zpos2 = 0 := by rw [g2Zpos2_nf, g2X3_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Zpos2 * g2X4 - g2X4 * g2Zpos2 = 0 := by rw [g2Zpos2_nf, g2X4_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Zpos2 * g2E0 - g2E0 * g2Zpos2 = 0 := by rw [g2Zpos2_nf, g2E0_nf]; simp; module
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Zpos2 * g2F0 - g2F0 * g2Zpos2 = 0 := by rw [g2Zpos2_nf, g2F0_nf]; simp; module
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Zpos2 * g2Y1 - g2Y1 * g2Zpos2 = -g2X2 := by rw [g2Zpos2_nf, g2Y1_nf, g2X2_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 2)
  · have h : g2Zpos2 * g2Y2 - g2Y2 * g2Zpos2 = g2X1 := by rw [g2Zpos2_nf, g2Y2_nf, g2X1_nf]; simp; module
    rw [h]; exact hmem 1
  · have h : g2Zpos2 * g2Y3 - g2Y3 * g2Zpos2 = -g2X3 := by rw [g2Zpos2_nf, g2Y3_nf, g2X3_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 3)
  · have h : g2Zpos2 * g2Y4 - g2Y4 * g2Zpos2 = g2X4 := by rw [g2Zpos2_nf, g2Y4_nf, g2X4_nf]; simp; module
    rw [h]; exact hmem 4
  · rw [g2_zpos2_zneg2_aux]; exact hmem 12
  · have hH := g2H1_comm_basis 0; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 0))
  · have hH := g2H2_comm_basis 0; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 0))
  · rw [g2_grade1_contact_and_serre_syzygies.1]; exact hmem 0
  · rw [g2_grade1_contact_and_serre_syzygies.2.2.1]; exact Submodule.zero_mem _
  · rw [g2_grade1_contact_and_serre_syzygies.2.2.2.1]; exact Submodule.zero_mem _
  · have h : g2X1 * g2E0 - g2E0 * g2X1 = 0 := by rw [g2X1_nf, g2E0_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2X1 * g2F0 - g2F0 * g2X1 = g2X4 := by rw [g2X1_nf, g2F0_nf, g2X4_nf]; simp; module
    rw [h]; exact hmem 4
  · rw [g2_x1_y1_aux]; exact Submodule.sub_mem _ (hmem 12) (hmem 13)
  · have h : g2X1 * g2Y2 - g2Y2 * g2X1 = 0 := by rw [g2X1_nf, g2Y2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2X1 * g2Y3 - g2Y3 * g2X1 = -g2E0 := by rw [g2X1_nf, g2Y3_nf, g2E0_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 5)
  · have h : g2X1 * g2Y4 - g2Y4 * g2X1 = 0 := by rw [g2X1_nf, g2Y4_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2X1 * g2Zneg2 - g2Zneg2 * g2X1 = -g2Y2 := by rw [g2X1_nf, g2Zneg2_nf, g2Y2_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 8)
  · have hH := g2H1_comm_basis 1; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 1))
  · have hH := g2H2_comm_basis 1; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 1))
  · rw [g2_grade1_contact_and_serre_syzygies.2.2.2.2.1]; exact Submodule.zero_mem _
  · rw [g2_grade1_contact_and_serre_syzygies.2.2.2.2.2.1]; exact Submodule.zero_mem _
  · have h : g2X2 * g2E0 - g2E0 * g2X2 = -g2X3 := by rw [g2X2_nf, g2E0_nf, g2X3_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 3)
  · have h : g2X2 * g2F0 - g2F0 * g2X2 = 0 := by rw [g2X2_nf, g2F0_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2X2 * g2Y1 - g2Y1 * g2X2 = 0 := by rw [g2X2_nf, g2Y1_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · rw [g2_x2_y2_aux]; exact hmem 13
  · have h : g2X2 * g2Y3 - g2Y3 * g2X2 = 0 := by rw [g2X2_nf, g2Y3_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2X2 * g2Y4 - g2Y4 * g2X2 = g2F0 := by rw [g2X2_nf, g2Y4_nf, g2F0_nf]; simp; module
    rw [h]; exact hmem 6
  · have h : g2X2 * g2Zneg2 - g2Zneg2 * g2X2 = g2Y1 := by rw [g2X2_nf, g2Zneg2_nf, g2Y1_nf]; simp; module
    rw [h]; exact hmem 7
  · have hH := g2H1_comm_basis 2; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 2))
  · have hH := g2H2_comm_basis 2; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 2))
  · rw [g2_grade1_contact_and_serre_syzygies.2.1]; exact Submodule.smul_mem _ _ (hmem 0)
  · rw [g2_x3_e0_aux]; exact Submodule.smul_mem _ _ (hmem 4)
  · rw [g2_x3_f0_aux]; exact Submodule.smul_mem _ _ (hmem 2)
  · have h : g2X3 * g2Y1 - g2Y1 * g2X3 = 0 := by rw [g2X3_nf, g2Y1_nf]; simp; module
    rw [h]; exact Submodule.zero_mem _
  · have h : g2X3 * g2Y2 - g2Y2 * g2X3 = g2E0 := by rw [g2X3_nf, g2Y2_nf, g2E0_nf]; simp; module
    rw [h]; exact hmem 5
  · rw [g2_x3_y3_aux]; exact Submodule.smul_mem _ _ (hmem 6)
  · rw [g2_x3_y4_aux]; exact Submodule.neg_mem _ (Submodule.add_mem _ (hmem 12) (hmem 13))
  · have h : g2X3 * g2Zneg2 - g2Zneg2 * g2X3 = g2Y3 := by rw [g2X3_nf, g2Zneg2_nf, g2Y3_nf]; simp; module
    rw [h]; exact hmem 9
  · have hH := g2H1_comm_basis 3; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 3))
  · have hH := g2H2_comm_basis 3; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 3))

private theorem g2Bracket_row_4_to_7 (i j : Fin 14) (hi : 4 ≤ i.val ∧ i.val < 8) (hij : i < j) :
    g2Basis i * g2Basis j - g2Basis j * g2Basis i ∈ g2Submodule := by
  have hmem : ∀ k : Fin 14, g2Basis k ∈ g2Submodule :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  rw [Fin.lt_def] at hij
  fin_cases i <;> fin_cases j <;>
    dsimp only at hi hij <;>
    try (exfalso; have _ := hi; have _ := hij; omega)
  all_goals simp only [g2Basis]
  · rw [g2_x4_e0_aux]; exact Submodule.smul_mem _ _ (hmem 1)
  · rw [g2_x4_f0_aux]; exact Submodule.smul_mem _ _ (hmem 3)
  · have h : g2X4 * g2Y1 - g2Y1 * g2X4 = -g2F0 := by rw [g2X4_nf, g2Y1_nf, g2F0_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 6)
  · have h : g2X4 * g2Y2 - g2Y2 * g2X4 = 0 := by rw [g2X4_nf, g2Y2_nf]; simp; module
    rw [h]; exact Submodule.zero_mem _
  · rw [g2_x4_y3_aux]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem 12)) (hmem 13)
  · rw [g2_x4_y4_aux]; exact Submodule.smul_mem _ _ (hmem 5)
  · have h : g2X4 * g2Zneg2 - g2Zneg2 * g2X4 = -g2Y4 := by rw [g2X4_nf, g2Zneg2_nf, g2Y4_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 10)
  · have hH := g2H1_comm_basis 4; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 4))
  · have hH := g2H2_comm_basis 4; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 4))
  · rw [g2_e0_f0_aux]; exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hmem 13)) (hmem 12)
  · have h : g2E0 * g2Y1 - g2Y1 * g2E0 = g2Y3 := by rw [g2E0_nf, g2Y1_nf, g2Y3_nf]; simp; module
    rw [h]; exact hmem 9
  · have h : g2E0 * g2Y2 - g2Y2 * g2E0 = 0 := by rw [g2E0_nf, g2Y2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · rw [g2_e0_y3_aux]; exact Submodule.smul_mem _ _ (hmem 10)
  · rw [g2_e0_y4_aux]; exact Submodule.smul_mem _ _ (hmem 8)
  · have h : g2E0 * g2Zneg2 - g2Zneg2 * g2E0 = 0 := by rw [g2E0_nf, g2Zneg2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have hH := g2H1_comm_basis 5; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 5))
  · have hH := g2H2_comm_basis 5; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 5))
  · have h : g2F0 * g2Y1 - g2Y1 * g2F0 = 0 := by rw [g2F0_nf, g2Y1_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2F0 * g2Y2 - g2Y2 * g2F0 = -g2Y4 := by rw [g2F0_nf, g2Y2_nf, g2Y4_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 10)
  · rw [g2_f0_y3_aux]; exact Submodule.smul_mem _ _ (hmem 7)
  · rw [g2_f0_y4_aux]; exact Submodule.smul_mem _ _ (hmem 9)
  · have h : g2F0 * g2Zneg2 - g2Zneg2 * g2F0 = 0 := by rw [g2F0_nf, g2Zneg2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have hH := g2H1_comm_basis 6; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 6))
  · have hH := g2H2_comm_basis 6; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 6))
  · have h : g2Y1 * g2Y2 - g2Y2 * g2Y1 = -g2Zneg2 := by rw [g2Y1_nf, g2Y2_nf, g2Zneg2_nf]; simp; module
    rw [h]; exact Submodule.neg_mem _ (hmem 11)
  · have h : g2Y1 * g2Y3 - g2Y3 * g2Y1 = 0 := by rw [g2Y1_nf, g2Y3_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Y1 * g2Y4 - g2Y4 * g2Y1 = 0 := by rw [g2Y1_nf, g2Y4_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Y1 * g2Zneg2 - g2Zneg2 * g2Y1 = 0 := by rw [g2Y1_nf, g2Zneg2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have hH := g2H1_comm_basis 7; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 7))
  · have hH := g2H2_comm_basis 7; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 7))

private theorem g2Bracket_row_ge8 (i j : Fin 14) (hi : 8 ≤ i.val) (hij : i < j) :
    g2Basis i * g2Basis j - g2Basis j * g2Basis i ∈ g2Submodule := by
  have hmem : ∀ k : Fin 14, g2Basis k ∈ g2Submodule :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  rw [Fin.lt_def] at hij
  fin_cases i <;> fin_cases j <;>
    dsimp only at hi hij <;>
    try (exfalso; have _ := hi; have _ := hij; omega)
  all_goals simp only [g2Basis]
  · have h : g2Y2 * g2Y3 - g2Y3 * g2Y2 = 0 := by rw [g2Y2_nf, g2Y3_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Y2 * g2Y4 - g2Y4 * g2Y2 = 0 := by rw [g2Y2_nf, g2Y4_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have h : g2Y2 * g2Zneg2 - g2Zneg2 * g2Y2 = 0 := by rw [g2Y2_nf, g2Zneg2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have hH := g2H1_comm_basis 8; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 8))
  · have hH := g2H2_comm_basis 8; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 8))
  · rw [g2_y3_y4_aux]; exact Submodule.smul_mem _ _ (hmem 11)
  · have h : g2Y3 * g2Zneg2 - g2Zneg2 * g2Y3 = 0 := by rw [g2Y3_nf, g2Zneg2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have hH := g2H1_comm_basis 9; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 9))
  · have hH := g2H2_comm_basis 9; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 9))
  · have h : g2Y4 * g2Zneg2 - g2Zneg2 * g2Y4 = 0 := by rw [g2Y4_nf, g2Zneg2_nf]; simp
    rw [h]; exact Submodule.zero_mem _
  · have hH := g2H1_comm_basis 10; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 10))
  · have hH := g2H2_comm_basis 10; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 10))
  · have hH := g2H1_comm_basis 11; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 11))
  · have hH := g2H2_comm_basis 11; simp only [g2Basis] at hH; rw [← neg_sub, hH]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 11))
  · rw [g2_five_grading_and_cartan.1]; exact Submodule.zero_mem _

end MatrixUnitExpand2

private theorem g2Basis_bracket_mem (i j : Fin 14) :
    g2Basis i * g2Basis j - g2Basis j * g2Basis i ∈ g2Submodule := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · by_cases hi4 : i.val < 4
    · exact g2Bracket_row_lt4 i j hi4 hij
    · by_cases hi8 : i.val < 8
      · exact g2Bracket_row_4_to_7 i j ⟨Nat.le_of_not_lt hi4, hi8⟩ hij
      · exact g2Bracket_row_ge8 i j (Nat.le_of_not_lt hi8) hij
  · rw [sub_self]
    exact Submodule.zero_mem _
  · have hanti : g2Basis i * g2Basis j - g2Basis j * g2Basis i =
        -(g2Basis j * g2Basis i - g2Basis i * g2Basis j) := (neg_sub _ _).symm
    rw [hanti]
    refine Submodule.neg_mem _ ?_
    by_cases hj4 : j.val < 4
    · exact g2Bracket_row_lt4 j i hj4 hji
    · by_cases hj8 : j.val < 8
      · exact g2Bracket_row_4_to_7 j i ⟨Nat.le_of_not_lt hj4, hj8⟩ hji
      · exact g2Bracket_row_ge8 j i (Nat.le_of_not_lt hj8) hji

/-- Complete closure of `g2Submodule` (`g_{2(2)} ⊂ M₁₆(ℝ)`) under the matrix Lie commutator. -/
theorem g2Submodule_lie_closed {A B : Matrix Krein16Idx Krein16Idx ℝ}
    (hA : A ∈ g2Submodule) (hB : B ∈ g2Submodule) :
    A * B - B * A ∈ g2Submodule := by
  have hfix : ∀ B' : Matrix Krein16Idx Krein16Idx ℝ, B' ∈ g2Submodule →
      ∀ A' ∈ g2Submodule, A' * B' - B' * A' ∈ g2Submodule := by
    intro B' hB' A' hA'
    refine Submodule.span_induction (hx := hA') ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩
      refine Submodule.span_induction (hx := hB') ?_ ?_ ?_ ?_
      · rintro _ ⟨j, rfl⟩
        exact g2Basis_bracket_mem i j
      · rw [Matrix.mul_zero, Matrix.zero_mul, sub_self]
        exact Submodule.zero_mem _
      · intro X Y _ _ hX hY
        have hlin : g2Basis i * (X + Y) - (X + Y) * g2Basis i =
            (g2Basis i * X - X * g2Basis i) + (g2Basis i * Y - Y * g2Basis i) := by
          rw [Matrix.mul_add, Matrix.add_mul]
          abel
        rw [hlin]
        exact Submodule.add_mem _ hX hY
      · intro r X _ hX
        have hlin : g2Basis i * (r • X) - (r • X) * g2Basis i =
            r • (g2Basis i * X - X * g2Basis i) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        rw [hlin]
        exact Submodule.smul_mem _ r hX
    · rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]
      exact Submodule.zero_mem _
    · intro X Y _ _ hX hY
      have hlin : (X + Y) * B' - B' * (X + Y) = (X * B' - B' * X) + (Y * B' - B' * Y) := by
        rw [Matrix.add_mul, Matrix.mul_add]
        abel
      rw [hlin]
      exact Submodule.add_mem _ hX hY
    · intro r X _ hX
      have hlin : (r • X) * B' - B' * (r • X) = r • (X * B' - B' * X) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      rw [hlin]
      exact Submodule.smul_mem _ r hX
  exact hfix B hB A hA

/-- Lie bracket soldered onto the triality-fixed coordinate carrier through the explicit matrix
carrier equivalence. This is an induced bracket; the raw root-coordinate model does not itself
define a bracket. -/
def s3FixedSolderedBracket (x y : s3FixedSpin44Submodule) : s3FixedSpin44Submodule :=
  s3FixedToG2CarrierEquiv.symm
    ⟨((s3FixedToG2CarrierEquiv x).1 * (s3FixedToG2CarrierEquiv y).1 -
        (s3FixedToG2CarrierEquiv y).1 * (s3FixedToG2CarrierEquiv x).1),
      g2Submodule_lie_closed (s3FixedToG2CarrierEquiv x).2
        (s3FixedToG2CarrierEquiv y).2⟩

/-- The soldered bracket is carried exactly to the matrix commutator. -/
@[simp] theorem s3FixedToG2CarrierEquiv_solderedBracket
    (x y : s3FixedSpin44Submodule) :
    s3FixedToG2CarrierEquiv (s3FixedSolderedBracket x y) =
      ⟨((s3FixedToG2CarrierEquiv x).1 * (s3FixedToG2CarrierEquiv y).1 -
          (s3FixedToG2CarrierEquiv y).1 * (s3FixedToG2CarrierEquiv x).1),
        g2Submodule_lie_closed (s3FixedToG2CarrierEquiv x).2
          (s3FixedToG2CarrierEquiv y).2⟩ := by
  simp [s3FixedSolderedBracket]

/-- The transported bracket is alternating. -/
theorem s3FixedSolderedBracket_self (x : s3FixedSpin44Submodule) :
    s3FixedSolderedBracket x x = 0 := by
  apply s3FixedToG2CarrierEquiv.injective
  simp [s3FixedToG2CarrierEquiv_solderedBracket]

/-- The transported bracket satisfies Jacobi by the associative commutator identity. -/
theorem s3FixedSolderedBracket_jacobi (x y z : s3FixedSpin44Submodule) :
    s3FixedSolderedBracket x (s3FixedSolderedBracket y z) +
      s3FixedSolderedBracket y (s3FixedSolderedBracket z x) +
      s3FixedSolderedBracket z (s3FixedSolderedBracket x y) = 0 := by
  apply s3FixedToG2CarrierEquiv.injective
  simp only [map_add, map_zero, s3FixedToG2CarrierEquiv_solderedBracket]
  apply Subtype.ext
  simp
  noncomm_ring

/-- Scalar compatibility of the soldered bracket in its second argument. -/
theorem s3FixedSolderedBracket_smul_right (r : ℝ)
    (x y : s3FixedSpin44Submodule) :
    s3FixedSolderedBracket x (r • y) = r • s3FixedSolderedBracket x y := by
  apply s3FixedToG2CarrierEquiv.injective
  simp only [s3FixedToG2CarrierEquiv_solderedBracket, map_smul]
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [smul_sub]
  simp

/-- Lie-ring structure on the coordinate carrier, soldered through the proved matrix equivalence. -/
instance : LieRing s3FixedSpin44Submodule where
  bracket := s3FixedSolderedBracket
  add_lie := by
    intro x y z
    apply s3FixedToG2CarrierEquiv.injective
    simp only [map_add, s3FixedToG2CarrierEquiv_solderedBracket]
    apply Subtype.ext
    simp
    noncomm_ring
  lie_add := by
    intro x y z
    apply s3FixedToG2CarrierEquiv.injective
    simp only [map_add, s3FixedToG2CarrierEquiv_solderedBracket]
    apply Subtype.ext
    simp
    noncomm_ring
  lie_self := s3FixedSolderedBracket_self
  leibniz_lie := by
    intro x y z
    apply s3FixedToG2CarrierEquiv.injective
    simp only [map_add, s3FixedToG2CarrierEquiv_solderedBracket]
    apply Subtype.ext
    simp
    noncomm_ring

/-- Real Lie-algebra structure compatible with scalar multiplication on the triality-fixed
coordinate carrier. -/
instance : LieAlgebra ℝ s3FixedSpin44Submodule where
  lie_smul := s3FixedSolderedBracket_smul_right

/-- Joint eigenspace support in the explicit G₂ basis: a matrix in `g2Submodule` that is an
eigenvector for both Cartan adjoint actions can have nonzero basis coefficients only at indices
with that same pair of weights. The statement is conditional on the eigenvector equations and
uses linear independence of the actual 14 matrices; no dimension count is substituted. -/
theorem g2_joint_eigenvector_basis_support
    {X : Matrix Krein16Idx Krein16Idx ℝ} (hX : X ∈ g2Submodule) (μ ν : ℝ)
    (hμ : g2H1 * X - X * g2H1 = μ • X)
    (hν : g2Halpha * X - X * g2Halpha = ν • X) :
    ∃ c : Fin 14 → ℝ, X = ∑ k : Fin 14, c k • g2Basis k ∧
      ∀ k : Fin 14, c k ≠ 0 →
        (g2Grade k : ℝ) = μ ∧ (g2AlphaWeight k : ℝ) = ν := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
  have hlin := Fintype.linearIndependent_iff.mp g2Basis_linearIndependent
  have hsumμ :
      ∑ k : Fin 14, (c k * (g2Grade k : ℝ)) • g2Basis k =
        ∑ k : Fin 14, (μ * c k) • g2Basis k := by
    rw [← hc] at hμ
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Finset.sum_sub_distrib, ← smul_sub] at hμ
    simp_rw [g2_five_grading_and_cartan.2.1, smul_smul] at hμ
    simpa only [Finset.smul_sum, smul_smul] using hμ
  have hsumν :
      ∑ k : Fin 14, (c k * (g2AlphaWeight k : ℝ)) • g2Basis k =
        ∑ k : Fin 14, (ν * c k) • g2Basis k := by
    rw [← hc] at hν
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Finset.sum_sub_distrib, ← smul_sub] at hν
    simp_rw [g2_five_grading_and_cartan.2.2, smul_smul] at hν
    simpa only [Finset.smul_sum, smul_smul] using hν
  have hzeroμ :
      ∑ k : Fin 14, (c k * ((g2Grade k : ℝ) - μ)) • g2Basis k = 0 := by
    calc
      ∑ k : Fin 14, (c k * ((g2Grade k : ℝ) - μ)) • g2Basis k =
          (∑ k : Fin 14, (c k * (g2Grade k : ℝ)) • g2Basis k) -
            (∑ k : Fin 14, (μ * c k) • g2Basis k) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              simp [mul_sub, sub_smul, mul_comm]
      _ = 0 := by rw [hsumμ, sub_self]
  have hzeroν :
      ∑ k : Fin 14, (c k * ((g2AlphaWeight k : ℝ) - ν)) • g2Basis k = 0 := by
    calc
      ∑ k : Fin 14, (c k * ((g2AlphaWeight k : ℝ) - ν)) • g2Basis k =
          (∑ k : Fin 14, (c k * (g2AlphaWeight k : ℝ)) • g2Basis k) -
            (∑ k : Fin 14, (ν * c k) • g2Basis k) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              simp [mul_sub, sub_smul, mul_comm]
      _ = 0 := by rw [hsumν, sub_self]
  refine ⟨c, hc.symm, ?_⟩
  intro k hck
  have hμk := hlin (fun m => c m * ((g2Grade m : ℝ) - μ)) hzeroμ k
  have hνk := hlin (fun m => c m * ((g2AlphaWeight m : ℝ) - ν)) hzeroν k
  have hgrade : (g2Grade k : ℝ) - μ = 0 :=
    (mul_eq_zero.mp hμk).resolve_left hck
  have halpha : (g2AlphaWeight k : ℝ) - ν = 0 :=
    (mul_eq_zero.mp hνk).resolve_left hck
  exact ⟨sub_eq_zero.mp hgrade, sub_eq_zero.mp halpha⟩

/-- For every pair of explicit G₂ root or Cartan basis elements, the matrix commutator expands
in the 14-element basis using only components whose two Cartan weights are the sums of the
input weights. This is the concrete structure-constant support rule in the matrix carrier. -/
theorem g2_basis_bracket_support (i j : Fin 14) :
    ∃ c : Fin 14 → ℝ,
      g2Basis i * g2Basis j - g2Basis j * g2Basis i =
        ∑ k : Fin 14, c k • g2Basis k ∧
      ∀ k : Fin 14, c k ≠ 0 →
        (g2Grade k : ℝ) = ((g2Grade i + g2Grade j : ℤ) : ℝ) ∧
        (g2AlphaWeight k : ℝ) = ((g2AlphaWeight i + g2AlphaWeight j : ℤ) : ℝ) := by
  have hi : g2Basis i ∈ g2Submodule := Submodule.subset_span ⟨i, rfl⟩
  have hj : g2Basis j ∈ g2Submodule := Submodule.subset_span ⟨j, rfl⟩
  have hbr := g2_basis_bracket_weights i j
  exact g2_joint_eigenvector_basis_support
    (g2Submodule_lie_closed hi hj)
    ((g2Grade i + g2Grade j : ℤ) : ℝ)
    ((g2AlphaWeight i + g2AlphaWeight j : ℤ) : ℝ)
    hbr.1 hbr.2

/-- Strict centerlessness of the 14-dimensional split `g_{2(2)}` subalgebra:
`Z ∈ g2Submodule ∧ (∀ W ∈ g2Submodule, [W, Z] = 0) → Z = 0`. -/
theorem g2Submodule_center_trivial {Z : Matrix Krein16Idx Krein16Idx ℝ}
    (hZ : Z ∈ g2Submodule) (hcent : ∀ W ∈ g2Submodule, W * Z - Z * W = 0) :
    Z = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hZ
  have hmem : ∀ k : Fin 14, g2Basis k ∈ g2Submodule := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hlin := Fintype.linearIndependent_iff.mp g2Basis_linearIndependent
  have hH1_zero : ∑ k : Fin 14, (c k * (g2Grade k : ℝ)) • g2Basis k = 0 := by
    have hz1 := hcent g2H1 (hmem 12)
    rw [← hc] at hz1
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Finset.sum_sub_distrib, ← smul_sub] at hz1
    simp_rw [g2_five_grading_and_cartan.2.1, smul_smul] at hz1
    exact hz1
  have hc_grade : ∀ k : Fin 14, g2Grade k ≠ 0 → c k = 0 := by
    intro k hk
    have hmul0 := hlin (fun m => c m * (g2Grade m : ℝ)) hH1_zero k
    have hgk : (g2Grade k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    exact (mul_eq_zero.mp hmul0).resolve_right hgk
  have hHalpha_mem : g2Halpha ∈ g2Submodule := by
    unfold g2Halpha
    exact Submodule.sub_mem _ (hmem 12) (Submodule.smul_mem _ 2 (hmem 13))
  have hHa_zero : ∑ k : Fin 14, (c k * (g2AlphaWeight k : ℝ)) • g2Basis k = 0 := by
    have hza := hcent g2Halpha hHalpha_mem
    rw [← hc] at hza
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Finset.sum_sub_distrib, ← smul_sub] at hza
    simp_rw [g2_five_grading_and_cartan.2.2, smul_smul] at hza
    exact hza
  have hc_alpha : ∀ k : Fin 14, g2AlphaWeight k ≠ 0 → c k = 0 := by
    intro k hk
    have hmul0 := hlin (fun m => c m * (g2AlphaWeight m : ℝ)) hHa_zero k
    have hak : (g2AlphaWeight k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    exact (mul_eq_zero.mp hmul0).resolve_right hak
  have hc_noncartan : ∀ k : Fin 14, k ≠ 12 → k ≠ 13 → c k = 0 := by
    intro k hk12 hk13
    fin_cases k
    · exact hc_grade 0 (by decide)
    · exact hc_grade 1 (by decide)
    · exact hc_grade 2 (by decide)
    · exact hc_grade 3 (by decide)
    · exact hc_grade 4 (by decide)
    · exact hc_alpha 5 (by decide)
    · exact hc_alpha 6 (by decide)
    · exact hc_grade 7 (by decide)
    · exact hc_grade 8 (by decide)
    · exact hc_grade 9 (by decide)
    · exact hc_grade 10 (by decide)
    · exact hc_grade 11 (by decide)
    · exact absurd rfl hk12
    · exact absurd rfl hk13
  have hZ_cartan : Z = c 12 • g2H1 + c 13 • g2H2 := by
    rw [← hc]
    have hc_other : ∀ k : Fin 14, k ≠ 12 → k ≠ 13 → c k • g2Basis k = 0 := by
      intro k hk12 hk13
      rw [hc_noncartan k hk12 hk13, zero_smul]
    have hsplit : (∑ k : Fin 14, c k • g2Basis k) =
        c 12 • g2Basis 12 + (∑ k ∈ Finset.univ.erase 12, c k • g2Basis k) := by
      rw [← Finset.add_sum_erase Finset.univ (fun k => c k • g2Basis k) (Finset.mem_univ 12)]
    have hsplit2 : (∑ k ∈ Finset.univ.erase 12, c k • g2Basis k) =
        c 13 • g2Basis 13 + (∑ k ∈ (Finset.univ.erase 12).erase 13, c k • g2Basis k) := by
      rw [← Finset.add_sum_erase (Finset.univ.erase 12) (fun k => c k • g2Basis k)
        (Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ 13⟩)]
    have hrest : (∑ k ∈ (Finset.univ.erase 12).erase 13, c k • g2Basis k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rcases Finset.mem_erase.mp hk with ⟨hk13, hk'⟩
      exact hc_other k (Finset.mem_erase.mp hk').1 hk13
    rw [hsplit, hsplit2, hrest, add_zero]
    simp only [g2Basis]
  have hZ_zp2 : g2Zpos2 * Z - Z * g2Zpos2 = 0 := hcent g2Zpos2 (hmem 0)
  have hZ_e0 : g2E0 * Z - Z * g2E0 = 0 := hcent g2E0 (hmem 5)
  have hz_e0_eq : g2E0 * Z - Z * g2E0 = c 13 • g2E0 := by
    rw [hZ_cartan, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    have hsplit : (c 12 • (g2E0 * g2H1) + c 13 • (g2E0 * g2H2)) -
        (c 12 • (g2H1 * g2E0) + c 13 • (g2H2 * g2E0)) =
        (-c 12) • (g2H1 * g2Basis 5 - g2Basis 5 * g2H1) +
          (-c 13) • (g2H2 * g2Basis 5 - g2Basis 5 * g2H2) := by
      simp only [g2Basis, smul_sub, neg_smul]
      abel
    rw [hsplit, g2H1_comm_basis 5, g2H2_comm_basis 5]
    simp [g2Grade, g2Basis]
  have hz_zp2_eq : g2Zpos2 * Z - Z * g2Zpos2 = (-(2 * c 12 + c 13)) • g2Zpos2 := by
    rw [hZ_cartan, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    have hsplit : (c 12 • (g2Zpos2 * g2H1) + c 13 • (g2Zpos2 * g2H2)) -
        (c 12 • (g2H1 * g2Zpos2) + c 13 • (g2H2 * g2Zpos2)) =
        (-c 12) • (g2H1 * g2Basis 0 - g2Basis 0 * g2H1) +
          (-c 13) • (g2H2 * g2Basis 0 - g2Basis 0 * g2H2) := by
      simp only [g2Basis, smul_sub, neg_smul]
      abel
    rw [hsplit, g2H1_comm_basis 0, g2H2_comm_basis 0]
    simp only [g2Grade, Matrix.cons_val_zero, Int.cast_ofNat, smul_smul, g2Basis, Int.cast_one,
      mul_one, ← add_smul]
    congr 1
    rw [neg_mul, mul_comm (c 12) 2, ← neg_add]
  have hc13_zero : c 13 = 0 := by
    rw [hz_e0_eq] at hZ_e0
    have hpt := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (g2Pivot 5).1 (g2Pivot 5).2) hZ_e0
    have hpv := g2Basis_eval_pivot 5 5
    simp only [↓reduceIte, g2Basis, g2PivotVal] at hpv
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hpt
    rw [hpv] at hpt
    norm_num at hpt
    exact hpt
  have hc12_zero : c 12 = 0 := by
    rw [hz_zp2_eq, hc13_zero] at hZ_zp2
    have hpt := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (g2Pivot 0).1 (g2Pivot 0).2) hZ_zp2
    have hpv := g2Basis_eval_pivot 0 0
    simp only [↓reduceIte, g2Basis, g2PivotVal, Matrix.cons_val_zero] at hpv
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hpt
    rw [hpv] at hpt
    linarith
  rw [hZ_cartan, hc12_zero, hc13_zero, zero_smul, zero_smul, add_zero]

/-- Top-grade central commutativity: `[Z₊₂, X_i] = 0` (`i = 1..4`) and `[Y_i, Z₋₂] = 0` (`i = 1..4`). -/
theorem g2_top_grade_central_commutativity :
    (g2Zpos2 * g2X1 - g2X1 * g2Zpos2 = 0 ∧
     g2Zpos2 * g2X2 - g2X2 * g2Zpos2 = 0 ∧
     g2Zpos2 * g2X3 - g2X3 * g2Zpos2 = 0 ∧
     g2Zpos2 * g2X4 - g2X4 * g2Zpos2 = 0) ∧
    (g2Y1 * g2Zneg2 - g2Zneg2 * g2Y1 = 0 ∧
     g2Y2 * g2Zneg2 - g2Zneg2 * g2Y2 = 0 ∧
     g2Y3 * g2Zneg2 - g2Zneg2 * g2Y3 = 0 ∧
     g2Y4 * g2Zneg2 - g2Zneg2 * g2Y4 = 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [g2Zpos2_nf, g2X1_nf]; simp; try abel
  · rw [g2Zpos2_nf, g2X2_nf]; simp; try abel
  · rw [g2Zpos2_nf, g2X3_nf]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg]; simp; try abel
  · rw [g2Zpos2_nf, g2X4_nf]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg]; simp; try abel
  · rw [g2Y1_nf, g2Zneg2_nf]; simp; try abel
  · rw [g2Y2_nf, g2Zneg2_nf]; simp; try abel
  · rw [g2Y3_nf, g2Zneg2_nf]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg]; simp; try abel
  · rw [g2Y4_nf, g2Zneg2_nf]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg]; simp; try abel

/-! ### Canonical `8 × 8` Split-Signature `so(4,4)` Representation `rhoVec8` & Isomorphism (`g₂(2) ↪ so(7) ⊂ so(4,4)`) -/

/-- Split signature `(4,4)` bilinear metric `diag(1, 1, 1, 1, -1, -1, -1, -1)` on `ℝ⁸`. -/
def eta44 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal ![1, 1, 1, 1, -1, -1, -1, -1]

/-- Explicit OpenGauss `T16` non-commutativity witness on `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem vec8_mat_noncommutative :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 0 0) h
  dsimp [A, B] at h00
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight] at h00
  norm_num at h00

private theorem eta44_entry (a b : Fin 8) :
    eta44 a b = if a = b then (if a.val < 4 then 1 else -1) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [eta44]

/-- `eta44` is symmetric, involutive (`eta44² = 1`), and traceless (`signature (4,4)`). -/
theorem eta44_properties :
    eta44ᵀ = eta44 ∧ eta44 * eta44 = 1 ∧ Matrix.trace eta44 = 0 := by
  have hsymm : eta44ᵀ = eta44 := by
    ext i j
    rw [Matrix.transpose_apply, eta44_entry, eta44_entry]
    by_cases hij : i = j <;> simp [hij, eq_comm]
  have hsq : eta44 * eta44 = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, eta44_entry]
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; split_ifs <;> norm_num
      · simp [hij]
    · intro k _ hki
      simp [hki.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have htr : Matrix.trace eta44 = 0 := by
    unfold Matrix.trace eta44
    rw [Fin.sum_univ_eight]
    simp
  exact ⟨hsymm, hsq, htr⟩

/-- Canonical adjoint vector representation `M₁₆(ℝ) →ₗ[ℝ] M₈(ℝ)` extracting the `Cl⁽¹⁾(4,4)`
coordinates of `[X, γ_b]` via Hilbert–Schmidt trace projection. -/
def rhoVec8 : Matrix Krein16Idx Krein16Idx ℝ →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun X := Matrix.of fun a b =>
    ((if a.val < 4 then (1 : ℝ) else -1) / 16) *
      Matrix.trace (cl44Gen a * (X * cl44Gen b - cl44Gen b * X))
  map_add' X Y := by
    ext a b
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.add_mul, Matrix.mul_add]
    have hsplit : cl44Gen a * (X * cl44Gen b + Y * cl44Gen b - (cl44Gen b * X + cl44Gen b * Y)) =
        cl44Gen a * (X * cl44Gen b - cl44Gen b * X) +
          cl44Gen a * (Y * cl44Gen b - cl44Gen b * Y) := by
      noncomm_ring
    rw [hsplit, Matrix.trace_add, mul_add]
  map_smul' r X := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, RingHom.id_apply,
      Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, Matrix.trace_smul, mul_left_comm]

/-- For EVERY matrix `X ∈ M₁₆(ℝ)`, `rhoVec8 X` is `eta44`-skew (`∈ so(4,4)`). -/
theorem rhoVec8_so44_skew (X : Matrix Krein16Idx Krein16Idx ℝ) :
    (rhoVec8 X)ᵀ * eta44 + eta44 * rhoVec8 X = 0 := by
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply,
    eta44_entry]
  have hs1 : (∑ c : Fin 8, rhoVec8 X c a * (if c = b then (if c.val < 4 then 1 else -1) else 0)) =
      rhoVec8 X b a * (if b.val < 4 then 1 else -1) := by
    rw [Finset.sum_eq_single b]
    · simp only [↓reduceIte]
    · intro c _ hcb; simp only [hcb, ↓reduceIte, mul_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have hs2 : (∑ c : Fin 8, (if a = c then (if a.val < 4 then 1 else -1) else 0) * rhoVec8 X c b) =
      (if a.val < 4 then 1 else -1) * rhoVec8 X a b := by
    rw [Finset.sum_eq_single a]
    · simp only [↓reduceIte]
    · intro c _ hca; simp only [hca.symm, ↓reduceIte, zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  rw [hs1, hs2]
  simp only [rhoVec8, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  have hsig_a : (if a.val < 4 then (1 : ℝ) else -1) * ((if a.val < 4 then (1 : ℝ) else -1) / 16) =
      (1 / 16 : ℝ) := by
    split_ifs <;> norm_num
  have hsig_b : ((if b.val < 4 then (1 : ℝ) else -1) / 16) * (if b.val < 4 then (1 : ℝ) else -1) =
      (1 / 16 : ℝ) := by
    split_ifs <;> norm_num
  have hnorm1 : (((if b.val < 4 then (1 : ℝ) else -1) / 16) *
      Matrix.trace (cl44Gen b * (X * cl44Gen a - cl44Gen a * X))) *
      (if b.val < 4 then (1 : ℝ) else -1) =
      (1 / 16 : ℝ) * Matrix.trace (cl44Gen b * (X * cl44Gen a - cl44Gen a * X)) := by
    rw [mul_right_comm, hsig_b]
  have hnorm2 : (if a.val < 4 then (1 : ℝ) else -1) *
      (((if a.val < 4 then (1 : ℝ) else -1) / 16) *
        Matrix.trace (cl44Gen a * (X * cl44Gen b - cl44Gen b * X))) =
      (1 / 16 : ℝ) * Matrix.trace (cl44Gen a * (X * cl44Gen b - cl44Gen b * X)) := by
    rw [← mul_assoc, hsig_a]
  rw [hnorm1, hnorm2, ← mul_add]
  have hc1 : Matrix.trace (cl44Gen b * (X * cl44Gen a - cl44Gen a * X)) =
      Matrix.trace (cl44Gen a * (cl44Gen b * X)) - Matrix.trace (cl44Gen b * cl44Gen a * X) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc, Matrix.trace_mul_comm (cl44Gen b * X) (cl44Gen a),
      ← Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]
  have hc2 : Matrix.trace (cl44Gen a * (X * cl44Gen b - cl44Gen b * X)) =
      Matrix.trace (cl44Gen b * cl44Gen a * X) - Matrix.trace (cl44Gen a * (cl44Gen b * X)) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc, Matrix.trace_mul_comm (cl44Gen a * X) (cl44Gen b)]
    simp only [Matrix.mul_assoc]
  rw [hc1, hc2]
  linarith

/-- Exact vector-representation matrix of a Clifford bivector. For `a ≠ b`,
`ad(γₐγ_b)` rotates only the `(a,b)` coordinate plane, with the split-signature
signs determined by the Clifford squares. This fixes the root-vector normalization
needed to compare the Cl(4,4) bracket with D₄ root coordinates. -/
theorem rhoVec8_bivector_entry {a b : Fin 8} (hab : a ≠ b) (i j : Fin 8) :
    rhoVec8 (cl44Bivector a b) i j =
      if i = a ∧ j = b then 2 * (if b.val < 4 then (1 : ℝ) else -1)
      else if i = b ∧ j = a then -(2 * (if a.val < 4 then (1 : ℝ) else -1))
      else 0 := by
  let q : Fin 8 → ℝ := fun k => if k.val < 4 then 1 else -1
  have hb : cl44Bivector a b * cl44Gen b - cl44Gen b * cl44Bivector a b =
      (2 * q b) • cl44Gen a := by
    rw [cl44Bivector_orthogonal_shear.2.1 hab]
    simp [q]
  have ha : cl44Bivector a b * cl44Gen a - cl44Gen a * cl44Bivector a b =
      -(2 * q a) • cl44Gen b := by
    have hba := cl44Bivector_orthogonal_shear.2.1 hab.symm
    have hswap : cl44Bivector a b = -cl44Bivector b a := by
      unfold cl44Bivector
      exact eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab.symm)
    calc
      cl44Bivector a b * cl44Gen a - cl44Gen a * cl44Bivector a b =
          -(cl44Bivector b a * cl44Gen a - cl44Gen a * cl44Bivector b a) := by
            rw [hswap]; noncomm_ring
      _ = -(2 * q a) • cl44Gen b := by rw [hba]; simp [q]
  have hzero (c : Fin 8) (hca : c ≠ a) (hcb : c ≠ b) :
      cl44Bivector a b * cl44Gen c - cl44Gen c * cl44Bivector a b = 0 :=
    cl44Bivector_orthogonal_shear.1 hca hcb
  have hq_sq (k : Fin 8) : q k * q k = 1 := by
    dsimp [q]
    split_ifs <;> norm_num
  simp only [rhoVec8, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  by_cases hjb : j = b
  · subst j
    rw [hb, Matrix.mul_smul, Matrix.trace_smul, trace_cl44Gen_mul]
    by_cases hia : i = a
    · subst i
      simp [q]
      split_ifs <;> norm_num
    · simp [q, hia, hab.symm]
  · by_cases hja : j = a
    · subst j
      rw [ha, Matrix.mul_smul, Matrix.trace_smul, trace_cl44Gen_mul]
      by_cases hib : i = b
      · subst i
        simp [q, hab]
        split_ifs <;> norm_num
      · simp [q, hib, hab]
    · rw [hzero j hja hjb]
      simp [hjb, hja]

/-- Any `V ∈ cl44Vec1Submodule` reconstructs identically from its Hilbert–Schmidt trace coordinates. -/
theorem cl44Vec1Submodule_coord {V : Matrix Krein16Idx Krein16Idx ℝ} (hV : V ∈ cl44Vec1Submodule) :
    V = ∑ a : Fin 8, (((if a.val < 4 then (1 : ℝ) else -1) / 16) *
      Matrix.trace (cl44Gen a * V)) • cl44Gen a := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hV
  have hcoef : ∀ a : Fin 8,
      (((if a.val < 4 then (1 : ℝ) else -1) / 16) * Matrix.trace (cl44Gen a * V)) = c a := by
    intro a
    rw [← hc, Matrix.mul_sum, Matrix.trace_sum]
    have hsum : (∑ b : Fin 8, Matrix.trace (cl44Gen a * (c b • cl44Gen b))) =
        c a * (if a.val < 4 then 16 else -16) := by
      rw [Finset.sum_eq_single a]
      · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_cl44Gen_mul]
        simp only [↓reduceIte]
      · intro b _ hb
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_cl44Gen_mul]
        simp only [hb.symm, ↓reduceIte, mul_zero]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    rw [hsum]
    split_ifs <;> linarith
  simp_rw [hcoef]
  exact hc.symm

/-- Submodule `Cl⁽²⁾(4,4)` spanned by all bivectors `B_{ab}` (`a ≠ b`). -/
def cl44BivectorSpan : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ {B | ∃ a b : Fin 8, a ≠ b ∧ B = cl44Bivector a b}

private lemma biv_mem {a b : Fin 8} (hab : a ≠ b) : cl44Bivector a b ∈ cl44BivectorSpan :=
  Submodule.subset_span ⟨a, b, hab, rfl⟩

/-- The concrete null-vector root vector constructed above belongs to the
existing Clifford bivector subspace. -/
theorem d4_rootVectorPlusPlus_mem_bivectorSpan : d4RootVectorPlusPlus ∈ cl44BivectorSpan := by
  change (cl44Gen 0 + cl44Gen 4) * (cl44Gen 1 + cl44Gen 5) ∈ cl44BivectorSpan
  simp only [Matrix.add_mul, Matrix.mul_add]
  change (cl44Bivector 0 1 + cl44Bivector 4 1) +
      (cl44Bivector 0 5 + cl44Bivector 4 5) ∈ cl44BivectorSpan
  exact Submodule.add_mem _
    (Submodule.add_mem _ (biv_mem (by decide)) (biv_mem (by decide)))
    (Submodule.add_mem _ (biv_mem (by decide)) (biv_mem (by decide)))

private lemma cl44Bivector_reverse {a b : Fin 8} (hab : a ≠ b) :
    cl44Bivector b a = -cl44Bivector a b := by
  unfold cl44Bivector
  exact eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab)

private lemma cl44Bivector_swap {a b : Fin 8} (hab : a ≠ b) :
    cl44Bivector a b = -cl44Bivector b a := by
  rw [cl44Bivector_reverse hab]
  simp

private lemma cl44Bivector_bracket_mem {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    cl44Bivector a b * cl44Bivector c d - cl44Bivector c d * cl44Bivector a b ∈
      cl44BivectorSpan := by
  rcases cl44Bivector_orthogonal_shear with ⟨_, _, hoverlap, hdisjoint⟩
  by_cases hca : c = a
  · subst c
    by_cases hdb : d = b
    · subst d
      simp only [sub_self]
      exact Submodule.zero_mem _
    · have hbd : b ≠ d := fun h => hdb h.symm
      have hbr := (hoverlap hab.symm hcd hbd).1
      have hEq : cl44Bivector a b * cl44Bivector a d -
          cl44Bivector a d * cl44Bivector a b =
          -((2 : ℝ) • ((if a.val < 4 then (1 : ℝ) else -1) • cl44Bivector b d)) := by
        rw [cl44Bivector_swap hab]
        calc
          -cl44Bivector b a * cl44Bivector a d - cl44Bivector a d * (-cl44Bivector b a) =
              -(cl44Bivector b a * cl44Bivector a d - cl44Bivector a d * cl44Bivector b a) := by
                noncomm_ring
          _ = -((2 : ℝ) • ((if a.val < 4 then (1 : ℝ) else -1) • cl44Bivector b d)) := by rw [hbr]
      rw [hEq]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (biv_mem hbd)))
  · by_cases hcb : c = b
    · subst c
      by_cases hda : d = a
      · subst d
        rw [cl44Bivector_swap hab]
        have hEq : -cl44Bivector b a * cl44Bivector b a -
            cl44Bivector b a * (-cl44Bivector b a) = 0 := by noncomm_ring
        rw [hEq]
        exact Submodule.zero_mem _
      · have had : a ≠ d := fun h => hda h.symm
        have hbr := (hoverlap hab hcd had).1
        rw [hbr]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (biv_mem had))
    · by_cases hda : d = a
      · subst d
        have hac : a ≠ c := fun h => hca h.symm
        have hbc : b ≠ c := fun h => hcb h.symm
        have hbr := (hoverlap hab.symm hac hbc).1
        have hEq : cl44Bivector a b * cl44Bivector c a -
            cl44Bivector c a * cl44Bivector a b =
            (2 : ℝ) • ((if a.val < 4 then (1 : ℝ) else -1) • cl44Bivector b c) := by
          rw [cl44Bivector_swap hab, cl44Bivector_swap hca]
          calc
            -cl44Bivector b a * (-cl44Bivector a c) -
                (-cl44Bivector a c) * (-cl44Bivector b a) =
                cl44Bivector b a * cl44Bivector a c - cl44Bivector a c * cl44Bivector b a := by
                  noncomm_ring
            _ = (2 : ℝ) • ((if a.val < 4 then (1 : ℝ) else -1) • cl44Bivector b c) := hbr
        rw [hEq]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (biv_mem hbc))
      · by_cases hdb : d = b
        · subst d
          have hac : a ≠ c := fun h => hca h.symm
          have hbc : b ≠ c := fun h => hcb h.symm
          have hbr := (hoverlap hab hbc hac).1
          have hEq : cl44Bivector a b * cl44Bivector c b -
              cl44Bivector c b * cl44Bivector a b =
              -((2 : ℝ) • ((if b.val < 4 then (1 : ℝ) else -1) • cl44Bivector a c)) := by
            rw [cl44Bivector_swap hcb]
            calc
              cl44Bivector a b * (-cl44Bivector b c) -
                  (-cl44Bivector b c) * cl44Bivector a b =
                  -(cl44Bivector a b * cl44Bivector b c - cl44Bivector b c * cl44Bivector a b) := by
                    noncomm_ring
              _ = -((2 : ℝ) • ((if b.val < 4 then (1 : ℝ) else -1) • cl44Bivector a c)) := by rw [hbr]
          rw [hEq]
          exact Submodule.neg_mem _ (Submodule.smul_mem _ _
            (Submodule.smul_mem _ _ (biv_mem hac)))
        · have hac : a ≠ c := fun h => hca h.symm
          have had : a ≠ d := fun h => hda h.symm
          have hbc : b ≠ c := fun h => hcb h.symm
          have hbd : b ≠ d := fun h => hdb h.symm
          have hdis := (hdisjoint hac had hbc hbd).1
          rw [hdis]
          exact Submodule.zero_mem _

theorem cl44BivectorSpan_lie_closed {A B : Matrix Krein16Idx Krein16Idx ℝ}
    (hA : A ∈ cl44BivectorSpan) (hB : B ∈ cl44BivectorSpan) :
    A * B - B * A ∈ cl44BivectorSpan := by
  have hfix : ∀ B' : Matrix Krein16Idx Krein16Idx ℝ, B' ∈ cl44BivectorSpan →
      ∀ A' ∈ cl44BivectorSpan, A' * B' - B' * A' ∈ cl44BivectorSpan := by
    intro B' hB' A' hA'
    refine Submodule.span_induction (hx := hA') ?_ ?_ ?_ ?_
    · rintro _ ⟨a, b, hab, rfl⟩
      refine Submodule.span_induction (hx := hB') ?_ ?_ ?_ ?_
      · rintro _ ⟨c, d, hcd, rfl⟩
        exact cl44Bivector_bracket_mem hab hcd
      · rw [Matrix.mul_zero, Matrix.zero_mul, sub_self]
        exact Submodule.zero_mem _
      · intro X Y _ _ hX hY
        have hlin : cl44Bivector a b * (X + Y) - (X + Y) * cl44Bivector a b =
            (cl44Bivector a b * X - X * cl44Bivector a b) +
            (cl44Bivector a b * Y - Y * cl44Bivector a b) := by
          rw [Matrix.mul_add, Matrix.add_mul]
          abel
        rw [hlin]
        exact Submodule.add_mem _ hX hY
      · intro r X _ hX
        have hlin : cl44Bivector a b * (r • X) - (r • X) * cl44Bivector a b =
            r • (cl44Bivector a b * X - X * cl44Bivector a b) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        rw [hlin]
        exact Submodule.smul_mem _ r hX
    · rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]
      exact Submodule.zero_mem _
    · intro X Y _ _ hX hY
      have hlin : (X + Y) * B' - B' * (X + Y) =
          (X * B' - B' * X) + (Y * B' - B' * Y) := by
        rw [Matrix.add_mul, Matrix.mul_add]
        abel
      rw [hlin]
      exact Submodule.add_mem _ hX hY
    · intro r X _ hX
      have hlin : (r • X) * B' - B' * (r • X) = r • (X * B' - B' * X) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      rw [hlin]
      exact Submodule.smul_mem _ r hX
  exact hfix B hB A hA

private lemma ladder_prod_ud_mem {i j : Fin 8} (hi : i.val ∈ [1, 2, 3]) (hj : j.val ∈ [1, 2, 3])
    (hij : i ≠ j)
    (ui dj : Matrix Krein16Idx Krein16Idx ℝ)
    (hui : (2 : ℝ) • ui = cl44Gen i - cl44Gen ⟨i.val + 4, by simp at hi; omega⟩)
    (hdj : (2 : ℝ) • dj = cl44Gen j + cl44Gen ⟨j.val + 4, by simp at hj; omega⟩) :
    ui * dj ∈ cl44BivectorSpan := by
  let i' : Fin 8 := ⟨i.val + 4, by simp at hi; omega⟩
  let j' : Fin 8 := ⟨j.val + 4, by simp at hj; omega⟩
  have hmul4 : (4 : ℝ) • (ui * dj) =
      cl44Bivector i j + cl44Bivector i j' - cl44Bivector i' j - cl44Bivector i' j' := by
    have h4 : (4 : ℝ) • (ui * dj) = ((2 : ℝ) • ui) * ((2 : ℝ) • dj) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
    rw [h4, hui, hdj]
    unfold cl44Bivector
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  have h14 : ui * dj = (1 / 4 : ℝ) • ((4 : ℝ) • (ui * dj)) := by
    rw [smul_smul]; norm_num
  rw [h14, hmul4]
  have hij' : i ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [j'] at h; simp at hi hj; omega
  have hi'j : i' ≠ j := by intro h; rw [Fin.ext_iff] at h; dsimp [i'] at h; simp at hi hj; omega
  have hi'j' : i' ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [i', j'] at h; exact hij (Fin.ext (by omega))
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.sub_mem _
    (Submodule.add_mem _ (biv_mem hij) (biv_mem hij')) (biv_mem hi'j)) (biv_mem hi'j'))

private lemma ladder_prod_uu_mem {i j : Fin 8} (hi : i.val ∈ [1, 2, 3]) (hj : j.val ∈ [1, 2, 3])
    (hij : i ≠ j)
    (ui uj : Matrix Krein16Idx Krein16Idx ℝ)
    (hui : (2 : ℝ) • ui = cl44Gen i - cl44Gen ⟨i.val + 4, by simp at hi; omega⟩)
    (huj : (2 : ℝ) • uj = cl44Gen j - cl44Gen ⟨j.val + 4, by simp at hj; omega⟩) :
    ui * uj ∈ cl44BivectorSpan := by
  let i' : Fin 8 := ⟨i.val + 4, by simp at hi; omega⟩
  let j' : Fin 8 := ⟨j.val + 4, by simp at hj; omega⟩
  have hmul4 : (4 : ℝ) • (ui * uj) =
      cl44Bivector i j - cl44Bivector i j' - cl44Bivector i' j + cl44Bivector i' j' := by
    have h4 : (4 : ℝ) • (ui * uj) = ((2 : ℝ) • ui) * ((2 : ℝ) • uj) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
    rw [h4, hui, huj]
    unfold cl44Bivector
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    abel
  have h14 : ui * uj = (1 / 4 : ℝ) • ((4 : ℝ) • (ui * uj)) := by
    rw [smul_smul]; norm_num
  rw [h14, hmul4]
  have hij' : i ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [j'] at h; simp at hi hj; omega
  have hi'j : i' ≠ j := by intro h; rw [Fin.ext_iff] at h; dsimp [i'] at h; simp at hi hj; omega
  have hi'j' : i' ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [i', j'] at h; exact hij (Fin.ext (by omega))
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.sub_mem _
    (Submodule.sub_mem _ (biv_mem hij) (biv_mem hij')) (biv_mem hi'j)) (biv_mem hi'j'))

private lemma ladder_prod_dd_mem {i j : Fin 8} (hi : i.val ∈ [1, 2, 3]) (hj : j.val ∈ [1, 2, 3])
    (hij : i ≠ j)
    (di dj : Matrix Krein16Idx Krein16Idx ℝ)
    (hdi : (2 : ℝ) • di = cl44Gen i + cl44Gen ⟨i.val + 4, by simp at hi; omega⟩)
    (hdj : (2 : ℝ) • dj = cl44Gen j + cl44Gen ⟨j.val + 4, by simp at hj; omega⟩) :
    di * dj ∈ cl44BivectorSpan := by
  let i' : Fin 8 := ⟨i.val + 4, by simp at hi; omega⟩
  let j' : Fin 8 := ⟨j.val + 4, by simp at hj; omega⟩
  have hmul4 : (4 : ℝ) • (di * dj) =
      cl44Bivector i j + cl44Bivector i j' + cl44Bivector i' j + cl44Bivector i' j' := by
    have h4 : (4 : ℝ) • (di * dj) = ((2 : ℝ) • di) * ((2 : ℝ) • dj) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
    rw [h4, hdi, hdj]
    unfold cl44Bivector
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  have h14 : di * dj = (1 / 4 : ℝ) • ((4 : ℝ) • (di * dj)) := by
    rw [smul_smul]; norm_num
  rw [h14, hmul4]
  have hij' : i ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [j'] at h; simp at hi hj; omega
  have hi'j : i' ≠ j := by intro h; rw [Fin.ext_iff] at h; dsimp [i'] at h; simp at hi hj; omega
  have hi'j' : i' ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [i', j'] at h; exact hij (Fin.ext (by omega))
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (biv_mem hij) (biv_mem hij')) (biv_mem hi'j)) (biv_mem hi'j'))

private lemma et0_mul_op_mem {j : Fin 8} (hj : j.val ∈ [1, 2, 3])
    (op : Matrix Krein16Idx Krein16Idx ℝ) (sgn : ℝ)
    (hop : (2 : ℝ) • op = cl44Gen j + sgn • cl44Gen ⟨j.val + 4, by simp at hj; omega⟩) :
    et0Op * op ∈ cl44BivectorSpan := by
  let j' : Fin 8 := ⟨j.val + 4, by simp at hj; omega⟩
  have het0 : et0Op = cl44Gen 4 := rfl
  have hmul2 : (2 : ℝ) • (et0Op * op) = cl44Bivector 4 j + sgn • cl44Bivector 4 j' := by
    rw [← Matrix.mul_smul, hop, het0, Matrix.mul_add, Matrix.mul_smul]
    rfl
  have h12 : et0Op * op = (1 / 2 : ℝ) • ((2 : ℝ) • (et0Op * op)) := by
    rw [smul_smul]; norm_num
  rw [h12, hmul2]
  have h4j : (4 : Fin 8) ≠ j := by intro h; rw [Fin.ext_iff] at h; simp at hj; omega
  have h4j' : (4 : Fin 8) ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [j'] at h; simp at hj; omega
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (biv_mem h4j) (Submodule.smul_mem _ sgn (biv_mem h4j')))

private lemma g2Cartan_diff_mem {i j : Fin 8} (hi : i.val < 4) (hj : j.val < 4)
    (ui di uj dj : Matrix Krein16Idx Krein16Idx ℝ)
    (hui : (2 : ℝ) • ui = cl44Gen i - cl44Gen ⟨i.val + 4, by omega⟩)
    (hdi : (2 : ℝ) • di = cl44Gen i + cl44Gen ⟨i.val + 4, by omega⟩)
    (huj : (2 : ℝ) • uj = cl44Gen j - cl44Gen ⟨j.val + 4, by omega⟩)
    (hdj : (2 : ℝ) • dj = cl44Gen j + cl44Gen ⟨j.val + 4, by omega⟩) :
    ui * di - uj * dj ∈ cl44BivectorSpan := by
  let i' : Fin 8 := ⟨i.val + 4, by omega⟩
  let j' : Fin 8 := ⟨j.val + 4, by omega⟩
  have hii' : i ≠ i' := by intro h; rw [Fin.ext_iff] at h; dsimp [i'] at h; omega
  have hjj' : j ≠ j' := by intro h; rw [Fin.ext_iff] at h; dsimp [j'] at h; omega
  have hid_prod : (4 : ℝ) • (ui * di) = (2 : ℝ) • (1 : Matrix Krein16Idx Krein16Idx ℝ) +
      (2 : ℝ) • cl44Bivector i i' := by
    have h4 : (4 : ℝ) • (ui * di) = ((2 : ℝ) • ui) * ((2 : ℝ) • di) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
    rw [h4, hui, hdi, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
    have hsq1 : cl44Gen i * cl44Gen i = 1 := by rw [cl44Gen_sq]; simp [hi]
    have hsq2 : cl44Gen i' * cl44Gen i' = -1 := by
      rw [cl44Gen_sq]
      have : ¬ i'.val < 4 := by simp [i']
      simp [this]
    have hanti : cl44Gen i' * cl44Gen i = -(cl44Gen i * cl44Gen i') :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hii')
    rw [hsq1, hsq2, hanti]
    change (1 + cl44Bivector i i') - (-cl44Bivector i i' + -1) =
      (2 : ℝ) • (1 : Matrix Krein16Idx Krein16Idx ℝ) + (2 : ℝ) • cl44Bivector i i'
    rw [two_smul, two_smul]
    abel
  have hjd_prod : (4 : ℝ) • (uj * dj) = (2 : ℝ) • (1 : Matrix Krein16Idx Krein16Idx ℝ) +
      (2 : ℝ) • cl44Bivector j j' := by
    have h4 : (4 : ℝ) • (uj * dj) = ((2 : ℝ) • uj) * ((2 : ℝ) • dj) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
    rw [h4, huj, hdj, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
    have hsq1 : cl44Gen j * cl44Gen j = 1 := by rw [cl44Gen_sq]; simp [hj]
    have hsq2 : cl44Gen j' * cl44Gen j' = -1 := by
      rw [cl44Gen_sq]
      have : ¬ j'.val < 4 := by simp [j']
      simp [this]
    have hanti : cl44Gen j' * cl44Gen j = -(cl44Gen j * cl44Gen j') :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hjj')
    rw [hsq1, hsq2, hanti]
    change (1 + cl44Bivector j j') - (-cl44Bivector j j' + -1) =
      (2 : ℝ) • (1 : Matrix Krein16Idx Krein16Idx ℝ) + (2 : ℝ) • cl44Bivector j j'
    rw [two_smul, two_smul]
    abel
  have hdiff4 : (4 : ℝ) • (ui * di - uj * dj) =
      (2 : ℝ) • cl44Bivector i i' - (2 : ℝ) • cl44Bivector j j' := by
    rw [smul_sub, hid_prod, hjd_prod]
    abel
  have h14 : ui * di - uj * dj = (1 / 4 : ℝ) • ((4 : ℝ) • (ui * di - uj * dj)) := by
    rw [smul_smul]; norm_num
  rw [h14, hdiff4]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.smul_mem _ _ (biv_mem hii')) (Submodule.smul_mem _ _ (biv_mem hjj')))

/-- Every matrix in `g2Submodule` belongs to `cl44BivectorSpan = Cl⁽²⁾(4,4)`. -/
theorem g2Submodule_le_bivectorSpan : g2Submodule ≤ cl44BivectorSpan := by
  unfold g2Submodule
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have hl := ladder_ops_clifford_identities
  have h5 : (5 : Fin 8) = ⟨(1 : Fin 8).val + 4, by decide⟩ := by decide
  have h6 : (6 : Fin 8) = ⟨(2 : Fin 8).val + 4, by decide⟩ := by decide
  have h7 : (7 : Fin 8) = ⟨(3 : Fin 8).val + 4, by decide⟩ := by decide
  have heu1 : (2 : ℝ) • u1Op = cl44Gen 1 + (-1 : ℝ) • cl44Gen ⟨(1 : Fin 8).val + 4, by decide⟩ := by
    rw [hl.1, ← h5, neg_one_smul, sub_eq_add_neg]
  have heu2 : (2 : ℝ) • u2Op = cl44Gen 2 + (-1 : ℝ) • cl44Gen ⟨(2 : Fin 8).val + 4, by decide⟩ := by
    rw [hl.2.2.1, ← h6, neg_one_smul, sub_eq_add_neg]
  have heu3 : (2 : ℝ) • u3Op = cl44Gen 3 + (-1 : ℝ) • cl44Gen ⟨(3 : Fin 8).val + 4, by decide⟩ := by
    rw [hl.2.2.2.2.1, ← h7, neg_one_smul, sub_eq_add_neg]
  have hed1 : (2 : ℝ) • d1Op = cl44Gen 1 + (1 : ℝ) • cl44Gen ⟨(1 : Fin 8).val + 4, by decide⟩ := by
    rw [hl.2.1, ← h5, one_smul]
  have hed2 : (2 : ℝ) • d2Op = cl44Gen 2 + (1 : ℝ) • cl44Gen ⟨(2 : Fin 8).val + 4, by decide⟩ := by
    rw [hl.2.2.2.1, ← h6, one_smul]
  have hed3 : (2 : ℝ) • d3Op = cl44Gen 3 + (1 : ℝ) • cl44Gen ⟨(3 : Fin 8).val + 4, by decide⟩ := by
    rw [hl.2.2.2.2.2, ← h7, one_smul]
  fin_cases k <;> simp only [g2Basis]
  · exact ladder_prod_ud_mem (by decide) (by decide) (by decide) u1Op d3Op hl.1 hl.2.2.2.2.2
  · exact ladder_prod_ud_mem (by decide) (by decide) (by decide) u1Op d2Op hl.1 hl.2.2.2.1
  · exact ladder_prod_ud_mem (by decide) (by decide) (by decide) u2Op d3Op hl.2.2.1 hl.2.2.2.2.2
  · exact Submodule.add_mem _
      (ladder_prod_uu_mem (by decide) (by decide) (by decide) u1Op u2Op hl.1 hl.2.2.1)
      (et0_mul_op_mem (by decide) d3Op 1 hed3)
  · exact Submodule.sub_mem _
      (ladder_prod_dd_mem (by decide) (by decide) (by decide) d2Op d3Op hl.2.2.2.1 hl.2.2.2.2.2)
      (et0_mul_op_mem (by decide) u1Op (-1) heu1)
  · exact Submodule.add_mem _
      (ladder_prod_uu_mem (by decide) (by decide) (by decide) u3Op u1Op hl.2.2.2.2.1 hl.1)
      (et0_mul_op_mem (by decide) d2Op 1 hed2)
  · exact Submodule.sub_mem _
      (ladder_prod_dd_mem (by decide) (by decide) (by decide) d3Op d1Op hl.2.2.2.2.2 hl.2.1)
      (et0_mul_op_mem (by decide) u2Op (-1) heu2)
  · exact ladder_prod_ud_mem (by decide) (by decide) (by decide) u2Op d1Op hl.2.2.1 hl.2.1
  · exact ladder_prod_ud_mem (by decide) (by decide) (by decide) u3Op d2Op hl.2.2.2.2.1 hl.2.2.2.1
  · exact Submodule.add_mem _
      (ladder_prod_uu_mem (by decide) (by decide) (by decide) u2Op u3Op hl.2.2.1 hl.2.2.2.2.1)
      (et0_mul_op_mem (by decide) d1Op 1 hed1)
  · exact Submodule.sub_mem _
      (ladder_prod_dd_mem (by decide) (by decide) (by decide) d1Op d2Op hl.2.1 hl.2.2.2.1)
      (et0_mul_op_mem (by decide) u3Op (-1) heu3)
  · exact ladder_prod_ud_mem (by decide) (by decide) (by decide) u3Op d1Op hl.2.2.2.2.1 hl.2.1
  · exact g2Cartan_diff_mem (by decide) (by decide) u1Op d1Op u3Op d3Op hl.1 hl.2.1 hl.2.2.2.2.1 hl.2.2.2.2.2
  · exact g2Cartan_diff_mem (by decide) (by decide) u2Op d2Op u3Op d3Op hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2.1 hl.2.2.2.2.2

/-- Each triality-orbit coordinate is represented by its named root matrix inside the actual
Cl⁽²⁾(4,4) bivector span. This combines the orbit-basis soldering with the established Clifford
membership of the explicit G₂ basis. -/
theorem d4TrialityOrbitCoordinate_maps_into_cl44Bivectors (o : Fin 12) :
    (s3FixedToG2CarrierEquiv (d4TrialityOrbitCoordinate o)).1 ∈ cl44BivectorSpan := by
  rw [d4TrialityOrbitCoordinate_maps_to_g2RootBasis]
  exact g2Submodule_le_bivectorSpan
    (Submodule.subset_span ⟨d4OrbitToG2RootBasis o, rfl⟩)

/-- Every element of the Clifford bivector span normalizes `Cl⁽¹⁾(4,4)`, and its commutator with
each vector generator is reconstructed by the corresponding column of `rhoVec8`. -/
theorem cl44BivectorSpan_normalizes_vec1 {B : Matrix Krein16Idx Krein16Idx ℝ}
    (hB : B ∈ cl44BivectorSpan)
    (b : Fin 8) :
    B * cl44Gen b - cl44Gen b * B ∈ cl44Vec1Submodule ∧
    B * cl44Gen b - cl44Gen b * B = ∑ a : Fin 8, rhoVec8 B a b • cl44Gen a := by
  have hmem : B * cl44Gen b - cl44Gen b * B ∈ cl44Vec1Submodule := by
    refine Submodule.span_induction (hx := hB) ?_ ?_ ?_ ?_
    · rintro _ ⟨a', b', hab', rfl⟩
      exact cl44Bivector_normalizes_vec1 hab' (Submodule.subset_span ⟨b, rfl⟩)
    · rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]
      exact Submodule.zero_mem _
    · intro X Y _ _ hX hY
      have hlin : (X + Y) * cl44Gen b - cl44Gen b * (X + Y) =
          (X * cl44Gen b - cl44Gen b * X) + (Y * cl44Gen b - cl44Gen b * Y) := by
        rw [Matrix.add_mul, Matrix.mul_add]
        abel
      rw [hlin]
      exact Submodule.add_mem _ hX hY
    · intro r X _ hX
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      exact Submodule.smul_mem _ r hX
  exact ⟨hmem, cl44Vec1Submodule_coord hmem⟩

/-- If the adjoint-coordinate readout of a bivector-span element vanishes, then that operator
commutes with every Clifford vector generator. This is the kernel-to-centralizer half of the
faithfulness problem for the concrete `Cl⁽²⁾(4,4)` action. -/
theorem rhoVec8_zero_commutes_cl44Gen {B : Matrix Krein16Idx Krein16Idx ℝ}
    (hB : B ∈ cl44BivectorSpan) (hρ : rhoVec8 B = 0) (b : Fin 8) :
    B * cl44Gen b - cl44Gen b * B = 0 := by
  have hC : B * cl44Gen b - cl44Gen b * B ∈ cl44Vec1Submodule :=
    (cl44BivectorSpan_normalizes_vec1 hB b).1
  have hcoord := cl44Vec1Submodule_coord hC
  have hentry : ∀ a : Fin 8,
      ((if a.val < 4 then (1 : ℝ) else -1) / 16) *
        Matrix.trace (cl44Gen a * (B * cl44Gen b - cl44Gen b * B)) = 0 := by
    intro a
    have hab := congrFun (congrFun hρ a) b
    simpa [rhoVec8] using hab
  simp_rw [hentry] at hcoord
  simpa using hcoord

/-- Every `B ∈ g2Submodule` stabilizes `e₀ = cl44Gen 0`, so `rhoVec8 B` vanishes identically on
row `0` and column `0`, embedding `g_{2(2)}` inside the `7 × 7` block `e₀^⊥`. -/
theorem rhoVec8_zero_first_row_col {B : Matrix Krein16Idx Krein16Idx ℝ} (hB : B ∈ g2Submodule)
    (k : Fin 8) :
    rhoVec8 B 0 k = 0 ∧ rhoVec8 B k 0 = 0 := by
  have he0 := (g2Submodule_mem_stabilizer hB).2.2.1
  have hcol : rhoVec8 B k 0 = 0 := by
    simp only [rhoVec8, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, he0, sub_self,
      Matrix.trace_zero, mul_zero]
  have hskew := rhoVec8_so44_skew B
  have h0k := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 0 k) hskew
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply,
    eta44_entry] at h0k
  have hs1 : (∑ c : Fin 8, rhoVec8 B c 0 * (if c = k then (if c.val < 4 then 1 else -1) else 0)) =
      rhoVec8 B k 0 * (if k.val < 4 then 1 else -1) := by
    rw [Finset.sum_eq_single k]
    · simp only [↓reduceIte]
    · intro c _ hck; simp only [hck, ↓reduceIte, mul_zero]
    · intro hk'; exact absurd (Finset.mem_univ k) hk'
  have hs2 : (∑ c : Fin 8, (if (0 : Fin 8) = c then (if (0 : Fin 8).val < 4 then (1 : ℝ) else -1) else 0) *
      rhoVec8 B c k) = rhoVec8 B 0 k := by
    rw [Finset.sum_eq_single 0]
    · norm_num
    · intro c _ hc0; simp only [hc0.symm, ↓reduceIte, zero_mul]
    · intro h0'; exact absurd (Finset.mem_univ 0) h0'
  rw [hs1, hs2, hcol, zero_mul, zero_add] at h0k
  exact ⟨h0k, hcol⟩

/-- The adjoint-coordinate map preserves commutators for every pair of inputs in the Clifford
bivector span. -/
theorem rhoVec8_bivectorSpan_lie_hom {A B : Matrix Krein16Idx Krein16Idx ℝ}
    (hA : A ∈ cl44BivectorSpan) (hB : B ∈ cl44BivectorSpan) :
    rhoVec8 (A * B - B * A) = rhoVec8 A * rhoVec8 B - rhoVec8 B * rhoVec8 A := by
  ext a c
  have hjac : (A * B - B * A) * cl44Gen c - cl44Gen c * (A * B - B * A) =
      (A * (B * cl44Gen c - cl44Gen c * B) - (B * cl44Gen c - cl44Gen c * B) * A) -
        (B * (A * cl44Gen c - cl44Gen c * A) - (A * cl44Gen c - cl44Gen c * A) * B) := by
    noncomm_ring
  have hc_b := (cl44BivectorSpan_normalizes_vec1 hB c).2
  have hc_a := (cl44BivectorSpan_normalizes_vec1 hA c).2
  have hexp1 : A * (B * cl44Gen c - cl44Gen c * B) - (B * cl44Gen c - cl44Gen c * B) * A =
      ∑ b : Fin 8, rhoVec8 B b c • (∑ a' : Fin 8, rhoVec8 A a' b • cl44Gen a') := by
    rw [hc_b, Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, (cl44BivectorSpan_normalizes_vec1 hA b).2]
  have hexp2 : B * (A * cl44Gen c - cl44Gen c * A) - (A * cl44Gen c - cl44Gen c * A) * B =
      ∑ b : Fin 8, rhoVec8 A b c • (∑ a' : Fin 8, rhoVec8 B a' b • cl44Gen a') := by
    rw [hc_a, Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, (cl44BivectorSpan_normalizes_vec1 hB b).2]
  have hrhs_sum :
      (∑ b : Fin 8, rhoVec8 B b c • (∑ a' : Fin 8, rhoVec8 A a' b • cl44Gen a')) -
        (∑ b : Fin 8, rhoVec8 A b c • (∑ a' : Fin 8, rhoVec8 B a' b • cl44Gen a')) =
      ∑ a' : Fin 8, ((rhoVec8 A * rhoVec8 B - rhoVec8 B * rhoVec8 A) a' c) • cl44Gen a' := by
    simp_rw [Finset.smul_sum, smul_smul]
    have hcomm1 :
        (∑ b : Fin 8, ∑ a' : Fin 8, (rhoVec8 B b c * rhoVec8 A a' b) • cl44Gen a') =
          ∑ a' : Fin 8, ∑ b : Fin 8, (rhoVec8 B b c * rhoVec8 A a' b) • cl44Gen a' :=
      Finset.sum_comm
    have hcomm2 :
        (∑ b : Fin 8, ∑ a' : Fin 8, (rhoVec8 A b c * rhoVec8 B a' b) • cl44Gen a') =
          ∑ a' : Fin 8, ∑ b : Fin 8, (rhoVec8 A b c * rhoVec8 B a' b) • cl44Gen a' :=
      Finset.sum_comm
    rw [hcomm1, hcomm2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    simp_rw [← Finset.sum_smul, ← sub_smul]
    congr 1
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hact_mem : (A * B - B * A) * cl44Gen c - cl44Gen c * (A * B - B * A) ∈
      cl44Vec1Submodule := by
    rw [hjac, hexp1, hexp2]
    have hAcol : ∀ b : Fin 8,
        (∑ a' : Fin 8, rhoVec8 A a' b • cl44Gen a') ∈ cl44Vec1Submodule := by
      intro b
      apply Submodule.sum_mem
      intro a' _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a', rfl⟩)
    have hBcol : ∀ b : Fin 8,
        (∑ a' : Fin 8, rhoVec8 B a' b • cl44Gen a') ∈ cl44Vec1Submodule := by
      intro b
      apply Submodule.sum_mem
      intro a' _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a', rfl⟩)
    exact Submodule.sub_mem _
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hAcol b))
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hBcol b))
  have hc_ab : (A * B - B * A) * cl44Gen c - cl44Gen c * (A * B - B * A) =
      ∑ a' : Fin 8, rhoVec8 (A * B - B * A) a' c • cl44Gen a' :=
    cl44Vec1Submodule_coord hact_mem
  have htot : ∑ a' : Fin 8, rhoVec8 (A * B - B * A) a' c • cl44Gen a' =
      ∑ a' : Fin 8, ((rhoVec8 A * rhoVec8 B - rhoVec8 B * rhoVec8 A) a' c) • cl44Gen a' := by
    rw [← hc_ab, hjac, hexp1, hexp2, hrhs_sum]
  have hdiff0 : ∑ a' : Fin 8, (rhoVec8 (A * B - B * A) a' c -
      (rhoVec8 A * rhoVec8 B - rhoVec8 B * rhoVec8 A) a' c) • cl44Gen a' = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr htot
  have hlin := Fintype.linearIndependent_iff.mp cl44Gen_linearIndependent _ hdiff0 a
  exact sub_eq_zero.mp hlin

section Cl44BivectorLieStructure

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The matrix span of Clifford bivectors, equipped with the commutator inherited from `M₁₆(ℝ)`,
is a Lie subalgebra. -/
def cl44BivectorLieSubalgebra : LieSubalgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  { cl44BivectorSpan with
    lie_mem' := fun hA hB => cl44BivectorSpan_lie_closed hA hB }

/-- The adjoint-coordinate action of the Clifford bivector Lie algebra on `Cl⁽¹⁾(4,4)` is a
Lie homomorphism into `M₈(ℝ)`. -/
def rhoVec8BivectorLieHom :
    cl44BivectorLieSubalgebra →ₗ⁅ℝ⁆ Matrix (Fin 8) (Fin 8) ℝ where
  toLinearMap := rhoVec8.comp cl44BivectorSpan.subtype
  map_lie' := by
    intro A B
    change rhoVec8 (A.1 * B.1 - B.1 * A.1) =
      rhoVec8 A.1 * rhoVec8 B.1 - rhoVec8 B.1 * rhoVec8 A.1
    exact rhoVec8_bivectorSpan_lie_hom A.2 B.2

end Cl44BivectorLieStructure

/-- The D₄-orbit root vector keeps its Cartan weight after the actual Clifford adjoint action
is read out on `Cl⁽¹⁾(4,4)`. The source is the 16-by-16 Clifford matrix representation and the
target is its 8-by-8 vector representation; the equality uses the proved commutator homomorphism,
not a bracket defined by transport. -/
theorem d4_orbit_root_vector_weight_in_rhoVec8 (p : Fin 2 → ℝ) (o : Fin 12) :
    let k := d4OrbitToG2RootBasis o
    rhoVec8 (d4FixedCartanMatrix p) * rhoVec8 (g2Basis k) -
        rhoVec8 (g2Basis k) * rhoVec8 (d4FixedCartanMatrix p) =
      d4OrbitCartanEvaluation p o • rhoVec8 (g2Basis k) := by
  let k := d4OrbitToG2RootBasis o
  have hH1 : g2H1 ∈ g2Submodule := Submodule.subset_span ⟨12, rfl⟩
  have hH2 : g2H2 ∈ g2Submodule := Submodule.subset_span ⟨13, rfl⟩
  have hCartan : d4FixedCartanMatrix p ∈ g2Submodule := by
    unfold d4FixedCartanMatrix
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ hH1)
      (Submodule.smul_mem _ _ hH2)
  have hRoot : g2Basis k ∈ g2Submodule := Submodule.subset_span ⟨k, rfl⟩
  have hsource := d4_fixed_cartan_action_matches_g2_basis p o
  have hreadout := congrArg rhoVec8 hsource
  rw [map_smul, rhoVec8_bivectorSpan_lie_hom
    (g2Submodule_le_bivectorSpan hCartan)
    (g2Submodule_le_bivectorSpan hRoot)] at hreadout
  exact hreadout.symm

private lemma comm_add_closed {X P Q : Matrix Krein16Idx Krein16Idx ℝ}
    (hP : X * P = P * X) (hQ : X * Q = Q * X) : X * (P + Q) = (P + Q) * X := by
  rw [Matrix.mul_add, Matrix.add_mul, hP, hQ]

private lemma comm_sub_closed {X P Q : Matrix Krein16Idx Krein16Idx ℝ}
    (hP : X * P = P * X) (hQ : X * Q = Q * X) : X * (P - Q) = (P - Q) * X := by
  rw [Matrix.mul_sub, Matrix.sub_mul, hP, hQ]

private lemma comm_mul_closed {X P Q : Matrix Krein16Idx Krein16Idx ℝ}
    (hP : X * P = P * X) (hQ : X * Q = Q * X) : X * (P * Q) = (P * Q) * X := by
  rw [← Matrix.mul_assoc, hP, Matrix.mul_assoc, hQ, Matrix.mul_assoc]

private lemma comm_smul_cancel2 {Z op lhs : Matrix Krein16Idx Krein16Idx ℝ}
    (h2 : (2 : ℝ) • op = lhs) (hlhs : Z * lhs = lhs * Z) : Z * op = op * Z := by
  have h : (2 : ℝ) • (Z * op) = (2 : ℝ) • (op * Z) := by
    rw [← Matrix.mul_smul, ← Matrix.smul_mul, h2, hlhs]
  have hsub : (2 : ℝ) • (Z * op - op * Z) = 0 := by rw [smul_sub, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left (by norm_num))

/-- `rhoVec8` is injective on `g2Submodule`, hence maps `g_{2(2)}` isomorphically onto a
14-dimensional Lie subalgebra of `so(4,4) ⊂ M₈(ℝ)` supported on `e₀^⊥` (`7 × 7`). -/
theorem rhoVec8_isomorphic_image_finrank14 :
    (∀ Z ∈ g2Submodule, rhoVec8 Z = 0 → Z = 0) ∧
    Module.finrank ℝ (Submodule.map rhoVec8 g2Submodule) = 14 := by
  have hinj : ∀ Z ∈ g2Submodule, rhoVec8 Z = 0 → Z = 0 := by
    intro Z hZ hrho0
    have hgen : ∀ b : Fin 8, Z * cl44Gen b = cl44Gen b * Z := by
      intro b
      have hn := (cl44BivectorSpan_normalizes_vec1 (g2Submodule_le_bivectorSpan hZ) b).2
      rw [hrho0] at hn
      simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero] at hn
      exact sub_eq_zero.mp hn
    have hl := ladder_ops_clifford_identities
    have het0 : Z * et0Op = et0Op * Z := hgen 4
    have hu1 : Z * u1Op = u1Op * Z := comm_smul_cancel2 hl.1 (comm_sub_closed (hgen 1) (hgen 5))
    have hd1 : Z * d1Op = d1Op * Z := comm_smul_cancel2 hl.2.1 (comm_add_closed (hgen 1) (hgen 5))
    have hu2 : Z * u2Op = u2Op * Z := comm_smul_cancel2 hl.2.2.1 (comm_sub_closed (hgen 2) (hgen 6))
    have hd2 : Z * d2Op = d2Op * Z := comm_smul_cancel2 hl.2.2.2.1 (comm_add_closed (hgen 2) (hgen 6))
    have hu3 : Z * u3Op = u3Op * Z := comm_smul_cancel2 hl.2.2.2.2.1 (comm_sub_closed (hgen 3) (hgen 7))
    have hd3 : Z * d3Op = d3Op * Z := comm_smul_cancel2 hl.2.2.2.2.2 (comm_add_closed (hgen 3) (hgen 7))
    have hbas : ∀ k : Fin 14, Z * g2Basis k = g2Basis k * Z := by
      intro k
      fin_cases k <;> simp only [g2Basis]
      · exact comm_mul_closed hu1 hd3
      · exact comm_mul_closed hu1 hd2
      · exact comm_mul_closed hu2 hd3
      · exact comm_add_closed (comm_mul_closed hu1 hu2) (comm_mul_closed het0 hd3)
      · exact comm_sub_closed (comm_mul_closed hd2 hd3) (comm_mul_closed het0 hu1)
      · exact comm_add_closed (comm_mul_closed hu3 hu1) (comm_mul_closed het0 hd2)
      · exact comm_sub_closed (comm_mul_closed hd3 hd1) (comm_mul_closed het0 hu2)
      · exact comm_mul_closed hu2 hd1
      · exact comm_mul_closed hu3 hd2
      · exact comm_add_closed (comm_mul_closed hu2 hu3) (comm_mul_closed het0 hd1)
      · exact comm_sub_closed (comm_mul_closed hd1 hd2) (comm_mul_closed het0 hu3)
      · exact comm_mul_closed hu3 hd1
      · exact comm_sub_closed (comm_mul_closed hu1 hd1) (comm_mul_closed hu3 hd3)
      · exact comm_sub_closed (comm_mul_closed hu2 hd2) (comm_mul_closed hu3 hd3)
    have hcent : ∀ W ∈ g2Submodule, W * Z - Z * W = 0 := by
      intro W hW
      refine Submodule.span_induction (hx := hW) ?_ ?_ ?_ ?_
      · rintro _ ⟨k, rfl⟩
        rw [← hbas k, sub_self]
      · rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]
      · intro X Y _ _ hX hY
        rw [Matrix.add_mul, Matrix.mul_add]
        calc (X * Z + Y * Z) - (Z * X + Z * Y)
            = (X * Z - Z * X) + (Y * Z - Z * Y) := by abel
          _ = 0 := by rw [hX, hY, add_zero]
      · intro r X _ hX
        rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, hX, smul_zero]
    exact g2Submodule_center_trivial hZ hcent
  let f : g2Submodule →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := rhoVec8.comp g2Submodule.subtype
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨Z, hZ⟩ hker
    apply Subtype.ext
    exact hinj Z hZ hker
  have hrange : LinearMap.range f = Submodule.map rhoVec8 g2Submodule := by
    change LinearMap.range (rhoVec8.comp g2Submodule.subtype) = Submodule.map rhoVec8 g2Submodule
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hdim : Module.finrank ℝ (Submodule.map rhoVec8 g2Submodule) = 14 := by
    rw [← hrange]
    have heq := (LinearEquiv.ofInjective f hfinj).finrank_eq
    rw [← heq, finrank_g2Submodule_and_owner_bridge.1]
  exact ⟨hinj, hdim⟩

/-- Each of the twelve orbit root directions has a nonzero image in the 8D vector
representation. Thus the preceding weight equation identifies genuine root vectors, not only
formal eigen-equations that could hold on the zero matrix. -/
theorem d4_orbit_root_vector_rhoVec8_ne_zero (o : Fin 12) :
    rhoVec8 (g2Basis (d4OrbitToG2RootBasis o)) ≠ 0 := by
  intro hzero
  have hBmem : g2Basis (d4OrbitToG2RootBasis o) ∈ g2Submodule :=
    Submodule.subset_span ⟨d4OrbitToG2RootBasis o, rfl⟩
  have hBzero := rhoVec8_isomorphic_image_finrank14.1 _ hBmem hzero
  have hpivot := congrArg
    (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (g2Pivot (d4OrbitToG2RootBasis o)).1
      (g2Pivot (d4OrbitToG2RootBasis o)).2) hBzero
  have hval : g2PivotVal (d4OrbitToG2RootBasis o) = 0 := by
    simpa [g2Basis_eval_pivot] using hpivot
  exact g2PivotVal_ne_zero _ hval

/-! ### Constructive Matrix Lie Group `SplitG2MatrixGroup ≤ GL₁₆(ℝ)`, `NormedSpace.exp` Integration & Tangent Recovery -/

section MatrixEntryDerivHelper

private def matEntryLinear {n : Type*} (i j : n) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma ring_hasDerivAt_clm_exp {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (φ : 𝔸 →L[ℝ] ℝ) (X : 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (NormedSpace.exp (s • X)))
      (φ (NormedSpace.exp (t • X) * X)) t :=
  φ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)

private lemma ring_hasDerivAt_clm_exp' {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (φ : 𝔸 →L[ℝ] ℝ) (X : 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (NormedSpace.exp (s • X)))
      (φ (X * NormedSpace.exp (t • X))) t :=
  φ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t)

private lemma hasDerivAt_exp_smul_entry {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (t : ℝ) (i j : n) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) i j)
      ((NormedSpace.exp (t • X) * X) i j) t := by
  open scoped Matrix.Norms.Operator in
  exact @ring_hasDerivAt_clm_exp (Matrix n n ℝ) _ _
    (NormedAlgebra.restrictScalars ℚ ℝ (Matrix n n ℝ)) _
    (LinearMap.toContinuousLinearMap (matEntryLinear i j)) X t

private lemma hasDerivAt_exp_smul_entry' {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (t : ℝ) (i j : n) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) i j)
      ((X * NormedSpace.exp (t • X)) i j) t := by
  open scoped Matrix.Norms.Operator in
  exact @ring_hasDerivAt_clm_exp' (Matrix n n ℝ) _ _
    (NormedAlgebra.restrictScalars ℚ ℝ (Matrix n n ℝ)) _
    (LinearMap.toContinuousLinearMap (matEntryLinear i j)) X t

end MatrixEntryDerivHelper

section SplitG2LieGroup

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Explicit `14`-dimensional split `g_{2(2)}` Lie subalgebra inside `M₁₆(ℝ)` with the associative
commutator bracket `⁅A, B⁆ = A * B - B * A`. -/
def g2LieSubalgebra : LieSubalgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  { g2Submodule with
    lie_mem' := fun hA hB => g2Submodule_lie_closed hA hB }

/-- The concrete matrix G₂ subalgebra embeds into the ambient Clifford bivector Lie algebra by
the actual inclusion of its matrices into `cl44BivectorSpan`. -/
def g2IntoCl44BivectorLieHom :
    g2LieSubalgebra →ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra where
  toFun x := ⟨x.1, g2Submodule_le_bivectorSpan x.2⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl

/-- Injectivity of the G₂-to-Clifford-bivector Lie morphism is inherited from subtype
inclusion, so the formalized 14-dimensional Lie algebra is a genuine Lie subalgebra of the
Cl⁽²⁾(4,4) carrier. -/
theorem g2IntoCl44BivectorLieHom_injective :
    Function.Injective g2IntoCl44BivectorLieHom := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : cl44BivectorLieSubalgebra =>
    (z : Matrix Krein16Idx Krein16Idx ℝ)) h

/-- Lie equivalence from the triality-fixed coordinate carrier, equipped with its soldered
commutator, to the concrete matrix `g₂` Lie subalgebra. The source bracket is transported along
the already-proved carrier equivalence, and `map_lie'` records that compatibility explicitly. -/
noncomputable def s3FixedToG2LieEquiv :
    s3FixedSpin44Submodule ≃ₗ⁅ℝ⁆ g2LieSubalgebra := by
  let f : s3FixedSpin44Submodule →ₗ⁅ℝ⁆ g2LieSubalgebra :=
    { toFun := fun x => ⟨(s3FixedToG2CarrierEquiv x).1,
        (s3FixedToG2CarrierEquiv x).2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact congrArg Subtype.val (s3FixedToG2CarrierEquiv.map_add x y)
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact congrArg Subtype.val (s3FixedToG2CarrierEquiv.map_smul r x)
      map_lie' := by
        intro x y
        apply Subtype.ext
        exact congrArg Subtype.val (s3FixedToG2CarrierEquiv_solderedBracket x y) }
  apply LieEquiv.ofBijective f
  constructor
  · intro x y h
    apply s3FixedToG2CarrierEquiv.injective
    apply Subtype.ext
    exact congrArg Subtype.val h
  · intro z
    let z' : g2Submodule := ⟨z.1, z.2⟩
    rcases s3FixedToG2CarrierEquiv.surjective z' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hx

/-- Composite Lie morphism from the triality-fixed coordinate carrier into the actual Cl⁽²⁾(4,4)
bivector Lie algebra. Its source bracket is the soldered one documented above; its target and
image are the concrete Clifford matrix carrier. -/
noncomputable def s3FixedToCl44BivectorLieHom :
    s3FixedSpin44Submodule →ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra :=
  g2IntoCl44BivectorLieHom.comp s3FixedToG2LieEquiv.toLieHom

/-- The composite soldering is injective, hence realizes the 14-dimensional source inside the
actual Clifford bivector Lie algebra. -/
theorem s3FixedToCl44BivectorLieHom_injective :
    Function.Injective s3FixedToCl44BivectorLieHom := by
  intro x y h
  apply s3FixedToG2LieEquiv.injective
  exact g2IntoCl44BivectorLieHom_injective h

/-- The image of the triality-fixed soldering is exactly the concrete G₂ image inside the
Clifford bivector Lie algebra. Thus the soldering neither loses nor adds operator directions:
its 14-dimensional image is the embedded matrix `g₂` subalgebra. -/
theorem s3FixedToCl44BivectorLieHom_range_eq_g2_range :
    LinearMap.range s3FixedToCl44BivectorLieHom.toLinearMap =
      LinearMap.range g2IntoCl44BivectorLieHom.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨s3FixedToG2LieEquiv x, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := s3FixedToG2LieEquiv.surjective z
    refine ⟨x, ?_⟩
    exact congrArg g2IntoCl44BivectorLieHom hx

/-- `Module.finrank ℝ g2LieSubalgebra = 14`. -/
theorem finrank_g2LieSubalgebra : Module.finrank ℝ g2LieSubalgebra = 14 :=
  finrank_g2Submodule_and_owner_bridge.1

/-- The actual Clifford-operator image of the soldering has dimension `14`, computed from its
exact range identification with the concrete split-`g₂` subalgebra. -/
theorem s3FixedToCl44BivectorLieHom_range_finrank :
    Module.finrank ℝ (LinearMap.range s3FixedToCl44BivectorLieHom.toLinearMap) = 14 := by
  rw [s3FixedToCl44BivectorLieHom_range_eq_g2_range,
    LinearMap.finrank_range_of_inj g2IntoCl44BivectorLieHom_injective,
    finrank_g2LieSubalgebra]

/-- Faithful Lie-algebra embedding `g_{2(2)} ↪ M₈(ℝ)` (`⊂ so(4,4)` supported on `e₀^⊥`). -/
def g2RhoVec8LieHom : g2LieSubalgebra →ₗ⁅ℝ⁆ Matrix (Fin 8) (Fin 8) ℝ where
  toLinearMap := rhoVec8.comp g2Submodule.subtype
  map_lie' {x y} := by
    change rhoVec8 (x.1 * y.1 - y.1 * x.1) = rhoVec8 x.1 * rhoVec8 y.1 - rhoVec8 y.1 * rhoVec8 x.1
    exact rhoVec8_bivectorSpan_lie_hom
      (g2Submodule_le_bivectorSpan x.2) (g2Submodule_le_bivectorSpan y.2)

/-- Injectivity of `g2RhoVec8LieHom`. -/
theorem g2RhoVec8LieHom_injective : Function.Injective g2RhoVec8LieHom := by
  intro x y hxy
  apply Subtype.ext
  have hzero : rhoVec8 (x.1 - y.1) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (rhoVec8_isomorphic_image_finrank14.1 (x.1 - y.1)
    (Submodule.sub_mem _ x.2 y.2) hzero)

/-- **Split Exceptional Matrix Lie Group `G_{2(2)} ≤ GL₁₆(ℝ)`**: invertible real spinor matrices
preserving `kreinMetric88`, commuting with chiral grading `gamma44` and base vector `e₀`, fixing the
extremal Majorana–Weyl spinor `majoranaRefSpinor`, and normalizing `Cl⁽¹⁾(4,4)` by conjugation. -/
def SplitG2MatrixGroup : Subgroup (Matrix.GeneralLinearGroup Krein16Idx ℝ) where
  carrier :=
    { u |
      (u.val)ᵀ * kreinMetric88 * u.val = kreinMetric88 ∧
      u.val * gamma44 = gamma44 * u.val ∧
      u.val * cl44Gen 0 = cl44Gen 0 * u.val ∧
      u.val.mulVec majoranaRefSpinor = majoranaRefSpinor ∧
      ∀ v ∈ cl44Vec1Submodule, u.val * v * (u⁻¹).val ∈ cl44Vec1Submodule }
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc ((a * b).val)ᵀ * kreinMetric88 * (a * b).val
          = (b.val)ᵀ * ((a.val)ᵀ * kreinMetric88 * a.val) * b.val := by
              rw [Units.val_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = (b.val)ᵀ * kreinMetric88 * b.val := by rw [ha.1]
        _ = kreinMetric88 := hb.1
    · calc (a * b).val * gamma44
          = a.val * (b.val * gamma44) := by rw [Units.val_mul, Matrix.mul_assoc]
        _ = a.val * (gamma44 * b.val) := by rw [hb.2.1]
        _ = (a.val * gamma44) * b.val := by simp only [Matrix.mul_assoc]
        _ = gamma44 * (a * b).val := by rw [ha.2.1, Units.val_mul, Matrix.mul_assoc]
    · calc (a * b).val * cl44Gen 0
          = a.val * (b.val * cl44Gen 0) := by rw [Units.val_mul, Matrix.mul_assoc]
        _ = a.val * (cl44Gen 0 * b.val) := by rw [hb.2.2.1]
        _ = (a.val * cl44Gen 0) * b.val := by simp only [Matrix.mul_assoc]
        _ = cl44Gen 0 * (a * b).val := by rw [ha.2.2.1, Units.val_mul, Matrix.mul_assoc]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb.2.2.2.1, ha.2.2.2.1]
    · intro v hv
      have hbin := hb.2.2.2.2 v hv
      have hain := ha.2.2.2.2 (b.val * v * (b⁻¹).val) hbin
      have hinv : ((a * b)⁻¹).val = (b⁻¹).val * (a⁻¹).val := by
        rw [_root_.mul_inv_rev, Units.val_mul]
      rw [Units.val_mul, hinv]
      simpa only [Matrix.mul_assoc] using hain
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    · simp only [Units.val_one, Matrix.one_mul, Matrix.mul_one]
    · simp only [Units.val_one, Matrix.one_mul, Matrix.mul_one]
    · simp only [Units.val_one, Matrix.one_mulVec]
    · intro v hv
      simpa only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] using hv
  inv_mem' {u} hu := by
    have huL : (u⁻¹).val * u.val = 1 := Units.inv_mul u
    have huR : u.val * (u⁻¹).val = 1 := Units.mul_inv u
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc ((u⁻¹).val)ᵀ * kreinMetric88 * (u⁻¹).val
          = ((u⁻¹).val)ᵀ * ((u.val)ᵀ * kreinMetric88 * u.val) * (u⁻¹).val := by rw [hu.1]
        _ = (((u⁻¹).val)ᵀ * (u.val)ᵀ) * kreinMetric88 * (u.val * (u⁻¹).val) := by
              simp only [Matrix.mul_assoc]
        _ = (u.val * (u⁻¹).val)ᵀ * kreinMetric88 * (u.val * (u⁻¹).val) := by
              rw [← Matrix.transpose_mul]
        _ = kreinMetric88 := by rw [huR, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    · calc (u⁻¹).val * gamma44
          = (u⁻¹).val * gamma44 * (u.val * (u⁻¹).val) := by rw [huR, Matrix.mul_one]
        _ = (u⁻¹).val * (gamma44 * u.val) * (u⁻¹).val := by simp only [Matrix.mul_assoc]
        _ = ((u⁻¹).val * u.val) * gamma44 * (u⁻¹).val := by
              rw [← hu.2.1]; simp only [Matrix.mul_assoc]
        _ = gamma44 * (u⁻¹).val := by rw [huL, Matrix.one_mul]
    · calc (u⁻¹).val * cl44Gen 0
          = (u⁻¹).val * cl44Gen 0 * (u.val * (u⁻¹).val) := by rw [huR, Matrix.mul_one]
        _ = (u⁻¹).val * (cl44Gen 0 * u.val) * (u⁻¹).val := by simp only [Matrix.mul_assoc]
        _ = ((u⁻¹).val * u.val) * cl44Gen 0 * (u⁻¹).val := by
              rw [← hu.2.2.1]; simp only [Matrix.mul_assoc]
        _ = cl44Gen 0 * (u⁻¹).val := by rw [huL, Matrix.one_mul]
    · calc (u⁻¹).val.mulVec majoranaRefSpinor
          = (u⁻¹).val.mulVec (u.val.mulVec majoranaRefSpinor) := by rw [hu.2.2.2.1]
        _ = ((u⁻¹).val * u.val).mulVec majoranaRefSpinor := Matrix.mulVec_mulVec _ _ _
        _ = majoranaRefSpinor := by rw [huL, Matrix.one_mulVec]
    · intro v hv
      have hu5 := hu.2.2.2.2
      let conjU : cl44Vec1Submodule →ₗ[ℝ] cl44Vec1Submodule :=
        { toFun := fun x => ⟨u.val * x.1 * (u⁻¹).val, hu5 x.1 x.2⟩
          map_add' := fun x y => by
            apply Subtype.ext
            simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
          map_smul' := fun r x => by
            apply Subtype.ext
            simp only [Submodule.coe_smul_of_tower, RingHom.id_apply, Matrix.mul_smul,
              Matrix.smul_mul] }
      have hconj_inj : Function.Injective conjU := by
        intro x y hxy
        apply Subtype.ext
        have heq := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => (u⁻¹).val * M * u.val)
          (congrArg Subtype.val hxy)
        dsimp [conjU] at heq
        have hrec : ∀ w : Matrix Krein16Idx Krein16Idx ℝ,
            (u⁻¹).val * (u.val * w * (u⁻¹).val) * u.val = w := fun w => by
          calc (u⁻¹).val * (u.val * w * (u⁻¹).val) * u.val
              = ((u⁻¹).val * u.val) * w * ((u⁻¹).val * u.val) := by
                  simp only [Matrix.mul_assoc]
            _ = w := by rw [huL, Matrix.one_mul, Matrix.mul_one]
        simpa only [hrec] using heq
      obtain ⟨w, hw⟩ := LinearMap.surjective_of_injective hconj_inj ⟨v, hv⟩
      have hw_val : u.val * w.1 * (u⁻¹).val = v := congrArg Subtype.val hw
      have hres : (u⁻¹).val * v * ((u⁻¹)⁻¹).val = w.1 := by
        rw [inv_inv, ← hw_val]
        calc (u⁻¹).val * (u.val * w.1 * (u⁻¹).val) * u.val
            = ((u⁻¹).val * u.val) * w.1 * ((u⁻¹).val * u.val) := by
                simp only [Matrix.mul_assoc]
          _ = w.1 := by rw [huL, Matrix.one_mul, Matrix.mul_one]
      rw [hres]
      exact w.2

/-- One-parameter matrix exponential subgroup `exp(t • X) ∈ GL₁₆(ℝ)`. -/
def expMat16GL (X : Matrix Krein16Idx Krein16Idx ℝ) (t : ℝ) :
    Matrix.GeneralLinearGroup Krein16Idx ℝ where
  val := NormedSpace.exp (t • X)
  inv := NormedSpace.exp ((-t) • X)
  val_inv := by
    have hcomm : Commute (t • X) ((-t) • X) := ((Commute.refl X).smul_left t).smul_right (-t)
    rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul, add_neg_cancel, zero_smul,
      NormedSpace.exp_zero]
  inv_val := by
    have hcomm : Commute ((-t) • X) (t • X) := ((Commute.refl X).smul_left (-t)).smul_right t
    rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul, neg_add_cancel, zero_smul,
      NormedSpace.exp_zero]

/-- One-parameter group laws for `expMat16GL`: identity at `0` and multiplicativity `exp((s+t)X) = exp(sX)exp(tX)`. -/
theorem expMat16GL_one_parameter_laws (X : Matrix Krein16Idx Krein16Idx ℝ) (s t : ℝ) :
    expMat16GL X 0 = 1 ∧ expMat16GL X (s + t) = expMat16GL X s * expMat16GL X t := by
  refine ⟨?_, ?_⟩
  · apply Units.ext
    simp only [expMat16GL, zero_smul, NormedSpace.exp_zero, Units.val_one]
  · apply Units.ext
    have hcomm : Commute (s • X) (t • X) := ((Commute.refl X).smul_left s).smul_right t
    simp only [expMat16GL, Units.val_mul, add_smul]
    exact Matrix.exp_add_of_commute (s • X) (t • X) hcomm

private def gamma44Unit : (Matrix Krein16Idx Krein16Idx ℝ)ˣ where
  val := gamma44
  inv := gamma44
  val_inv := gamma44_properties.2.1
  inv_val := gamma44_properties.2.1

private def cl44Gen0Unit : (Matrix Krein16Idx Krein16Idx ℝ)ˣ where
  val := cl44Gen 0
  inv := cl44Gen 0
  val_inv := by rw [cl44Gen_sq 0]; norm_num
  inv_val := by rw [cl44Gen_sq 0]; norm_num

private def kreinMetric88Unit : (Matrix Krein16Idx Krein16Idx ℝ)ˣ where
  val := kreinMetric88
  inv := kreinMetric88
  val_inv := kreinMetric88_properties.2.2.1
  inv_val := kreinMetric88_properties.2.2.1

private lemma exp_comm_of_comm {X A : Matrix Krein16Idx Krein16Idx ℝ}
    (U : (Matrix Krein16Idx Krein16Idx ℝ)ˣ) (hU : U.val = A) (hUinv : (U⁻¹).val = A)
    (hcomm : X * A = A * X) (hsq : A * A = 1) (t : ℝ) :
    NormedSpace.exp (t • X) * A = A * NormedSpace.exp (t • X) := by
  have hconj : U.val * (t • X) * (U⁻¹).val = t • X := by
    rw [hU, hUinv, Matrix.mul_smul, Matrix.smul_mul, ← hcomm, Matrix.mul_assoc, hsq, Matrix.mul_one]
  have hexp := Matrix.exp_units_conj U (t • X)
  change NormedSpace.exp (U.val * (t • X) * (U⁻¹).val) =
    U.val * NormedSpace.exp (t • X) * (U⁻¹).val at hexp
  rw [hconj, hU, hUinv] at hexp
  calc NormedSpace.exp (t • X) * A
      = (A * NormedSpace.exp (t • X) * A) * A := by rw [← hexp]
    _ = A * NormedSpace.exp (t • X) * (A * A) := Matrix.mul_assoc _ _ _
    _ = A * NormedSpace.exp (t • X) := by rw [hsq, Matrix.mul_one]

private lemma exp_preserves_kreinMetric {X : Matrix Krein16Idx Krein16Idx ℝ}
    (hk : Xᵀ * kreinMetric88 + kreinMetric88 * X = 0) (t : ℝ) :
    (NormedSpace.exp (t • X))ᵀ * kreinMetric88 * NormedSpace.exp (t • X) = kreinMetric88 := by
  have hk_neg : Xᵀ * kreinMetric88 = kreinMetric88 * (-X) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left hk
  have hk_conj : Xᵀ = kreinMetric88 * (-X) * kreinMetric88 := by
    calc Xᵀ = (Xᵀ * kreinMetric88) * kreinMetric88 := by
          rw [Matrix.mul_assoc, kreinMetric88_properties.2.2.1, Matrix.mul_one]
      _ = (kreinMetric88 * (-X)) * kreinMetric88 := by rw [hk_neg]
  have htr_conj : (t • X)ᵀ =
      kreinMetric88Unit.val * ((-t) • X) * (kreinMetric88Unit⁻¹).val := by
    change (t • X)ᵀ = kreinMetric88 * ((-t) • X) * kreinMetric88
    calc (t • X)ᵀ = t • Xᵀ := Matrix.transpose_smul t X
      _ = t • (kreinMetric88 * (-X) * kreinMetric88) := by rw [hk_conj]
      _ = -(t • (kreinMetric88 * X * kreinMetric88)) := by
          rw [Matrix.mul_neg, Matrix.neg_mul, smul_neg]
      _ = kreinMetric88 * ((-t) • X) * kreinMetric88 := by
          rw [Matrix.mul_smul, Matrix.smul_mul, neg_smul]
  have hexp_tr : (NormedSpace.exp (t • X))ᵀ =
      kreinMetric88 * NormedSpace.exp ((-t) • X) * kreinMetric88 := by
    rw [← Matrix.exp_transpose, htr_conj]
    exact Matrix.exp_units_conj kreinMetric88Unit ((-t) • X)
  have hcomm : Commute ((-t) • X) (t • X) := ((Commute.refl X).smul_left (-t)).smul_right t
  have hcancel : NormedSpace.exp ((-t) • X) * NormedSpace.exp (t • X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul, neg_add_cancel, zero_smul,
      NormedSpace.exp_zero]
  calc (NormedSpace.exp (t • X))ᵀ * kreinMetric88 * NormedSpace.exp (t • X)
      = (kreinMetric88 * NormedSpace.exp ((-t) • X) * kreinMetric88) * kreinMetric88 *
          NormedSpace.exp (t • X) := by rw [hexp_tr]
    _ = kreinMetric88 * NormedSpace.exp ((-t) • X) * (kreinMetric88 * kreinMetric88) *
          NormedSpace.exp (t • X) := by simp only [Matrix.mul_assoc]
    _ = kreinMetric88 * (NormedSpace.exp ((-t) • X) * NormedSpace.exp (t • X)) := by
          rw [kreinMetric88_properties.2.2.1, Matrix.mul_one, Matrix.mul_assoc]
    _ = kreinMetric88 := by rw [hcancel, Matrix.mul_one]

private lemma matrix_hasDerivAt_mul {l m n : Type*} [Fintype m]
    {A : ℝ → Matrix l m ℝ} {dA : Matrix l m ℝ}
    {B : ℝ → Matrix m n ℝ} {dB : Matrix m n ℝ} {t : ℝ}
    (hA : ∀ i k, HasDerivAt (fun s => A s i k) (dA i k) t)
    (hB : ∀ k j, HasDerivAt (fun s => B s k j) (dB k j) t)
    (i : l) (j : n) :
    HasDerivAt (fun s => (A s * B s) i j) ((dA * B t + A t * dB) i j) t := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).mul (hB k j)

private lemma matrix_hasDerivAt_mul_const {l m n : Type*} [Fintype m]
    {A : ℝ → Matrix l m ℝ} {dA : Matrix l m ℝ} (C : Matrix m n ℝ) {t : ℝ}
    (hA : ∀ i k, HasDerivAt (fun s => A s i k) (dA i k) t)
    (i : l) (j : n) :
    HasDerivAt (fun s => (A s * C) i j) ((dA * C) i j) t := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).mul_const (C k j)

private lemma matrix_hasDerivAt_const_mul {l m n : Type*} [Fintype m]
    (C : Matrix l m ℝ) {B : ℝ → Matrix m n ℝ} {dB : Matrix m n ℝ} {t : ℝ}
    (hB : ∀ k j, HasDerivAt (fun s => B s k j) (dB k j) t)
    (i : l) (j : n) :
    HasDerivAt (fun s => (C * B s) i j) ((C * dB) i j) t := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hB k j).const_mul (C i k)

private lemma exp_fixes_majoranaRefSpinor {X : Matrix Krein16Idx Krein16Idx ℝ}
    (hX : X.mulVec majoranaRefSpinor = 0) (t : ℝ) :
    (NormedSpace.exp (t • X)).mulVec majoranaRefSpinor = majoranaRefSpinor := by
  ext i
  let f : ℝ → ℝ := fun s => ((NormedSpace.exp (s • X)).mulVec majoranaRefSpinor) i
  have hf_diff : ∀ s : ℝ, HasDerivAt f 0 s := fun s => by
    have hmul : HasDerivAt
        (fun τ : ℝ => ∑ j : Krein16Idx, NormedSpace.exp (τ • X) i j * majoranaRefSpinor j)
        (∑ j : Krein16Idx, ((NormedSpace.exp (s • X) * X) i j) * majoranaRefSpinor j) s :=
      HasDerivAt.fun_sum fun j _ =>
        (hasDerivAt_exp_smul_entry X s i j).mul_const (majoranaRefSpinor j)
    refine hmul.congr_deriv ?_
    change ((NormedSpace.exp (s • X) * X).mulVec majoranaRefSpinor) i = 0
    rw [← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero, Pi.zero_apply]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hf_diff s).differentiableAt)
    (fun s => (hf_diff s).deriv) t 0
  dsimp [f] at hconst
  simpa only [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec] using hconst

/-- **Global Clifford-to-`SO(4,4)` Adjoint Exponential Intertwining**: for every `Z ∈ g_{2(2)}`
and every `t : ℝ`, `Ad(exp(t Z))` acts on `Cl⁽¹⁾(4,4)` as the matrix exponential `exp(t · rhoVec8 Z) ∈ SO(4,4)`. -/
theorem expMat16GL_cl44_intertwining {Z : Matrix Krein16Idx Krein16Idx ℝ} (hZ : Z ∈ g2Submodule)
    (t : ℝ) (b : Fin 8) :
    NormedSpace.exp (t • Z) * cl44Gen b * NormedSpace.exp ((-t) • Z) =
      ∑ a : Fin 8, (NormedSpace.exp (t • rhoVec8 Z) a b) • cl44Gen a := by
  let E₁ : ℝ → Matrix Krein16Idx Krein16Idx ℝ := fun s => NormedSpace.exp (s • (-Z))
  let V : ℝ → Matrix Krein16Idx Krein16Idx ℝ := fun s =>
    ∑ a : Fin 8, (NormedSpace.exp (s • rhoVec8 Z) a b) • cl44Gen a
  let E₂ : ℝ → Matrix Krein16Idx Krein16Idx ℝ := fun s => NormedSpace.exp (s • Z)
  let F : ℝ → Matrix Krein16Idx Krein16Idx ℝ := fun s => (E₁ s * V s) * E₂ s
  have hE₁_diff : ∀ s i k,
      HasDerivAt (fun τ => E₁ τ i k) ((-(NormedSpace.exp (s • (-Z)) * Z)) i k) s := by
    intro s i k
    simpa only [E₁, Matrix.mul_neg] using hasDerivAt_exp_smul_entry (-Z) s i k
  have hE₂_diff : ∀ s k j,
      HasDerivAt (fun τ => E₂ τ k j) ((Z * NormedSpace.exp (s • Z)) k j) s :=
    fun s k j => hasDerivAt_exp_smul_entry' Z s k j
  have hV_diff : ∀ s i k,
      HasDerivAt (fun τ => V τ i k) ((Z * V s - V s * Z) i k) s := by
    intro s i k
    have hsum : HasDerivAt
        (fun τ : ℝ => ∑ a : Fin 8, NormedSpace.exp (τ • rhoVec8 Z) a b * cl44Gen a i k)
        (∑ a : Fin 8, ((rhoVec8 Z * NormedSpace.exp (s • rhoVec8 Z)) a b) * cl44Gen a i k) s :=
      HasDerivAt.fun_sum fun a _ =>
        (hasDerivAt_exp_smul_entry' (rhoVec8 Z) s a b).mul_const (cl44Gen a i k)
    refine hsum.congr_deriv ?_
    have hcomm_V : Z * V s - V s * Z =
        ∑ c : Fin 8, NormedSpace.exp (s • rhoVec8 Z) c b •
          (∑ a : Fin 8, rhoVec8 Z a c • cl44Gen a) := by
      dsimp [V]
      rw [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
        (cl44BivectorSpan_normalizes_vec1 (g2Submodule_le_bivectorSpan hZ) c).2]
    have hpt := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M i k) hcomm_V
    rw [hpt]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by
      rw [mul_assoc, mul_left_comm]
  have hF_diff : ∀ s p q, HasDerivAt (fun τ => F τ p q) 0 s := by
    intro s p q
    have hEV := matrix_hasDerivAt_mul (fun i k => hE₁_diff s i k) (fun k j => hV_diff s k j)
    have hF_raw := matrix_hasDerivAt_mul (fun i k => hEV i k) (fun k j => hE₂_diff s k j) p q
    refine hF_raw.congr_deriv ?_
    have hcancel :
        (((-(E₁ s * Z)) * V s + E₁ s * (Z * V s - V s * Z)) * E₂ s +
          (E₁ s * V s) * (Z * E₂ s)) = 0 := by
      noncomm_ring
    exact congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M p q) hcancel
  have hF_const : F t = F 0 := by
    ext p q
    exact is_const_of_deriv_eq_zero (fun s => (hF_diff s p q).differentiableAt)
      (fun s => (hF_diff s p q).deriv) t 0
  have hF0 : F 0 = cl44Gen b := by
    have hV0 : V 0 = cl44Gen b := by
      dsimp [V]
      simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_apply]
      rw [Finset.sum_eq_single b]
      · simp only [↓reduceIte, one_smul]
      · intro a _ hab; simp only [hab, ↓reduceIte, zero_smul]
      · intro hb; exact absurd (Finset.mem_univ b) hb
    dsimp [F, E₁, E₂]
    simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one, hV0]
  have hFt : E₁ t * V t * E₂ t = cl44Gen b := hF_const.trans hF0
  have hE₁_eq : E₁ t = NormedSpace.exp ((-t) • Z) := by
    dsimp [E₁]; rw [smul_neg, ← neg_smul]
  have hL : E₂ t * E₁ t = 1 := by
    dsimp [E₂]; rw [hE₁_eq]; exact (expMat16GL Z t).val_inv
  rw [← hE₁_eq]
  calc NormedSpace.exp (t • Z) * cl44Gen b * E₁ t
      = E₂ t * (E₁ t * V t * E₂ t) * E₁ t := by rw [hFt]
    _ = (E₂ t * E₁ t) * V t * (E₂ t * E₁ t) := by simp only [Matrix.mul_assoc]
    _ = V t := by rw [hL, Matrix.one_mul, Matrix.mul_one]

/-- Every generator `Z ∈ g_{2(2)}` integrates via `NormedSpace.exp` into `SplitG2MatrixGroup ≤ GL₁₆(ℝ)`. -/
theorem expMat16GL_mem_splitG2MatrixGroup {Z : Matrix Krein16Idx Krein16Idx ℝ} (hZ : Z ∈ g2Submodule)
    (t : ℝ) : expMat16GL Z t ∈ SplitG2MatrixGroup := by
  have hstab := g2Submodule_mem_stabilizer hZ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact exp_preserves_kreinMetric hstab.1 t
  · exact exp_comm_of_comm gamma44Unit rfl rfl hstab.2.1 gamma44_properties.2.1 t
  · exact exp_comm_of_comm cl44Gen0Unit rfl rfl hstab.2.2.1 cl44Gen0Unit.val_inv t
  · exact exp_fixes_majoranaRefSpinor hstab.2.2.2 t
  · intro v hv
    refine Submodule.span_induction (hx := hv) ?_ ?_ ?_ ?_
    · rintro _ ⟨b, rfl⟩
      change NormedSpace.exp (t • Z) * cl44Gen b * NormedSpace.exp ((-t) • Z) ∈ cl44Vec1Submodule
      rw [expMat16GL_cl44_intertwining hZ t b]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · rw [Matrix.mul_zero, Matrix.zero_mul]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      change (expMat16GL Z t).val * (x + y) * ((expMat16GL Z t)⁻¹).val ∈ cl44Vec1Submodule
      rw [Matrix.mul_add, Matrix.add_mul]
      exact Submodule.add_mem _ hx hy
    · intro r x _ hx
      change (expMat16GL Z t).val * (r • x) * ((expMat16GL Z t)⁻¹).val ∈ cl44Vec1Submodule
      rw [Matrix.mul_smul, Matrix.smul_mul]
      exact Submodule.smul_mem _ r hx

/-- Orthogonal Hilbert–Schmidt trace projection onto `Cl⁽¹⁾(4,4) = span{γ₀,…,γ₇}`. -/
def projVec1 (M : Matrix Krein16Idx Krein16Idx ℝ) : Matrix Krein16Idx Krein16Idx ℝ :=
  ∑ a : Fin 8, (((if a.val < 4 then (1 : ℝ) else -1) / 16) *
    Matrix.trace (cl44Gen a * M)) • cl44Gen a

private lemma projVec1_mem (M : Matrix Krein16Idx Krein16Idx ℝ) :
    projVec1 M ∈ cl44Vec1Submodule :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

private lemma hasDerivAt_projVec1 {C : ℝ → Matrix Krein16Idx Krein16Idx ℝ}
    {dC : Matrix Krein16Idx Krein16Idx ℝ} {t₀ : ℝ}
    (hC : ∀ p q, HasDerivAt (fun s => C s p q) (dC p q) t₀)
    (p q : Krein16Idx) :
    HasDerivAt (fun s => projVec1 (C s) p q) (projVec1 dC p q) t₀ := by
  unfold projVec1
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun a _ => ?_
  refine HasDerivAt.mul_const ?_ (cl44Gen a p q)
  refine HasDerivAt.const_mul (((if a.val < 4 then (1 : ℝ) else -1) / 16)) ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun r _ =>
    HasDerivAt.fun_sum fun k _ => (hC k r).const_mul (cl44Gen a r k)

/-- **Tangent Lie-Algebra Recovery via `HasDerivAt` at `t = 0`**:
Any `X ∈ M₁₆(ℝ)` satisfies `d/dt|_{t=0} expMat16GL X t = X` entrywise, and whenever
`∀ t : ℝ, expMat16GL X t ∈ SplitG2MatrixGroup`, its tangent generator `X` satisfies
`IsSplitG2Stabilizer X` and normalizes `Cl⁽¹⁾(4,4)`. -/
theorem splitG2_tangent_of_exp_mem (X : Matrix Krein16Idx Krein16Idx ℝ) :
    (∀ i j, HasDerivAt (fun t : ℝ => (expMat16GL X t).val i j) (X i j) 0) ∧
    ((∀ t : ℝ, expMat16GL X t ∈ SplitG2MatrixGroup) →
      IsSplitG2Stabilizer X ∧ ∀ v ∈ cl44Vec1Submodule, X * v - v * X ∈ cl44Vec1Submodule) := by
  have hderiv0 : ∀ i j, HasDerivAt (fun t : ℝ => (expMat16GL X t).val i j) (X i j) 0 := by
    intro i j
    simpa only [expMat16GL, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] using
      hasDerivAt_exp_smul_entry X 0 i j
  have hderiv0_neg : ∀ i j, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-X)) i j) ((-X) i j) 0 := by
    intro i j
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] using
      hasDerivAt_exp_smul_entry (-X) 0 i j
  refine ⟨hderiv0, ?_⟩
  intro hmem
  have hid0 : (expMat16GL X 0).val = 1 := by simp [expMat16GL]
  have hk : Xᵀ * kreinMetric88 + kreinMetric88 * X = 0 := by
    ext i j
    have htr_deriv : ∀ r c, HasDerivAt (fun t : ℝ => ((expMat16GL X t).val)ᵀ r c) (Xᵀ r c) 0 :=
      fun r c => by simpa only [Matrix.transpose_apply] using hderiv0 c r
    have hconst_prod :
        ∀ t : ℝ, ((expMat16GL X t).val)ᵀ * kreinMetric88 * (expMat16GL X t).val = kreinMetric88 :=
      fun t => (hmem t).1
    have hleft := matrix_hasDerivAt_mul_const kreinMetric88 htr_deriv
    have htot := matrix_hasDerivAt_mul hleft hderiv0 i j
    have heq : (fun s : ℝ => (((expMat16GL X s).val)ᵀ * kreinMetric88 * (expMat16GL X s).val) i j) =
        fun _ => kreinMetric88 i j := funext fun s => congrArg (fun M => M i j) (hconst_prod s)
    rw [heq] at htot
    have hval := htot.unique (hasDerivAt_const (0 : ℝ) (kreinMetric88 i j))
    rw [hid0, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul] at hval
    exact hval
  have hgam : X * gamma44 = gamma44 * X := by
    ext i j
    have hl := matrix_hasDerivAt_mul_const gamma44 hderiv0 i j
    have hr := matrix_hasDerivAt_const_mul gamma44 hderiv0 i j
    have hfn : (fun s : ℝ => ((expMat16GL X s).val * gamma44) i j) =
        fun s : ℝ => (gamma44 * (expMat16GL X s).val) i j :=
      funext fun s => congrArg (fun M => M i j) (hmem s).2.1
    rw [hfn] at hl
    exact hl.unique hr
  have he0 : X * cl44Gen 0 = cl44Gen 0 * X := by
    ext i j
    have hl := matrix_hasDerivAt_mul_const (cl44Gen 0) hderiv0 i j
    have hr := matrix_hasDerivAt_const_mul (cl44Gen 0) hderiv0 i j
    have hfn : (fun s : ℝ => ((expMat16GL X s).val * cl44Gen 0) i j) =
        fun s : ℝ => (cl44Gen 0 * (expMat16GL X s).val) i j :=
      funext fun s => congrArg (fun M => M i j) (hmem s).2.2.1
    rw [hfn] at hl
    exact hl.unique hr
  have hspin : X.mulVec majoranaRefSpinor = 0 := by
    ext i
    have hl : HasDerivAt
        (fun s : ℝ => ∑ j : Krein16Idx, (expMat16GL X s).val i j * majoranaRefSpinor j)
        (∑ j : Krein16Idx, X i j * majoranaRefSpinor j) 0 :=
      HasDerivAt.fun_sum fun j _ => (hderiv0 i j).mul_const (majoranaRefSpinor j)
    have hfn : (fun s : ℝ => ∑ j : Krein16Idx, (expMat16GL X s).val i j * majoranaRefSpinor j) =
        fun _ => majoranaRefSpinor i :=
      funext fun s => congrArg (fun v => v i) (hmem s).2.2.2.1
    rw [hfn] at hl
    exact hl.unique (hasDerivAt_const (0 : ℝ) (majoranaRefSpinor i))
  have hnorm : ∀ v ∈ cl44Vec1Submodule, X * v - v * X ∈ cl44Vec1Submodule := by
    intro v hv
    let C : ℝ → Matrix Krein16Idx Krein16Idx ℝ :=
      fun s => (expMat16GL X s).val * v * NormedSpace.exp (s • (-X))
    have hC_in : ∀ s : ℝ, C s ∈ cl44Vec1Submodule := fun s => by
      have hneg : s • (-X) = (-s) • X := by rw [smul_neg, neg_smul]
      dsimp [C]
      rw [hneg]
      exact (hmem s).2.2.2.2 v hv
    have hC_proj : ∀ s : ℝ, C s = projVec1 (C s) := fun s =>
      cl44Vec1Submodule_coord (hC_in s)
    have hC_deriv : ∀ p q, HasDerivAt (fun s => C s p q) ((X * v - v * X) p q) 0 := by
      intro p q
      have hl := matrix_hasDerivAt_mul_const v hderiv0
      have htot := matrix_hasDerivAt_mul hl hderiv0_neg p q
      refine htot.congr_deriv ?_
      have hneg0 : NormedSpace.exp ((0 : ℝ) • (-X)) = 1 := by simp
      rw [hid0, hneg0, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, ← sub_eq_add_neg]
    have hP_deriv := hasDerivAt_projVec1 hC_deriv
    have hsub_eq : X * v - v * X = projVec1 (X * v - v * X) := by
      ext p q
      have hC_fn : (fun s => C s p q) = fun s => projVec1 (C s) p q :=
        funext fun s => congrArg (fun M => M p q) (hC_proj s)
      have h1 := hC_deriv p q
      rw [hC_fn] at h1
      exact h1.unique (hP_deriv p q)
    rw [hsub_eq]
    exact projVec1_mem _
  exact ⟨⟨hk, hgam, he0, hspin⟩, hnorm⟩

/-- **Unified `SplitG2MatrixGroup` & `SplitG2RealFormCapstone` Bridge Theorem**. -/
theorem splitG2_matrix_lie_group_exponential_and_tangent :
    (Module.finrank ℝ g2LieSubalgebra = 14 ∧
      Module.finrank ℝ g2LieSubalgebra = Module.finrank ℝ (Submodule.map rhoVec8 g2Submodule) ∧
      Function.Injective g2RhoVec8LieHom) ∧
    (∀ (X : Matrix Krein16Idx Krein16Idx ℝ) (s t : ℝ),
      expMat16GL X 0 = 1 ∧ expMat16GL X (s + t) = expMat16GL X s * expMat16GL X t) ∧
    (∀ Z ∈ g2Submodule, ∀ (t : ℝ) (b : Fin 8),
      NormedSpace.exp (t • Z) * cl44Gen b * NormedSpace.exp ((-t) • Z) =
        ∑ a : Fin 8, (NormedSpace.exp (t • rhoVec8 Z) a b) • cl44Gen a) ∧
    (∀ Z ∈ g2Submodule, ∀ t : ℝ, expMat16GL Z t ∈ SplitG2MatrixGroup) ∧
    (∀ X : Matrix Krein16Idx Krein16Idx ℝ,
      (∀ i j, HasDerivAt (fun t : ℝ => (expMat16GL X t).val i j) (X i j) 0) ∧
      ((∀ t : ℝ, expMat16GL X t ∈ SplitG2MatrixGroup) →
        IsSplitG2Stabilizer X ∧ ∀ v ∈ cl44Vec1Submodule, X * v - v * X ∈ cl44Vec1Submodule)) ∧
    (∀ (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) (s t : ℝ),
      (∃ F : InfoGeometry.Canonical.RealSplitOctonionAut,
        (F : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) =
          InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 t) ∧
      InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D (s + t) =
        InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D s *
          InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D t) := by
  refine ⟨⟨finrank_g2LieSubalgebra, ?_, g2RhoVec8LieHom_injective⟩,
    expMat16GL_one_parameter_laws,
    fun _ hZ t b => expMat16GL_cl44_intertwining hZ t b,
    fun _ hZ t => expMat16GL_mem_splitG2MatrixGroup hZ t,
    splitG2_tangent_of_exp_mem,
    fun D s t =>
      ⟨InfoGeometry.Lie.SplitG2RealFormCapstone.split_g2_derivation_exponential_is_real_automorphism D t,
       InfoGeometry.Lie.SplitG2RealFormCapstone.split_g2_flow_is_one_parameter_subgroup D s t⟩⟩
  rw [finrank_g2LieSubalgebra, rhoVec8_isomorphic_image_finrank14.2]

end SplitG2LieGroup

end ExplicitSplitG2InCl44

/-! ## Section 5: Witt Free Lie Dimension Formula & Pigeonhole Non-Embeddability (`294 > 256`) -/

section WittPigeonhole

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Numerator `∑_{d ∣ n} μ(d) r^{n/d}` in Witt's free Lie algebra dimension formula. -/
def wittFreeLieNumerator (r n : ℕ) : ℤ :=
  ∑ d ∈ Nat.divisors n, μ d * ((r : ℤ) ^ (n / d))

/-- Witt dimension formula `dim L_n(r) = (1/n) ∑_{d ∣ n} μ(d) r^{n/d}`. -/
def wittFreeLieDim (r n : ℕ) : ℤ :=
  wittFreeLieNumerator r n / (n : ℤ)

/-- Cumulative 5-step free Lie dimension `∑_{n=1}^{N} dim L_n(r)`. -/
def wittFreeLieCumDim (r N : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 N, wittFreeLieDim r n

/-- Proof that `4` is not squarefree (`2 * 2 ∣ 4`, yet `¬ IsUnit 2`), yielding `μ(4) = 0`. -/
theorem not_squarefree_four : ¬ Squarefree (4 : ℕ) := by
  intro hsq
  have hu : IsUnit (2 : ℕ) := hsq 2 (by norm_num)
  rw [Nat.isUnit_iff] at hu
  omega

/-- Exact Möbius values on `1..5` rooted in Mathlib's `ArithmeticFunction.moebius`. -/
theorem moebius_one_to_five :
    μ 1 = 1 ∧ μ 2 = -1 ∧ μ 3 = -1 ∧ μ 4 = 0 ∧ μ 5 = -1 := by
  have h1 : μ 1 = 1 := ArithmeticFunction.moebius_apply_one
  have h2 : μ 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : μ 3 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h4 : μ 4 = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree not_squarefree_four
  have h5 : μ 5 = -1 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5)
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Exact Witt free Lie dimensions for rank `4` through step `5`:
`[4, 6, 20, 60, 204]`, cumulative sum `= 294 > 256`. -/
theorem witt_rank4_dimensions :
    wittFreeLieDim 4 1 = 4 ∧
    wittFreeLieDim 4 2 = 6 ∧
    wittFreeLieDim 4 3 = 20 ∧
    wittFreeLieDim 4 4 = 60 ∧
    wittFreeLieDim 4 5 = 204 ∧
    wittFreeLieCumDim 4 5 = 294 := by
  have hd1 : Nat.divisors 1 = {1} := by decide
  have hd2 : Nat.divisors 2 = {1, 2} := by decide
  have hd3 : Nat.divisors 3 = {1, 3} := by decide
  have hd4 : Nat.divisors 4 = {1, 2, 4} := by decide
  have hd5 : Nat.divisors 5 = {1, 5} := by decide
  have hm := moebius_one_to_five
  have w1 : wittFreeLieDim 4 1 = 4 := by
    unfold wittFreeLieDim wittFreeLieNumerator
    rw [hd1, Finset.sum_singleton, hm.1]
    norm_num
  have w2 : wittFreeLieDim 4 2 = 6 := by
    unfold wittFreeLieDim wittFreeLieNumerator
    rw [hd2, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), hm.1, hm.2.1]
    norm_num
  have w3 : wittFreeLieDim 4 3 = 20 := by
    unfold wittFreeLieDim wittFreeLieNumerator
    rw [hd3, Finset.sum_pair (by decide : (1 : ℕ) ≠ 3), hm.1, hm.2.2.1]
    norm_num
  have w4 : wittFreeLieDim 4 4 = 60 := by
    unfold wittFreeLieDim wittFreeLieNumerator
    rw [hd4, Finset.sum_insert (by decide), Finset.sum_pair (by decide),
      hm.1, hm.2.1, hm.2.2.2.1]
    norm_num
  have w5 : wittFreeLieDim 4 5 = 204 := by
    unfold wittFreeLieDim wittFreeLieNumerator
    rw [hd5, Finset.sum_pair (by decide : (1 : ℕ) ≠ 5), hm.1, hm.2.2.2.2]
    norm_num
  have hcum : wittFreeLieCumDim 4 5 = 294 := by
    have hIcc : Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
    unfold wittFreeLieCumDim
    rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_pair (by decide), w1, w2, w3, w4, w5]
    norm_num
  exact ⟨w1, w2, w3, w4, w5, hcum⟩

/-- **Pigeonhole Non-Embeddability (`294 > 256`)**: no injective `ℝ`-linear map exists from a
294-dimensional cumulative 5-step free Lie algebra space `Fin 294 → ℝ` into `M₁₆(ℝ)` (`finrank = 256`). -/
theorem no_injective_fiveStepFreeLie4_into_mat16 :
    ¬ ∃ L : (Fin 294 → ℝ) →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ, Function.Injective L := by
  rintro ⟨L, hL⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hL
  rw [Module.finrank_fin_fun, finrank_mat16] at hle
  omega

/-- **Forced Syzygy Kernel Lower Bound**: every `ℝ`-linear map `L : (Fin 294 → ℝ) →ₗ[ℝ] M₁₆(ℝ)`
has a nontrivial syzygy kernel (`ker L ≠ ⊥`) of dimension at least `294 - 256 = 38`. -/
theorem fiveStepFreeLie4_ker_ne_bot_and_syzygy_bound
    (L : (Fin 294 → ℝ) →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ) :
    LinearMap.ker L ≠ ⊥ ∧ 38 ≤ Module.finrank ℝ (LinearMap.ker L) := by
  have hdim_dom : Module.finrank ℝ (Fin 294 → ℝ) = 294 := by rw [Module.finrank_fin_fun]
  have hdim_cod : Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) = 256 := finrank_mat16
  have hlt : Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) <
      Module.finrank ℝ (Fin 294 → ℝ) := by
    rw [hdim_cod, hdim_dom]
    omega
  have hker_ne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  have hrn := L.finrank_range_add_finrank_ker
  have hrange_le : Module.finrank ℝ (LinearMap.range L) ≤
      Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) := Submodule.finrank_le _
  rw [hdim_dom] at hrn
  rw [hdim_cod] at hrange_le
  exact ⟨hker_ne, by omega⟩

/-! ### Genuine 294-Element Shirshov–Lyndon Basis in Mathlib's `FreeLieAlgebra ℝ (Fin 4)` & Universal Syzygy Theorems -/

section FreeLie294Lyndon

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Computable Boolean equality on words over `Fin 4` (avoids `Classical.propDecidable` inside `decide`). -/
def wordEq : List (Fin 4) → List (Fin 4) → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a.1 b.1 && wordEq as bs
  | _, _ => false

private lemma wordEq_iff (u v : List (Fin 4)) : wordEq u v = true ↔ u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simp [wordEq]
    | cons _ _ => simp [wordEq]
  | cons a us ih =>
    cases v with
    | nil => simp [wordEq]
    | cons b vs =>
      simp only [wordEq, Bool.and_eq_true, Nat.beq_eq, List.cons.injEq, Fin.ext_iff]
      exact and_congr_right fun _ => ih vs

/-- Strict lexicographic order on words over `Fin 4` using pure `Bool` primitives. -/
def wordLexLt : List (Fin 4) → List (Fin 4) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      match Nat.blt a.1 b.1, Nat.blt b.1 a.1 with
      | true, _ => true
      | false, true => false
      | false, false => wordLexLt as bs

/-- Shortlex order (length first, then lexicographic) on words over `Fin 4`. -/
def wordOrderLt (u v : List (Fin 4)) : Bool :=
  Nat.blt u.length v.length || (Nat.beq u.length v.length && wordLexLt u v)

/-- Nonempty proper suffixes of a word, ordered from longest to shortest. -/
def properSuffixes : List (Fin 4) → List (List (Fin 4))
  | [] => []
  | _ :: t =>
      match t with
      | [] => []
      | _ :: _ => t :: properSuffixes t

/-- Computable Chen–Fox–Lyndon primality predicate: `w` is nonempty and lexicographically
strictly smaller than every nonempty proper suffix. -/
def isLyndonWord (w : List (Fin 4)) : Bool :=
  !w.isEmpty && (properSuffixes w).all (fun s => wordLexLt w s)

/-- Canonical ordered 4-letter alphabet over `Fin 4`. -/
def fin4List : List (Fin 4) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

/-- All words of length `n` over `Fin 4` in strict lexicographic order. -/
def wordsOfLen : ℕ → List (List (Fin 4))
  | 0 => [[]]
  | n + 1 => fin4List.flatMap fun a => (wordsOfLen n).map (a :: ·)

/-- All Lyndon words of exact degree `d` over `Fin 4`. -/
def lyndonWordsOfDeg (d : ℕ) : List (List (Fin 4)) :=
  (wordsOfLen d).filter isLyndonWord

/-- Cumulative ordered list of all `4 + 6 + 20 + 60 + 204 = 294` Lyndon words of degree `1..5`. -/
def lyndonList294 : List (List (Fin 4)) :=
  [1, 2, 3, 4, 5].flatMap lyndonWordsOfDeg

/-- Indexed `Fin 294` family of all Lyndon words of degree `1..5` over `Fin 4`. -/
def lyndonWord294 (i : Fin 294) : List (Fin 4) :=
  lyndonList294.getD i.1 []

/-- Binary bracket tree type over `Fin 4`. -/
inductive LieTree4 : Type
  | leaf : Fin 4 → LieTree4
  | node : LieTree4 → LieTree4 → LieTree4
  deriving DecidableEq, Repr

/-- Number of free generators (leaves) in a bracket tree. -/
def LieTree4.leafCount : LieTree4 → ℕ
  | .leaf _ => 1
  | .node l r => l.leafCount + r.leafCount

/-- Pure `Bool` equality on `LieTree4`. -/
def treeEq : LieTree4 → LieTree4 → Bool
  | .leaf a, .leaf b => Nat.beq a.1 b.1
  | .node l₁ r₁, .node l₂ r₂ => treeEq l₁ l₂ && treeEq r₁ r₂
  | _, _ => false

private lemma treeEq_iff (t₁ t₂ : LieTree4) : treeEq t₁ t₂ = true ↔ t₁ = t₂ := by
  induction t₁ generalizing t₂ with
  | leaf a =>
    cases t₂ with
    | leaf b => simp [treeEq, Nat.beq_eq, Fin.ext_iff]
    | node _ _ => simp [treeEq]
  | node l₁ r₁ ihl ihr =>
    cases t₂ with
    | leaf _ => simp [treeEq]
    | node l₂ r₂ =>
      simp only [treeEq, Bool.and_eq_true, LieTree4.node.injEq]
      exact and_congr (ihl l₂) (ihr r₂)

/-- Standard Chen–Fox–Lyndon bracketing `w ↦ [std u, std v]` splitting at the longest proper Lyndon suffix `v`. -/
def stdLyndonBracketAux : ℕ → List (Fin 4) → LieTree4
  | 0, w => match w with | a :: _ => .leaf a | [] => .leaf ⟨0, by decide⟩
  | fuel + 1, w =>
      match w with
      | [] => .leaf ⟨0, by decide⟩
      | a :: rest =>
          match rest with
          | [] => .leaf a
          | _ :: _ =>
              match (properSuffixes w).find? isLyndonWord with
              | some v =>
                  let u := w.take (w.length - v.length)
                  .node (stdLyndonBracketAux fuel u) (stdLyndonBracketAux fuel v)
              | none => .leaf ⟨0, by decide⟩

/-- Computable standard Shirshov–Lyndon bracket tree for word index `i : Fin 294`. -/
def lyndonTree294 (i : Fin 294) : LieTree4 :=
  stdLyndonBracketAux 6 (lyndonWord294 i)

/-- Interpret a formal bracket tree `LieTree4` inside Mathlib's genuine `FreeLieAlgebra ℝ (Fin 4)`. -/
def evalFreeLie : LieTree4 → FreeLieAlgebra ℝ (Fin 4)
  | .leaf a => FreeLieAlgebra.of ℝ a
  | .node l r => ⁅evalFreeLie l, evalFreeLie r⁆

/-- The `294` explicit Shirshov–Lyndon basis elements inside `FreeLieAlgebra ℝ (Fin 4)`. -/
def lyndonFreeLie4 (i : Fin 294) : FreeLieAlgebra ℝ (Fin 4) :=
  evalFreeLie (lyndonTree294 i)

/-- Raw associative-polynomial expansion `[x, y] = x y - y x` of a bracket tree `LieTree4`. -/
def treeToPoly : LieTree4 → List (List (Fin 4) × ℤ)
  | .leaf a => [([a], 1)]
  | .node l r =>
      let pl := treeToPoly l
      let pr := treeToPoly r
      (pl.flatMap fun uc => pr.map fun vc => (uc.1 ++ vc.1, uc.2 * vc.2)) ++
      (pr.flatMap fun uc => pl.map fun vc => (uc.1 ++ vc.1, -(uc.2 * vc.2)))

/-- Exact coefficient of word `w` in an associative polynomial `p`. -/
def polyCoeff (w : List (Fin 4)) : List (List (Fin 4) × ℤ) → ℤ
  | [] => 0
  | uc :: rest => (if wordEq uc.1 w then uc.2 else 0) + polyCoeff w rest

/-- Computable strict-shortlex chain checker over a list of words. -/
def checkChainAux : List (Fin 4) → List (List (Fin 4)) → Bool
  | _, [] => true
  | prev, cur :: rest =>
      match wordOrderLt prev cur with
      | true => checkChainAux cur rest
      | false => false

/-- True iff `l` is strictly increasing under `wordOrderLt`. -/
def isStrictChainOrderLt : List (List (Fin 4)) → Bool
  | [] => true
  | u :: rest => checkChainAux u rest

/-- Pure `Bool` Shirshov triangularity predicate for a Lyndon word `w`. -/
def shirshovOk (w : List (Fin 4)) : Bool :=
  let p := treeToPoly (stdLyndonBracketAux 6 w)
  (polyCoeff w p == 1) && p.all (fun mc => !wordOrderLt mc.1 w)

/-- Prepend action on `(List (Fin 4) → ℝ)` realizing the free associative algebra inside `End ℝ (List (Fin 4) → ℝ)`. -/
def prependWordOp (a : Fin 4) : Module.End ℝ (List (Fin 4) → ℝ) where
  toFun φ w := match w with
    | b :: u => if a = b then φ u else 0
    | [] => 0
  map_add' φ ψ := by
    ext w
    cases w with
    | nil => simp
    | cons b u => by_cases hab : a = b <;> simp [hab]
  map_smul' r φ := by
    ext w
    cases w with
    | nil => simp
    | cons b u => by_cases hab : a = b <;> simp [hab, smul_eq_mul]

/-- Iterated prepend endomorphism indexed by a word `u : List (Fin 4)`. -/
def prependWordList : List (Fin 4) → Module.End ℝ (List (Fin 4) → ℝ)
  | [] => 1
  | a :: u => prependWordOp a * prependWordList u

private lemma prependWordList_append (u v : List (Fin 4)) :
    prependWordList (u ++ v) = prependWordList u * prependWordList v := by
  induction u with
  | nil => simp [prependWordList]
  | cons a u ih => simp [prependWordList, ih, mul_assoc]

/-- Empty-word indicator vector in `List (Fin 4) → ℝ`. -/
def emptyWordInd : List (Fin 4) → ℝ :=
  fun u => if u = [] then 1 else 0

private lemma prependWordList_emptyWordInd (u w : List (Fin 4)) :
    (prependWordList u emptyWordInd) w = if u = w then 1 else 0 := by
  induction u generalizing w with
  | nil =>
    change emptyWordInd w = if [] = w then 1 else 0
    simp only [emptyWordInd, eq_comm]
  | cons a u ih =>
    cases w with
    | nil =>
      change (prependWordOp a (prependWordList u emptyWordInd)) [] =
        if a :: u = [] then 1 else 0
      simp [prependWordOp]
    | cons b w' =>
      change (prependWordOp a (prependWordList u emptyWordInd)) (b :: w') =
        if a :: u = b :: w' then 1 else 0
      dsimp [prependWordOp]
      by_cases hab : a = b
      · subst hab
        simp [ih w']
      · simp [hab]

/-- Magnus-representation Lie homomorphism `FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ End ℝ (List (Fin 4) → ℝ)`. -/
def wordEndHom : FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ Module.End ℝ (List (Fin 4) → ℝ) :=
  FreeLieAlgebra.lift ℝ prependWordOp

/-- Exact `ℝ`-linear word-coefficient extraction functional `FreeLieAlgebra ℝ (Fin 4) →ₗ[ℝ] ℝ`. -/
def wordCoeffLinear (w : List (Fin 4)) : FreeLieAlgebra ℝ (Fin 4) →ₗ[ℝ] ℝ where
  toFun x := (wordEndHom x emptyWordInd) w
  map_add' x y := by
    rw [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' r x := by
    rw [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_eq_mul]

/-- Interpret an associative word-coefficient list `p` inside `End ℝ (List (Fin 4) → ℝ)`. -/
def evalPolyEnd : List (List (Fin 4) × ℤ) → Module.End ℝ (List (Fin 4) → ℝ)
  | [] => 0
  | (u, c) :: rest => (c : ℝ) • prependWordList u + evalPolyEnd rest

private lemma evalPolyEnd_append (p q : List (List (Fin 4) × ℤ)) :
    evalPolyEnd (p ++ q) = evalPolyEnd p + evalPolyEnd q := by
  induction p with
  | nil => simp [evalPolyEnd]
  | cons mc rest ih =>
    rcases mc with ⟨u, c⟩
    simp [evalPolyEnd, ih, add_assoc]

private lemma evalPolyEnd_map_mul (u : List (Fin 4)) (cu : ℤ) (q : List (List (Fin 4) × ℤ)) :
    evalPolyEnd (q.map fun vc => (u ++ vc.1, cu * vc.2)) =
      ((cu : ℝ) • prependWordList u) * evalPolyEnd q := by
  induction q with
  | nil => simp [evalPolyEnd]
  | cons vc rest ih =>
    rcases vc with ⟨v, cv⟩
    simp only [List.map_cons, evalPolyEnd]
    rw [ih, prependWordList_append, mul_add]
    congr 1
    rw [Int.cast_mul, smul_mul_assoc, mul_smul_comm, smul_smul]

private lemma evalPolyEnd_map_neg_mul (u : List (Fin 4)) (cu : ℤ) (q : List (List (Fin 4) × ℤ)) :
    evalPolyEnd (q.map fun vc => (u ++ vc.1, -(cu * vc.2))) =
      -(((cu : ℝ) • prependWordList u) * evalPolyEnd q) := by
  induction q with
  | nil => simp [evalPolyEnd]
  | cons vc rest ih =>
    rcases vc with ⟨v, cv⟩
    simp only [List.map_cons, evalPolyEnd]
    rw [ih, prependWordList_append, mul_add, neg_add]
    congr 1
    apply eq_neg_of_add_eq_zero_left
    rw [Int.cast_neg, Int.cast_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← add_smul, neg_add_cancel, zero_smul]

private lemma evalPolyEnd_flatMap_mul (p q : List (List (Fin 4) × ℤ)) :
    evalPolyEnd (p.flatMap fun uc => q.map fun vc => (uc.1 ++ vc.1, uc.2 * vc.2)) =
      evalPolyEnd p * evalPolyEnd q := by
  induction p with
  | nil => simp [evalPolyEnd]
  | cons uc rest ih =>
    rcases uc with ⟨u, cu⟩
    simp only [List.flatMap_cons, evalPolyEnd_append, evalPolyEnd]
    rw [evalPolyEnd_map_mul, ih, add_mul]

private lemma evalPolyEnd_flatMap_neg_mul (p q : List (List (Fin 4) × ℤ)) :
    evalPolyEnd (p.flatMap fun uc => q.map fun vc => (uc.1 ++ vc.1, -(uc.2 * vc.2))) =
      -(evalPolyEnd p * evalPolyEnd q) := by
  induction p with
  | nil => simp [evalPolyEnd]
  | cons uc rest ih =>
    rcases uc with ⟨u, cu⟩
    simp only [List.flatMap_cons, evalPolyEnd_append, evalPolyEnd]
    rw [evalPolyEnd_map_neg_mul, ih, add_mul, neg_add]

private lemma wordEndHom_evalFreeLie (t : LieTree4) :
    wordEndHom (evalFreeLie t) = evalPolyEnd (treeToPoly t) := by
  induction t with
  | leaf a =>
    dsimp [evalFreeLie, treeToPoly, evalPolyEnd, prependWordList, wordEndHom]
    rw [FreeLieAlgebra.lift_of_apply, mul_one, Int.cast_one, one_smul, add_zero]
  | node l r ihl ihr =>
    change wordEndHom ⁅evalFreeLie l, evalFreeLie r⁆ = evalPolyEnd (treeToPoly (LieTree4.node l r))
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, ihl, ihr]
    dsimp [treeToPoly]
    rw [evalPolyEnd_append, evalPolyEnd_flatMap_mul, evalPolyEnd_flatMap_neg_mul, sub_eq_add_neg]

private lemma evalPolyEnd_emptyWordInd (w : List (Fin 4)) (p : List (List (Fin 4) × ℤ)) :
    (evalPolyEnd p emptyWordInd) w = (polyCoeff w p : ℝ) := by
  induction p with
  | nil => simp [evalPolyEnd, polyCoeff]
  | cons uc rest ih =>
    rcases uc with ⟨u, c⟩
    simp only [evalPolyEnd, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, prependWordList_emptyWordInd, polyCoeff, ih, Int.cast_add]
    cases hweq : wordEq u w
    · have hu : u ≠ w := fun h => by
        have ht := (wordEq_iff u w).mpr h
        rw [hweq] at ht
        exact Bool.false_ne_true ht
      simp [hu]
    · have hu : u = w := (wordEq_iff u w).mp hweq
      simp [hu]

private lemma wordCoeffLinear_evalFreeLie (w : List (Fin 4)) (t : LieTree4) :
    wordCoeffLinear w (evalFreeLie t) = (polyCoeff w (treeToPoly t) : ℝ) := by
  change (wordEndHom (evalFreeLie t) emptyWordInd) w = (polyCoeff w (treeToPoly t) : ℝ)
  rw [wordEndHom_evalFreeLie, evalPolyEnd_emptyWordInd]

private lemma polyCoeff_zero_of_forall_ne (w : List (Fin 4)) (p : List (List (Fin 4) × ℤ))
    (hne : ∀ mc ∈ p, mc.1 ≠ w) : polyCoeff w p = 0 := by
  induction p with
  | nil => rfl
  | cons mc rest ih =>
    rcases mc with ⟨u, c⟩
    have hu : u ≠ w := hne (u, c) (by simp)
    have hweq : wordEq u w = false := by
      cases h : wordEq u w
      · rfl
      · exact absurd ((wordEq_iff u w).mp h) hu
    have hrest : polyCoeff w rest = 0 := ih fun x hx => hne x (by simp [hx])
    simp [polyCoeff, hweq, hrest]

/-- A nonzero coefficient in an associative expansion is witnessed by an
actual monomial carrying the requested word. -/
private lemma polyCoeff_ne_zero_has_word_mem (w : List (Fin 4))
    (p : List (List (Fin 4) × ℤ)) (h : polyCoeff w p ≠ 0) :
    ∃ mc ∈ p, mc.1 = w := by
  induction p with
  | nil => simp [polyCoeff] at h
  | cons mc rest ih =>
    cases heq : wordEq mc.1 w with
    | true => exact ⟨mc, by simp, (wordEq_iff mc.1 w).mp heq⟩
    | false =>
      have hrest : polyCoeff w rest ≠ 0 := by
        intro hz
        apply h
        simp [polyCoeff, heq, hz]
      obtain ⟨m, hm, hmw⟩ := ih hrest
      exact ⟨m, by simp [hm], hmw⟩

/-- Every monomial word in a bracket-tree expansion has length equal to the
number of leaves of that tree. -/
private theorem treeToPoly_word_length (t : LieTree4) :
    ∀ mc ∈ treeToPoly t, mc.1.length = t.leafCount := by
  induction t with
  | leaf a =>
    intro mc h
    simp [treeToPoly, LieTree4.leafCount] at h ⊢
    rcases h with rfl
    rfl
  | node l r ihl ihr =>
    intro mc h
    simp only [treeToPoly, List.mem_append] at h
    rcases h with h | h
    · rcases List.mem_flatMap.mp h with ⟨u, hu, h⟩
      rcases List.mem_map.mp h with ⟨v, hv, hEq⟩
      cases hEq
      have huLen := ihl u hu
      have hvLen := ihr v hv
      simp [LieTree4.leafCount, huLen, hvLen]
    · rcases List.mem_flatMap.mp h with ⟨u, hu, h⟩
      rcases List.mem_map.mp h with ⟨v, hv, hEq⟩
      cases hEq
      have huLen := ihr u hu
      have hvLen := ihl v hv
      simp [LieTree4.leafCount, huLen, hvLen, Nat.add_comm]

private lemma wordLexLt_trans {u v w : List (Fin 4)}
    (huv : wordLexLt u v = true) (hvw : wordLexLt v w = true) :
    wordLexLt u w = true := by
  induction u generalizing v w with
  | nil =>
    cases v with
    | nil => simp [wordLexLt] at huv
    | cons b vs =>
      cases w with
      | nil => simp [wordLexLt] at hvw
      | cons c ws => simp [wordLexLt]
  | cons a us ih =>
    cases v with
    | nil => simp [wordLexLt] at huv
    | cons b vs =>
      cases w with
      | nil => simp [wordLexLt] at hvw
      | cons c ws =>
        dsimp only [wordLexLt] at huv hvw ⊢
        cases hab1 : Nat.blt a.1 b.1 <;> cases hba1 : Nat.blt b.1 a.1
        · rw [hab1, hba1] at huv
          have hab_eq : a.1 = b.1 := by
            have h1 : ¬ a.1 < b.1 := by rw [← Nat.blt_eq, hab1]; decide
            have h2 : ¬ b.1 < a.1 := by rw [← Nat.blt_eq, hba1]; decide
            omega
          cases hbc1 : Nat.blt b.1 c.1 <;> cases hcb1 : Nat.blt c.1 b.1
          · rw [hbc1, hcb1] at hvw
            have hbc_eq : b.1 = c.1 := by
              have h1 : ¬ b.1 < c.1 := by rw [← Nat.blt_eq, hbc1]; decide
              have h2 : ¬ c.1 < b.1 := by rw [← Nat.blt_eq, hcb1]; decide
              omega
            have hn1 : Nat.blt a.1 c.1 = false := by
              cases h : Nat.blt a.1 c.1; rfl; exfalso; have := Nat.blt_eq.mp h; omega
            have hn2 : Nat.blt c.1 a.1 = false := by
              cases h : Nat.blt c.1 a.1; rfl; exfalso; have := Nat.blt_eq.mp h; omega
            rw [hn1, hn2]
            exact ih huv hvw
          · rw [hbc1, hcb1] at hvw; dsimp only at hvw; exact absurd hvw Bool.false_ne_true
          · have hac1 : Nat.blt a.1 c.1 = true := hab_eq ▸ hbc1
            rw [hac1]
          · have hac1 : Nat.blt a.1 c.1 = true := hab_eq ▸ hbc1
            rw [hac1]
        · rw [hab1, hba1] at huv; dsimp only at huv; exact absurd huv Bool.false_ne_true
        · have hab : a.1 < b.1 := Nat.blt_eq.mp hab1
          have hbc_le : b.1 ≤ c.1 := by
            cases hbc1 : Nat.blt b.1 c.1
            · cases hcb1 : Nat.blt c.1 b.1
              · have h1 : ¬ b.1 < c.1 := by rw [← Nat.blt_eq, hbc1]; decide
                have h2 : ¬ c.1 < b.1 := by rw [← Nat.blt_eq, hcb1]; decide
                omega
              · rw [hbc1, hcb1] at hvw; dsimp only at hvw; exact absurd hvw Bool.false_ne_true
            · have h1 : b.1 < c.1 := Nat.blt_eq.mp hbc1; omega
          have hac1 : Nat.blt a.1 c.1 = true := Nat.blt_eq.mpr (lt_of_lt_of_le hab hbc_le)
          rw [hac1]
        · have hab : a.1 < b.1 := Nat.blt_eq.mp hab1
          have hbc_le : b.1 ≤ c.1 := by
            cases hbc1 : Nat.blt b.1 c.1
            · cases hcb1 : Nat.blt c.1 b.1
              · have h1 : ¬ b.1 < c.1 := by rw [← Nat.blt_eq, hbc1]; decide
                have h2 : ¬ c.1 < b.1 := by rw [← Nat.blt_eq, hcb1]; decide
                omega
              · rw [hbc1, hcb1] at hvw; dsimp only at hvw; exact absurd hvw Bool.false_ne_true
            · have h1 : b.1 < c.1 := Nat.blt_eq.mp hbc1; omega
          have hac1 : Nat.blt a.1 c.1 = true := Nat.blt_eq.mpr (lt_of_lt_of_le hab hbc_le)
          rw [hac1]

private lemma wordOrderLt_trans {u v w : List (Fin 4)}
    (huv : wordOrderLt u v = true) (hvw : wordOrderLt v w = true) :
    wordOrderLt u w = true := by
  unfold wordOrderLt at huv hvw ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at huv hvw ⊢
  rcases huv with huv_len | ⟨huv_eq, huv_lex⟩ <;> rcases hvw with hvw_len | ⟨hvw_eq, hvw_lex⟩
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨huv_eq.trans hvw_eq, wordLexLt_trans huv_lex hvw_lex⟩

set_option maxRecDepth 4096 in
private lemma lyndon_master_bool_checks :
    Nat.beq (lyndonWordsOfDeg 1).length 4 = true ∧
    Nat.beq (lyndonWordsOfDeg 2).length 6 = true ∧
    Nat.beq (lyndonWordsOfDeg 3).length 20 = true ∧
    Nat.beq (lyndonWordsOfDeg 4).length 60 = true ∧
    Nat.beq (lyndonWordsOfDeg 5).length 204 = true ∧
    Nat.beq lyndonList294.length 294 = true ∧
    isStrictChainOrderLt lyndonList294 = true ∧
    lyndonList294.all shirshovOk = true ∧
    (lyndonWordsOfDeg 1).all (fun w => Nat.beq w.length 1) = true ∧
    (lyndonWordsOfDeg 2).all (fun w => Nat.beq w.length 2) = true ∧
    (lyndonWordsOfDeg 3).all (fun w => Nat.beq w.length 3) = true ∧
    (lyndonWordsOfDeg 4).all (fun w => Nat.beq w.length 4) = true ∧
    (lyndonWordsOfDeg 5).all (fun w => Nat.beq w.length 5) = true ∧
    treeEq (lyndonTree294 0) (LieTree4.leaf 0) = true ∧
    treeEq (lyndonTree294 1) (LieTree4.leaf 1) = true ∧
    treeEq (lyndonTree294 2) (LieTree4.leaf 2) = true ∧
    treeEq (lyndonTree294 3) (LieTree4.leaf 3) = true ∧
    treeEq (lyndonTree294 4) (LieTree4.node (LieTree4.leaf 0) (LieTree4.leaf 1)) = true ∧
    treeEq (lyndonTree294 9) (LieTree4.node (LieTree4.leaf 2) (LieTree4.leaf 3)) = true := by
  decide

set_option maxRecDepth 4096
set_option maxRecDepth 4096 in
/-- Exact cardinality of Lyndon words by degree `[4, 6, 20, 60, 204]`, sum `= 294`, matching Witt's formula. -/
theorem lyndonWordsOfDeg_counts :
    (lyndonWordsOfDeg 1).length = 4 ∧
    (lyndonWordsOfDeg 2).length = 6 ∧
    (lyndonWordsOfDeg 3).length = 20 ∧
    (lyndonWordsOfDeg 4).length = 60 ∧
    (lyndonWordsOfDeg 5).length = 204 ∧
    lyndonList294.length = 294 := by
  have hm := lyndon_master_bool_checks
  exact ⟨Nat.eq_of_beq_eq_true hm.1, Nat.eq_of_beq_eq_true hm.2.1,
    Nat.eq_of_beq_eq_true hm.2.2.1, Nat.eq_of_beq_eq_true hm.2.2.2.1,
    Nat.eq_of_beq_eq_true hm.2.2.2.2.1, Nat.eq_of_beq_eq_true hm.2.2.2.2.2.1⟩

private lemma getD_mem_of_lt {α : Type*} (l : List α) (d : α) {n : ℕ} (hn : n < l.length) :
    l.getD n d ∈ l := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a t ih =>
    cases n with
    | zero => simp [List.getD]
    | succ m =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hn
      simpa [List.getD] using List.mem_cons_of_mem a (ih hn)

private lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (d : α) {n : ℕ} (hn : n < l₁.length) :
    (l₁ ++ l₂).getD n d = l₁.getD n d := by
  induction l₁ generalizing n with
  | nil => simp at hn
  | cons a t ih =>
    cases n with
    | zero => rfl
    | succ m => exact ih (Nat.succ_lt_succ_iff.mp hn)

private lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (d : α) (n : ℕ) :
    (l₁ ++ l₂).getD (l₁.length + n) d = l₂.getD n d := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    simp [List.length_cons, Nat.succ_add, List.getD] at ih ⊢
    exact ih

private lemma checkChainAux_getD (prev : List (Fin 4)) (l : List (List (Fin 4)))
    (hc : checkChainAux prev l = true) {n : ℕ} (hn : n < l.length) :
    wordOrderLt prev (l.getD n []) = true := by
  induction l generalizing prev n with
  | nil => simp at hn
  | cons cur rest ih =>
    dsimp only [checkChainAux] at hc
    cases hpc : wordOrderLt prev cur
    · rw [hpc] at hc; dsimp only at hc; exact absurd hc Bool.false_ne_true
    · rw [hpc] at hc
      cases n with
      | zero => simpa [List.getD] using hpc
      | succ m =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hn
        exact wordOrderLt_trans hpc (ih cur hc hn)

private lemma isStrictChainOrderLt_getD (l : List (List (Fin 4)))
    (hc : isStrictChainOrderLt l = true) {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    wordOrderLt (l.getD i []) (l.getD j []) = true := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons u rest ih =>
    dsimp only [isStrictChainOrderLt] at hc
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ m =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
        exact checkChainAux_getD u rest hc hj
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        have hrest : isStrictChainOrderLt rest = true := by
          cases rest with
          | nil => rfl
          | cons v rest' =>
            dsimp only [checkChainAux] at hc
            cases huv : wordOrderLt u v
            · rw [huv] at hc; dsimp only at hc; exact absurd hc Bool.false_ne_true
            · rw [huv] at hc; exact hc
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
        exact ih hrest (Nat.succ_lt_succ_iff.mp hij) hj

private lemma lyndonWord294_lt {i j : Fin 294} (hij : i < j) :
    wordOrderLt (lyndonWord294 i) (lyndonWord294 j) = true := by
  have hchain := lyndon_master_bool_checks.2.2.2.2.2.2.1
  have hlen := lyndonWordsOfDeg_counts.2.2.2.2.2
  have hj_lt : j.1 < lyndonList294.length := by rw [hlen]; exact j.isLt
  exact isStrictChainOrderLt_getD lyndonList294 hchain (Fin.lt_def.mp hij) hj_lt

private lemma shirshovOk_mem (i : Fin 294) : shirshovOk (lyndonWord294 i) = true := by
  have hall := List.all_eq_true.mp lyndon_master_bool_checks.2.2.2.2.2.2.2.1
  have hlen := lyndonWordsOfDeg_counts.2.2.2.2.2
  have hi_lt : i.1 < lyndonList294.length := by rw [hlen]; exact i.isLt
  exact hall (lyndonWord294 i) (getD_mem_of_lt lyndonList294 [] hi_lt)

/-- The certified standard bracket tree for each indexed Lyndon word has
exactly the word's degree in leaves. The proof uses the actual nonzero
associative coefficient certificate, not a finite case enumeration. -/
theorem lyndonTree294_leafCount_eq_wordLength (i : Fin 294) :
    (lyndonTree294 i).leafCount = (lyndonWord294 i).length := by
  have hsh := shirshovOk_mem i
  dsimp only [shirshovOk] at hsh
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  have hcoeff : polyCoeff (lyndonWord294 i) (treeToPoly (lyndonTree294 i)) ≠ 0 := by
    change polyCoeff (lyndonWord294 i)
      (treeToPoly (stdLyndonBracketAux 6 (lyndonWord294 i))) ≠ 0
    rw [hsh.1]
    norm_num
  obtain ⟨mc, hmc, hword⟩ :=
    polyCoeff_ne_zero_has_word_mem (lyndonWord294 i)
      (treeToPoly (lyndonTree294 i)) hcoeff
  have hlen := treeToPoly_word_length (lyndonTree294 i) mc hmc
  rw [hword] at hlen
  exact hlen.symm

private lemma wordCoeff_lyndon_upper {i j : Fin 294} (hij : i < j) :
    wordCoeffLinear (lyndonWord294 i) (lyndonFreeLie4 j) = 0 := by
  unfold lyndonFreeLie4
  rw [wordCoeffLinear_evalFreeLie]
  have hlt := lyndonWord294_lt hij
  have hsh := shirshovOk_mem j
  dsimp only [shirshovOk] at hsh
  simp only [Bool.and_eq_true] at hsh
  have hall_no : (treeToPoly (lyndonTree294 j)).all
      (fun mc => !wordOrderLt mc.1 (lyndonWord294 j)) = true := hsh.2
  have hall := List.all_eq_true.mp hall_no
  have hne : ∀ mc ∈ treeToPoly (lyndonTree294 j), mc.1 ≠ lyndonWord294 i := by
    intro mc hmc heq
    have hnot : wordOrderLt mc.1 (lyndonWord294 j) = false := by
      simpa using hall mc hmc
    rw [heq, hlt] at hnot
    exact Bool.false_ne_true hnot.symm
  rw [polyCoeff_zero_of_forall_ne _ _ hne, Int.cast_zero]

private lemma wordCoeff_lyndon_diag (i : Fin 294) :
    wordCoeffLinear (lyndonWord294 i) (lyndonFreeLie4 i) = 1 := by
  unfold lyndonFreeLie4 lyndonTree294
  rw [wordCoeffLinear_evalFreeLie]
  have hsh := shirshovOk_mem i
  dsimp only [shirshovOk] at hsh
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  rw [hsh.1, Int.cast_one]

/-- **Main Theorem (Shirshov–Lyndon Basis Independence)**:
All `294` explicit bracket trees `lyndonFreeLie4 : Fin 294 → FreeLieAlgebra ℝ (Fin 4)` of degrees
`1..5` are genuinely `ℝ`-linearly independent inside Mathlib's infinite-dimensional free Lie algebra. -/
theorem lyndonFreeLie4_linearIndependent : LinearIndependent ℝ lyndonFreeLie4 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hzero : ∀ n : ℕ, ∀ i : Fin 294, i.1 < n → c i = 0 := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | rfl
      · exact ih i hik
      · have hlin := congrArg (wordCoeffLinear (lyndonWord294 i)) hc
        rw [map_sum, _root_.map_zero] at hlin
        have hsum :
            (∑ m : Fin 294, wordCoeffLinear (lyndonWord294 i) (c m • lyndonFreeLie4 m)) = c i := by
          rw [Finset.sum_eq_single i]
          · rw [map_smul, wordCoeff_lyndon_diag i, smul_eq_mul, mul_one]
          · intro m _ hm
            rw [map_smul, smul_eq_mul]
            rcases lt_or_gt_of_ne hm with hmi | him
            · have hm_lt : m.1 < i.1 := Fin.lt_def.mp hmi
              rw [ih m hm_lt, zero_mul]
            · rw [wordCoeff_lyndon_upper him, mul_zero]
          · intro hi'; exact absurd (Finset.mem_univ i) hi'
        linarith
  intro i
  exact hzero 294 i i.isLt

/-- Cumulative 5-step free Lie submodule inside `FreeLieAlgebra ℝ (Fin 4)`. -/
def fiveStepFreeLieSubmodule : Submodule ℝ (FreeLieAlgebra ℝ (Fin 4)) :=
  Submodule.span ℝ (Set.range lyndonFreeLie4)

instance : Module.Finite ℝ fiveStepFreeLieSubmodule :=
  Module.Finite.of_basis (Module.Basis.span lyndonFreeLie4_linearIndependent)

/-- Grade-1..5 submodules inside `FreeLieAlgebra ℝ (Fin 4)` matching `[4, 6, 20, 60, 204]`. -/
def freeLie4Deg1Submodule : Submodule ℝ (FreeLieAlgebra ℝ (Fin 4)) :=
  Submodule.span ℝ (Set.range fun k : Fin 4 => lyndonFreeLie4 ⟨k.1, by omega⟩)

def freeLie4Deg2Submodule : Submodule ℝ (FreeLieAlgebra ℝ (Fin 4)) :=
  Submodule.span ℝ (Set.range fun k : Fin 6 => lyndonFreeLie4 ⟨4 + k.1, by omega⟩)

def freeLie4Deg3Submodule : Submodule ℝ (FreeLieAlgebra ℝ (Fin 4)) :=
  Submodule.span ℝ (Set.range fun k : Fin 20 => lyndonFreeLie4 ⟨10 + k.1, by omega⟩)

def freeLie4Deg4Submodule : Submodule ℝ (FreeLieAlgebra ℝ (Fin 4)) :=
  Submodule.span ℝ (Set.range fun k : Fin 60 => lyndonFreeLie4 ⟨30 + k.1, by omega⟩)

def freeLie4Deg5Submodule : Submodule ℝ (FreeLieAlgebra ℝ (Fin 4)) :=
  Submodule.span ℝ (Set.range fun k : Fin 204 => lyndonFreeLie4 ⟨90 + k.1, by omega⟩)

/-- Exact degree verification of the 5 grade slices inside `lyndonWord294` and exact `finrank`s
`[4, 6, 20, 60, 204]` (sum `= 294`) matching `witt_rank4_dimensions`. -/
theorem freeLie4_grade_finranks :
    (∀ k : Fin 4, (lyndonWord294 ⟨k.1, by omega⟩).length = 1) ∧
    (∀ k : Fin 6, (lyndonWord294 ⟨4 + k.1, by omega⟩).length = 2) ∧
    (∀ k : Fin 20, (lyndonWord294 ⟨10 + k.1, by omega⟩).length = 3) ∧
    (∀ k : Fin 60, (lyndonWord294 ⟨30 + k.1, by omega⟩).length = 4) ∧
    (∀ k : Fin 204, (lyndonWord294 ⟨90 + k.1, by omega⟩).length = 5) ∧
    Module.finrank ℝ freeLie4Deg1Submodule = 4 ∧
    Module.finrank ℝ freeLie4Deg2Submodule = 6 ∧
    Module.finrank ℝ freeLie4Deg3Submodule = 20 ∧
    Module.finrank ℝ freeLie4Deg4Submodule = 60 ∧
    Module.finrank ℝ freeLie4Deg5Submodule = 204 ∧
    Module.finrank ℝ fiveStepFreeLieSubmodule = 294 := by
  have hm := lyndon_master_bool_checks
  have hc := lyndonWordsOfDeg_counts
  have hlist_eq : lyndonList294 =
      lyndonWordsOfDeg 1 ++ (lyndonWordsOfDeg 2 ++
        (lyndonWordsOfDeg 3 ++ (lyndonWordsOfDeg 4 ++ lyndonWordsOfDeg 5))) := by
    simp [lyndonList294]
  have hwlen1 : ∀ w ∈ lyndonWordsOfDeg 1, w.length = 1 := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hm.2.2.2.2.2.2.2.2.1 w hw)
  have hwlen2 : ∀ w ∈ lyndonWordsOfDeg 2, w.length = 2 := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hm.2.2.2.2.2.2.2.2.2.1 w hw)
  have hwlen3 : ∀ w ∈ lyndonWordsOfDeg 3, w.length = 3 := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hm.2.2.2.2.2.2.2.2.2.2.1 w hw)
  have hwlen4 : ∀ w ∈ lyndonWordsOfDeg 4, w.length = 4 := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hm.2.2.2.2.2.2.2.2.2.2.2.1 w hw)
  have hwlen5 : ∀ w ∈ lyndonWordsOfDeg 5, w.length = 5 := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hm.2.2.2.2.2.2.2.2.2.2.2.2.1 w hw)
  have hd1 : ∀ k : Fin 4, (lyndonWord294 ⟨k.1, by omega⟩).length = 1 := by
    intro k
    have hk : k.1 < (lyndonWordsOfDeg 1).length := by rw [hc.1]; exact k.isLt
    change (lyndonList294.getD k.1 []).length = 1
    rw [hlist_eq, getD_append_left (lyndonWordsOfDeg 1) _ [] hk]
    exact hwlen1 _ (getD_mem_of_lt (lyndonWordsOfDeg 1) [] hk)
  have hd2 : ∀ k : Fin 6, (lyndonWord294 ⟨4 + k.1, by omega⟩).length = 2 := by
    intro k
    have hk : k.1 < (lyndonWordsOfDeg 2).length := by rw [hc.2.1]; exact k.isLt
    change (lyndonList294.getD (4 + k.1) []).length = 2
    rw [hlist_eq, show 4 + k.1 = (lyndonWordsOfDeg 1).length + k.1 by rw [hc.1],
      getD_append_right (lyndonWordsOfDeg 1), getD_append_left (lyndonWordsOfDeg 2) _ [] hk]
    exact hwlen2 _ (getD_mem_of_lt (lyndonWordsOfDeg 2) [] hk)
  have hd3 : ∀ k : Fin 20, (lyndonWord294 ⟨10 + k.1, by omega⟩).length = 3 := by
    intro k
    have hk : k.1 < (lyndonWordsOfDeg 3).length := by rw [hc.2.2.1]; exact k.isLt
    change (lyndonList294.getD (10 + k.1) []).length = 3
    rw [hlist_eq, show 10 + k.1 = (lyndonWordsOfDeg 1).length + ((lyndonWordsOfDeg 2).length + k.1) by
        rw [hc.1, hc.2.1]; omega,
      getD_append_right (lyndonWordsOfDeg 1), getD_append_right (lyndonWordsOfDeg 2),
      getD_append_left (lyndonWordsOfDeg 3) _ [] hk]
    exact hwlen3 _ (getD_mem_of_lt (lyndonWordsOfDeg 3) [] hk)
  have hd4 : ∀ k : Fin 60, (lyndonWord294 ⟨30 + k.1, by omega⟩).length = 4 := by
    intro k
    have hk : k.1 < (lyndonWordsOfDeg 4).length := by rw [hc.2.2.2.1]; exact k.isLt
    change (lyndonList294.getD (30 + k.1) []).length = 4
    rw [hlist_eq, show 30 + k.1 = (lyndonWordsOfDeg 1).length +
        ((lyndonWordsOfDeg 2).length + ((lyndonWordsOfDeg 3).length + k.1)) by
        rw [hc.1, hc.2.1, hc.2.2.1]; omega,
      getD_append_right (lyndonWordsOfDeg 1), getD_append_right (lyndonWordsOfDeg 2),
      getD_append_right (lyndonWordsOfDeg 3), getD_append_left (lyndonWordsOfDeg 4) _ [] hk]
    exact hwlen4 _ (getD_mem_of_lt (lyndonWordsOfDeg 4) [] hk)
  have hd5 : ∀ k : Fin 204, (lyndonWord294 ⟨90 + k.1, by omega⟩).length = 5 := by
    intro k
    have hk : k.1 < (lyndonWordsOfDeg 5).length := by rw [hc.2.2.2.2.1]; exact k.isLt
    change (lyndonList294.getD (90 + k.1) []).length = 5
    rw [hlist_eq, show 90 + k.1 = (lyndonWordsOfDeg 1).length +
        ((lyndonWordsOfDeg 2).length + ((lyndonWordsOfDeg 3).length +
          ((lyndonWordsOfDeg 4).length + k.1))) by
        rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1]; omega,
      getD_append_right (lyndonWordsOfDeg 1), getD_append_right (lyndonWordsOfDeg 2),
      getD_append_right (lyndonWordsOfDeg 3), getD_append_right (lyndonWordsOfDeg 4)]
    exact hwlen5 _ (getD_mem_of_lt (lyndonWordsOfDeg 5) [] hk)
  have hf1 : Module.finrank ℝ freeLie4Deg1Submodule = 4 := by
    have hinj : Function.Injective (fun k : Fin 4 => (⟨k.1, by omega⟩ : Fin 294)) := by
      intro a b h; simp only [Fin.ext_iff] at h ⊢; omega
    change Module.finrank ℝ (Submodule.span ℝ (Set.range (lyndonFreeLie4 ∘
      fun k : Fin 4 => (⟨k.1, by omega⟩ : Fin 294)))) = 4
    rw [finrank_span_eq_card (lyndonFreeLie4_linearIndependent.comp _ hinj), Fintype.card_fin]
  have hf2 : Module.finrank ℝ freeLie4Deg2Submodule = 6 := by
    have hinj : Function.Injective (fun k : Fin 6 => (⟨4 + k.1, by omega⟩ : Fin 294)) := by
      intro a b h; simp only [Fin.ext_iff] at h ⊢; omega
    change Module.finrank ℝ (Submodule.span ℝ (Set.range (lyndonFreeLie4 ∘
      fun k : Fin 6 => (⟨4 + k.1, by omega⟩ : Fin 294)))) = 6
    rw [finrank_span_eq_card (lyndonFreeLie4_linearIndependent.comp _ hinj), Fintype.card_fin]
  have hf3 : Module.finrank ℝ freeLie4Deg3Submodule = 20 := by
    have hinj : Function.Injective (fun k : Fin 20 => (⟨10 + k.1, by omega⟩ : Fin 294)) := by
      intro a b h; simp only [Fin.ext_iff] at h ⊢; omega
    change Module.finrank ℝ (Submodule.span ℝ (Set.range (lyndonFreeLie4 ∘
      fun k : Fin 20 => (⟨10 + k.1, by omega⟩ : Fin 294)))) = 20
    rw [finrank_span_eq_card (lyndonFreeLie4_linearIndependent.comp _ hinj), Fintype.card_fin]
  have hf4 : Module.finrank ℝ freeLie4Deg4Submodule = 60 := by
    have hinj : Function.Injective (fun k : Fin 60 => (⟨30 + k.1, by omega⟩ : Fin 294)) := by
      intro a b h; simp only [Fin.ext_iff] at h ⊢; omega
    change Module.finrank ℝ (Submodule.span ℝ (Set.range (lyndonFreeLie4 ∘
      fun k : Fin 60 => (⟨30 + k.1, by omega⟩ : Fin 294)))) = 60
    rw [finrank_span_eq_card (lyndonFreeLie4_linearIndependent.comp _ hinj), Fintype.card_fin]
  have hf5 : Module.finrank ℝ freeLie4Deg5Submodule = 204 := by
    have hinj : Function.Injective (fun k : Fin 204 => (⟨90 + k.1, by omega⟩ : Fin 294)) := by
      intro a b h; simp only [Fin.ext_iff] at h ⊢; omega
    change Module.finrank ℝ (Submodule.span ℝ (Set.range (lyndonFreeLie4 ∘
      fun k : Fin 204 => (⟨90 + k.1, by omega⟩ : Fin 294)))) = 204
    rw [finrank_span_eq_card (lyndonFreeLie4_linearIndependent.comp _ hinj), Fintype.card_fin]
  have hft : Module.finrank ℝ fiveStepFreeLieSubmodule = 294 := by
    unfold fiveStepFreeLieSubmodule
    rw [finrank_span_eq_card lyndonFreeLie4_linearIndependent, Fintype.card_fin]
  exact ⟨hd1, hd2, hd3, hd4, hd5, hf1, hf2, hf3, hf4, hf5, hft⟩

/-- **Universal `FreeLieAlgebra.lift` Non-Injectivity & Syzygy Ideal Lower Bound**:
For EVERY generator map `f : Fin 4 → M₁₆(ℝ)`, the canonical Lie algebra homomorphism
`FreeLieAlgebra.lift ℝ f : FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ M₁₆(ℝ)` is non-injective, has a nontrivial
Lie ideal kernel (`ker ≠ ⊥`), and its 5-step truncation has syzygy kernel of dimension at least
`294 - 256 = 38`. -/
theorem freeLieAlgebra4_lift_mat16_not_injective_and_syzygy_ideal
    (f : Fin 4 → Matrix Krein16Idx Krein16Idx ℝ) :
    let Φ : FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ Matrix Krein16Idx Krein16Idx ℝ := FreeLieAlgebra.lift ℝ f
    let res : fiveStepFreeLieSubmodule →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ :=
      Φ.toLinearMap.comp fiveStepFreeLieSubmodule.subtype
    ¬ Function.Injective Φ ∧ Φ.ker ≠ ⊥ ∧ 38 ≤ Module.finrank ℝ (LinearMap.ker res) := by
  intro Φ res
  have hlt : Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) <
      Module.finrank ℝ fiveStepFreeLieSubmodule := by
    rw [finrank_mat16, freeLie4_grade_finranks.2.2.2.2.2.2.2.2.2.2]
    omega
  have hres_ker_ne : LinearMap.ker res ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨v, hv_ker, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hres_ker_ne
  have hv1_ne : (v : FreeLieAlgebra ℝ (Fin 4)) ≠ 0 := by
    intro hv0
    apply hv_ne
    exact Subtype.ext hv0
  have hv_phi : Φ (v : FreeLieAlgebra ℝ (Fin 4)) = 0 := hv_ker
  have hnotinj : ¬ Function.Injective Φ := by
    intro hinj
    apply hv1_ne
    apply hinj
    rw [hv_phi, _root_.map_zero]
  have hker_ne : Φ.ker ≠ ⊥ := by
    intro hbot
    apply hv1_ne
    have hmem : (v : FreeLieAlgebra ℝ (Fin 4)) ∈ Φ.ker := hv_phi
    rw [hbot] at hmem
    exact hmem
  have hrn := res.finrank_range_add_finrank_ker
  have hrange_le : Module.finrank ℝ (LinearMap.range res) ≤
      Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) := Submodule.finrank_le _
  rw [freeLie4_grade_finranks.2.2.2.2.2.2.2.2.2.2] at hrn
  rw [finrank_mat16] at hrange_le
  exact ⟨hnotinj, hker_ne, by omega⟩

/-- The four positive Chevalley generators `(X₁, X₂, X₃, X₄)` of `g_{2(2)} ⊂ M₁₆(ℝ)`. -/
def g2ChevalleyX : Fin 4 → Matrix Krein16Idx Krein16Idx ℝ
  | 0 => g2X1
  | 1 => g2X2
  | 2 => g2X3
  | 3 => g2X4

/-- Canonical 5-element basis `[Z_{+2}, X₁, X₂, X₃, X₄]` of the 5D positive nilradical `n₊ ⊂ g_{2(2)}`. -/
def g2PosNilBasis : Fin 5 → Matrix Krein16Idx Krein16Idx ℝ
  | 0 => g2Zpos2
  | 1 => g2X1
  | 2 => g2X2
  | 3 => g2X3
  | 4 => g2X4

/-- Five-dimensional positive nilradical submodule `n₊ = span{Z_{+2}, X₁, X₂, X₃, X₄} ⊂ M₁₆(ℝ)`. -/
def g2PosNilSubmodule : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ (Set.range g2PosNilBasis)

private lemma g2PosNilBasis_linearIndependent : LinearIndependent ℝ g2PosNilBasis := by
  have heq : g2PosNilBasis = g2Basis ∘ fun k : Fin 5 => ⟨k.1, by omega⟩ := by
    ext k i j
    fin_cases k <;> rfl
  have hinj : Function.Injective (fun k : Fin 5 => (⟨k.1, by omega⟩ : Fin 14)) := by
    intro a b h; simp only [Fin.ext_iff] at h ⊢; omega
  rw [heq]
  exact g2Basis_linearIndependent.comp _ hinj

private lemma g2PosNilSubmodule_lie_closed {A B : Matrix Krein16Idx Krein16Idx ℝ}
    (hA : A ∈ g2PosNilSubmodule) (hB : B ∈ g2PosNilSubmodule) :
    A * B - B * A ∈ g2PosNilSubmodule := by
  have hmem : ∀ k : Fin 5, g2PosNilBasis k ∈ g2PosNilSubmodule :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  have hbas : ∀ i j : Fin 5, g2PosNilBasis i * g2PosNilBasis j - g2PosNilBasis j * g2PosNilBasis i ∈
      g2PosNilSubmodule := by
    intro i j
    have hgc := g2_grade1_contact_and_serre_syzygies
    have htc := g2_top_grade_central_commutativity.1
    fin_cases i <;> fin_cases j <;> dsimp only [g2PosNilBasis]
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [htc.1]; exact Submodule.zero_mem _
    · rw [htc.2.1]; exact Submodule.zero_mem _
    · rw [htc.2.2.1]; exact Submodule.zero_mem _
    · rw [htc.2.2.2]; exact Submodule.zero_mem _
    · rw [← neg_sub, htc.1, neg_zero]; exact Submodule.zero_mem _
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [hgc.1]; exact hmem 0
    · rw [hgc.2.2.1]; exact Submodule.zero_mem _
    · rw [hgc.2.2.2.1]; exact Submodule.zero_mem _
    · rw [← neg_sub, htc.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.1]; exact Submodule.neg_mem _ (hmem 0)
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [hgc.2.2.2.2.1]; exact Submodule.zero_mem _
    · rw [hgc.2.2.2.2.2.1]; exact Submodule.zero_mem _
    · rw [← neg_sub, htc.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [hgc.2.1]; exact Submodule.smul_mem _ _ (hmem 0)
    · rw [← neg_sub, htc.2.2.2, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.2.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.1]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem 0))
    · rw [sub_self]; exact Submodule.zero_mem _
  have hfix : ∀ B' ∈ g2PosNilSubmodule, ∀ A' ∈ g2PosNilSubmodule, A' * B' - B' * A' ∈ g2PosNilSubmodule := by
    intro B' hB' A' hA'
    refine Submodule.span_induction (hx := hA') ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩
      refine Submodule.span_induction (hx := hB') ?_ ?_ ?_ ?_
      · rintro _ ⟨j, rfl⟩; exact hbas i j
      · rw [Matrix.mul_zero, Matrix.zero_mul, sub_self]; exact Submodule.zero_mem _
      · intro X Y _ _ hX hY
        have hlin : g2PosNilBasis i * (X + Y) - (X + Y) * g2PosNilBasis i =
            (g2PosNilBasis i * X - X * g2PosNilBasis i) + (g2PosNilBasis i * Y - Y * g2PosNilBasis i) := by
          rw [Matrix.mul_add, Matrix.add_mul]; abel
        rw [hlin]; exact Submodule.add_mem _ hX hY
      · intro r X _ hX
        have hlin : g2PosNilBasis i * (r • X) - (r • X) * g2PosNilBasis i =
            r • (g2PosNilBasis i * X - X * g2PosNilBasis i) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        rw [hlin]; exact Submodule.smul_mem _ r hX
    · rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]; exact Submodule.zero_mem _
    · intro X Y _ _ hX hY
      have hlin : (X + Y) * B' - B' * (X + Y) = (X * B' - B' * X) + (Y * B' - B' * Y) := by
        rw [Matrix.add_mul, Matrix.mul_add]; abel
      rw [hlin]; exact Submodule.add_mem _ hX hY
    · intro r X _ hX
      have hlin : (r • X) * B' - B' * (r • X) = r • (X * B' - B' * X) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      rw [hlin]; exact Submodule.smul_mem _ r hX
  exact hfix B hB A hA

/-- Five-dimensional positive nilradical Lie subalgebra `n₊ ≤ M₁₆(ℝ)`. -/
def g2PosNilLieSubalgebra : LieSubalgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  { g2PosNilSubmodule with
    lie_mem' := fun hA hB => g2PosNilSubmodule_lie_closed hA hB }

/-- The central grade-`+2` line inside the positive nilradical. -/
def g2PosNilCenterLine : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ ({g2Zpos2} : Set (Matrix Krein16Idx Krein16Idx ℝ))

/-- Every bracket of two elements of the concrete positive nilradical lands in
its one-dimensional grade-`+2` line. This upgrades the displayed generator
table to a class-two statement on the whole five-dimensional carrier. -/
theorem g2PosNilSubmodule_bracket_mem_centerLine
    {A B : Matrix Krein16Idx Krein16Idx ℝ}
    (hA : A ∈ g2PosNilSubmodule) (hB : B ∈ g2PosNilSubmodule) :
    A * B - B * A ∈ g2PosNilCenterLine := by
  have hz : g2Zpos2 ∈ g2PosNilCenterLine := Submodule.subset_span (by simp)
  have hbas : ∀ i j : Fin 5,
      g2PosNilBasis i * g2PosNilBasis j - g2PosNilBasis j * g2PosNilBasis i ∈
        g2PosNilCenterLine := by
    intro i j
    have hgc := g2_grade1_contact_and_serre_syzygies
    have htc := g2_top_grade_central_commutativity.1
    fin_cases i <;> fin_cases j <;> dsimp only [g2PosNilBasis]
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [htc.1]; exact Submodule.zero_mem _
    · rw [htc.2.1]; exact Submodule.zero_mem _
    · rw [htc.2.2.1]; exact Submodule.zero_mem _
    · rw [htc.2.2.2]; exact Submodule.zero_mem _
    · rw [← neg_sub, htc.1, neg_zero]; exact Submodule.zero_mem _
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [hgc.1]; exact hz
    · rw [hgc.2.2.1]; exact Submodule.zero_mem _
    · rw [hgc.2.2.2.1]; exact Submodule.zero_mem _
    · rw [← neg_sub, htc.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.1]; exact Submodule.neg_mem _ hz
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [hgc.2.2.2.2.1]; exact Submodule.zero_mem _
    · rw [hgc.2.2.2.2.2.1]; exact Submodule.zero_mem _
    · rw [← neg_sub, htc.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [sub_self]; exact Submodule.zero_mem _
    · rw [hgc.2.1]; exact Submodule.smul_mem _ _ hz
    · rw [← neg_sub, htc.2.2.2, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.2.2.2.2.1, neg_zero]; exact Submodule.zero_mem _
    · rw [← neg_sub, hgc.2.1]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hz)
    · rw [sub_self]; exact Submodule.zero_mem _
  have hfix : ∀ A' ∈ g2PosNilSubmodule, ∀ B' ∈ g2PosNilSubmodule,
      A' * B' - B' * A' ∈ g2PosNilCenterLine := by
    intro A' hA' B' hB'
    refine Submodule.span_induction (hx := hA') ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩
      refine Submodule.span_induction (hx := hB') ?_ ?_ ?_ ?_
      · rintro _ ⟨j, rfl⟩; exact hbas i j
      · rw [Matrix.mul_zero, Matrix.zero_mul, sub_self]; exact Submodule.zero_mem _
      · intro X Y _ _ hX hY
        have hlin : g2PosNilBasis i * (X + Y) - (X + Y) * g2PosNilBasis i =
            (g2PosNilBasis i * X - X * g2PosNilBasis i) +
              (g2PosNilBasis i * Y - Y * g2PosNilBasis i) := by
          rw [Matrix.mul_add, Matrix.add_mul]; abel
        rw [hlin]; exact Submodule.add_mem _ hX hY
      · intro r X _ hX
        have hlin : g2PosNilBasis i * (r • X) - (r • X) * g2PosNilBasis i =
            r • (g2PosNilBasis i * X - X * g2PosNilBasis i) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        rw [hlin]; exact Submodule.smul_mem _ r hX
    · rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]; exact Submodule.zero_mem _
    · intro X Y _ _ hX hY
      have hlin : (X + Y) * B' - B' * (X + Y) =
          (X * B' - B' * X) + (Y * B' - B' * Y) := by
        rw [Matrix.add_mul, Matrix.mul_add]; abel
      rw [hlin]; exact Submodule.add_mem _ hX hY
    · intro r X _ hX
      have hlin : (r • X) * B' - B' * (r • X) = r • (X * B' - B' * X) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      rw [hlin]; exact Submodule.smul_mem _ r hX
  exact hfix A hA B hB

/-- The grade-`+2` line is central in the concrete positive nilradical. -/
theorem g2PosNilCenterLine_bracket_eq_zero
    {Z B : Matrix Krein16Idx Krein16Idx ℝ}
    (hZ : Z ∈ g2PosNilCenterLine) (hB : B ∈ g2PosNilSubmodule) :
    Z * B - B * Z = 0 := by
  have hbas : ∀ k : Fin 5, g2Zpos2 * g2PosNilBasis k -
      g2PosNilBasis k * g2Zpos2 = 0 := by
    intro k
    have htc := g2_top_grade_central_commutativity.1
    fin_cases k <;> dsimp only [g2PosNilBasis]
    · rw [sub_self]
    · exact htc.1
    · exact htc.2.1
    · exact htc.2.2.1
    · exact htc.2.2.2
  refine Submodule.span_induction (hx := hZ) ?_ ?_ ?_ ?_
  · rintro _ rfl
    refine Submodule.span_induction (hx := hB) ?_ ?_ ?_ ?_
    · rintro _ ⟨k, rfl⟩; exact hbas k
    · simp
    · intro X Y _ _ hX hY
      rw [Matrix.mul_add, Matrix.add_mul]
      have hlin : g2Zpos2 * X + g2Zpos2 * Y - (X * g2Zpos2 + Y * g2Zpos2) =
          (g2Zpos2 * X - X * g2Zpos2) + (g2Zpos2 * Y - Y * g2Zpos2) := by abel
      rw [hlin, hX, hY, add_zero]
    · intro r X _ hX
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hX, smul_zero]
  · simp
  · intro X Y _ _ hX hY
    rw [Matrix.add_mul, Matrix.mul_add]
    have hlin : X * B + Y * B - (B * X + B * Y) =
        (X * B - B * X) + (Y * B - B * Y) := by abel
    rw [hlin, hX, hY, zero_add]
  · intro r X _ hX
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, hX, smul_zero]

/-- Every iterated bracket of length three in the concrete positive
nilradical vanishes: its inner bracket lies in the grade-`+2` line, which is
central. -/
theorem g2PosNilSubmodule_bracket_bracket_eq_zero
    {A B C : Matrix Krein16Idx Krein16Idx ℝ}
    (hA : A ∈ g2PosNilSubmodule) (hB : B ∈ g2PosNilSubmodule)
    (hC : C ∈ g2PosNilSubmodule) :
    (A * B - B * A) * C - C * (A * B - B * A) = 0 := by
  exact g2PosNilCenterLine_bracket_eq_zero
    (g2PosNilSubmodule_bracket_mem_centerLine hA hB) hC

/-- The positive nilradical, as the declared Lie-subalgebra carrier, is
two-step nilpotent: every triple Lie bracket vanishes. -/
theorem g2PosNilLieSubalgebra_twoStep_nilpotent
    (x y z : g2PosNilLieSubalgebra) : ⁅⁅x, y⁆, z⁆ = 0 := by
  apply Subtype.ext
  exact g2PosNilSubmodule_bracket_bracket_eq_zero x.2 y.2 z.2

/-- The free Lie algebra on the four grade-`+1` generators, with codomain the
actual five-dimensional positive nilradical rather than the ambient matrix
algebra. -/
def g2PosNilFreeLieHom : FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ g2PosNilLieSubalgebra :=
  FreeLieAlgebra.lift ℝ (fun i =>
    ⟨g2ChevalleyX i, by
      fin_cases i
      · exact Submodule.subset_span ⟨1, rfl⟩
      · exact Submodule.subset_span ⟨2, rfl⟩
      · exact Submodule.subset_span ⟨3, rfl⟩
      · exact Submodule.subset_span ⟨4, rfl⟩⟩)

/-- The image of every non-leaf bracket tree lies in the central line. -/
theorem g2PosNilFreeLieHom_eval_node_mem_centerLine (l r : LieTree4) :
    (g2PosNilFreeLieHom (evalFreeLie (.node l r)) :
      Matrix Krein16Idx Krein16Idx ℝ) ∈ g2PosNilCenterLine := by
  change (g2PosNilFreeLieHom ⁅evalFreeLie l, evalFreeLie r⁆ :
      Matrix Krein16Idx Krein16Idx ℝ) ∈ g2PosNilCenterLine
  rw [LieHom.map_lie]
  exact g2PosNilSubmodule_bracket_mem_centerLine
    (g2PosNilFreeLieHom (evalFreeLie l)).2
    (g2PosNilFreeLieHom (evalFreeLie r)).2

/-- Every bracket tree with at least three leaves evaluates to zero in the
concrete positive nilradical. This is the tree-level consequence of the
verified class-two bracket law, and applies uniformly to all higher Lie words. -/
theorem g2PosNilFreeLieHom_eval_tree_eq_zero_of_leafCount
    (t : LieTree4) (ht : 3 ≤ t.leafCount) :
    g2PosNilFreeLieHom (evalFreeLie t) = 0 := by
  induction t with
  | leaf a => simp [LieTree4.leafCount] at ht
  | node l r ihl ihr =>
    cases l with
    | leaf a =>
      cases r with
      | leaf b => simp [LieTree4.leafCount] at ht
      | node r₁ r₂ =>
        change g2PosNilFreeLieHom ⁅evalFreeLie (.leaf a),
            evalFreeLie (.node r₁ r₂)⁆ = 0
        rw [LieHom.map_lie]
        apply Subtype.ext
        rw [LieSubalgebra.coe_bracket g2PosNilLieSubalgebra,
          LieRing.of_associative_ring_bracket]
        have hc := g2PosNilFreeLieHom_eval_node_mem_centerLine r₁ r₂
        have hz := g2PosNilCenterLine_bracket_eq_zero hc
          (g2PosNilFreeLieHom (evalFreeLie (.leaf a))).2
        have hskew :
            (g2PosNilFreeLieHom (evalFreeLie (.leaf a)) : Matrix Krein16Idx Krein16Idx ℝ) *
                (g2PosNilFreeLieHom (evalFreeLie (.node r₁ r₂)) : Matrix Krein16Idx Krein16Idx ℝ) -
              (g2PosNilFreeLieHom (evalFreeLie (.node r₁ r₂)) : Matrix Krein16Idx Krein16Idx ℝ) *
                (g2PosNilFreeLieHom (evalFreeLie (.leaf a)) : Matrix Krein16Idx Krein16Idx ℝ) = 0 := by
          rw [← neg_sub, hz, neg_zero]
        exact hskew
    | node l₁ l₂ =>
      change g2PosNilFreeLieHom ⁅evalFreeLie (.node l₁ l₂), evalFreeLie r⁆ = 0
      rw [LieHom.map_lie]
      apply Subtype.ext
      rw [LieSubalgebra.coe_bracket g2PosNilLieSubalgebra,
        LieRing.of_associative_ring_bracket]
      exact g2PosNilCenterLine_bracket_eq_zero
        (g2PosNilFreeLieHom_eval_node_mem_centerLine l₁ l₂)
        (g2PosNilFreeLieHom (evalFreeLie r)).2

/-- The already-certified degree blocks of the Lyndon basis imply that every
index from `10` onward has a word of length at least three. -/
theorem lyndonWord294_length_ge_three {i : Fin 294} (hi : 10 ≤ i.1) :
    3 ≤ (lyndonWord294 i).length := by
  rcases freeLie4_grade_finranks with ⟨_, _, hlen3, hlen4, hlen5, _, _, _, _, _, _⟩
  by_cases h30 : i.1 < 30
  · let k : Fin 20 := ⟨i.1 - 10, by omega⟩
    have hidx : (⟨10 + k.1, by omega⟩ : Fin 294) = i := by
      apply Fin.ext
      simp [k]
      omega
    rw [← hidx, hlen3 k]
  · by_cases h90 : i.1 < 90
    · let k : Fin 60 := ⟨i.1 - 30, by omega⟩
      have hidx : (⟨30 + k.1, by omega⟩ : Fin 294) = i := by
        apply Fin.ext
        simp [k]
        omega
      rw [← hidx, hlen4 k]
      omega
    · let k : Fin 204 := ⟨i.1 - 90, by omega⟩
      have hidx : (⟨90 + k.1, by omega⟩ : Fin 294) = i := by
        apply Fin.ext
        simp [k]
        omega
      rw [← hidx, hlen5 k]
      omega

/-- Every degree-3, degree-4, and degree-5 Lyndon basis vector is killed by
the concrete operator evaluation map. This is the finite-basis consequence of
the binary-tree vanishing theorem and the certified Lyndon degree blocks. -/
theorem g2PosNilFreeLieHom_lyndon_eq_zero_of_index_ge_ten
    {i : Fin 294} (hi : 10 ≤ i.1) :
    g2PosNilFreeLieHom (lyndonFreeLie4 i) = 0 := by
  unfold lyndonFreeLie4
  apply g2PosNilFreeLieHom_eval_tree_eq_zero_of_leafCount
  rw [lyndonTree294_leafCount_eq_wordLength]
  exact lyndonWord294_length_ge_three hi

/-- The four cross-root Lyndon brackets in degree two vanish under the
concrete Chevalley evaluation map. Together with the displayed Cartan-ratio
relation between indices 4 and 9, these are the five degree-two kernel
directions. -/
theorem g2PosNilFreeLieHom_zero_on_cross_degree2_lyndon :
    g2PosNilFreeLieHom (lyndonFreeLie4 5) = 0 ∧
    g2PosNilFreeLieHom (lyndonFreeLie4 6) = 0 ∧
    g2PosNilFreeLieHom (lyndonFreeLie4 7) = 0 ∧
    g2PosNilFreeLieHom (lyndonFreeLie4 8) = 0 := by
  have ht5 : lyndonTree294 5 = LieTree4.node (LieTree4.leaf 0) (LieTree4.leaf 2) := by decide
  have ht6 : lyndonTree294 6 = LieTree4.node (LieTree4.leaf 0) (LieTree4.leaf 3) := by decide
  have ht7 : lyndonTree294 7 = LieTree4.node (LieTree4.leaf 1) (LieTree4.leaf 2) := by decide
  have ht8 : lyndonTree294 8 = LieTree4.node (LieTree4.leaf 1) (LieTree4.leaf 3) := by decide
  have heval (i j : Fin 4) (h : g2ChevalleyX i * g2ChevalleyX j -
      g2ChevalleyX j * g2ChevalleyX i = 0) :
      g2PosNilFreeLieHom (⁅FreeLieAlgebra.of ℝ i, FreeLieAlgebra.of ℝ j⁆) = 0 := by
    simp only [g2PosNilFreeLieHom, LieHom.map_lie,
      FreeLieAlgebra.lift_of_apply]
    apply Subtype.ext
    change g2ChevalleyX i * g2ChevalleyX j - g2ChevalleyX j * g2ChevalleyX i = 0
    exact h
  constructor
  · change g2PosNilFreeLieHom (evalFreeLie (lyndonTree294 5)) = 0
    rw [ht5]
    simpa [evalFreeLie, lyndonFreeLie4, g2PosNilFreeLieHom,
      FreeLieAlgebra.lift_of_apply] using
      heval 0 2 g2_grade1_contact_and_serre_syzygies.2.2.1
  constructor
  · change g2PosNilFreeLieHom (evalFreeLie (lyndonTree294 6)) = 0
    rw [ht6]
    simpa [evalFreeLie, lyndonFreeLie4, g2PosNilFreeLieHom,
      FreeLieAlgebra.lift_of_apply] using
      heval 0 3 g2_grade1_contact_and_serre_syzygies.2.2.2.1
  constructor
  · change g2PosNilFreeLieHom (evalFreeLie (lyndonTree294 7)) = 0
    rw [ht7]
    simpa [evalFreeLie, lyndonFreeLie4, g2PosNilFreeLieHom,
      FreeLieAlgebra.lift_of_apply] using
      heval 1 2 g2_grade1_contact_and_serre_syzygies.2.2.2.2.1
  · change g2PosNilFreeLieHom (evalFreeLie (lyndonTree294 8)) = 0
    rw [ht8]
    simpa [evalFreeLie, lyndonFreeLie4, g2PosNilFreeLieHom,
      FreeLieAlgebra.lift_of_apply] using
      heval 1 3 g2_grade1_contact_and_serre_syzygies.2.2.2.2.2.1

/-- The degree-3 Lyndon component is contained in the concrete evaluation
kernel. -/
theorem g2PosNilFreeLieHom_zero_on_freeLie4Deg3
    (x : freeLie4Deg3Submodule) :
    g2PosNilFreeLieHom (x : FreeLieAlgebra ℝ (Fin 4)) = 0 := by
  refine Submodule.span_induction (hx := x.2) ?_ ?_ ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact g2PosNilFreeLieHom_lyndon_eq_zero_of_index_ge_ten (by change 10 ≤ 10 + k.1; omega)
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, ha, smul_zero]

/-- The degree-4 Lyndon component is contained in the concrete evaluation
kernel. -/
theorem g2PosNilFreeLieHom_zero_on_freeLie4Deg4
    (x : freeLie4Deg4Submodule) :
    g2PosNilFreeLieHom (x : FreeLieAlgebra ℝ (Fin 4)) = 0 := by
  refine Submodule.span_induction (hx := x.2) ?_ ?_ ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact g2PosNilFreeLieHom_lyndon_eq_zero_of_index_ge_ten (by change 10 ≤ 30 + k.1; omega)
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, ha, smul_zero]

/-- The degree-5 Lyndon component is contained in the concrete evaluation
kernel. -/
theorem g2PosNilFreeLieHom_zero_on_freeLie4Deg5
    (x : freeLie4Deg5Submodule) :
    g2PosNilFreeLieHom (x : FreeLieAlgebra ℝ (Fin 4)) = 0 := by
  refine Submodule.span_induction (hx := x.2) ?_ ?_ ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact g2PosNilFreeLieHom_lyndon_eq_zero_of_index_ge_ten (by change 10 ≤ 90 + k.1; omega)
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, ha, smul_zero]

/-- Including the nilradical-valued free-Lie map into matrices recovers the
original operator evaluation map on every free Lie word. -/
theorem g2PosNilFreeLieHom_comp_inclusion :
    g2PosNilLieSubalgebra.incl.comp g2PosNilFreeLieHom =
      FreeLieAlgebra.lift ℝ g2ChevalleyX := by
  apply FreeLieAlgebra.hom_ext
  intro i
  simp [g2PosNilFreeLieHom, FreeLieAlgebra.lift_of_apply, g2ChevalleyX]

/-- The concrete free-Lie map surjects onto the full positive nilradical:
the four root generators are images of free generators, and the central
grade-`+2` basis vector is their `[X₁, X₂]` bracket. -/
theorem g2PosNilFreeLieHom_surjective : Function.Surjective g2PosNilFreeLieHom := by
  intro y
  have hpre : ∀ x ∈ g2PosNilSubmodule, ∃ w : FreeLieAlgebra ℝ (Fin 4),
      (g2PosNilFreeLieHom w : Matrix Krein16Idx Krein16Idx ℝ) = x := by
    intro x hx
    refine Submodule.span_induction (mem := ?_) (zero := ?_) (add := ?_) (smul := ?_) hx
    · intro z hz
      rcases hz with ⟨k, rfl⟩
      fin_cases k
      · refine ⟨⁅FreeLieAlgebra.of ℝ (0 : Fin 4), FreeLieAlgebra.of ℝ (1 : Fin 4)⁆, ?_⟩
        change (g2PosNilLieSubalgebra.incl.comp g2PosNilFreeLieHom)
            ⁅FreeLieAlgebra.of ℝ (0 : Fin 4), FreeLieAlgebra.of ℝ (1 : Fin 4)⁆ = g2Zpos2
        rw [g2PosNilFreeLieHom_comp_inclusion, LieHom.map_lie,
          FreeLieAlgebra.lift_of_apply, FreeLieAlgebra.lift_of_apply]
        rw [LieRing.of_associative_ring_bracket]
        exact g2_grade1_contact_and_serre_syzygies.1
      · exact ⟨FreeLieAlgebra.of ℝ (0 : Fin 4), by simp [g2PosNilFreeLieHom, g2ChevalleyX,
          g2PosNilBasis]⟩
      · exact ⟨FreeLieAlgebra.of ℝ (1 : Fin 4), by simp [g2PosNilFreeLieHom, g2ChevalleyX,
          g2PosNilBasis]⟩
      · exact ⟨FreeLieAlgebra.of ℝ (2 : Fin 4), by simp [g2PosNilFreeLieHom, g2ChevalleyX,
          g2PosNilBasis]⟩
      · exact ⟨FreeLieAlgebra.of ℝ (3 : Fin 4), by simp [g2PosNilFreeLieHom, g2ChevalleyX,
          g2PosNilBasis]⟩
    · exact ⟨0, by simp⟩
    · rintro x z _ _ ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u + v, by simp [map_add, hu, hv]⟩
    · rintro a x _ ⟨u, hu⟩
      exact ⟨a • u, by simp [map_smul, hu]⟩
  obtain ⟨w, hw⟩ := hpre y.1 y.2
  exact ⟨w, Subtype.ext hw⟩

/-- The first isomorphism theorem identifies the quotient by the concrete
kernel with the actual image Lie subalgebra. The preceding surjectivity theorem
shows this image is the whole positive nilradical. -/
theorem g2PosNilFreeLieQuotient_equiv_range :
    Nonempty ((FreeLieAlgebra ℝ (Fin 4) ⧸ g2PosNilFreeLieHom.ker) ≃ₗ⁅ℝ⁆
      g2PosNilFreeLieHom.range) :=
  ⟨g2PosNilFreeLieHom.quotKerEquivRange⟩

/-- The quotient by the actual operator-evaluation kernel is Lie-isomorphic to
the five-dimensional matrix nilradical.  This composes the first isomorphism
theorem with the inclusion of the surjective map's range; it explicitly
identifies the two carriers rather than leaving the result at an abstract
range subtype. -/
noncomputable def g2PosNilFreeLieQuotientEquiv :
    (FreeLieAlgebra ℝ (Fin 4) ⧸ g2PosNilFreeLieHom.ker) ≃ₗ⁅ℝ⁆
      g2PosNilLieSubalgebra :=
  g2PosNilFreeLieHom.quotKerEquivRange.trans
    (LieEquiv.ofBijective g2PosNilFreeLieHom.range.incl
      ⟨(fun _ _ h => Subtype.ext (by simpa only [LieSubalgebra.coe_incl] using h)), by
        intro y
        obtain ⟨x, hx⟩ := g2PosNilFreeLieHom_surjective y
        exact ⟨⟨y, ⟨x, hx⟩⟩, rfl⟩⟩)

/-- The quotient equivalence followed by matrix inclusion is the original free
Lie evaluation map on quotient representatives. -/
theorem g2PosNilFreeLieQuotientEquiv_mk (x : FreeLieAlgebra ℝ (Fin 4)) :
    (g2PosNilFreeLieQuotientEquiv (Submodule.Quotient.mk x) :
      g2PosNilLieSubalgebra) = g2PosNilFreeLieHom x := by
  apply Subtype.ext
  rfl

/-- Explicit Chevalley–Serre relation `3 • [x₀, x₁] - [x₂, x₃]` inside `FreeLieAlgebra ℝ (Fin 4)`. -/
def serreRelFreeLie4 : FreeLieAlgebra ℝ (Fin 4) :=
  (3 : ℝ) • ⁅FreeLieAlgebra.of ℝ (0 : Fin 4), FreeLieAlgebra.of ℝ (1 : Fin 4)⁆ -
    ⁅FreeLieAlgebra.of ℝ (2 : Fin 4), FreeLieAlgebra.of ℝ (3 : Fin 4)⁆

private lemma lyndonTrees_chevalley_ids :
    lyndonTree294 0 = LieTree4.leaf 0 ∧
    lyndonTree294 1 = LieTree4.leaf 1 ∧
    lyndonTree294 2 = LieTree4.leaf 2 ∧
    lyndonTree294 3 = LieTree4.leaf 3 ∧
    lyndonTree294 4 = LieTree4.node (LieTree4.leaf 0) (LieTree4.leaf 1) ∧
    lyndonTree294 9 = LieTree4.node (LieTree4.leaf 2) (LieTree4.leaf 3) := by
  have hm := lyndon_master_bool_checks.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact ⟨(treeEq_iff _ _).mp hm.1, (treeEq_iff _ _).mp hm.2.1, (treeEq_iff _ _).mp hm.2.2.1,
    (treeEq_iff _ _).mp hm.2.2.2.1, (treeEq_iff _ _).mp hm.2.2.2.2.1, (treeEq_iff _ _).mp hm.2.2.2.2.2⟩

private theorem serreRelFreeLie4_eq_lyndon :
    serreRelFreeLie4 = (3 : ℝ) • lyndonFreeLie4 4 + (-1 : ℝ) • lyndonFreeLie4 9 := by
  have hids := lyndonTrees_chevalley_ids
  have hl4 : lyndonFreeLie4 4 = ⁅FreeLieAlgebra.of ℝ (0 : Fin 4), FreeLieAlgebra.of ℝ (1 : Fin 4)⁆ := by
    unfold lyndonFreeLie4; rw [hids.2.2.2.2.1]; rfl
  have hl9 : lyndonFreeLie4 9 = ⁅FreeLieAlgebra.of ℝ (2 : Fin 4), FreeLieAlgebra.of ℝ (3 : Fin 4)⁆ := by
    unfold lyndonFreeLie4; rw [hids.2.2.2.2.2]; rfl
  unfold serreRelFreeLie4
  rw [hl4, hl9, neg_one_smul, sub_eq_add_neg]

private theorem serreRelFreeLie4_mem_fiveStep :
    serreRelFreeLie4 ∈ fiveStepFreeLieSubmodule := by
  rw [serreRelFreeLie4_eq_lyndon]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨9, rfl⟩))

/-- The displayed Serre-relation witness, viewed in the five-step source carrier. -/
def serreRelFiveStep : fiveStepFreeLieSubmodule :=
  ⟨serreRelFreeLie4, serreRelFreeLie4_mem_fiveStep⟩

/-- The proposed 289 kernel generators are ordered by their first nonzero
Lyndon coordinate: one degree-two Serre relation, the four cross-root
brackets, then all 284 degree-three-through-five Lyndon vectors. -/
def fiveStepKernelCoordinate (i : Fin 289) : Fin 294 :=
  if i.1 = 0 then 4 else if i.1 < 5 then ⟨i.1 + 4, by omega⟩
    else ⟨i.1 + 5, by omega⟩

/-- The canonical 289 candidate kernel vectors, represented in the actual
five-step free-Lie submodule. -/
noncomputable def fiveStepKernelGenerator (i : Fin 289) : fiveStepFreeLieSubmodule :=
  if _h : i.1 = 0 then serreRelFiveStep
  else ⟨lyndonFreeLie4 (fiveStepKernelCoordinate i),
    Submodule.subset_span ⟨fiveStepKernelCoordinate i, rfl⟩⟩

/-- The leading Lyndon coordinates of the candidate kernel family are strictly
increasing with the generator index. -/
theorem fiveStepKernelCoordinate_strict {i j : Fin 289} (hij : i < j) :
    fiveStepKernelCoordinate i < fiveStepKernelCoordinate j := by
  have hij' : i.1 < j.1 := Fin.lt_def.mp hij
  have hval (k : Fin 289) : (fiveStepKernelCoordinate k).1 =
      if k = 0 then 4 else if k.1 < 5 then k.1 + 4 else k.1 + 5 := by
    by_cases hk0 : k.1 = 0
    · have hk : k = 0 := Fin.ext hk0
      simp [fiveStepKernelCoordinate, hk]
    · have hkne : k ≠ 0 := fun hk => hk0 (congrArg Fin.val hk)
      by_cases hk5 : k.1 < 5
      · simp [fiveStepKernelCoordinate, hk0, hkne, hk5]
      · simp [fiveStepKernelCoordinate, hk0, hkne, hk5]
  apply Fin.lt_def.mpr
  rw [hval, hval]
  split_ifs <;> omega

/-- The first nonzero Lyndon coefficient of each proposed kernel generator is
nonzero: it is `3` for the Serre relation and `1` for every other vector. -/
theorem wordCoeff_fiveStepKernelGenerator_leading (i : Fin 289) :
    wordCoeffLinear (lyndonWord294 (fiveStepKernelCoordinate i))
      (fiveStepKernelGenerator i).1 = if i.1 = 0 then 3 else 1 := by
  by_cases hi0 : i.1 = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    change wordCoeffLinear (lyndonWord294 4) serreRelFreeLie4 = 3
    rw [serreRelFreeLie4_eq_lyndon, map_add, map_smul, map_smul,
      wordCoeff_lyndon_diag]
    rw [wordCoeff_lyndon_upper (by decide)]
    norm_num
  · simp [fiveStepKernelGenerator, hi0, wordCoeff_lyndon_diag]

/-- Later candidate generators have zero coefficient at an earlier
generator's leading Lyndon word (upper-triangularity of the Lyndon basis). -/
theorem wordCoeff_fiveStepKernelGenerator_upper {i j : Fin 289} (hij : i < j) :
    wordCoeffLinear (lyndonWord294 (fiveStepKernelCoordinate i))
      (fiveStepKernelGenerator j).1 = 0 := by
  have hij' : i.1 < j.1 := Fin.lt_def.mp hij
  have hj0 : j.1 ≠ 0 := by omega
  simp [fiveStepKernelGenerator, hj0,
    wordCoeff_lyndon_upper (fiveStepKernelCoordinate_strict hij)]

/-- The 289 candidate kernel generators are linearly independent. The proof
uses the triangular Lyndon coefficient functionals in increasing coordinate
order, with coefficient `3` at the Serre relation's pivot and `1` elsewhere. -/
theorem fiveStepKernelGenerator_linearIndependent :
    LinearIndependent ℝ fiveStepKernelGenerator := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : (∑ i : Fin 289, c i • (fiveStepKernelGenerator i).1) = 0 :=
    congrArg Subtype.val hc
  have hprefix : ∀ n : ℕ, ∀ i : Fin 289, i.1 < n → c i = 0 := by
    intro n
    induction n with
    | zero =>
        intro i hi
        omega
    | succ n ih =>
        intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hin | heq
        · exact ih i hin
        · have hi_eq : i = ⟨n, by omega⟩ := Fin.ext heq
          rw [hi_eq]
          let i0 : Fin 289 := ⟨n, by omega⟩
          let q := fiveStepKernelCoordinate i0
          have hcoeff := congrArg (wordCoeffLinear (lyndonWord294 q)) hsum
          rw [map_sum, _root_.map_zero] at hcoeff
          have hcoeff_sum :
              (∑ m : Fin 289,
                wordCoeffLinear (lyndonWord294 q)
                  (c m • (fiveStepKernelGenerator m).1)) =
                c i0 * (if n = 0 then (3 : ℝ) else 1) := by
            rw [Finset.sum_eq_single i0]
            · rw [map_smul, smul_eq_mul,
                wordCoeff_fiveStepKernelGenerator_leading]
            · intro m _ hmi
              rw [map_smul, smul_eq_mul]
              rcases lt_or_gt_of_ne hmi with hlt | hgt
              · have hm : m.1 < n := by
                  have hlt' := Fin.lt_def.mp hlt
                  simpa [i0] using hlt'
                rw [ih m hm, zero_mul]
              · have hgt' : i0 < m := Fin.lt_def.mpr hgt
                rw [wordCoeff_fiveStepKernelGenerator_upper hgt', mul_zero]
            · intro hi'
              exact False.elim (hi' (Finset.mem_univ i0))
          rw [hcoeff_sum] at hcoeff
          have hlead_ne : (if n = 0 then (3 : ℝ) else 1) ≠ 0 := by
            split_ifs <;> norm_num
          have hprod : c i0 * (if n = 0 then (3 : ℝ) else 1) = 0 := by
            simpa [i0] using hcoeff
          have hci : c i0 = 0 := (mul_eq_zero.mp hprod).resolve_right hlead_ne
          simpa [i0] using hci
  intro i
  exact hprefix 289 i i.isLt

/-- Every proposed kernel generator is annihilated by the concrete free-Lie
evaluation into the positive nilradical. -/
theorem g2PosNilFreeLieHom_fiveStepKernelGenerator_zero (i : Fin 289) :
    g2PosNilFreeLieHom (fiveStepKernelGenerator i).1 = 0 := by
  have hserre : g2PosNilFreeLieHom serreRelFreeLie4 = 0 := by
    change g2PosNilFreeLieHom
      ((3 : ℝ) • ⁅FreeLieAlgebra.of ℝ (0 : Fin 4), FreeLieAlgebra.of ℝ (1 : Fin 4)⁆ -
        ⁅FreeLieAlgebra.of ℝ (2 : Fin 4), FreeLieAlgebra.of ℝ (3 : Fin 4)⁆) = 0
    rw [map_sub, map_smul, LieHom.map_lie, LieHom.map_lie]
    simp only [g2PosNilFreeLieHom, FreeLieAlgebra.lift_of_apply]
    apply Subtype.ext
    change (3 : ℝ) • (g2X1 * g2X2 - g2X2 * g2X1) -
      (g2X3 * g2X4 - g2X4 * g2X3) = 0
    exact g2_grade1_contact_and_serre_syzygies.2.2.2.2.2.2
  rcases g2PosNilFreeLieHom_zero_on_cross_degree2_lyndon with
    ⟨h5, h6, h7, h8⟩
  by_cases hi0 : i.1 = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    simpa [fiveStepKernelGenerator, serreRelFiveStep] using hserre
  · have hgen : (fiveStepKernelGenerator i).1 =
        lyndonFreeLie4 (fiveStepKernelCoordinate i) := by
      simp [fiveStepKernelGenerator, hi0]
    by_cases hi5 : i.1 < 5
    · rw [hgen]
      interval_cases hv : i.1
      · omega
      · simpa [fiveStepKernelCoordinate, hv] using h5
      · simpa [fiveStepKernelCoordinate, hv] using h6
      · simpa [fiveStepKernelCoordinate, hv] using h7
      · simpa [fiveStepKernelCoordinate, hv] using h8
    · have hidx : 10 ≤ (fiveStepKernelCoordinate i).1 := by
        simp [fiveStepKernelCoordinate, hi0, hi5]
        omega
      rw [hgen]
      exact g2PosNilFreeLieHom_lyndon_eq_zero_of_index_ge_ten hidx

/-- Restriction of the concrete matrix-valued Chevalley evaluation to the
five-step free-Lie carrier. -/
def fiveStepRestrictedG2Eval : fiveStepFreeLieSubmodule →ₗ[ℝ]
    Matrix Krein16Idx Krein16Idx ℝ :=
  (FreeLieAlgebra.lift ℝ g2ChevalleyX).toLinearMap.comp
    fiveStepFreeLieSubmodule.subtype

/-- Each of the 289 independent candidate generators lies in the kernel of
the restricted matrix evaluation map. -/
theorem fiveStepKernelGenerator_mem_ker (i : Fin 289) :
    fiveStepKernelGenerator i ∈ LinearMap.ker fiveStepRestrictedG2Eval := by
  rw [LinearMap.mem_ker]
  change (FreeLieAlgebra.lift ℝ g2ChevalleyX) (fiveStepKernelGenerator i).1 = 0
  rw [← g2PosNilFreeLieHom_comp_inclusion]
  exact congrArg Subtype.val (g2PosNilFreeLieHom_fiveStepKernelGenerator_zero i)

/-- **A Serre-relation witness and exact kernel rank for the five-step free-Lie map**:
Under `Φ := FreeLieAlgebra.lift ℝ g2ChevalleyX`:
1. The displayed nonzero relation `serreRelFreeLie4 = 3 • ⁅x₀, x₁⁆ - ⁅x₂, x₃⁆`
   lies in `fiveStepFreeLieSubmodule` and in `Φ.ker`;
2. The image of the restricted map is the 5-dimensional positive nilradical `n₊`;
3. Its kernel has dimension `294 - 5 = 289`.

This theorem does not identify the kernel with the ideal generated by all Chevalley–Serre
relations; it records one relation witness and the dimension of the full restricted kernel. In
particular, the submodule spanned by this single displayed relation is not the full kernel. -/
theorem g2ChevalleyX_serre_relation_and_fiveStep_kernel_rank :
    let Φ : FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ Matrix Krein16Idx Krein16Idx ℝ :=
      FreeLieAlgebra.lift ℝ g2ChevalleyX
    let res : fiveStepFreeLieSubmodule →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ :=
      Φ.toLinearMap.comp fiveStepFreeLieSubmodule.subtype
    serreRelFreeLie4 ≠ 0 ∧
    serreRelFreeLie4 ∈ fiveStepFreeLieSubmodule ∧
    serreRelFreeLie4 ∈ Φ.ker ∧
    LinearMap.range res = g2PosNilSubmodule ∧
    Module.finrank ℝ (LinearMap.range res) = 5 ∧
    Module.finrank ℝ (LinearMap.ker res) = 289 ∧
    Submodule.span ℝ ({serreRelFiveStep} : Set fiveStepFreeLieSubmodule) ≠ LinearMap.ker res := by
  intro Φ res
  have hids := lyndonTrees_chevalley_ids
  have hl0 : lyndonFreeLie4 0 = FreeLieAlgebra.of ℝ (0 : Fin 4) := by
    unfold lyndonFreeLie4; rw [hids.1]; rfl
  have hl1 : lyndonFreeLie4 1 = FreeLieAlgebra.of ℝ (1 : Fin 4) := by
    unfold lyndonFreeLie4; rw [hids.2.1]; rfl
  have hl2 : lyndonFreeLie4 2 = FreeLieAlgebra.of ℝ (2 : Fin 4) := by
    unfold lyndonFreeLie4; rw [hids.2.2.1]; rfl
  have hl3 : lyndonFreeLie4 3 = FreeLieAlgebra.of ℝ (3 : Fin 4) := by
    unfold lyndonFreeLie4; rw [hids.2.2.2.1]; rfl
  have hl4 : lyndonFreeLie4 4 = ⁅FreeLieAlgebra.of ℝ (0 : Fin 4), FreeLieAlgebra.of ℝ (1 : Fin 4)⁆ := by
    unfold lyndonFreeLie4; rw [hids.2.2.2.2.1]; rfl
  have hl9 : lyndonFreeLie4 9 = ⁅FreeLieAlgebra.of ℝ (2 : Fin 4), FreeLieAlgebra.of ℝ (3 : Fin 4)⁆ := by
    unfold lyndonFreeLie4; rw [hids.2.2.2.2.2]; rfl
  have hserre_eq := serreRelFreeLie4_eq_lyndon
  have hserre_ne : serreRelFreeLie4 ≠ 0 := by
    intro h0
    rw [hserre_eq] at h0
    have hcoeff : ∀ i : Fin 294,
        (if i = 4 then (3 : ℝ) else if i = 9 then -1 else 0) = 0 := by
      refine Fintype.linearIndependent_iff.mp lyndonFreeLie4_linearIndependent _ ?_
      have hsplit : ∀ v : Fin 294 → FreeLieAlgebra ℝ (Fin 4),
          (∑ i : Fin 294, (if i = 4 then (3 : ℝ) else if i = 9 then -1 else 0) • v i) =
            (3 : ℝ) • v 4 + (-1 : ℝ) • v 9 := by
        intro v
        have h9 : (9 : Fin 294) ≠ 4 := by decide
        have hrest : (∑ i ∈ (Finset.univ.erase (4 : Fin 294)).erase (9 : Fin 294),
            (if i = 4 then (3 : ℝ) else if i = 9 then -1 else 0) • v i) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          rcases Finset.mem_erase.mp hi with ⟨hi9, hi'⟩
          have hi4 := (Finset.mem_erase.mp hi').1
          simp [hi4, hi9]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (4 : Fin 294)),
          ← Finset.add_sum_erase (Finset.univ.erase (4 : Fin 294)) _
            (Finset.mem_erase.mpr ⟨h9, Finset.mem_univ (9 : Fin 294)⟩)]
        rw [hrest]
        simp [h9]
      rw [hsplit lyndonFreeLie4]
      exact h0
    have h4 := hcoeff 4
    norm_num at h4
  have hserre_mem : serreRelFreeLie4 ∈ fiveStepFreeLieSubmodule :=
    serreRelFreeLie4_mem_fiveStep
  have hserre_ker : serreRelFreeLie4 ∈ Φ.ker := by
    change Φ serreRelFreeLie4 = 0
    unfold serreRelFreeLie4
    rw [map_sub, map_smul, LieHom.map_lie, LieHom.map_lie]
    dsimp [Φ]
    simp only [FreeLieAlgebra.lift_of_apply, g2ChevalleyX, LieRing.of_associative_ring_bracket]
    exact g2_grade1_contact_and_serre_syzygies.2.2.2.2.2.2
  -- Use the already-defined Lie hom into the actual positive nilradical.  This
  -- makes the restricted kernel calculation and the quotient theorem share
  -- one carrier map, rather than reintroducing a local lift here.
  let φSub : FreeLieAlgebra ℝ (Fin 4) →ₗ⁅ℝ⁆ g2PosNilLieSubalgebra :=
    g2PosNilFreeLieHom
  have hcomp : g2PosNilLieSubalgebra.incl.comp φSub = Φ :=
    g2PosNilFreeLieHom_comp_inclusion
  have hrange_le : LinearMap.range res ≤ g2PosNilSubmodule := by
    rintro y ⟨⟨x, _⟩, rfl⟩
    have hx : res ⟨x, ‹_›⟩ = Φ x := rfl
    rw [hx, ← hcomp]
    exact (φSub x).2
  have hrange_ge : g2PosNilSubmodule ≤ LinearMap.range res := by
    unfold g2PosNilSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · refine ⟨⟨lyndonFreeLie4 4, Submodule.subset_span ⟨4, rfl⟩⟩, ?_⟩
      change Φ (lyndonFreeLie4 4) = g2PosNilBasis 0
      rw [hl4, LieHom.map_lie]
      dsimp [Φ, g2PosNilBasis]
      rw [FreeLieAlgebra.lift_of_apply, FreeLieAlgebra.lift_of_apply,
        LieRing.of_associative_ring_bracket]
      dsimp [g2ChevalleyX]
      exact g2_grade1_contact_and_serre_syzygies.1
    · refine ⟨⟨lyndonFreeLie4 0, Submodule.subset_span ⟨0, rfl⟩⟩, ?_⟩
      change Φ (lyndonFreeLie4 0) = g2PosNilBasis 1
      rw [hl0]
      simp [Φ, g2ChevalleyX, g2PosNilBasis]
    · refine ⟨⟨lyndonFreeLie4 1, Submodule.subset_span ⟨1, rfl⟩⟩, ?_⟩
      change Φ (lyndonFreeLie4 1) = g2PosNilBasis 2
      rw [hl1]
      simp [Φ, g2ChevalleyX, g2PosNilBasis]
    · refine ⟨⟨lyndonFreeLie4 2, Submodule.subset_span ⟨2, rfl⟩⟩, ?_⟩
      change Φ (lyndonFreeLie4 2) = g2PosNilBasis 3
      rw [hl2]
      simp [Φ, g2ChevalleyX, g2PosNilBasis]
    · refine ⟨⟨lyndonFreeLie4 3, Submodule.subset_span ⟨3, rfl⟩⟩, ?_⟩
      change Φ (lyndonFreeLie4 3) = g2PosNilBasis 4
      rw [hl3]
      simp [Φ, g2ChevalleyX, g2PosNilBasis]
  have hrange_eq : LinearMap.range res = g2PosNilSubmodule :=
    le_antisymm hrange_le hrange_ge
  have hdim_range : Module.finrank ℝ (LinearMap.range res) = 5 := by
    rw [hrange_eq]
    unfold g2PosNilSubmodule
    rw [finrank_span_eq_card g2PosNilBasis_linearIndependent, Fintype.card_fin]
  have hdim_ker : Module.finrank ℝ (LinearMap.ker res) = 289 := by
    have hrn := res.finrank_range_add_finrank_ker
    rw [freeLie4_grade_finranks.2.2.2.2.2.2.2.2.2.2, hdim_range] at hrn
    omega
  have hsingle : Module.finrank ℝ
      (Submodule.span ℝ ({serreRelFiveStep} : Set fiveStepFreeLieSubmodule)) = 1 := by
    apply finrank_span_singleton
    intro heq
    exact hserre_ne (congrArg Subtype.val heq)
  have hspan_ne : Submodule.span ℝ
      ({serreRelFiveStep} : Set fiveStepFreeLieSubmodule) ≠ LinearMap.ker res := by
    intro heq
    have hfinrank := congrArg
      (fun M : Submodule ℝ fiveStepFreeLieSubmodule => Module.finrank ℝ M) heq
    rw [hsingle, hdim_ker] at hfinrank
    norm_num at hfinrank
  exact ⟨hserre_ne, hserre_mem, hserre_ker, hrange_eq, hdim_range, hdim_ker, hspan_ne⟩

/-- Exact finite five-step kernel presentation: it is spanned by the five
degree-two Serre directions and all 284 degree-three-through-five Lyndon
vectors, with no additional relations in this truncation. -/
theorem fiveStepRestrictedG2Eval_kernel_eq_candidate_span :
    LinearMap.ker fiveStepRestrictedG2Eval =
      Submodule.span ℝ (Set.range fiveStepKernelGenerator) := by
  have hle : Submodule.span ℝ (Set.range fiveStepKernelGenerator) ≤
      LinearMap.ker fiveStepRestrictedG2Eval := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact fiveStepKernelGenerator_mem_ker i
  have hspan_dim : Module.finrank ℝ
      (Submodule.span ℝ (Set.range fiveStepKernelGenerator)) = 289 := by
    rw [finrank_span_eq_card fiveStepKernelGenerator_linearIndependent,
      Fintype.card_fin]
  have hker_dim : Module.finrank ℝ (LinearMap.ker fiveStepRestrictedG2Eval) = 289 := by
    have hkernel :=
      g2ChevalleyX_serre_relation_and_fiveStep_kernel_rank.2.2.2.2.2.1
    change Module.finrank ℝ (LinearMap.ker
      ((FreeLieAlgebra.lift ℝ g2ChevalleyX).toLinearMap.comp
        fiveStepFreeLieSubmodule.subtype)) = 289 at hkernel
    exact hkernel
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan_dim, hker_dim])).symm

/-- The restricted five-step evaluation has the entire concrete positive
nilradical as its range. This is the finite-carrier soldering statement needed
to transport the first isomorphism theorem to the five-step quotient. -/
theorem fiveStepRestrictedG2Eval_range_eq_posNil :
    LinearMap.range fiveStepRestrictedG2Eval = g2PosNilSubmodule := by
  rcases g2ChevalleyX_serre_relation_and_fiveStep_kernel_rank with
    ⟨_, _, _, hrange, _, _, _⟩
  change LinearMap.range
    ((FreeLieAlgebra.lift ℝ g2ChevalleyX).toLinearMap.comp
      fiveStepFreeLieSubmodule.subtype) = g2PosNilSubmodule at hrange
  exact hrange

/-- The quotient of the actual finite five-step source by its evaluated kernel
is linearly equivalent to the concrete five-dimensional positive nilradical.
This is the restricted-carrier counterpart of the unrestricted free-Lie
quotient theorem above. -/
noncomputable def fiveStepRestrictedG2QuotientEquiv :
    (fiveStepFreeLieSubmodule ⧸ LinearMap.ker fiveStepRestrictedG2Eval) ≃ₗ[ℝ]
      g2PosNilSubmodule :=
  fiveStepRestrictedG2Eval.quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _ fiveStepRestrictedG2Eval_range_eq_posNil)

/-- On every quotient representative, the finite quotient equivalence is
exactly the restricted concrete matrix evaluation. -/
theorem fiveStepRestrictedG2QuotientEquiv_mk
    (x : fiveStepFreeLieSubmodule) :
    (fiveStepRestrictedG2QuotientEquiv
      (Submodule.Quotient.mk x :
        fiveStepFreeLieSubmodule ⧸ LinearMap.ker fiveStepRestrictedG2Eval) :
      Matrix Krein16Idx Krein16Idx ℝ) = fiveStepRestrictedG2Eval x := by
  simp [fiveStepRestrictedG2QuotientEquiv,
    LinearMap.quotKerEquivRange_apply_mk]

/-- The finite five-step quotient has dimension five, exactly the dimension of
the concrete positive nilradical. -/
theorem fiveStepRestrictedG2Quotient_finrank :
    Module.finrank ℝ
      (fiveStepFreeLieSubmodule ⧸ LinearMap.ker fiveStepRestrictedG2Eval) = 5 := by
  rw [LinearEquiv.finrank_eq fiveStepRestrictedG2QuotientEquiv]
  unfold g2PosNilSubmodule
  rw [finrank_span_eq_card g2PosNilBasis_linearIndependent, Fintype.card_fin]

end FreeLie294Lyndon

end WittPigeonhole

/-! ## Section 6: 15-Element Graded Acyclic Causal Poset & Master `Ξ_⊤` Coagulation -/

section CausalPoset15

/-- Fifteen-node graded causal poset spanning Grades `0..6` from primal defect `Δ₀` (`Phase 0`)
through `Cl(4,4)`, Krein–Bivector Shear, Triality–`g_{2(2)}`, and Witt–Jacobi to `Ξ_⊤` (`V. Coagula`). -/
inductive KreinG2CausalNode : Type
  | Delta0
  | T
  | S
  | K_TT
  | Pi_ST
  | Sigma_TS
  | Gamma_SS
  | G
  | Tau
  | A0
  | B
  | A_omega
  | H
  | E
  | Xi_top
  deriving DecidableEq, Repr

/-- Exact grade assignment `0..6` for the 15 causal poset nodes. -/
def nodeGrade : KreinG2CausalNode → ℕ
  | .Delta0 => 0
  | .T => 1
  | .S => 1
  | .K_TT => 2
  | .Pi_ST => 2
  | .Sigma_TS => 2
  | .Gamma_SS => 2
  | .G => 3
  | .Tau => 3
  | .A0 => 4
  | .B => 4
  | .A_omega => 5
  | .H => 5
  | .E => 5
  | .Xi_top => 6

def nodeToFin : KreinG2CausalNode → Fin 15
  | .Delta0 => 0
  | .T => 1
  | .S => 2
  | .K_TT => 3
  | .Pi_ST => 4
  | .Sigma_TS => 5
  | .Gamma_SS => 6
  | .G => 7
  | .Tau => 8
  | .A0 => 9
  | .B => 10
  | .A_omega => 11
  | .H => 12
  | .E => 13
  | .Xi_top => 14

def nodeOfFin : Fin 15 → KreinG2CausalNode
  | ⟨0, _⟩ => .Delta0
  | ⟨1, _⟩ => .T
  | ⟨2, _⟩ => .S
  | ⟨3, _⟩ => .K_TT
  | ⟨4, _⟩ => .Pi_ST
  | ⟨5, _⟩ => .Sigma_TS
  | ⟨6, _⟩ => .Gamma_SS
  | ⟨7, _⟩ => .G
  | ⟨8, _⟩ => .Tau
  | ⟨9, _⟩ => .A0
  | ⟨10, _⟩ => .B
  | ⟨11, _⟩ => .A_omega
  | ⟨12, _⟩ => .H
  | ⟨13, _⟩ => .E
  | ⟨14, _⟩ => .Xi_top

private theorem nodeOfFin_toFin (x : KreinG2CausalNode) : nodeOfFin (nodeToFin x) = x := by
  cases x
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The 24 direct Hasse covering relations `u ⋖ v` across Grades `0..6`. -/
def Covers : KreinG2CausalNode → KreinG2CausalNode → Bool
  | .Delta0, .T => true
  | .Delta0, .S => true
  | .T, .K_TT => true
  | .T, .Pi_ST => true
  | .T, .Sigma_TS => true
  | .S, .Pi_ST => true
  | .S, .Sigma_TS => true
  | .S, .Gamma_SS => true
  | .Pi_ST, .G => true
  | .Sigma_TS, .G => true
  | .Pi_ST, .Tau => true
  | .Sigma_TS, .Tau => true
  | .K_TT, .A0 => true
  | .G, .A0 => true
  | .G, .B => true
  | .Tau, .B => true
  | .Gamma_SS, .B => true
  | .A0, .A_omega => true
  | .A0, .H => true
  | .B, .H => true
  | .B, .E => true
  | .A_omega, .Xi_top => true
  | .H, .Xi_top => true
  | .E, .Xi_top => true
  | _, _ => false

/-- Exact reflexive-transitive closure `u ≤ v` of `Covers` across all 15 nodes. -/
def causalLe (u v : KreinG2CausalNode) : Bool :=
  if u = v then true
  else match u with
    | .Delta0 => true
    | .T => match v with
        | .K_TT | .Pi_ST | .Sigma_TS | .G | .Tau | .A0 | .B | .A_omega | .H | .E | .Xi_top => true
        | _ => false
    | .S => match v with
        | .Pi_ST | .Sigma_TS | .Gamma_SS | .G | .Tau | .A0 | .B | .A_omega | .H | .E | .Xi_top => true
        | _ => false
    | .K_TT => match v with
        | .A0 | .A_omega | .H | .Xi_top => true
        | _ => false
    | .Pi_ST | .Sigma_TS => match v with
        | .G | .Tau | .A0 | .B | .A_omega | .H | .E | .Xi_top => true
        | _ => false
    | .Gamma_SS => match v with
        | .B | .H | .E | .Xi_top => true
        | _ => false
    | .G => match v with
        | .A0 | .B | .A_omega | .H | .E | .Xi_top => true
        | _ => false
    | .Tau => match v with
        | .B | .H | .E | .Xi_top => true
        | _ => false
    | .A0 => match v with
        | .A_omega | .H | .Xi_top => true
        | _ => false
    | .B => match v with
        | .H | .E | .Xi_top => true
        | _ => false
    | .A_omega | .H | .E => v == .Xi_top
    | .Xi_top => false

instance : PartialOrder KreinG2CausalNode where
  le u v := causalLe u v = true
  le_refl u := by
    have href : ∀ i : Fin 15, causalLe (nodeOfFin i) (nodeOfFin i) = true := by decide
    rw [← nodeOfFin_toFin u]
    exact href (nodeToFin u)
  le_trans u v w huv hvw := by
    have htr : ∀ i j k : Fin 15,
        causalLe (nodeOfFin i) (nodeOfFin j) = true →
        causalLe (nodeOfFin j) (nodeOfFin k) = true →
        causalLe (nodeOfFin i) (nodeOfFin k) = true := by decide
    rw [← nodeOfFin_toFin u, ← nodeOfFin_toFin w]
    refine htr (nodeToFin u) (nodeToFin v) (nodeToFin w) ?_ ?_
    · rw [nodeOfFin_toFin, nodeOfFin_toFin]
      exact huv
    · rw [nodeOfFin_toFin, nodeOfFin_toFin]
      exact hvw
  le_antisymm u v huv hvu := by
    have hanti : ∀ i j : Fin 15,
        causalLe (nodeOfFin i) (nodeOfFin j) = true →
        causalLe (nodeOfFin j) (nodeOfFin i) = true →
        i = j := by decide
    have hidx : nodeToFin u = nodeToFin v := by
      refine hanti (nodeToFin u) (nodeToFin v) ?_ ?_
      · rw [nodeOfFin_toFin, nodeOfFin_toFin]
        exact huv
      · rw [nodeOfFin_toFin, nodeOfFin_toFin]
        exact hvu
    rw [← nodeOfFin_toFin u, ← nodeOfFin_toFin v, hidx]

instance : DecidableRel (· ≤ · : KreinG2CausalNode → KreinG2CausalNode → Prop) :=
  fun u v => inferInstanceAs (Decidable (causalLe u v = true))

instance : DecidableRel (· < · : KreinG2CausalNode → KreinG2CausalNode → Prop) :=
  fun u v => inferInstanceAs (Decidable (causalLe u v = true ∧ ¬ causalLe v u = true))

/-- Every Hasse cover strictly increases the causal grade `0..6`. -/
theorem covers_strict_grade (u v : KreinG2CausalNode) (h : Covers u v = true) :
    nodeGrade u < nodeGrade v := by
  have hfin : ∀ i j : Fin 15,
      Covers (nodeOfFin i) (nodeOfFin j) = true →
      nodeGrade (nodeOfFin i) < nodeGrade (nodeOfFin j) := by decide
  rw [← nodeOfFin_toFin u, ← nodeOfFin_toFin v] at h ⊢
  exact hfin (nodeToFin u) (nodeToFin v) h

/-- Every edge of `Covers` is a minimal Hasse covering relation (transitively reduced). -/
theorem covers_transitively_reduced (u v : KreinG2CausalNode) (h : Covers u v = true) :
    u < v ∧ ¬ ∃ w : KreinG2CausalNode, u < w ∧ w < v := by
  have hfin : ∀ i j : Fin 15, Covers (nodeOfFin i) (nodeOfFin j) = true →
      nodeOfFin i < nodeOfFin j ∧
      (∀ k : Fin 15, ¬ (nodeOfFin i < nodeOfFin k ∧ nodeOfFin k < nodeOfFin j)) := by decide
  have hpair := hfin (nodeToFin u) (nodeToFin v) (by rw [nodeOfFin_toFin, nodeOfFin_toFin]; exact h)
  rw [nodeOfFin_toFin, nodeOfFin_toFin] at hpair
  refine ⟨hpair.1, ?_⟩
  rintro ⟨w, hw1, hw2⟩
  have hno := hpair.2 (nodeToFin w)
  rw [nodeOfFin_toFin] at hno
  exact hno ⟨hw1, hw2⟩

/-- Explicit pairwise-incomparable antichains: `{K_TT, G, Tau, Gamma_SS}` and `{A0, Tau, Gamma_SS}`. -/
theorem causal_antichains_verified :
    (¬ (KreinG2CausalNode.K_TT ≤ KreinG2CausalNode.G) ∧
     ¬ (KreinG2CausalNode.G ≤ KreinG2CausalNode.K_TT) ∧
     ¬ (KreinG2CausalNode.K_TT ≤ KreinG2CausalNode.Tau) ∧
     ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.K_TT) ∧
     ¬ (KreinG2CausalNode.K_TT ≤ KreinG2CausalNode.Gamma_SS) ∧
     ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.K_TT) ∧
     ¬ (KreinG2CausalNode.G ≤ KreinG2CausalNode.Tau) ∧
     ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.G) ∧
     ¬ (KreinG2CausalNode.G ≤ KreinG2CausalNode.Gamma_SS) ∧
     ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.G) ∧
     ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.Gamma_SS) ∧
     ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.Tau)) ∧
    (¬ (KreinG2CausalNode.A0 ≤ KreinG2CausalNode.Tau) ∧
     ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.A0) ∧
     ¬ (KreinG2CausalNode.A0 ≤ KreinG2CausalNode.Gamma_SS) ∧
     ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.A0)) := by
  have hkG : ¬ (KreinG2CausalNode.K_TT ≤ KreinG2CausalNode.G) := by decide
  have hGk : ¬ (KreinG2CausalNode.G ≤ KreinG2CausalNode.K_TT) := by decide
  have hkT : ¬ (KreinG2CausalNode.K_TT ≤ KreinG2CausalNode.Tau) := by decide
  have hTk : ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.K_TT) := by decide
  have hkS : ¬ (KreinG2CausalNode.K_TT ≤ KreinG2CausalNode.Gamma_SS) := by decide
  have hSk : ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.K_TT) := by decide
  have hGT : ¬ (KreinG2CausalNode.G ≤ KreinG2CausalNode.Tau) := by decide
  have hTG : ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.G) := by decide
  have hGS : ¬ (KreinG2CausalNode.G ≤ KreinG2CausalNode.Gamma_SS) := by decide
  have hSG : ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.G) := by decide
  have hTS : ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.Gamma_SS) := by decide
  have hST : ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.Tau) := by decide
  have hAT : ¬ (KreinG2CausalNode.A0 ≤ KreinG2CausalNode.Tau) := by decide
  have hTA : ¬ (KreinG2CausalNode.Tau ≤ KreinG2CausalNode.A0) := by decide
  have hAS : ¬ (KreinG2CausalNode.A0 ≤ KreinG2CausalNode.Gamma_SS) := by decide
  have hSA : ¬ (KreinG2CausalNode.Gamma_SS ≤ KreinG2CausalNode.A0) := by decide
  exact ⟨⟨hkG, hGk, hkT, hTk, hkS, hSk, hGT, hTG, hGS, hSG, hTS, hST⟩, ⟨hAT, hTA, hAS, hSA⟩⟩

/-- Global minimum `Δ₀ ≤ x` for all 15 nodes. -/
theorem bot_le_all (x : KreinG2CausalNode) : KreinG2CausalNode.Delta0 ≤ x := by
  have hfin : ∀ i : Fin 15, KreinG2CausalNode.Delta0 ≤ nodeOfFin i := by decide
  rw [← nodeOfFin_toFin x]
  exact hfin (nodeToFin x)

/-- Global maximum `x ≤ Ξ_⊤` for all 15 nodes. -/
theorem all_le_top (x : KreinG2CausalNode) : x ≤ KreinG2CausalNode.Xi_top := by
  have hfin : ∀ i : Fin 15, nodeOfFin i ≤ KreinG2CausalNode.Xi_top := by decide
  rw [← nodeOfFin_toFin x]
  exact hfin (nodeToFin x)

/-- Exact least-upper-bound join `IsLUB {H, E} Ξ_⊤` completing the `V. Coagula` terminal apex. -/
theorem xi_top_isLUB_H_E :
    IsLUB ({KreinG2CausalNode.H, KreinG2CausalNode.E} : Set KreinG2CausalNode)
      KreinG2CausalNode.Xi_top := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl
    · decide
    · decide
  · intro u hu
    have hH : KreinG2CausalNode.H ≤ u := hu (Set.mem_insert _ _)
    have hE : KreinG2CausalNode.E ≤ u := hu (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    cases u <;> first | exact absurd hH (by decide) | exact absurd hE (by decide) | decide

end CausalPoset15

/-! ## Section 7: QMS `TypedArchetype` Registrations & `V. COAGULA` Closing Theorem -/

section ArchetypeRegistrations

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Proved `TypedArchetype` for Phase 1: derivations, Leibniz defect, `D² ∉ der`, and Ax.4 Jacobi ceiling. -/
def archKreinDerivationDefect : TypedArchetype Unit .proved where
  name := `archKreinDerivationDefect
  phase := 1
  claim := fun _ =>
    IsProductDerivation matMulBilin2 innerDerivationWitness ∧
    leibnizDefect matMulBilin2 (innerDerivationWitness.comp innerDerivationWitness)
      !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] = !![(-8 : ℝ), 0; 0, 0] ∧
    ¬ IsProductDerivation matMulBilin2 (innerDerivationWitness.comp innerDerivationWitness) ∧
    (∀ X Y Z : Matrix Krein16Idx Krein16Idx ℝ,
      assocComm X (assocComm Y Z) + assocComm Y (assocComm Z X) +
        assocComm Z (assocComm X Y) = 0) ∧
    (∀ (D : Matrix Krein16Idx Krein16Idx ℝ →+ Matrix Krein16Idx Krein16Idx ℝ),
      (∀ x y, D (x * y) = D x * y + x * D y) →
      ∀ x y, D (D (x * y)) - D (D x) * y - x * D (D y) = D x * D y + D x * D y)
  evidence := fun _ =>
    ⟨innerDerivationWitness_sq_not_derivation.1,
     innerDerivationWitness_sq_not_derivation.2.1,
     innerDerivationWitness_sq_not_derivation.2.2,
     fun X Y Z => ax4_associative_jacobi_ceiling X Y Z,
     fun D hD x y => derivation_sq_leibniz_defect_nonAssocRing D hD x y⟩

/-- Proved `TypedArchetype` for Phase 2: `Cl(4,4)` on `Krein16Idx`, `Γ_{4,4}`, `kreinMetric88`,
Krein-skewness of all 28 bivectors, orthogonal Lie/Jordan bivector shear, and 4-vector escape out of `Cl⁽¹⁾`. -/
def archKreinCl44BivectorShear : TypedArchetype Unit .proved where
  name := `archKreinCl44BivectorShear
  phase := 2
  claim := fun _ =>
    Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) = 256 ∧
    Module.finrank ℝ cl44Vec1Submodule = 8 ∧
    (∀ a : Fin 8, cl44Gen a * cl44Gen a = if a.val < 4 then 1 else -1) ∧
    (gamma44 * gamma44 = 1 ∧ Matrix.trace gamma44 = 0) ∧
    (kreinMetric88ᵀ = kreinMetric88 ∧ kreinMetric88 * kreinMetric88 = 1 ∧
      Matrix.trace kreinMetric88 = 0 ∧ kreinMetric88 * gamma44 = gamma44 * kreinMetric88) ∧
    (∀ a b : Fin 8, a ≠ b →
      cl44Bivector a b * gamma44 = gamma44 * cl44Bivector a b ∧
      (cl44Bivector a b)ᵀ * kreinMetric88 + kreinMetric88 * cl44Bivector a b = 0) ∧
    cl44FourVec * cl44Gen 0 - cl44Gen 0 * cl44FourVec ∉ cl44Vec1Submodule
  evidence := fun _ =>
    ⟨finrank_mat16,
     finrank_cl44Vec1Submodule,
     cl44Gen_sq,
     ⟨gamma44_properties.2.1, gamma44_properties.2.2.1⟩,
     ⟨kreinMetric88_properties.2.1, kreinMetric88_properties.2.2.1,
      kreinMetric88_properties.2.2.2.1, kreinMetric88_properties.2.2.2.2⟩,
     fun _ _ hab => cl44Bivector_chiral_even_and_krein_skew hab,
     cl44FourVec_exits_vec1_normalizer.2.2.2⟩

/-- Proved `TypedArchetype` collecting the root-set `S₃` action and its 14D coordinate fixed space
(including fixed Cartan dimension `2`), together with a constructed linear equivalence from that
carrier to the explicit matrix `g2Submodule`, alongside the result (b), an explicit
14D split `g_{2(2)} ⊂ Cl⁽²⁾(4,4)` with 5-grading, Cartan ratio `3`, Jordan jump, Lie bracket
closure and bracket-weight additivity, trivial center, `CanonicalZornDerivations` owner bridge, faithful `8 × 8` `so(4,4)` vector
representation `rhoVec8`, and matrix Lie group `SplitG2MatrixGroup ≤ GL₁₆(ℝ)` with `NormedSpace.exp`
flow and tangent recovery. The claim below contains both results as a conjunction. The equivalence
is a Lie equivalence after equipping the fixed coordinate carrier with the bracket transported from
`g2LieSubalgebra` through the explicit matrix carrier equivalence. This proves a Lie-algebra
isomorphism for that transported bracket. It does not yet identify the transported bracket with the
restriction of an intrinsic D₄ Chevalley bracket on the Cartan/root-coordinate carrier: no such
bracket-realization map to the Cl(4,4) bivectors is part of this owner. -/
def archCartanS3TrialitySplitG2 : TypedArchetype Unit .proved where
  name := `archCartanS3TrialitySplitG2
  phase := 3
  claim := fun _ =>
    Module.finrank ℝ s3FixedCartanSubmodule = 2 ∧
    d4TrialityRootPermutationPresentation ∧
    Finset.univ.filter (fun k : Fin 24 => d4PermVS k = k ∧ d4PermSpin k = k) =
      ({0, 3, 4, 7, 13, 14} : Finset (Fin 24)) ∧
    (∀ o : Fin 12,
      trialitySwapVS.mulVec (d4OrbitMean o) = d4OrbitMean o ∧
      trialitySwapSpin.mulVec (d4OrbitMean o) = d4OrbitMean o) ∧
    (∀ o : Fin 12,
      (∑ i : Fin 4, d4OrbitMean o i ^ 2) =
        if o.val = 0 ∨ o.val = 3 ∨ o.val = 4 ∨ o.val = 7 ∨ o.val = 10 ∨ o.val = 11
        then 2 else (2 : ℝ) / 3) ∧
    (∀ o : Fin 12,
      d4FoldedRootWeight (d4OrbitMean o) =
        ((g2Grade (d4OrbitToG2RootBasis o) : ℝ),
          (g2AlphaWeight (d4OrbitToG2RootBasis o) : ℝ))) ∧
    (∀ o : Fin 12,
      (s3FixedToG2CarrierEquiv (d4TrialityOrbitCoordinate o)).1 =
        g2Basis (d4OrbitToG2RootBasis o)) ∧
    (∀ p : Fin 2 → ℝ, ∀ o : Fin 12,
      rhoVec8 (d4FixedCartanMatrix p) *
          rhoVec8 (g2Basis (d4OrbitToG2RootBasis o)) -
        rhoVec8 (g2Basis (d4OrbitToG2RootBasis o)) *
          rhoVec8 (d4FixedCartanMatrix p) =
        d4OrbitCartanEvaluation p o •
          rhoVec8 (g2Basis (d4OrbitToG2RootBasis o))) ∧
    (∀ o : Fin 12,
      rhoVec8 (g2Basis (d4OrbitToG2RootBasis o)) ≠ 0) ∧
    (∀ i j : Fin 14,
      let C := g2Basis i * g2Basis j - g2Basis j * g2Basis i
      (g2H1 * C - C * g2H1 =
          ((g2Grade i + g2Grade j : ℤ) : ℝ) • C) ∧
      (g2Halpha * C - C * g2Halpha =
          ((g2AlphaWeight i + g2AlphaWeight j : ℤ) : ℝ) • C)) ∧
    (∀ i j : Fin 14,
      ∃ c : Fin 14 → ℝ,
        g2Basis i * g2Basis j - g2Basis j * g2Basis i =
          ∑ k : Fin 14, c k • g2Basis k ∧
        ∀ k : Fin 14, c k ≠ 0 →
          (g2Grade k : ℝ) = ((g2Grade i + g2Grade j : ℤ) : ℝ) ∧
          (g2AlphaWeight k : ℝ) = ((g2AlphaWeight i + g2AlphaWeight j : ℤ) : ℝ)) ∧
    (∀ k : Fin 24, trialityCycle3.mulVec (d4Root k) = d4Root (d4TrialityCycle k)) ∧
    Module.finrank ℝ s3FixedSpin44Submodule = 14 ∧
    Module.finrank ℝ g2Submodule = 14 ∧
    Nonempty (s3FixedSpin44Submodule ≃ₗ⁅ℝ⁆ g2LieSubalgebra) ∧
    Module.finrank ℝ g2Submodule =
      Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations ∧
    g2X3 * g2X4 - g2X4 * g2X3 = (3 : ℝ) • (g2X1 * g2X2 - g2X2 * g2X1) ∧
    (∀ c : Fin 6 → ℝ,
      g2ContactBracketMap c =
        c 0 • (g2X1 * g2X2 - g2X2 * g2X1) +
          c 1 • (g2X1 * g2X3 - g2X3 * g2X1) +
          c 2 • (g2X1 * g2X4 - g2X4 * g2X1) +
          c 3 • (g2X2 * g2X3 - g2X3 * g2X2) +
          c 4 • (g2X2 * g2X4 - g2X4 * g2X2) +
          c 5 • (g2X3 * g2X4 - g2X4 * g2X3)) ∧
    Module.finrank ℝ (LinearMap.ker g2ContactBracketMap) = 5 ∧
    LinearMap.range g2ContactBracketMap =
      Submodule.span ℝ ({g2Zpos2} : Set (Matrix Krein16Idx Krein16Idx ℝ)) ∧
    Module.finrank ℝ (LinearMap.range g2ContactBracketMap) = 1 ∧
    Nonempty (((Fin 6 → ℝ) ⧸ LinearMap.ker g2ContactBracketMap) ≃ₗ[ℝ]
      Submodule.span ℝ ({g2Zpos2} : Set (Matrix Krein16Idx Krein16Idx ℝ))) ∧
    (g2X1 * g2X2 + g2X2 * g2X1) ∉ g2Submodule ∧
    (∀ A B, A ∈ g2Submodule → B ∈ g2Submodule → A * B - B * A ∈ g2Submodule) ∧
    (∀ Z ∈ g2Submodule, (∀ W ∈ g2Submodule, W * Z - Z * W = 0) → Z = 0) ∧
    (∀ A B, A ∈ g2Submodule → B ∈ g2Submodule →
      rhoVec8 (A * B - B * A) = rhoVec8 A * rhoVec8 B - rhoVec8 B * rhoVec8 A) ∧
    (∀ B ∈ g2Submodule, ∀ k : Fin 8, rhoVec8 B 0 k = 0 ∧ rhoVec8 B k 0 = 0) ∧
    Module.finrank ℝ (Submodule.map rhoVec8 g2Submodule) = 14 ∧
    (g2Zpos2 * g2X1 - g2X1 * g2Zpos2 = 0 ∧ g2Y1 * g2Zneg2 - g2Zneg2 * g2Y1 = 0) ∧
    Function.Injective g2RhoVec8LieHom ∧
    (∀ Z ∈ g2Submodule, ∀ t : ℝ, expMat16GL Z t ∈ SplitG2MatrixGroup) ∧
    (∀ Z ∈ g2Submodule, ∀ (t : ℝ) (b : Fin 8),
      NormedSpace.exp (t • Z) * cl44Gen b * NormedSpace.exp ((-t) • Z) =
        ∑ a : Fin 8, (NormedSpace.exp (t • rhoVec8 Z) a b) • cl44Gen a) ∧
    (∀ X : Matrix Krein16Idx Krein16Idx ℝ,
      (∀ t : ℝ, expMat16GL X t ∈ SplitG2MatrixGroup) → IsSplitG2Stabilizer X)
  evidence := fun _ =>
    ⟨finrank_s3FixedCartanSubmodule,
     d4_triality_root_permutation_presentation,
     d4_triality_common_fixed_roots,
     d4_triality_folded_root_means.1,
     d4_triality_folded_root_means.2,
     d4_folded_root_weights_match_g2_basis,
     d4TrialityOrbitCoordinate_maps_to_g2RootBasis,
     d4_orbit_root_vector_weight_in_rhoVec8,
     d4_orbit_root_vector_rhoVec8_ne_zero,
     fun i j => g2_basis_bracket_weights i j,
     g2_basis_bracket_support,
     d4_triality_cycle_permutes_roots,
     finrank_spin44_triality_cutting_28_to_14.2,
     finrank_g2Submodule_and_owner_bridge.1,
     ⟨s3FixedToG2LieEquiv⟩,
     finrank_g2Submodule_and_owner_bridge.2,
     by rw [g2_grade1_contact_and_serre_syzygies.1, g2_grade1_contact_and_serre_syzygies.2.1],
     g2ContactBracketMap_eq_matrix_bracket_sum,
     g2ContactBracketMap_kernel_finrank,
     g2ContactBracketMap_range_eq_centerLine,
     g2ContactBracketMap_range_finrank,
     g2ContactBracketMap_quotient_equiv_centerLine,
     g2_jordan_anticomm_clifford_jump.2.2,
     fun _ _ hA hB => g2Submodule_lie_closed hA hB,
     fun _ hZ hc => g2Submodule_center_trivial hZ hc,
     fun _ _ hA hB => rhoVec8_bivectorSpan_lie_hom
       (g2Submodule_le_bivectorSpan hA) (g2Submodule_le_bivectorSpan hB),
     fun _ hB k => rhoVec8_zero_first_row_col hB k,
     rhoVec8_isomorphic_image_finrank14.2,
     ⟨g2_top_grade_central_commutativity.1.1, g2_top_grade_central_commutativity.2.1⟩,
     g2RhoVec8LieHom_injective,
     fun _ hZ t => expMat16GL_mem_splitG2MatrixGroup hZ t,
     fun _ hZ t b => expMat16GL_cl44_intertwining hZ t b,
     fun X hX => ((splitG2_tangent_of_exp_mem X).2 hX).1⟩

/-- Proved `TypedArchetype` for Phase 4: Witt cumulative rank-4 free Lie dimension `294 > 256`,
genuine `294`-element Shirshov–Lyndon basis `LinearIndependent ℝ lyndonFreeLie4` in `FreeLieAlgebra ℝ (Fin 4)`,
universal `FreeLieAlgebra.lift` non-injectivity (`ker ≠ ⊥`, 5-step syzygy `finrank ≥ 38`), and exact `289`-D
Chevalley–Serre syzygy kernel on `g2ChevalleyX`. -/
def archWittPigeonholeAndJacobiCeiling : TypedArchetype Unit .proved where
  name := `archWittPigeonholeAndJacobiCeiling
  phase := 4
  claim := fun _ =>
    wittFreeLieCumDim 4 5 = 294 ∧
    (¬ ∃ L : (Fin 294 → ℝ) →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ, Function.Injective L) ∧
    (∀ L : (Fin 294 → ℝ) →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ,
      LinearMap.ker L ≠ ⊥ ∧ 38 ≤ Module.finrank ℝ (LinearMap.ker L)) ∧
    LinearIndependent ℝ lyndonFreeLie4 ∧
    Module.finrank ℝ fiveStepFreeLieSubmodule = 294 ∧
    (∀ f : Fin 4 → Matrix Krein16Idx Krein16Idx ℝ,
      ¬ Function.Injective (FreeLieAlgebra.lift ℝ f) ∧
      (FreeLieAlgebra.lift ℝ f).ker ≠ ⊥ ∧
      38 ≤ Module.finrank ℝ (LinearMap.ker
        ((FreeLieAlgebra.lift ℝ f).toLinearMap.comp fiveStepFreeLieSubmodule.subtype))) ∧
    (serreRelFreeLie4 ≠ 0 ∧
     serreRelFreeLie4 ∈ (FreeLieAlgebra.lift ℝ g2ChevalleyX).ker ∧
     Module.finrank ℝ (LinearMap.ker
       ((FreeLieAlgebra.lift ℝ g2ChevalleyX).toLinearMap.comp fiveStepFreeLieSubmodule.subtype)) = 289 ∧
     Submodule.span ℝ ({serreRelFiveStep} : Set fiveStepFreeLieSubmodule) ≠
       LinearMap.ker ((FreeLieAlgebra.lift ℝ g2ChevalleyX).toLinearMap.comp
         fiveStepFreeLieSubmodule.subtype)) ∧
    LinearMap.ker fiveStepRestrictedG2Eval =
      Submodule.span ℝ (Set.range fiveStepKernelGenerator) ∧
    Module.finrank ℝ
      (fiveStepFreeLieSubmodule ⧸ LinearMap.ker fiveStepRestrictedG2Eval) = 5
  evidence := fun _ =>
    ⟨witt_rank4_dimensions.2.2.2.2.2,
     no_injective_fiveStepFreeLie4_into_mat16,
     fiveStepFreeLie4_ker_ne_bot_and_syzygy_bound,
     lyndonFreeLie4_linearIndependent,
     freeLie4_grade_finranks.2.2.2.2.2.2.2.2.2.2,
     freeLieAlgebra4_lift_mat16_not_injective_and_syzygy_ideal,
     ⟨g2ChevalleyX_serre_relation_and_fiveStep_kernel_rank.1,
      g2ChevalleyX_serre_relation_and_fiveStep_kernel_rank.2.2.1,
      g2ChevalleyX_serre_relation_and_fiveStep_kernel_rank.2.2.2.2.2.1,
      g2ChevalleyX_serre_relation_and_fiveStep_kernel_rank.2.2.2.2.2.2⟩,
     fiveStepRestrictedG2Eval_kernel_eq_candidate_span,
     fiveStepRestrictedG2Quotient_finrank⟩

/-- **Master `V. COAGULA` (`Ξ_⊤`) Typed Archetype**: unites all four mathematical pillars with the
15-node graded acyclic Hasse poset (`Covers`, antichains, boundedness, and `IsLUB {H, E} Ξ_⊤`). -/
def archMasterXiTopCoagulation : TypedArchetype Unit .proved where
  name := `archMasterXiTopCoagulation
  phase := 5
  claim := fun _ =>
    archKreinDerivationDefect.claim () ∧
    archKreinCl44BivectorShear.claim () ∧
    archCartanS3TrialitySplitG2.claim () ∧
    archWittPigeonholeAndJacobiCeiling.claim () ∧
    (∀ u v, Covers u v = true → nodeGrade u < nodeGrade v) ∧
    (∀ u v, Covers u v = true → u < v ∧ ¬ ∃ w, u < w ∧ w < v) ∧
    (¬ (KreinG2CausalNode.K_TT ≤ KreinG2CausalNode.G) ∧
     ¬ (KreinG2CausalNode.G ≤ KreinG2CausalNode.K_TT)) ∧
    IsLUB ({KreinG2CausalNode.H, KreinG2CausalNode.E} : Set KreinG2CausalNode)
      KreinG2CausalNode.Xi_top
  evidence := fun _ =>
    ⟨archKreinDerivationDefect.evidence (),
     archKreinCl44BivectorShear.evidence (),
     archCartanS3TrialitySplitG2.evidence (),
     archWittPigeonholeAndJacobiCeiling.evidence (),
     covers_strict_grade,
     covers_transitively_reduced,
     ⟨causal_antichains_verified.1.1, causal_antichains_verified.1.2.1⟩,
     xi_top_isLUB_H_E⟩

/-- Constructive theorem-level witness that the entire `PHASE 0 — SOLVE` to `V. COAGULA`
chain closes cleanly on `Krein16Idx` with complete proofs and zero custom axioms. -/
theorem master_xi_top_coagulation_holds :
    archMasterXiTopCoagulation.claim () ∧
    (∃ A B : Matrix Krein16Idx Krein16Idx ℝ, A * B ≠ B * A) ∧
    dotProduct majoranaRefSpinor (kreinMetric88.mulVec majoranaRefSpinor) = 2 ∧
    (∀ x : KreinG2CausalNode, KreinG2CausalNode.Delta0 ≤ x ∧ x ≤ KreinG2CausalNode.Xi_top) := by
  have hmaster : archMasterXiTopCoagulation.claim () :=
    archMasterXiTopCoagulation.evidence ()
  have hnc : ∃ A B : Matrix Krein16Idx Krein16Idx ℝ, A * B ≠ B * A :=
    krein16_matrix_noncommutative
  have hnorm : dotProduct majoranaRefSpinor (kreinMetric88.mulVec majoranaRefSpinor) = 2 :=
    majoranaRefSpinor_chiral_and_krein_norm.2
  have hbnd : ∀ x : KreinG2CausalNode,
      KreinG2CausalNode.Delta0 ≤ x ∧ x ≤ KreinG2CausalNode.Xi_top := by
    intro x
    have hbot := bot_le_all x
    have htop := all_le_top x
    exact ⟨hbot, htop⟩
  refine ⟨hmaster, hnc, hnorm, hbnd⟩

#register_archetype archKreinDerivationDefect
#audit_archetype archKreinDerivationDefect
#register_archetype archKreinCl44BivectorShear
#audit_archetype archKreinCl44BivectorShear
#register_archetype archCartanS3TrialitySplitG2
#audit_archetype archCartanS3TrialitySplitG2
#register_archetype archWittPigeonholeAndJacobiCeiling
#audit_archetype archWittPigeonholeAndJacobiCeiling
#register_archetype archMasterXiTopCoagulation
#audit_archetype archMasterXiTopCoagulation

end ArchetypeRegistrations

section KreinErlangenUnification

open scoped InnerProductSpace
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

theorem gamma44_transpose : gamma44ᵀ = gamma44 := by
  unfold gamma44
  rw [tensor4_transpose, cl11Grad_transpose]

private lemma euclidean_krein16_inner_eq_dotProduct
    (u v : EuclideanSpace ℝ Krein16Idx) :
    ⟪u, v⟫_ℝ = dotProduct (WithLp.ofLp u) (WithLp.ofLp v) := by
  rw [PiLp.inner_apply]
  simp only [dotProduct, Real.inner_apply]

noncomputable def toEuclideanCLM (M : Matrix Krein16Idx Krein16Idx ℝ) :
    EuclideanSpace ℝ Krein16Idx →L[ℝ] EuclideanSpace ℝ Krein16Idx :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

@[simp] lemma toEuclideanCLM_apply (M : Matrix Krein16Idx Krein16Idx ℝ)
    (u : EuclideanSpace ℝ Krein16Idx) :
    toEuclideanCLM M u = Matrix.toEuclideanLin M u := rfl

lemma toEuclideanCLM_one :
    toEuclideanCLM (1 : Matrix Krein16Idx Krein16Idx ℝ) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ Krein16Idx) := by
  apply ContinuousLinearMap.ext
  intro u
  simp [toEuclideanCLM, Matrix.toLpLin_one]

lemma toEuclideanCLM_mul (A B : Matrix Krein16Idx Krein16Idx ℝ) :
    toEuclideanCLM (A * B) = (toEuclideanCLM A).comp (toEuclideanCLM B) := by
  apply ContinuousLinearMap.ext
  intro u
  simp [toEuclideanCLM, Matrix.toLpLin_mul_same]

lemma toEuclideanCLM_add (A B : Matrix Krein16Idx Krein16Idx ℝ) :
    toEuclideanCLM (A + B) = toEuclideanCLM A + toEuclideanCLM B := by
  apply ContinuousLinearMap.ext
  intro u
  simp [toEuclideanCLM, map_add]

lemma toEuclideanCLM_neg (A : Matrix Krein16Idx Krein16Idx ℝ) :
    toEuclideanCLM (-A) = -(toEuclideanCLM A) := by
  apply ContinuousLinearMap.ext
  intro u
  simp [toEuclideanCLM, map_neg]

lemma toEuclideanCLM_injective : Function.Injective toEuclideanCLM := by
  intro A B h
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro u
  exact congrArg (fun T : EuclideanSpace ℝ Krein16Idx →L[ℝ] EuclideanSpace ℝ Krein16Idx => T u) h

private lemma symmInvolMatrix_selfAdj
    (M : Matrix Krein16Idx Krein16Idx ℝ) (hT : Mᵀ = M)
    (u v : EuclideanSpace ℝ Krein16Idx) :
    ⟪Matrix.toEuclideanLin M u, v⟫_ℝ = ⟪u, Matrix.toEuclideanLin M v⟫_ℝ := by
  rw [euclidean_krein16_inner_eq_dotProduct, euclidean_krein16_inner_eq_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  calc
    dotProduct (M *ᵥ WithLp.ofLp u) (WithLp.ofLp v)
        = dotProduct (WithLp.ofLp v) (M *ᵥ WithLp.ofLp u) := dotProduct_comm _ _
    _ = dotProduct (WithLp.ofLp u) (Mᵀ *ᵥ WithLp.ofLp v) :=
          (Matrix.dotProduct_transpose_mulVec M (WithLp.ofLp u) (WithLp.ofLp v)).symm
    _ = dotProduct (WithLp.ofLp u) (M *ᵥ WithLp.ofLp v) := by rw [hT]

noncomputable def symmInvolMatrixLIE
    (M : Matrix Krein16Idx Krein16Idx ℝ) (hT : Mᵀ = M) (hsq : M * M = 1) :
    EuclideanSpace ℝ Krein16Idx ≃ₗᵢ[ℝ] EuclideanSpace ℝ Krein16Idx where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (Matrix.toEuclideanLin M) (Matrix.toEuclideanLin M)
    (by
      ext u
      rw [LinearMap.comp_apply, LinearMap.id_apply, ← LinearMap.comp_apply,
        ← Matrix.toLpLin_mul_same, hsq, Matrix.toLpLin_one, LinearMap.id_apply])
    (by
      ext u
      rw [LinearMap.comp_apply, LinearMap.id_apply, ← LinearMap.comp_apply,
        ← Matrix.toLpLin_mul_same, hsq, Matrix.toLpLin_one, LinearMap.id_apply])
  norm_map' u := by
    change ‖Matrix.toEuclideanLin M u‖ = ‖u‖
    have hinvol : Matrix.toEuclideanLin M (Matrix.toEuclideanLin M u) = u := by
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hsq, Matrix.toLpLin_one,
        LinearMap.id_apply]
    have hinner :
        ⟪Matrix.toEuclideanLin M u, Matrix.toEuclideanLin M u⟫_ℝ = ⟪u, u⟫_ℝ := by
      rw [symmInvolMatrix_selfAdj M hT, hinvol]
    have hsqnorm : ‖Matrix.toEuclideanLin M u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner]
    nlinarith [norm_nonneg (Matrix.toEuclideanLin M u), norm_nonneg u]

/-- Canonical double-real Krein space instance on `EuclideanSpace ℝ Krein16Idx` induced by `kreinMetric88`. -/
noncomputable instance (priority := 1000) instKreinSpaceEuclideanKrein16Idx :
    InfoGeometry.Krein.KreinSpace (EuclideanSpace ℝ Krein16Idx) where
  J := symmInvolMatrixLIE kreinMetric88
    kreinMetric88_properties.2.1 kreinMetric88_properties.2.2.1
  J_invol u := by
    change Matrix.toEuclideanLin kreinMetric88 (Matrix.toEuclideanLin kreinMetric88 u) = u
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      kreinMetric88_properties.2.2.1, Matrix.toLpLin_one, LinearMap.id_apply]
  J_selfAdj u v := symmInvolMatrix_selfAdj kreinMetric88 kreinMetric88_properties.2.1 u v

/-- Canonical chiral grading module on `EuclideanSpace ℝ Krein16Idx` induced by `gamma44`. -/
noncomputable instance instKreinGradedModuleEuclideanKrein16Idx :
    InfoGeometry.Krein.KreinGradedModule (EuclideanSpace ℝ Krein16Idx) where
  grade := symmInvolMatrixLIE gamma44 gamma44_transpose gamma44_properties.2.1
  grade_invol u := by
    change Matrix.toEuclideanLin gamma44 (Matrix.toEuclideanLin gamma44 u) = u
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      gamma44_properties.2.1, Matrix.toLpLin_one, LinearMap.id_apply]
  grade_selfAdj u v := symmInvolMatrix_selfAdj gamma44 gamma44_transpose u v

@[simp] lemma jCLM_euclideanKrein16Idx :
    InfoGeometry.Krein.KreinSpace.jCLM (H := EuclideanSpace ℝ Krein16Idx) =
      toEuclideanCLM kreinMetric88 := rfl

@[simp] lemma gradeCLM_euclideanKrein16Idx :
    InfoGeometry.Krein.KreinGradedModule.gradeCLM (H := EuclideanSpace ℝ Krein16Idx) =
      toEuclideanCLM gamma44 := rfl

theorem kreinInner_euclideanKrein16Idx (u v : EuclideanSpace ℝ Krein16Idx) :
    InfoGeometry.Krein.KreinSpace.kreinInner u v =
      dotProduct (WithLp.ofLp u) (kreinMetric88.mulVec (WithLp.ofLp v)) := by
  rw [InfoGeometry.Krein.KreinSpace.kreinInner_def]
  change ⟪Matrix.toEuclideanLin kreinMetric88 u, v⟫_ℝ = _
  rw [symmInvolMatrix_selfAdj kreinMetric88 kreinMetric88_properties.2.1,
    euclidean_krein16_inner_eq_dotProduct]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

theorem adjoint_toEuclideanCLM (M : Matrix Krein16Idx Krein16Idx ℝ) :
    ContinuousLinearMap.adjoint (toEuclideanCLM M) = toEuclideanCLM Mᵀ := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := toEuclideanCLM Mᵀ) (B := toEuclideanCLM M)).2 ?_
  intro u v
  rw [euclidean_krein16_inner_eq_dotProduct, euclidean_krein16_inner_eq_dotProduct]
  simp only [toEuclideanCLM_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  calc
    dotProduct (Mᵀ *ᵥ WithLp.ofLp u) (WithLp.ofLp v)
        = dotProduct (WithLp.ofLp v) (Mᵀ *ᵥ WithLp.ofLp u) := dotProduct_comm _ _
    _ = dotProduct (WithLp.ofLp u) (M *ᵥ WithLp.ofLp v) := by
          rw [← Matrix.dotProduct_transpose_mulVec Mᵀ (WithLp.ofLp u) (WithLp.ofLp v),
            Matrix.transpose_transpose]

theorem kreinAdjoint_toEuclideanCLM (M : Matrix Krein16Idx Krein16Idx ℝ) :
    InfoGeometry.Krein.KreinSpace.kreinAdjoint (toEuclideanCLM M) =
      toEuclideanCLM (kreinMetric88 * Mᵀ * kreinMetric88) := by
  rw [InfoGeometry.Krein.KreinSpace.kreinAdjoint, jCLM_euclideanKrein16Idx,
    adjoint_toEuclideanCLM, ← toEuclideanCLM_mul, ← toEuclideanCLM_mul, Matrix.mul_assoc]

theorem isKreinSkewAdjoint_toEuclideanCLM_iff (M : Matrix Krein16Idx Krein16Idx ℝ) :
    InfoGeometry.Krein.KreinSpace.IsKreinSkewAdjoint (toEuclideanCLM M) ↔
      Mᵀ * kreinMetric88 + kreinMetric88 * M = 0 := by
  unfold InfoGeometry.Krein.KreinSpace.IsKreinSkewAdjoint
  rw [kreinAdjoint_toEuclideanCLM, ← toEuclideanCLM_neg]
  rw [toEuclideanCLM_injective.eq_iff]
  constructor
  · intro h
    have hmul : kreinMetric88 * (kreinMetric88 * Mᵀ * kreinMetric88) =
        kreinMetric88 * (-M) := congrArg (kreinMetric88 * ·) h
    have h1 : Mᵀ * kreinMetric88 = -(kreinMetric88 * M) := by
      calc
        Mᵀ * kreinMetric88
            = (kreinMetric88 * kreinMetric88) * (Mᵀ * kreinMetric88) := by
                rw [kreinMetric88_properties.2.2.1, Matrix.one_mul]
        _ = kreinMetric88 * (kreinMetric88 * Mᵀ * kreinMetric88) := by
                simp only [Matrix.mul_assoc]
        _ = kreinMetric88 * (-M) := hmul
        _ = -(kreinMetric88 * M) := Matrix.mul_neg _ _
    exact add_eq_zero_iff_eq_neg.mpr h1
  · intro h
    have h1 : Mᵀ * kreinMetric88 = -(kreinMetric88 * M) := add_eq_zero_iff_eq_neg.mp h
    calc
      kreinMetric88 * Mᵀ * kreinMetric88
          = kreinMetric88 * (Mᵀ * kreinMetric88) := by rw [Matrix.mul_assoc]
      _ = kreinMetric88 * (-(kreinMetric88 * M)) := by rw [h1]
      _ = -((kreinMetric88 * kreinMetric88) * M) := by
            rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = -M := by rw [kreinMetric88_properties.2.2.1, Matrix.one_mul]

theorem isKreinSelfAdjoint_toEuclideanCLM_iff (M : Matrix Krein16Idx Krein16Idx ℝ) :
    InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint (toEuclideanCLM M) ↔
      Mᵀ * kreinMetric88 = kreinMetric88 * M := by
  unfold InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint
  rw [kreinAdjoint_toEuclideanCLM, toEuclideanCLM_injective.eq_iff]
  constructor
  · intro h
    have hmul : kreinMetric88 * (kreinMetric88 * Mᵀ * kreinMetric88) =
        kreinMetric88 * M := congrArg (kreinMetric88 * ·) h
    calc
      Mᵀ * kreinMetric88
          = (kreinMetric88 * kreinMetric88) * (Mᵀ * kreinMetric88) := by
              rw [kreinMetric88_properties.2.2.1, Matrix.one_mul]
      _ = kreinMetric88 * (kreinMetric88 * Mᵀ * kreinMetric88) := by
              simp only [Matrix.mul_assoc]
      _ = kreinMetric88 * M := hmul
  · intro h
    calc
      kreinMetric88 * Mᵀ * kreinMetric88
          = kreinMetric88 * (Mᵀ * kreinMetric88) := by rw [Matrix.mul_assoc]
      _ = (kreinMetric88 * kreinMetric88) * M := by rw [h, Matrix.mul_assoc]
      _ = M := by rw [kreinMetric88_properties.2.2.1, Matrix.one_mul]

theorem isKreinIsometry_toEuclideanCLM_iff (M : Matrix Krein16Idx Krein16Idx ℝ) :
    InfoGeometry.Krein.KreinSpace.IsKreinIsometry (toEuclideanCLM M) ↔
      Mᵀ * kreinMetric88 * M = kreinMetric88 := by
  rw [InfoGeometry.Krein.KreinSpace.isKreinIsometry_iff_star_comp_self,
    kreinAdjoint_toEuclideanCLM, ← toEuclideanCLM_mul, ← toEuclideanCLM_one,
    toEuclideanCLM_injective.eq_iff]
  constructor
  · intro h
    have hmul : kreinMetric88 * (kreinMetric88 * Mᵀ * kreinMetric88 * M) =
        kreinMetric88 * 1 := congrArg (kreinMetric88 * ·) h
    calc
      Mᵀ * kreinMetric88 * M
          = (kreinMetric88 * kreinMetric88) * (Mᵀ * kreinMetric88 * M) := by
              rw [kreinMetric88_properties.2.2.1, Matrix.one_mul]
      _ = kreinMetric88 * (kreinMetric88 * Mᵀ * kreinMetric88 * M) := by
              simp only [Matrix.mul_assoc]
      _ = kreinMetric88 * 1 := hmul
      _ = kreinMetric88 := Matrix.mul_one _
  · intro h
    calc
      kreinMetric88 * Mᵀ * kreinMetric88 * M
          = kreinMetric88 * (Mᵀ * kreinMetric88 * M) := by simp only [Matrix.mul_assoc]
      _ = kreinMetric88 * kreinMetric88 := by rw [h]
      _ = 1 := kreinMetric88_properties.2.2.1

theorem isEven_toEuclideanCLM_iff (M : Matrix Krein16Idx Krein16Idx ℝ) :
    InfoGeometry.Krein.KreinGradedModule.IsEven (toEuclideanCLM M) ↔
      M * gamma44 = gamma44 * M := by
  unfold InfoGeometry.Krein.KreinGradedModule.IsEven
    InfoGeometry.Krein.KreinGradedModule.gradeConj
  rw [gradeCLM_euclideanKrein16Idx, ← toEuclideanCLM_mul, ← toEuclideanCLM_mul,
    toEuclideanCLM_injective.eq_iff]
  constructor
  · intro h
    have hmul : gamma44 * (gamma44 * (M * gamma44)) = gamma44 * M :=
      congrArg (gamma44 * ·) h
    calc
      M * gamma44
          = (gamma44 * gamma44) * (M * gamma44) := by
              rw [gamma44_properties.2.1, Matrix.one_mul]
      _ = gamma44 * (gamma44 * (M * gamma44)) := by simp only [Matrix.mul_assoc]
      _ = gamma44 * M := hmul
  · intro h
    calc
      gamma44 * (M * gamma44) = gamma44 * (gamma44 * M) := by rw [h]
      _ = (gamma44 * gamma44) * M := by rw [Matrix.mul_assoc]
      _ = M := by rw [gamma44_properties.2.1, Matrix.one_mul]

theorem isOdd_toEuclideanCLM_iff (M : Matrix Krein16Idx Krein16Idx ℝ) :
    InfoGeometry.Krein.KreinGradedModule.IsOdd (toEuclideanCLM M) ↔
      M * gamma44 + gamma44 * M = 0 := by
  unfold InfoGeometry.Krein.KreinGradedModule.IsOdd
    InfoGeometry.Krein.KreinGradedModule.gradeConj
  rw [gradeCLM_euclideanKrein16Idx, ← toEuclideanCLM_mul, ← toEuclideanCLM_mul,
    ← toEuclideanCLM_neg, toEuclideanCLM_injective.eq_iff]
  constructor
  · intro h
    have hmul : gamma44 * (gamma44 * (M * gamma44)) = gamma44 * (-M) :=
      congrArg (gamma44 * ·) h
    have h1 : M * gamma44 = -(gamma44 * M) := by
      calc
        M * gamma44
            = (gamma44 * gamma44) * (M * gamma44) := by
                rw [gamma44_properties.2.1, Matrix.one_mul]
        _ = gamma44 * (gamma44 * (M * gamma44)) := by simp only [Matrix.mul_assoc]
        _ = gamma44 * (-M) := hmul
        _ = -(gamma44 * M) := Matrix.mul_neg _ _
    exact add_eq_zero_iff_eq_neg.mpr h1
  · intro h
    have h1 : M * gamma44 = -(gamma44 * M) := add_eq_zero_iff_eq_neg.mp h
    calc
      gamma44 * (M * gamma44) = gamma44 * (-(gamma44 * M)) := by rw [h1]
      _ = -((gamma44 * gamma44) * M) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = -M := by rw [gamma44_properties.2.1, Matrix.one_mul]

theorem cl44Gen_isKreinSelfAdjoint_and_isOdd (a : Fin 8) :
    InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint (toEuclideanCLM (cl44Gen a)) ∧
    InfoGeometry.Krein.KreinGradedModule.IsOdd (toEuclideanCLM (cl44Gen a)) :=
  ⟨(isKreinSelfAdjoint_toEuclideanCLM_iff (cl44Gen a)).2 (cl44Gen_krein_symm a),
   (isOdd_toEuclideanCLM_iff (cl44Gen a)).2 (gamma44_properties.2.2.2 a)⟩

/-- Positive-definite Krein spinor witness on `EuclideanSpace ℝ Krein16Idx` (`kreinInner = +2`). -/
def krein16PosWitness : EuclideanSpace ℝ Krein16Idx :=
  WithLp.toLp 2 majoranaRefSpinor

/-- Negative-definite Krein spinor witness on `EuclideanSpace ℝ Krein16Idx` (`kreinInner = -2`). -/
def krein16NegWitness : EuclideanSpace ℝ Krein16Idx :=
  WithLp.toLp 2 ((cl44Gen 4).mulVec majoranaRefSpinor)

theorem krein16PosWitness_kreinInner :
    InfoGeometry.Krein.KreinSpace.kreinInner krein16PosWitness krein16PosWitness = 2 := by
  rw [kreinInner_euclideanKrein16Idx]
  exact majoranaRefSpinor_chiral_and_krein_norm.2

theorem krein16NegWitness_kreinInner :
    InfoGeometry.Krein.KreinSpace.kreinInner krein16NegWitness krein16NegWitness = -2 := by
  rw [kreinInner_euclideanKrein16Idx]
  change dotProduct ((cl44Gen 4).mulVec majoranaRefSpinor)
      (kreinMetric88.mulVec ((cl44Gen 4).mulVec majoranaRefSpinor)) = -2
  have hsq4 : cl44Gen 4 * cl44Gen 4 = -1 := by
    rw [cl44Gen_sq]
    norm_num
  have hmat : (cl44Gen 4)ᵀ * kreinMetric88 * cl44Gen 4 = -kreinMetric88 := by
    rw [cl44Gen_krein_symm 4, Matrix.mul_assoc, hsq4, Matrix.mul_neg, Matrix.mul_one]
  calc
    dotProduct ((cl44Gen 4).mulVec majoranaRefSpinor)
        (kreinMetric88.mulVec ((cl44Gen 4).mulVec majoranaRefSpinor))
        = dotProduct (kreinMetric88.mulVec ((cl44Gen 4).mulVec majoranaRefSpinor))
            ((cl44Gen 4).mulVec majoranaRefSpinor) := dotProduct_comm _ _
    _ = dotProduct majoranaRefSpinor
          ((cl44Gen 4)ᵀ *ᵥ (kreinMetric88.mulVec ((cl44Gen 4).mulVec majoranaRefSpinor))) :=
          (Matrix.dotProduct_transpose_mulVec (cl44Gen 4) majoranaRefSpinor
            (kreinMetric88.mulVec ((cl44Gen 4).mulVec majoranaRefSpinor))).symm
    _ = dotProduct majoranaRefSpinor
          (((cl44Gen 4)ᵀ * kreinMetric88 * cl44Gen 4).mulVec majoranaRefSpinor) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = dotProduct majoranaRefSpinor ((-kreinMetric88).mulVec majoranaRefSpinor) := by
          rw [hmat]
    _ = -dotProduct majoranaRefSpinor (kreinMetric88.mulVec majoranaRefSpinor) := by
          rw [Matrix.neg_mulVec, dotProduct_neg]
    _ = -2 := by rw [majoranaRefSpinor_chiral_and_krein_norm.2]

/-- Explicit indefiniteness certificate for the double-real Krein metric on `EuclideanSpace ℝ Krein16Idx`. -/
theorem krein16_kreinInner_indefinite :
    0 < InfoGeometry.Krein.KreinSpace.kreinInner krein16PosWitness krein16PosWitness ∧
    InfoGeometry.Krein.KreinSpace.kreinInner krein16NegWitness krein16NegWitness < 0 := by
  rw [krein16PosWitness_kreinInner, krein16NegWitness_kreinInner]
  norm_num

/-- Associative `Cl(4,4)` matrix subalgebra generated by the 8 Dirac–Majorana matrices `cl44Gen`. -/
def cl44MatrixSubalgebra : Subalgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Algebra.adjoin ℝ (Set.range cl44Gen)

theorem cl44Bivector_mem_cl44MatrixSubalgebra (a b : Fin 8) :
    cl44Bivector a b ∈ cl44MatrixSubalgebra := by
  exact Subalgebra.mul_mem _
    (Algebra.subset_adjoin (Set.mem_range_self a))
    (Algebra.subset_adjoin (Set.mem_range_self b))

theorem g2Submodule_le_cl44MatrixSubalgebra :
    g2Submodule ≤ cl44MatrixSubalgebra.toSubmodule := by
  intro B hB
  have hbiv : B ∈ cl44BivectorSpan := g2Submodule_le_bivectorSpan hB
  refine Submodule.span_induction (hx := hbiv) ?_ ?_ ?_ ?_
  · rintro _ ⟨a, b, _, rfl⟩
    exact cl44Bivector_mem_cl44MatrixSubalgebra a b
  · exact Subalgebra.zero_mem _
  · intro x y _ _ hx hy
    exact Subalgebra.add_mem _ hx hy
  · intro r x _ hx
    exact Subalgebra.smul_mem _ hx r

/-- Associative operator subalgebra `Cl(4,4) ⊆ End(EuclideanSpace ℝ Krein16Idx)`. -/
noncomputable def cl44EuclideanOperatorAlgebra :
    Subalgebra ℝ (Module.End ℝ (EuclideanSpace ℝ Krein16Idx)) :=
  Subalgebra.map (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).toAlgHom
    cl44MatrixSubalgebra

/-- Faithful Lie-algebra representation `g_{2(2)} →ₗ⁅ℝ⁆ End(EuclideanSpace ℝ Krein16Idx)`. -/
noncomputable def g2EuclideanRep :
    g2LieSubalgebra →ₗ⁅ℝ⁆ Module.End ℝ (EuclideanSpace ℝ Krein16Idx) where
  toLinearMap := (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).toLinearMap.comp
    g2Submodule.subtype
  map_lie' {X Y} := by
    change Matrix.toLpLinAlgEquiv 2 (X.1 * Y.1 - Y.1 * X.1) =
      Matrix.toLpLinAlgEquiv 2 X.1 * Matrix.toLpLinAlgEquiv 2 Y.1 -
        Matrix.toLpLinAlgEquiv 2 Y.1 * Matrix.toLpLinAlgEquiv 2 X.1
    rw [map_sub, map_mul, map_mul]

theorem g2EuclideanRep_injective : Function.Injective g2EuclideanRep := by
  intro X Y hXY
  apply Subtype.ext
  exact (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).injective hXY

/-- Erlangen 2.0 operator-geometry datum for the split `g_{2(2)}` stabilizer inside `Cl(4,4)` acting
on the double-real Krein spinor module `EuclideanSpace ℝ Krein16Idx`. -/
noncomputable def g2Erlangen20Datum :
    InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.Erlangen20Datum
      ℝ
      (EuclideanSpace ℝ Krein16Idx)
      g2LieSubalgebra
      (Module.End ℝ (EuclideanSpace ℝ Krein16Idx) ×
        Module.End ℝ (EuclideanSpace ℝ Krein16Idx) ×
        Module.End ℝ (EuclideanSpace ℝ Krein16Idx))
      (EuclideanSpace ℝ Krein16Idx) where
  operatorAlgebra := cl44EuclideanOperatorAlgebra
  representation := g2EuclideanRep
  representation_mem X := ⟨X.1, g2Submodule_le_cl44MatrixSubalgebra X.2, rfl⟩
  symmetryData :=
    (Matrix.toEuclideanLin kreinMetric88,
     Matrix.toEuclideanLin gamma44,
     Matrix.toEuclideanLin (cl44Gen 0))
  invariantData := krein16PosWitness

theorem g2Erlangen20Datum_stabilizer_laws (X : g2LieSubalgebra) :
    InfoGeometry.Krein.KreinSpace.IsKreinSkewAdjoint (toEuclideanCLM X.1) ∧
    InfoGeometry.Krein.KreinGradedModule.IsEven (toEuclideanCLM X.1) ∧
    (g2Erlangen20Datum.representation X) * g2Erlangen20Datum.symmetryData.2.2 =
      g2Erlangen20Datum.symmetryData.2.2 * (g2Erlangen20Datum.representation X) ∧
    g2Erlangen20Datum.representation X g2Erlangen20Datum.invariantData = 0 := by
  have hstab : IsSplitG2Stabilizer X.1 := g2Submodule_mem_stabilizer X.2
  refine ⟨(isKreinSkewAdjoint_toEuclideanCLM_iff X.1).2 hstab.1,
    (isEven_toEuclideanCLM_iff X.1).2 hstab.2.1, ?_, ?_⟩
  · change Matrix.toLpLinAlgEquiv 2 X.1 * Matrix.toLpLinAlgEquiv 2 (cl44Gen 0) =
      Matrix.toLpLinAlgEquiv 2 (cl44Gen 0) * Matrix.toLpLinAlgEquiv 2 X.1
    rw [← map_mul, ← map_mul, hstab.2.2.1]
  · apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    change X.1.mulVec majoranaRefSpinor = 0
    exact hstab.2.2.2

/-- Conjugation algebra automorphism on `M₁₆(ℝ)` induced by `u ∈ SplitG2MatrixGroup`. -/
noncomputable def splitG2ConjAlgEquiv (u : SplitG2MatrixGroup) :
    Matrix Krein16Idx Krein16Idx ℝ ≃ₐ[ℝ] Matrix Krein16Idx Krein16Idx ℝ where
  toFun X := u.1.val * X * (u.1⁻¹).val
  invFun X := (u.1⁻¹).val * X * u.1.val
  left_inv X := by
    calc
      (u.1⁻¹).val * (u.1.val * X * (u.1⁻¹).val) * u.1.val
          = ((u.1⁻¹ * u.1 : Matrix.GeneralLinearGroup Krein16Idx ℝ).val) * X *
              ((u.1⁻¹ * u.1 : Matrix.GeneralLinearGroup Krein16Idx ℝ).val) := by
                simp only [Units.val_mul, Matrix.mul_assoc]
      _ = X := by simp
  right_inv X := by
    calc
      u.1.val * ((u.1⁻¹).val * X * u.1.val) * (u.1⁻¹).val
          = ((u.1 * u.1⁻¹ : Matrix.GeneralLinearGroup Krein16Idx ℝ).val) * X *
              ((u.1 * u.1⁻¹ : Matrix.GeneralLinearGroup Krein16Idx ℝ).val) := by
                simp only [Units.val_mul, Matrix.mul_assoc]
      _ = X := by simp
  map_mul' X Y := by
    calc
      u.1.val * (X * Y) * (u.1⁻¹).val
          = u.1.val * X * (1 : Matrix Krein16Idx Krein16Idx ℝ) * Y * (u.1⁻¹).val := by
              simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = u.1.val * X * ((u.1⁻¹ * u.1 : Matrix.GeneralLinearGroup Krein16Idx ℝ).val) * Y *
            (u.1⁻¹).val := by
              rw [inv_mul_cancel, Units.val_one]
      _ = (u.1.val * X * (u.1⁻¹).val) * (u.1.val * Y * (u.1⁻¹).val) := by
            simp only [Units.val_mul, Matrix.mul_assoc]
  map_add' X Y := by
    rw [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    calc
      u.1.val * algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) r * (u.1⁻¹).val
          = u.1.val * (u.1⁻¹).val * algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) r := by
              rw [Matrix.mul_assoc, Algebra.commutes, ← Matrix.mul_assoc]
      _ = ((u.1 * u.1⁻¹ : Matrix.GeneralLinearGroup Krein16Idx ℝ).val) *
            algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) r := by
              rw [Units.val_mul]
      _ = algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) r := by
              rw [mul_inv_cancel, Units.val_one, Matrix.one_mul]

/-- Left `SymmetryAction` of `SplitG2MatrixGroup` on `M₁₆(ℝ)` by conjugation. -/
noncomputable def splitG2MatrixSymmetryAction :
    InfoGeometry.OperatorAlgebra.SymmetryAction SplitG2MatrixGroup
      (Matrix Krein16Idx Krein16Idx ℝ) where
  act u := (splitG2ConjAlgEquiv u).toRingEquiv
  act_one X := by
    change (1 : Matrix.GeneralLinearGroup Krein16Idx ℝ).val * X *
      ((1 : Matrix.GeneralLinearGroup Krein16Idx ℝ)⁻¹).val = X
    simp
  act_mul g h X := by
    change (g.1 * h.1).val * X * ((g.1 * h.1)⁻¹).val =
      g.1.val * (h.1.val * X * (h.1⁻¹).val) * (g.1⁻¹).val
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]

/-- Left `SymmetryAction` of `SplitG2MatrixGroup` on `End(EuclideanSpace ℝ Krein16Idx)` by conjugation. -/
noncomputable def splitG2EuclideanSymmetryAction :
    InfoGeometry.OperatorAlgebra.SymmetryAction SplitG2MatrixGroup
      (Module.End ℝ (EuclideanSpace ℝ Krein16Idx)) where
  act u :=
    ((Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).symm.trans
      ((splitG2ConjAlgEquiv u).trans
        (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)))).toRingEquiv
  act_one T := by
    change (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx))
      (splitG2ConjAlgEquiv 1
        ((Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).symm T)) = T
    rw [show splitG2ConjAlgEquiv 1
        ((Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).symm T) =
      (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).symm T from
        splitG2MatrixSymmetryAction.act_one _]
    exact AlgEquiv.apply_symm_apply _ T
  act_mul g h T := by
    change Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv (g * h)
        ((Matrix.toLpLinAlgEquiv 2).symm T)) =
      Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv g
        ((Matrix.toLpLinAlgEquiv 2).symm (Matrix.toLpLinAlgEquiv 2
          (splitG2ConjAlgEquiv h ((Matrix.toLpLinAlgEquiv 2).symm T)))))
    rw [AlgEquiv.symm_apply_apply]
    exact congrArg (Matrix.toLpLinAlgEquiv 2) (splitG2MatrixSymmetryAction.act_mul g h _)

/-- `OperatorSymmetryAction` packaging `splitG2ConjAlgEquiv` with inverse-reversed `GroupAction` convention. -/
noncomputable def splitG2OperatorSymmetryAction :
    InfoGeometry.OperatorAlgebra.OperatorSymmetryAction SplitG2MatrixGroup
      (Matrix Krein16Idx Krein16Idx ℝ) where
  toFun g := splitG2ConjAlgEquiv g⁻¹
  map_one' := by
    apply AlgEquiv.ext
    intro X
    simp [splitG2ConjAlgEquiv]
  map_mul' g₁ g₂ := by
    apply AlgEquiv.ext
    intro X
    change ((g₁ * g₂)⁻¹).1.val * X * (((g₁ * g₂)⁻¹)⁻¹).1.val =
      (g₂⁻¹).1.val * ((g₁⁻¹).1.val * X * ((g₁⁻¹)⁻¹).1.val) * ((g₂⁻¹)⁻¹).1.val
    simp only [inv_inv, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

theorem toSymmetryAction_splitG2OperatorSymmetryAction :
    InfoGeometry.OperatorAlgebra.toSymmetryAction splitG2OperatorSymmetryAction =
      splitG2MatrixSymmetryAction := rfl

/-- Erlangen invariants of `SplitG2MatrixGroup`: `kreinMetric88` is preserved as a Krein isometry,
while `gamma44`, `cl44Gen 0`, and `cl44Vec1Submodule` are conjugation-invariant, and 1-parameter
`expMat16GL` subgroups act on `cl44Vec1Submodule` via `NormedSpace.exp (t • rhoVec8 Z)`. -/
theorem splitG2_erlangen_invariants :
    (∀ u : SplitG2MatrixGroup,
      InfoGeometry.Krein.KreinSpace.IsKreinIsometry (toEuclideanCLM u.1.val)) ∧
    InfoGeometry.OperatorAlgebra.IsInvariant splitG2MatrixSymmetryAction gamma44 ∧
    InfoGeometry.OperatorAlgebra.IsInvariant splitG2MatrixSymmetryAction (cl44Gen 0) ∧
    (∀ u : SplitG2MatrixGroup, ∀ v ∈ cl44Vec1Submodule,
      splitG2MatrixSymmetryAction.act u v ∈ cl44Vec1Submodule) ∧
    (∀ Z : g2LieSubalgebra, ∀ (t : ℝ) (b : Fin 8),
      splitG2MatrixSymmetryAction.act
        ⟨expMat16GL Z.1 t, expMat16GL_mem_splitG2MatrixGroup Z.2 t⟩ (cl44Gen b) =
        ∑ a : Fin 8, (NormedSpace.exp (t • rhoVec8 Z.1) a b) • cl44Gen a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u
    exact (isKreinIsometry_toEuclideanCLM_iff u.1.val).2 u.2.1
  · intro u
    change u.1.val * gamma44 * (u.1⁻¹).val = gamma44
    rw [u.2.2.1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · intro u
    change u.1.val * cl44Gen 0 * (u.1⁻¹).val = cl44Gen 0
    rw [u.2.2.2.1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · intro u v hv
    exact u.2.2.2.2.2 v hv
  · intro Z t b
    change (expMat16GL Z.1 t).val * cl44Gen b * ((expMat16GL Z.1 t)⁻¹).val = _
    have hinv : ((expMat16GL Z.1 t)⁻¹).val = NormedSpace.exp ((-t) • Z.1) := rfl
    rw [hinv]
    exact expMat16GL_cl44_intertwining Z.2 t b

end KreinErlangenUnification

end InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
