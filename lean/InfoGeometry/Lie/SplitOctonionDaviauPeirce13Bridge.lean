/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionCayleyDickson
import InfoGeometry.Canonical.SplitOctonionChiralNullDecomposition
import InfoGeometry.Lie.SplitOctonionCl33G2Stabilizer
import InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
import InfoGeometry.Lie.KreinCl44TrialityBottCayleyClosure
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
import InfoGeometry.Clifford.SplitQ44
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Clifford.RealSpacetimeQuaternion
import InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge
import InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
import InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
import InfoGeometry.Krein.DoubledSpace

/-!
# Split-Octonion Daviau Peirce 1+3, Cl(3,3)-Cl(4,4) Embedding, and Repository Bridges

This module bridges the M1–M3 split-octonion Cayley–Dickson, chiral Zorn nullspace,
and polarized `Cl(3,3) ≃ₐ[ℝ] M₈(ℝ)` / `G_{2(2)}` stabilizer constructions to:

1. **Daviau / `Cl(4,4)` / Peirce `1 + 3` & `KreinCl44SplitG2DerivationPosetSynthesis` (F13)**:
   - Chiral Weyl embeddings `cl33ToCl44EvenLeft` / `cl33ToCl44EvenRight` (`Cl(3,3) ↪ Cl⁰(4,4)`
     `≃ M₈(ℝ) × M₈(ℝ)`), orthogonal completeness `P_+ + P_- = 1`, `Cl⁰(4,4) ≃ gamma44Commutant`,
     and exact dimensions `64`, `128`, `256`.
   - Split Bott periodicity `Cl(4,4) ≃ₐ[ℝ] Cl(1,1) ᵍ⊗[ℝ] Cl(3,3)`, ungraded tensor product
     `Cl(4,4) ≃ₐ[ℝ] Cl(1,1) ⊗[ℝ] Cl(3,3) ≃ₐ[ℝ] M₂(ℝ) ⊗[ℝ] M₈(ℝ)`, and `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)`
     with `4 * 64 = 256`.
   - Real spacetime `Cl(1,3) ≃ₐ[ℝ] M₂(ℍ)` action on `SplitOctCD ≃ₗ[ℝ] ℍ × ℍ` (`𝒩_+ ⊕ 𝒩_-`)
     sending `timeProjector` to the `𝒩_+` chiral projector, `spatialSwap` to `𝒩_+ ↔ 𝒩_-`,
     and `diagonalQuaternion` to the `1 + 3` splitting matching `zorn_1331_decomposition`.
   - Exact Lie-algebra isomorphism `g2LieSubalgebra ≃ₗ⁅ℝ⁆ cdDerivSubalgebra` via the
     diagonal sign involution `cdG2SignMatrix = diag(1, 1, 1, 1, 1, -1, -1, -1)`, embedding
     the 8 `et0Op`-commuting generators into `cdEllDerivStabilizer`, transporting `J44`-skewness,
     and intertwining `expMat16GL` in `SplitG2MatrixGroup` with `SplitOctCDAut ⊂ SO44Subgroup`.
2. **`ZornDifferentialFormsCliffordBridge` & Exterior Fock Space (F14)**:
   - `zornCl33FormHodgeData : FormHodgeCliffordData ℝ (Fin 6 → ℝ) (Matrix (Fin 8) (Fin 8) ℝ)`
     with `cliffordMorphism = cliffordQ33ToMat8.toAlgHom` and grade-raising differential.
   - `ext3ToSplitOctCD : ExteriorAlgebra ℝ (Fin 3 → ℝ) ≃ₗ[ℝ] SplitOctCD` (Option A vacuum
     `∅ ↦ uPlusCD`, `Λ¹ ↦ span(eMinusCD)`, `Λ² ↦ span(ePlusCD)`, `Λ³ ↦ span(uMinusCD)`)
     intertwining `exteriorContract`, `exteriorWedge`, and `KahlerDirac` Chevalley operators
     with `leftMulMat`, plus `chevalleyFockEval` intertwining the 64D `chevalleyAction`.
3. **`InfoGeometry.Krein.DoubledSpace` (F15)**:
   - Isometric Krein equivalences `cdToDoubledChiralEquiv` (preserving `nullPairing = cdKreinForm`,
     intertwining `ellCD * ·` with `spectral_epsilon`, `cdGradingInvolution` with `modular_j`,
     `cdComplexI` with `complex_i`) and `cdToDoubledSplitEquiv` (preserving `kreinInner`).

## Scope & Open Boundary (`[bucket_3_open_debt]`)

All results proved here are strictly finite-dimensional algebraic, Clifford, Lie-algebraic,
one-parameter exponential, and Krein-space correspondences. Global 14D Lie-group
classification `Aut(SplitOctCD) ≃* G_{2(2)}` and physical Daviau interpretations (double
space-time manifolds, affine torsion rest mass, Dirac wave equations, electroweak/3+1
generations) lie outside the algebraic scope of this module (`[bucket_3_open_debt]`).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge

open scoped TensorProduct Matrix BigOperators
open InfoGeometry.Canonical.SplitOctonionCayleyDickson
open InfoGeometry.Canonical.SplitOctonionChiralNullDecomposition
open InfoGeometry.Lie.SplitOctonionCl33G2Stabilizer
open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
open InfoGeometry.Lie.KreinCl44TrialityBottCayleyClosure
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
open InfoGeometry.Clifford.RealSpacetimeQuaternion
open InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge
open InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
open InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
open InfoGeometry.Krein

/-! ## Section 1: Closed Non-Commutativity Witnesses (Trap T16) -/

/-- Closed T16 non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem t16_mat8_noncommutative :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A :=
  mat8_real_noncommutative

/-- Closed T16 non-commutativity witness for `Matrix Krein16Idx Krein16Idx ℝ`. -/
theorem t16_mat16_noncommutative :
    ∃ A B : Matrix Krein16Idx Krein16Idx ℝ, A * B ≠ B * A :=
  krein16_matrix_noncommutative

/-- Closed T16 non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem t16_mat2_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  mat2_noncommutative

/-- Closed T16 non-commutativity witness for `Quaternion ℝ`. -/
theorem t16_quaternion_noncommutative :
    ∃ x y : Quaternion ℝ, x * y ≠ y * x :=
  quaternion_noncommutative

/-- Closed T16 non-commutativity witness for `Matrix (Fin 2) (Fin 2) (Quaternion ℝ)`. -/
theorem t16_quatMatrix_noncommutative :
    ∃ A B : QuaternionMatrix, A * B ≠ B * A :=
  quaternionMatrix_noncommutative

/-- Closed T16 non-commutativity witness for `CliffordAlgebra Q33`. -/
theorem t16_cliffordQ33_noncommutative :
    ∃ a b : CliffordAlgebra Q33, a * b ≠ b * a :=
  ⟨_, _, cliffordQ33_noncommutative⟩

/-- Closed T16 non-commutativity witness for `HestenesCl14.Cl14`. -/
theorem t16_cl14_noncommutative :
    ∃ a b : HestenesCl14.Cl14, a * b ≠ b * a :=
  ⟨HestenesCl14.gamma 1, HestenesCl14.gamma 2, gamma_one_two_ne⟩

private lemma cl44AlgEquivMat16_iota_single (i : Fin 8) :
    cl44AlgEquivMat16
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single i 1)) = cl44Gen i := by
  have hι : cl44AlgEquivMat16
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single i 1)) =
      ∑ j : Fin 8, (Pi.single i (1 : ℝ) : Fin 8 → ℝ) j • cl44Gen j := by
    change CliffordAlgebra.lift InfoGeometry.Clifford.splitQ44 _
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single i 1)) = _
    rw [CliffordAlgebra.lift_ι_apply]
    rfl
  rw [hι, Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Closed T16 non-commutativity witness for `CliffordAlgebra InfoGeometry.Clifford.splitQ44`. -/
theorem t16_cl44_noncommutative :
    ∃ a b : CliffordAlgebra InfoGeometry.Clifford.splitQ44, a * b ≠ b * a := by
  refine ⟨CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 0 1),
    CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 1 1), ?_⟩
  intro h
  have hm := congrArg cl44AlgEquivMat16 h
  rw [map_mul, map_mul, cl44AlgEquivMat16_iota_single 0, cl44AlgEquivMat16_iota_single 1] at hm
  have h01 : cl44Gen 0 * cl44Gen 1 + cl44Gen 1 * cl44Gen 0 = 0 :=
    cl44Gen_anticomm (by decide)
  have h2mul : (2 : ℝ) • (cl44Gen 0 * cl44Gen 1) = 0 := by
    rw [two_smul]
    conv_lhs => arg 2; rw [hm]
    exact h01
  have hzero : cl44Gen 0 * cl44Gen 1 = 0 :=
    (smul_eq_zero.mp h2mul).resolve_left (by norm_num)
  have hsq := congrArg (fun M => cl44Gen 0 * M) hzero
  rw [← Matrix.mul_assoc, cl44Gen_sq 0] at hsq
  simp only [Fin.val_zero, show (0 : ℕ) < 4 by decide, ↓reduceIte, Matrix.one_mul,
    Matrix.mul_zero] at hsq
  have hent := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (0, 0, 0, 0) (0, 1, 0, 0)) hsq
  norm_num [cl44Gen, tensor4, cl11Grad, cl11Pos] at hent

/-- Closed T16 non-commutativity witness for `gamma44CommutantSubalgebra`. -/
theorem t16_gamma44Commutant_noncommutative :
    ∃ A B : gamma44CommutantSubalgebra, A * B ≠ B * A := by
  obtain ⟨A, B, hAB⟩ := mat8_real_noncommutative
  refine ⟨gamma44CommutantEquivProdMat8.symm (A, 0),
    gamma44CommutantEquivProdMat8.symm (B, 0), ?_⟩
  intro h
  apply hAB
  have h' := congrArg (fun z => (gamma44CommutantEquivProdMat8 z).1) h
  simpa [map_mul] using h'

/-- Closed T16 non-commutativity witness for `Module.End ℝ SplitOctCD`. -/
theorem t16_splitOctCDEnd_noncommutative :
    ∃ A B : Module.End ℝ SplitOctCD, A * B ≠ B * A :=
  leftMulEnd_noncommutative

/-- Closed T16 non-commutativity witness for `Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ))`. -/
theorem t16_ext3End_noncommutative :
    ∃ A B : Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)), A * B ≠ B * A := by
  refine ⟨exteriorContract (LinearMap.proj (0 : Fin 3)),
    exteriorWedge ℝ (Pi.single (0 : Fin 3) 1), ?_⟩
  intro h
  have hev := congrArg (fun T : Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)) => T 1) h
  simp only [Module.End.mul_apply, exteriorWedge_apply, mul_one, exteriorContract_iota,
    exteriorContract_one, map_zero, LinearMap.proj_apply, Pi.single_eq_same, one_smul] at hev
  have h1 : (1 : ExteriorAlgebra ℝ (Fin 3 → ℝ)) ≠ 0 := by
    intro h0
    have htr := congrArg (ExteriorAlgebra.lift ℝ (⟨0, fun _ => by simp⟩ :
      { f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ // ∀ m, f m * f m = 0 })) h0
    simp at htr
  exact h1 hev

/-- Closed T16 non-commutativity witness for `Module.End ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ))`. -/
theorem t16_ext6End_noncommutative :
    ∃ A B : Module.End ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ)), A * B ≠ B * A := by
  refine ⟨exteriorContract (LinearMap.proj (0 : Fin 6)),
    exteriorWedge ℝ (Pi.single (0 : Fin 6) 1), ?_⟩
  intro h
  have hev := congrArg (fun T : Module.End ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ)) => T 1) h
  simp only [Module.End.mul_apply, exteriorWedge_apply, mul_one, exteriorContract_iota,
    exteriorContract_one, map_zero, LinearMap.proj_apply, Pi.single_eq_same, one_smul] at hev
  have h1 : (1 : ExteriorAlgebra ℝ (Fin 6 → ℝ)) ≠ 0 := by
    intro h0
    have htr := congrArg (ExteriorAlgebra.lift ℝ (⟨0, fun _ => by simp⟩ :
      { f : (Fin 6 → ℝ) →ₗ[ℝ] ℝ // ∀ m, f m * f m = 0 })) h0
    simp at htr
  exact h1 hev

/-- Closed T16 non-commutativity witness for `SplitOctCD`. -/
theorem t16_splitOctCD_noncommutative :
    ∃ x y : SplitOctCD, x * y ≠ y * x :=
  splitOctCD_noncommutative

/-- Closed T16 non-commutativity witness for `CliffordAlgebra.even splitQ44`. -/
theorem t16_cl44Even_noncommutative :
    ∃ a b : CliffordAlgebra.even InfoGeometry.Clifford.splitQ44, a * b ≠ b * a := by
  let e0 : CliffordAlgebra InfoGeometry.Clifford.splitQ44 :=
    CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 0 1)
  let e1 : CliffordAlgebra InfoGeometry.Clifford.splitQ44 :=
    CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 1 1)
  let e2 : CliffordAlgebra InfoGeometry.Clifford.splitQ44 :=
    CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 2 1)
  have h01 : e0 * e1 ∈ CliffordAlgebra.even InfoGeometry.Clifford.splitQ44 := by
    change e0 * e1 ∈ CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 0
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mem_evenOdd_one InfoGeometry.Clifford.splitQ44 (Pi.single 0 1))
      (CliffordAlgebra.ι_mem_evenOdd_one InfoGeometry.Clifford.splitQ44 (Pi.single 1 1))
    have h1 : (1 : ZMod 2) + 1 = 0 := by decide
    rwa [h1] at h
  have h12 : e1 * e2 ∈ CliffordAlgebra.even InfoGeometry.Clifford.splitQ44 := by
    change e1 * e2 ∈ CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 0
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mem_evenOdd_one InfoGeometry.Clifford.splitQ44 (Pi.single 1 1))
      (CliffordAlgebra.ι_mem_evenOdd_one InfoGeometry.Clifford.splitQ44 (Pi.single 2 1))
    have h1 : (1 : ZMod 2) + 1 = 0 := by decide
    rwa [h1] at h
  refine ⟨⟨e0 * e1, h01⟩, ⟨e1 * e2, h12⟩, ?_⟩
  intro h
  have hval := congrArg (fun z : CliffordAlgebra.even InfoGeometry.Clifford.splitQ44 =>
    cl44AlgEquivMat16 z.1) h
  change cl44AlgEquivMat16 ((e0 * e1) * (e1 * e2)) =
    cl44AlgEquivMat16 ((e1 * e2) * (e0 * e1)) at hval
  simp only [map_mul, e0, e1, e2, cl44AlgEquivMat16_iota_single] at hval
  have h012 : (cl44Gen 0 * cl44Gen 1) * (cl44Gen 1 * cl44Gen 2) = cl44Gen 0 * cl44Gen 2 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cl44Gen 1), cl44Gen_sq 1]
    simp
  have h120 : (cl44Gen 1 * cl44Gen 2) * (cl44Gen 0 * cl44Gen 1) = -(cl44Gen 0 * cl44Gen 2) := by
    have ha02 : cl44Gen 2 * cl44Gen 0 = -(cl44Gen 0 * cl44Gen 2) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm (by decide))
    have ha01 : cl44Gen 1 * cl44Gen 0 = -(cl44Gen 0 * cl44Gen 1) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm (by decide))
    have ha12 : cl44Gen 2 * cl44Gen 1 = -(cl44Gen 1 * cl44Gen 2) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm (by decide))
    calc (cl44Gen 1 * cl44Gen 2) * (cl44Gen 0 * cl44Gen 1)
        = cl44Gen 1 * (cl44Gen 2 * cl44Gen 0) * cl44Gen 1 := by simp only [Matrix.mul_assoc]
      _ = -(cl44Gen 1 * (cl44Gen 0 * cl44Gen 2) * cl44Gen 1) := by rw [ha02]; simp
      _ = -((cl44Gen 1 * cl44Gen 0) * (cl44Gen 2 * cl44Gen 1)) := by simp only [Matrix.mul_assoc]
      _ = -(cl44Gen 0 * (cl44Gen 1 * cl44Gen 1) * cl44Gen 2) := by
            rw [ha01, ha12]; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
      _ = -(cl44Gen 0 * cl44Gen 2) := by rw [cl44Gen_sq 1]; simp
  rw [h012, h120] at hval
  have h2z : (2 : ℝ) • (cl44Gen 0 * cl44Gen 2) = 0 := by
    rw [two_smul]
    conv_lhs => arg 2; rw [hval]
    exact add_neg_cancel _
  have hzero : cl44Gen 0 * cl44Gen 2 = 0 := (smul_eq_zero.mp h2z).resolve_left (by norm_num)
  have hmul := congrArg (fun M => cl44Gen 0 * M) hzero
  rw [← Matrix.mul_assoc, cl44Gen_sq 0] at hmul
  simp only [Fin.val_zero, show (0 : ℕ) < 4 by decide, ↓reduceIte, Matrix.one_mul,
    Matrix.mul_zero] at hmul
  have hent := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => M (0, 0, 0, 0) (0, 0, 1, 0)) hmul
  norm_num [cl44Gen, tensor4, cl11Grad, cl11Pos] at hent

/-! ## Section 2: `Cl(3,3) ↪ Cl⁰(4,4) ≃ M₈(ℝ) × M₈(ℝ)` (Feature F13.1) -/

/-- Left Weyl chiral embedding `Cl(3,3) ↪ Cl⁰(4,4) ≃ gamma44CommutantSubalgebra`
into the `(+1)`-eigenspace block `(A, 0)`. -/
def cl33ToCl44EvenLeft : CliffordAlgebra Q33 →ₙₐ[ℝ] gamma44CommutantSubalgebra where
  toFun x := gamma44CommutantEquivProdMat8.symm (cliffordQ33ToMat8 x, 0)
  map_zero' := by simp
  map_add' x y := by
    apply gamma44CommutantEquivProdMat8.injective
    simp only [map_add, AlgEquiv.apply_symm_apply, Prod.mk_add_mk, add_zero]
  map_smul' r x := by
    apply gamma44CommutantEquivProdMat8.injective
    simp only [map_smul, AlgEquiv.apply_symm_apply, Prod.smul_mk, smul_zero]
    rfl
  map_mul' x y := by
    apply gamma44CommutantEquivProdMat8.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply, Prod.mk_mul_mk, mul_zero]

/-- Right Weyl chiral embedding `Cl(3,3) ↪ Cl⁰(4,4) ≃ gamma44CommutantSubalgebra`
into the `(-1)`-eigenspace block `(0, A)`. -/
def cl33ToCl44EvenRight : CliffordAlgebra Q33 →ₙₐ[ℝ] gamma44CommutantSubalgebra where
  toFun x := gamma44CommutantEquivProdMat8.symm (0, cliffordQ33ToMat8 x)
  map_zero' := by simp
  map_add' x y := by
    apply gamma44CommutantEquivProdMat8.injective
    simp only [map_add, AlgEquiv.apply_symm_apply, Prod.mk_add_mk, add_zero]
  map_smul' r x := by
    apply gamma44CommutantEquivProdMat8.injective
    simp only [map_smul, AlgEquiv.apply_symm_apply, Prod.smul_mk, smul_zero]
    rfl
  map_mul' x y := by
    apply gamma44CommutantEquivProdMat8.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply, Prod.mk_mul_mk, mul_zero]

/-- Unital diagonal embedding `Cl(3,3) →ₐ[ℝ] gamma44CommutantSubalgebra` sending `x` to
`(Φ(x), Φ(x))`. -/
def cl33ToCl44EvenDiag : CliffordAlgebra Q33 →ₐ[ℝ] gamma44CommutantSubalgebra where
  toFun x := gamma44CommutantEquivProdMat8.symm (cliffordQ33ToMat8 x, cliffordQ33ToMat8 x)
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, ← Prod.mk_mul_mk, map_mul gamma44CommutantEquivProdMat8.symm]
  map_zero' := by simp
  map_add' x y := by
    rw [map_add, ← Prod.mk_add_mk, map_add gamma44CommutantEquivProdMat8.symm]
  commutes' r := by
    apply gamma44CommutantEquivProdMat8.injective
    simp only [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    rfl

/-- Left chiral Weyl embedding of `Cl(3,3)` into `Cl⁰(4,4)` is injective. -/
theorem cl33_embeds_into_cl44EvenLeft : Function.Injective cl33ToCl44EvenLeft := by
  intro x y h
  have h1 := congrArg (fun z => (gamma44CommutantEquivProdMat8 z).1) h
  simp only [cl33ToCl44EvenLeft, NonUnitalAlgHom.coe_mk, AlgEquiv.apply_symm_apply] at h1
  exact cliffordQ33ToMat8.injective h1

/-- Right chiral Weyl embedding of `Cl(3,3)` into `Cl⁰(4,4)` is injective. -/
theorem cl33_embeds_into_cl44EvenRight : Function.Injective cl33ToCl44EvenRight := by
  intro x y h
  have h2 := congrArg (fun z => (gamma44CommutantEquivProdMat8 z).2) h
  simp only [cl33ToCl44EvenRight, NonUnitalAlgHom.coe_mk, AlgEquiv.apply_symm_apply] at h2
  exact cliffordQ33ToMat8.injective h2

/-- Diagonal unital embedding of `Cl(3,3)` into `Cl⁰(4,4)` is injective. -/
theorem cl33ToCl44EvenDiag_injective : Function.Injective cl33ToCl44EvenDiag := by
  intro x y h
  have h1 := congrArg (fun z => (gamma44CommutantEquivProdMat8 z).1) h
  simp only [cl33ToCl44EvenDiag, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, AlgEquiv.apply_symm_apply] at h1
  exact cliffordQ33ToMat8.injective h1

/-- Chiral Weyl idempotent completeness `P₊ + P₋ = 1` and block orthogonality
`P₊ Cl(3,3) · P₋ Cl(3,3) = 0`. -/
theorem cl33_cl44Even_weyl_completeness_and_orthogonality
    (x y : CliffordAlgebra Q33) :
    cl33ToCl44EvenLeft 1 + cl33ToCl44EvenRight 1 = 1 ∧
    cl33ToCl44EvenLeft x * cl33ToCl44EvenRight y = 0 ∧
    cl33ToCl44EvenRight y * cl33ToCl44EvenLeft x = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply gamma44CommutantEquivProdMat8.injective
    simp [cl33ToCl44EvenLeft, cl33ToCl44EvenRight]
  · apply gamma44CommutantEquivProdMat8.injective
    simp [cl33ToCl44EvenLeft, cl33ToCl44EvenRight, map_mul]
  · apply gamma44CommutantEquivProdMat8.injective
    simp [cl33ToCl44EvenLeft, cl33ToCl44EvenRight, map_mul]

private theorem cl44AlgEquivMat16_iota_anticomm_gamma44 (v : Fin 8 → ℝ) :
    cl44AlgEquivMat16 (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 v) * gamma44 =
      -(gamma44 * cl44AlgEquivMat16 (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 v)) := by
  have hι : cl44AlgEquivMat16 (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 v) =
      ∑ i : Fin 8, v i • cl44Gen i := by
    change CliffordAlgebra.lift InfoGeometry.Clifford.splitQ44 _
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 v) = _
    rw [CliffordAlgebra.lift_ι_apply]
    rfl
  rw [hι, Matrix.sum_mul, Matrix.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]
  congr 1
  exact eq_neg_of_add_eq_zero_left (gamma44_properties.2.2.2 i)

/-- Every element of the intrinsic even subalgebra `CliffordAlgebra.even splitQ44` maps
under `cl44AlgEquivMat16` into `gamma44CommutantSubalgebra`. -/
theorem cl44Even_mem_gamma44Commutant
    (x : CliffordAlgebra.even InfoGeometry.Clifford.splitQ44) :
    cl44AlgEquivMat16 x.1 ∈ gamma44CommutantSubalgebra := by
  change ∀ g ∈ ({gamma44} : Set (Matrix Krein16Idx Krein16Idx ℝ)),
    g * cl44AlgEquivMat16 x.1 = cl44AlgEquivMat16 x.1 * g
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  rcases x with ⟨x, hx⟩
  change x ∈ CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 0 at hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      rw [AlgEquiv.commutes, Algebra.commutes]
  | add y z _ _ hy hz =>
      rw [map_add, Matrix.mul_add, Matrix.add_mul, hy, hz]
  | ι_mul_ι_mul u v y _ hy =>
      rw [map_mul, map_mul]
      have hu := cl44AlgEquivMat16_iota_anticomm_gamma44 u
      have hv := cl44AlgEquivMat16_iota_anticomm_gamma44 v
      calc gamma44 * (cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) *
            cl44AlgEquivMat16 (CliffordAlgebra.ι _ v) * cl44AlgEquivMat16 y)
          = (gamma44 * cl44AlgEquivMat16 (CliffordAlgebra.ι _ u)) *
              cl44AlgEquivMat16 (CliffordAlgebra.ι _ v) * cl44AlgEquivMat16 y := by
            simp only [Matrix.mul_assoc]
        _ = (-(cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) * gamma44)) *
              cl44AlgEquivMat16 (CliffordAlgebra.ι _ v) * cl44AlgEquivMat16 y := by
            have hu' : gamma44 * cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) =
                -(cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) * gamma44) := by
              rw [hu, neg_neg]
            rw [hu']
        _ = cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) *
              (-(gamma44 * cl44AlgEquivMat16 (CliffordAlgebra.ι _ v))) *
              cl44AlgEquivMat16 y := by
            simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
        _ = cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) *
              (cl44AlgEquivMat16 (CliffordAlgebra.ι _ v) * gamma44) *
              cl44AlgEquivMat16 y := by
            have hv' : -(gamma44 * cl44AlgEquivMat16 (CliffordAlgebra.ι _ v)) =
                cl44AlgEquivMat16 (CliffordAlgebra.ι _ v) * gamma44 := by
              rw [hv]
            rw [hv']
        _ = cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) *
              cl44AlgEquivMat16 (CliffordAlgebra.ι _ v) *
                (gamma44 * cl44AlgEquivMat16 y) := by
            simp only [Matrix.mul_assoc]
        _ = (cl44AlgEquivMat16 (CliffordAlgebra.ι _ u) *
              cl44AlgEquivMat16 (CliffordAlgebra.ι _ v) * cl44AlgEquivMat16 y) *
              gamma44 := by
            rw [hy]; simp only [Matrix.mul_assoc]

/-- Exact algebra isomorphism `Cl⁰(4,4) ≃ₐ[ℝ] gamma44CommutantSubalgebra`,
yielding `Cl⁰(4,4) ≃ₐ[ℝ] M₈(ℝ) × M₈(ℝ)` of dimension `128`. -/
def cl44EvenEquivGamma44Commutant :
    CliffordAlgebra.even InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ] gamma44CommutantSubalgebra := by
  let hom : CliffordAlgebra.even InfoGeometry.Clifford.splitQ44 →ₐ[ℝ]
      gamma44CommutantSubalgebra :=
    { toFun := fun x => ⟨cl44AlgEquivMat16 x.1, cl44Even_mem_gamma44Commutant x⟩
      map_one' := Subtype.ext (map_one cl44AlgEquivMat16)
      map_mul' := fun x y => Subtype.ext (map_mul cl44AlgEquivMat16 x.1 y.1)
      map_zero' := Subtype.ext (map_zero cl44AlgEquivMat16)
      map_add' := fun x y => Subtype.ext (map_add cl44AlgEquivMat16 x.1 y.1)
      commutes' := fun r => Subtype.ext (cl44AlgEquivMat16.commutes r) }
  have hinj : Function.Injective hom := by
    intro x y h
    exact Subtype.ext (cl44AlgEquivMat16.injective (congrArg Subtype.val h))
  let g0 : CliffordAlgebra InfoGeometry.Clifford.splitQ44 :=
    CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 0 1)
  have hg0_sq : g0 * g0 = 1 := by
    change CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 0 1) *
        CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single 0 1) = 1
    rw [CliffordAlgebra.ι_sq_scalar, InfoGeometry.Clifford.splitQ44_apply]
    simp
  have hg0_odd : g0 ∈ CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 1 :=
    CliffordAlgebra.ι_mem_evenOdd_one _ _
  let eoEquiv : CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 0 ≃ₗ[ℝ]
      CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 1 :=
    { toFun := fun x => ⟨x.1 * g0, by
        simpa using SetLike.mul_mem_graded x.2 hg0_odd⟩
      invFun := fun x => ⟨x.1 * g0, by
        have h := SetLike.mul_mem_graded x.2 hg0_odd
        have h1 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h1] at h
        exact h⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc, hg0_sq])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc, hg0_sq])
      map_add' := fun x y => Subtype.ext (by simp [add_mul])
      map_smul' := fun r x => Subtype.ext (by simp) }
  haveI : FiniteDimensional ℝ (CliffordAlgebra InfoGeometry.Clifford.splitQ44) :=
    LinearEquiv.finiteDimensional cl44AlgEquivMat16.toLinearEquiv.symm
  have hfin_cl44 : Module.finrank ℝ (CliffordAlgebra InfoGeometry.Clifford.splitQ44) = 256 := by
    rw [cl44AlgEquivMat16.toLinearEquiv.finrank_eq, finrank_mat16]
  have hfin_even :
      Module.finrank ℝ (CliffordAlgebra.even InfoGeometry.Clifford.splitQ44) = 128 := by
    change Module.finrank ℝ (CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 0) = 128
    have hsum : Module.finrank ℝ (CliffordAlgebra InfoGeometry.Clifford.splitQ44) =
        Module.finrank ℝ (CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 0) +
          Module.finrank ℝ (CliffordAlgebra.evenOdd InfoGeometry.Clifford.splitQ44 1) := by
      rw [← Module.finrank_prod]
      exact LinearEquiv.finrank_eq
        (Submodule.prodEquivOfIsCompl _ _
          (CliffordAlgebra.evenOdd_isCompl InfoGeometry.Clifford.splitQ44)).symm
    have heq := LinearEquiv.finrank_eq eoEquiv
    rw [hfin_cl44, ← heq] at hsum
    omega
  have hrank : Module.finrank ℝ (CliffordAlgebra.even InfoGeometry.Clifford.splitQ44) =
      Module.finrank ℝ gamma44CommutantSubalgebra := by
    rw [hfin_even, gamma44_commutant_finrank]
  have hsurj : Function.Surjective hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := hom.toLinearMap) hrank).mp hinj
  exact AlgEquiv.ofBijective hom ⟨hinj, hsurj⟩

/-- Exact dimension audit `dim Cl(3,3) = 64`, `dim Cl⁰(4,4) = 128`, `dim Cl(4,4) = 256`. -/
theorem cl33_cl44Even_cl44_dimensions :
    Module.finrank ℝ (CliffordAlgebra Q33) = 64 ∧
    Module.finrank ℝ (CliffordAlgebra.even InfoGeometry.Clifford.splitQ44) = 128 ∧
    Module.finrank ℝ gamma44CommutantSubalgebra = 128 ∧
    Module.finrank ℝ (CliffordAlgebra InfoGeometry.Clifford.splitQ44) = 256 := by
  refine ⟨cliffordQ33_finrank, ?_, gamma44_commutant_finrank, ?_⟩
  · rw [cl44EvenEquivGamma44Commutant.toLinearEquiv.finrank_eq, gamma44_commutant_finrank]
  · rw [cl44AlgEquivMat16.toLinearEquiv.finrank_eq, finrank_mat16]

/-! ## Section 3: Bott Tensor Bridge `Cl(4,4) ≃ Cl(1,1) ⊗ Cl(3,3) ≃ M₂(ℝ) ⊗ M₈(ℝ)` (F13.2) -/

/-- Explicit quadratic-space isometry `Qsplit 3 ≃ᵢ Q33`. -/
def qsplit3EquivQ33 : (InfoGeometry.CliffordTower.Qsplit 3).IsometryEquiv Q33 where
  toFun s := ![s.1.1, s.2.1.1, s.2.2.1.1, s.1.2, s.2.1.2, s.2.2.1.2]
  invFun v := ((v 0, v 3), ((v 1, v 4), ((v 2, v 5), Fin.elim0)))
  left_inv s := by
    rcases s with ⟨⟨a0, b0⟩, ⟨⟨a1, b1⟩, ⟨⟨a2, b2⟩, z⟩⟩⟩
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    funext i
    exact Fin.elim0 i
  right_inv v := by
    funext i
    fin_cases i <;> rfl
  map_add' s t := by
    funext i
    fin_cases i <;> rfl
  map_smul' r s := by
    funext i
    fin_cases i <;> rfl
  map_app' s := by
    rcases s with ⟨⟨a0, b0⟩, ⟨⟨a1, b1⟩, ⟨⟨a2, b2⟩, z⟩⟩⟩
    simp only [InfoGeometry.CliffordTower.Qsplit,
      InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod_apply,
      zero_apply,
      Q33_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring

/-- Clifford algebra isomorphism `Cl(3,3) ≃ₐ[ℝ] Clsplit 3`. -/
def cliffordQ33EquivClsplit3 :
    CliffordAlgebra Q33 ≃ₐ[ℝ] InfoGeometry.CliffordTower.Clsplit 3 :=
  (CliffordAlgebra.equivOfIsometry qsplit3EquivQ33).symm

/-- Explicit quadratic-space isometry `Qsplit 4 ≃ᵢ splitQ44`. -/
def qsplit4EquivSplitQ44 :
    (InfoGeometry.CliffordTower.Qsplit 4).IsometryEquiv InfoGeometry.Clifford.splitQ44 where
  toFun s := ![s.1.1, s.2.1.1, s.2.2.1.1, s.2.2.2.1.1, s.1.2, s.2.1.2, s.2.2.1.2, s.2.2.2.1.2]
  invFun v := ((v 0, v 4), ((v 1, v 5), ((v 2, v 6), ((v 3, v 7), Fin.elim0))))
  left_inv s := by
    rcases s with ⟨⟨a0, b0⟩, ⟨⟨a1, b1⟩, ⟨⟨a2, b2⟩, ⟨⟨a3, b3⟩, z⟩⟩⟩⟩
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)))
    funext i
    exact Fin.elim0 i
  right_inv v := by
    funext i
    fin_cases i <;> rfl
  map_add' s t := by
    funext i
    fin_cases i <;> rfl
  map_smul' r s := by
    funext i
    fin_cases i <;> rfl
  map_app' s := by
    rcases s with ⟨⟨a0, b0⟩, ⟨⟨a1, b1⟩, ⟨⟨a2, b2⟩, ⟨⟨a3, b3⟩, z⟩⟩⟩⟩
    simp only [InfoGeometry.CliffordTower.Qsplit,
      InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod_apply,
      zero_apply,
      InfoGeometry.Clifford.splitQ44_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring

/-- Clifford algebra isomorphism `Cl(4,4) ≃ₐ[ℝ] BottPeriodicity.Cl44`. -/
def cliffordSplitQ44EquivClsplit4 :
    CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ] Cl44 :=
  (CliffordAlgebra.equivOfIsometry qsplit4EquivSplitQ44).symm

/-- Graded Bott periodicity factorization `Cl(4,4) ≃ₐ[ℝ] Cl(1,1) ᵍ⊗[ℝ] Cl(3,3)`. -/
def cl44_gradedTensor_cl11_cl33 :
    CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 ᵍ⊗[ℝ]
        CliffordAlgebra.evenOdd (SplitBottQuad 3)) :=
  cliffordSplitQ44EquivClsplit4.trans cl44_as_splitBottStep

/-- Ungraded Bott tensor factorization `Cl(4,4) ≃ₐ[ℝ] Cl(1,1) ⊗[ℝ] Cl(3,3)`. -/
def cl44_equiv_cl11_tensor_cl33 :
    CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      InfoGeometry.CliffordTower.Clsplit 1 ⊗[ℝ] CliffordAlgebra Q33 :=
  cliffordSplitQ44EquivClsplit4.trans
    ((splitTowerStep 3).trans
      ((matrixEquivCliffordTensor 1 (InfoGeometry.CliffordTower.Clsplit 3)).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl cliffordQ33EquivClsplit3.symm)))

/-- Matrix tensor realization `Cl(4,4) ≃ₐ[ℝ] M₂(ℝ) ⊗[ℝ] M₈(ℝ)`. -/
def cl44_equiv_mat2_tensor_mat8 :
    CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ ⊗[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  cl44_equiv_cl11_tensor_cl33.trans
    (Algebra.TensorProduct.congr
      ((splitTowerEquivMatrix 1).trans
        (Matrix.reindexAlgEquiv ℝ ℝ (finCongr (by norm_num : 2 ^ 1 = 2))))
      cliffordQ33ToMat8)

/-- Combined `Cl(3,3)` and `Cl(1,1)` Bott tensor theorem for `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)`. -/
theorem cl33_and_cl11_tensor_cl44 :
    Nonempty (CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 ᵍ⊗[ℝ]
        CliffordAlgebra.evenOdd (SplitBottQuad 3))) ∧
    Nonempty (CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      InfoGeometry.CliffordTower.Clsplit 1 ⊗[ℝ] CliffordAlgebra Q33) ∧
    Nonempty (CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ ⊗[ℝ] Matrix (Fin 8) (Fin 8) ℝ) ∧
    Nonempty (CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      Matrix Krein16Idx Krein16Idx ℝ) ∧
    Module.finrank ℝ (InfoGeometry.CliffordTower.Clsplit 1) *
      Module.finrank ℝ (CliffordAlgebra Q33) =
      Module.finrank ℝ (CliffordAlgebra InfoGeometry.Clifford.splitQ44) := by
  refine ⟨⟨cl44_gradedTensor_cl11_cl33⟩, ⟨cl44_equiv_cl11_tensor_cl33⟩,
    ⟨cl44_equiv_mat2_tensor_mat8⟩, ⟨cl44AlgEquivMat16⟩, ?_⟩
  have h1 : Module.finrank ℝ (InfoGeometry.CliffordTower.Clsplit 1) = 4 := by
    rw [(splitTowerEquivMatrix 1).toLinearEquiv.finrank_eq, Module.finrank_matrix,
      Fintype.card_fin]
    norm_num
  have h44 : Module.finrank ℝ (CliffordAlgebra InfoGeometry.Clifford.splitQ44) = 256 :=
    cl33_cl44Even_cl44_dimensions.2.2.2
  rw [h1, cliffordQ33_finrank, h44]

/-! ## Section 4: Daviau Peirce `1 + 3` & `Cl(1,3) ≃ₐ[ℝ] M₂(ℍ)` Bridge (F13.3) -/

/-- Chiral quaternion-pair decomposition `SplitOctCD ≃ₗ[ℝ] Quaternion ℝ × Quaternion ℝ`
projecting onto `𝒩_+` (`fst`) and `𝒩_-` (`snd`). -/
def splitOctCDEquivQuatPair : SplitOctCD ≃ₗ[ℝ] (Quaternion ℝ × Quaternion ℝ) where
  toFun x := (x.fst + star x.snd, x.fst - star x.snd)
  invFun p := ⟨(1 / 2 : ℝ) • (p.1 + p.2), (1 / 2 : ℝ) • star (p.1 - p.2)⟩
  left_inv x := by
    rcases x with ⟨⟨q0, q1, q2, q3⟩, ⟨r0, r1, r2, r3⟩⟩
    ext <;> simp <;> ring
  right_inv p := by
    rcases p with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
    refine Prod.ext ?_ ?_ <;> ext <;> simp <;> ring
  map_add' x y := by
    refine Prod.ext ?_ ?_ <;> ext <;> simp <;> ring
  map_smul' c x := by
    refine Prod.ext ?_ ?_ <;> ext <;> simp <;> ring

@[simp] theorem splitOctCDEquivQuatPair_uPlusCD :
    splitOctCDEquivQuatPair uPlusCD = (1, 0) := by
  (refine Prod.ext ?_ ?_ <;> ext <;>
    simp [splitOctCDEquivQuatPair, uPlusCD_components]); norm_num

@[simp] theorem splitOctCDEquivQuatPair_uMinusCD :
    splitOctCDEquivQuatPair uMinusCD = (0, 1) := by
  (refine Prod.ext ?_ ?_ <;> ext <;>
    simp [splitOctCDEquivQuatPair, uMinusCD_components]); norm_num

@[simp] theorem splitOctCDEquivQuatPair_ePlusCD (k : Fin 3) :
    splitOctCDEquivQuatPair (ePlusCD k) = (qBasis k, 0) := by
  fin_cases k <;> refine Prod.ext ?_ ?_ <;> ext <;>
    simp [splitOctCDEquivQuatPair, ePlusCD_components, qBasis] <;> norm_num

@[simp] theorem splitOctCDEquivQuatPair_eMinusCD (k : Fin 3) :
    splitOctCDEquivQuatPair (eMinusCD k) = (0, qBasis k) := by
  fin_cases k <;> refine Prod.ext ?_ ?_ <;> ext <;>
    simp [splitOctCDEquivQuatPair, eMinusCD_components, qBasis] <;> norm_num

theorem splitOctCDEquivQuatPair_mem_nullSpacePlus (x : SplitOctCD) :
    x ∈ nullSpacePlus ↔ (splitOctCDEquivQuatPair x).2 = 0 := by
  rw [mem_nullSpacePlus_iff]
  constructor
  · intro hx
    ext <;> simp [splitOctCDEquivQuatPair, hx]
  · intro hx
    have hq : x.fst - star x.snd = 0 := hx
    have hfst : x.fst = star x.snd := sub_eq_zero.mp hq
    rw [hfst, star_star]

theorem splitOctCDEquivQuatPair_mem_nullSpaceMinus (x : SplitOctCD) :
    x ∈ nullSpaceMinus ↔ (splitOctCDEquivQuatPair x).1 = 0 := by
  rw [mem_nullSpaceMinus_iff]
  constructor
  · intro hx
    ext <;> simp [splitOctCDEquivQuatPair, hx]
  · intro hx
    have hq : x.fst + star x.snd = 0 := hx
    have hsnd : star x.snd = -x.fst := eq_neg_of_add_eq_zero_right hq
    have h' := congrArg star hsnd
    simpa using h'

/-- Left action of `M₂(ℍ)` on `Quaternion ℝ × Quaternion ℝ`,
transported to `Module.End ℝ SplitOctCD`. -/
def quatMat2ToEndSplitOctCD : QuaternionMatrix →ₐ[ℝ] Module.End ℝ SplitOctCD where
  toFun M :=
    splitOctCDEquivQuatPair.symm.toLinearMap.comp
      (({ toFun := fun p =>
            (M 0 0 * p.1 + M 0 1 * p.2, M 1 0 * p.1 + M 1 1 * p.2)
          map_add' := fun p q => by
            refine Prod.ext ?_ ?_ <;> simp [mul_add] <;> abel
          map_smul' := fun r p => by
            refine Prod.ext ?_ ?_ <;> simp [Algebra.mul_smul_comm] } :
          (Quaternion ℝ × Quaternion ℝ) →ₗ[ℝ] (Quaternion ℝ × Quaternion ℝ)).comp
        splitOctCDEquivQuatPair.toLinearMap)
  map_one' := by
    apply LinearMap.ext; intro x
    apply splitOctCDEquivQuatPair.injective
    simp
  map_mul' M N := by
    apply LinearMap.ext; intro x
    apply splitOctCDEquivQuatPair.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      splitOctCDEquivQuatPair.apply_symm_apply, Module.End.mul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_apply, Fin.sum_univ_two]
    refine Prod.ext ?_ ?_ <;> noncomm_ring
  map_zero' := by
    apply LinearMap.ext; intro x
    apply splitOctCDEquivQuatPair.injective
    simp
  map_add' M N := by
    apply LinearMap.ext; intro x
    apply splitOctCDEquivQuatPair.injective
    refine Prod.ext ?_ ?_ <;>
      (simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        splitOctCDEquivQuatPair.apply_symm_apply, LinearMap.add_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.add_apply, add_mul, map_add, Prod.fst_add, Prod.snd_add];
       abel)
  commutes' r := by
    apply LinearMap.ext; intro x
    apply splitOctCDEquivQuatPair.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      splitOctCDEquivQuatPair.apply_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_mul_assoc]
    refine Prod.ext ?_ ?_ <;> simp [Algebra.smul_def]

theorem quatMat2ToEndSplitOctCD_injective :
    Function.Injective quatMat2ToEndSplitOctCD := by
  intro M N h
  apply Matrix.ext
  intro i j
  have h10 := congrArg (fun f : Module.End ℝ SplitOctCD =>
    splitOctCDEquivQuatPair (f (splitOctCDEquivQuatPair.symm (1, 0)))) h
  have h01 := congrArg (fun f : Module.End ℝ SplitOctCD =>
    splitOctCDEquivQuatPair (f (splitOctCDEquivQuatPair.symm (0, 1)))) h
  simp only [quatMat2ToEndSplitOctCD, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    splitOctCDEquivQuatPair.apply_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
    mul_one, mul_zero, add_zero, zero_add] at h10 h01
  fin_cases i <;> fin_cases j
  · exact congrArg Prod.fst h10
  · exact congrArg Prod.fst h01
  · exact congrArg Prod.snd h10
  · exact congrArg Prod.snd h01

/-- Faithful representation `Cl(1,3) →ₐ[ℝ] Module.End ℝ SplitOctCD`. -/
def cl13ToSplitOctCDEnd : HestenesCl14.Cl14 →ₐ[ℝ] Module.End ℝ SplitOctCD :=
  quatMat2ToEndSplitOctCD.comp cl13QuaternionEquiv.toAlgHom

theorem cl13ToSplitOctCDEnd_injective : Function.Injective cl13ToSplitOctCDEnd :=
  quatMat2ToEndSplitOctCD_injective.comp cl13QuaternionEquiv.injective

private def splitOctCDEndEquivMat8 :
    Module.End ℝ SplitOctCD ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrixAlgEquiv basisCD

/-- Faithful embedding `Cl(1,3) ↪ Cl(3,3)` realizing Daviau's spacetime subalgebra
inside `Cl(3,3) ≃ₐ[ℝ] M₈(ℝ)`. -/
def cl13ToCliffordQ33 : HestenesCl14.Cl14 →ₐ[ℝ] CliffordAlgebra Q33 :=
  cliffordQ33ToMat8.symm.toAlgHom.comp
    (splitOctCDEndEquivMat8.toAlgHom.comp cl13ToSplitOctCDEnd)

theorem cl13ToCliffordQ33_injective : Function.Injective cl13ToCliffordQ33 :=
  cliffordQ33ToMat8.symm.injective.comp
    (splitOctCDEndEquivMat8.injective.comp cl13ToSplitOctCDEnd_injective)

/-- **Daviau Peirce `1 + 3` & `Cl(1,3)` Bridge**:
1. `timeProjector = (1 + γ₀)/2` projects onto `nullSpacePlus` and `1 - timeProjector` onto
   `nullSpaceMinus`;
2. `spatialSwap = -γ₁γ₂γ₃` exchanges `uPlusCD ↔ uMinusCD` and `ePlusCD k ↔ eMinusCD k`;
3. `diagonalQuaternion q` preserves `nullSpacePlus` and `nullSpaceMinus` and splits `1 + 3` into
   `q.re` (`degreeZero ⊕ degreeThree`) and `q.im` (`degreeOne ⊕ degreeTwo`) in
   `SplitOctonion1331OperatorGradingBridge.zorn_1331_decomposition`;
4. `cl13ToCliffordQ33` embeds noncommutative `Cl(1,3)` injectively into `Cl(3,3)`. -/
theorem daviau_peirce13_cl13_bridge :
    (∀ x ∈ nullSpacePlus, cl13ToSplitOctCDEnd timeProjector x = x ∧
      cl13ToSplitOctCDEnd (1 - timeProjector) x = 0) ∧
    (∀ x ∈ nullSpaceMinus, cl13ToSplitOctCDEnd timeProjector x = 0 ∧
      cl13ToSplitOctCDEnd (1 - timeProjector) x = x) ∧
    (cl13ToSplitOctCDEnd spatialSwap uPlusCD = uMinusCD ∧
      cl13ToSplitOctCDEnd spatialSwap uMinusCD = uPlusCD ∧
      ∀ k : Fin 3, cl13ToSplitOctCDEnd spatialSwap (ePlusCD k) = eMinusCD k ∧
        cl13ToSplitOctCDEnd spatialSwap (eMinusCD k) = ePlusCD k) ∧
    (∀ q : Quaternion ℝ,
      cl13ToSplitOctCDEnd (diagonalQuaternion q) uPlusCD =
        q.re • uPlusCD +
          q.imI • ePlusCD 0 + q.imJ • ePlusCD 1 + q.imK • ePlusCD 2 ∧
      cl13ToSplitOctCDEnd (diagonalQuaternion q) uMinusCD =
        q.re • uMinusCD +
          q.imI • eMinusCD 0 + q.imJ • eMinusCD 1 + q.imK • eMinusCD 2 ∧
      splitOctCDEquivZornMatrix (cl13ToSplitOctCDEnd (diagonalQuaternion q) 1) =
        degreeZero (splitOctCDEquivZornMatrix
          (cl13ToSplitOctCDEnd (diagonalQuaternion q) 1)) +
        degreeOne (splitOctCDEquivZornMatrix
          (cl13ToSplitOctCDEnd (diagonalQuaternion q) 1)) +
        degreeTwo (splitOctCDEquivZornMatrix
          (cl13ToSplitOctCDEnd (diagonalQuaternion q) 1)) +
        degreeThree (splitOctCDEquivZornMatrix
          (cl13ToSplitOctCDEnd (diagonalQuaternion q) 1))) ∧
    (Function.Injective cl13ToCliffordQ33 ∧
      cl13ToCliffordQ33 (HestenesCl14.gamma 1) * cl13ToCliffordQ33 (HestenesCl14.gamma 2) ≠
        cl13ToCliffordQ33 (HestenesCl14.gamma 2) * cl13ToCliffordQ33 (HestenesCl14.gamma 1)) := by
  have htp_plus : ∀ x ∈ nullSpacePlus, cl13ToSplitOctCDEnd timeProjector x = x := by
    intro x hx
    have h2 := (splitOctCDEquivQuatPair_mem_nullSpacePlus x).mp hx
    apply splitOctCDEquivQuatPair.injective
    change splitOctCDEquivQuatPair
      (quatMat2ToEndSplitOctCD (cl13QuaternionEquiv timeProjector) x) = _
    have hrep : cl13QuaternionEquiv timeProjector = !![1, 0; 0, 0] :=
      quaternionRep_timeProjector
    simp only [quatMat2ToEndSplitOctCD, hrep, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      splitOctCDEquivQuatPair.apply_symm_apply, LinearMap.coe_mk, AddHom.coe_mk]
    refine Prod.ext ?_ ?_ <;> simp [h2]
  have htp_minus : ∀ x ∈ nullSpaceMinus, cl13ToSplitOctCDEnd timeProjector x = 0 := by
    intro x hx
    have h1 := (splitOctCDEquivQuatPair_mem_nullSpaceMinus x).mp hx
    apply splitOctCDEquivQuatPair.injective
    rw [map_zero]
    change splitOctCDEquivQuatPair
      (quatMat2ToEndSplitOctCD (cl13QuaternionEquiv timeProjector) x) = 0
    have hrep : cl13QuaternionEquiv timeProjector = !![1, 0; 0, 0] :=
      quaternionRep_timeProjector
    simp only [quatMat2ToEndSplitOctCD, hrep, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      splitOctCDEquivQuatPair.apply_symm_apply, LinearMap.coe_mk, AddHom.coe_mk]
    refine Prod.ext ?_ ?_ <;> simp [h1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hp := htp_plus x hx
    refine ⟨hp, ?_⟩
    rw [map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, hp, sub_self]
  · intro x hx
    have hm := htp_minus x hx
    refine ⟨hm, ?_⟩
    rw [map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, hm, sub_zero]
  · have hswap : cl13QuaternionEquiv spatialSwap = !![0, 1; 1, 0] :=
      quaternionRep_spatialSwap
    have hact : ∀ x : SplitOctCD, splitOctCDEquivQuatPair (cl13ToSplitOctCDEnd spatialSwap x) =
        ((splitOctCDEquivQuatPair x).2, (splitOctCDEquivQuatPair x).1) := by
      intro x
      change splitOctCDEquivQuatPair
        (quatMat2ToEndSplitOctCD (cl13QuaternionEquiv spatialSwap) x) = _
      simp [quatMat2ToEndSplitOctCD, hswap]
    refine ⟨?_, ?_, ?_⟩
    · apply splitOctCDEquivQuatPair.injective; simp [hact]
    · apply splitOctCDEquivQuatPair.injective; simp [hact]
    · intro k
      constructor <;> apply splitOctCDEquivQuatPair.injective <;> simp [hact]
  · intro q
    have hdiag : cl13QuaternionEquiv (diagonalQuaternion q) = !![q, 0; 0, q] :=
      quaternionRep_diagonalQuaternion q
    have hact : ∀ x : SplitOctCD,
        splitOctCDEquivQuatPair (cl13ToSplitOctCDEnd (diagonalQuaternion q) x) =
          (q * (splitOctCDEquivQuatPair x).1, q * (splitOctCDEquivQuatPair x).2) := by
      intro x
      change splitOctCDEquivQuatPair
        (quatMat2ToEndSplitOctCD (cl13QuaternionEquiv (diagonalQuaternion q)) x) = _
      simp [quatMat2ToEndSplitOctCD, hdiag]
    refine ⟨?_, ?_, ?_⟩
    · apply splitOctCDEquivQuatPair.injective
      rw [hact]
      simp only [splitOctCDEquivQuatPair_uPlusCD, mul_one, mul_zero, map_add, map_smul,
        splitOctCDEquivQuatPair_ePlusCD]
      refine Prod.ext ?_ ?_ <;> ext <;> simp [qBasis]
    · apply splitOctCDEquivQuatPair.injective
      rw [hact]
      simp only [splitOctCDEquivQuatPair_uMinusCD, mul_one, mul_zero, map_add, map_smul,
        splitOctCDEquivQuatPair_eMinusCD]
      refine Prod.ext ?_ ?_ <;> ext <;> simp [qBasis]
    · exact zorn_1331_decomposition _
  · refine ⟨cl13ToCliffordQ33_injective, ?_⟩
    intro h
    apply gamma_one_two_ne
    apply cl13ToCliffordQ33_injective
    simpa [map_mul] using h

/-! ## Section 5: Bridge to `KreinCl44SplitG2DerivationPosetSynthesis` (F13.4) -/

/-- Exact equality between `KreinCl44` metric `eta44` and `SplitOctCD` metric `J44`. -/
theorem eta44_eq_J44 : eta44 = J44 := rfl

/-- Involutive sign matrix conjugating `basisCD` (`sₖ = ℓ * iₖ`) to the Clifford vector frame
(`-sₖ = iₖ * ℓ`). -/
def cdG2SignMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal ![1, 1, 1, 1, 1, -1, -1, -1]

theorem cdG2SignMatrix_transpose : cdG2SignMatrixᵀ = cdG2SignMatrix := by
  simp [cdG2SignMatrix]

theorem cdG2SignMatrix_sq : cdG2SignMatrix * cdG2SignMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cdG2SignMatrix, Matrix.mul_apply, Fin.sum_univ_eight]

theorem cdG2SignMatrix_preserves_J44 :
    cdG2SignMatrixᵀ * J44 * cdG2SignMatrix = eta44 := by
  rw [cdG2SignMatrix_transpose, eta44_eq_J44]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cdG2SignMatrix, J44, Matrix.mul_apply, Fin.sum_univ_eight]

private def cdG2SignUnit : (Matrix (Fin 8) (Fin 8) ℝ)ˣ where
  val := cdG2SignMatrix
  inv := cdG2SignMatrix
  val_inv := cdG2SignMatrix_sq
  inv_val := cdG2SignMatrix_sq

private lemma cl44Gen_mul_self_add_swap (a b : Fin 8) (hab : a ≠ b) :
    cl44Gen a * cl44Gen b = -(cl44Gen b * cl44Gen a) :=
  eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab.symm)

private lemma rhoVec8_one : rhoVec8 (1 : Matrix Krein16Idx Krein16Idx ℝ) = 0 := by
  ext a b
  simp [rhoVec8]

private lemma rhoVec8_u1d1 : rhoVec8 (u1Op * d1Op) = (1 / 2 : ℝ) • rhoVec8 (cl44Bivector 1 5) := by
  have h4 : (4 : ℝ) • (u1Op * d1Op) = ((2 : ℝ) • u1Op) * ((2 : ℝ) • d1Op) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hl := ladder_ops_clifford_identities
  rw [hl.1, hl.2.1] at h4
  have hexp : (cl44Gen 1 - cl44Gen 5) * (cl44Gen 1 + cl44Gen 5) =
      (2 : ℝ) • (1 + cl44Bivector 1 5) := by
    have h11 : cl44Gen 1 * cl44Gen 1 = 1 := by rw [cl44Gen_sq 1]; norm_num
    have h55 : cl44Gen 5 * cl44Gen 5 = -1 := by rw [cl44Gen_sq 5]; norm_num
    have h51 : cl44Gen 5 * cl44Gen 1 = -cl44Bivector 1 5 := by
      unfold cl44Bivector; exact cl44Gen_mul_self_add_swap 5 1 (by decide)
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, h11, h55]
    change (1 + cl44Bivector 1 5) - (cl44Gen 5 * cl44Gen 1 + -1) = _
    rw [h51, two_smul]
    abel
  rw [hexp] at h4
  have hud : u1Op * d1Op = (1 / 2 : ℝ) • (1 + cl44Bivector 1 5) := by
    have h2 : (4 : ℝ) • (u1Op * d1Op) = (4 : ℝ) • ((1 / 2 : ℝ) • (1 + cl44Bivector 1 5)) := by
      rw [h4, smul_smul]; norm_num
    exact (smul_right_injective _ (by norm_num : (4 : ℝ) ≠ 0)) h2
  rw [hud, map_smul, map_add, rhoVec8_one, zero_add]

private lemma rhoVec8_u2d2 : rhoVec8 (u2Op * d2Op) = (1 / 2 : ℝ) • rhoVec8 (cl44Bivector 2 6) := by
  have h4 : (4 : ℝ) • (u2Op * d2Op) = ((2 : ℝ) • u2Op) * ((2 : ℝ) • d2Op) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hl := ladder_ops_clifford_identities
  rw [hl.2.2.1, hl.2.2.2.1] at h4
  have hexp : (cl44Gen 2 - cl44Gen 6) * (cl44Gen 2 + cl44Gen 6) =
      (2 : ℝ) • (1 + cl44Bivector 2 6) := by
    have h22 : cl44Gen 2 * cl44Gen 2 = 1 := by rw [cl44Gen_sq 2]; norm_num
    have h66 : cl44Gen 6 * cl44Gen 6 = -1 := by rw [cl44Gen_sq 6]; norm_num
    have h62 : cl44Gen 6 * cl44Gen 2 = -cl44Bivector 2 6 := by
      unfold cl44Bivector; exact cl44Gen_mul_self_add_swap 6 2 (by decide)
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, h22, h66]
    change (1 + cl44Bivector 2 6) - (cl44Gen 6 * cl44Gen 2 + -1) = _
    rw [h62, two_smul]
    abel
  rw [hexp] at h4
  have hud : u2Op * d2Op = (1 / 2 : ℝ) • (1 + cl44Bivector 2 6) := by
    have h2 : (4 : ℝ) • (u2Op * d2Op) = (4 : ℝ) • ((1 / 2 : ℝ) • (1 + cl44Bivector 2 6)) := by
      rw [h4, smul_smul]; norm_num
    exact (smul_right_injective _ (by norm_num : (4 : ℝ) ≠ 0)) h2
  rw [hud, map_smul, map_add, rhoVec8_one, zero_add]

private lemma rhoVec8_u3d3 : rhoVec8 (u3Op * d3Op) = (1 / 2 : ℝ) • rhoVec8 (cl44Bivector 3 7) := by
  have h4 : (4 : ℝ) • (u3Op * d3Op) = ((2 : ℝ) • u3Op) * ((2 : ℝ) • d3Op) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hl := ladder_ops_clifford_identities
  rw [hl.2.2.2.2.1, hl.2.2.2.2.2] at h4
  have hexp : (cl44Gen 3 - cl44Gen 7) * (cl44Gen 3 + cl44Gen 7) =
      (2 : ℝ) • (1 + cl44Bivector 3 7) := by
    have h33 : cl44Gen 3 * cl44Gen 3 = 1 := by rw [cl44Gen_sq 3]; norm_num
    have h77 : cl44Gen 7 * cl44Gen 7 = -1 := by rw [cl44Gen_sq 7]; norm_num
    have h73 : cl44Gen 7 * cl44Gen 3 = -cl44Bivector 3 7 := by
      unfold cl44Bivector; exact cl44Gen_mul_self_add_swap 7 3 (by decide)
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, h33, h77]
    change (1 + cl44Bivector 3 7) - (cl44Gen 7 * cl44Gen 3 + -1) = _
    rw [h73, two_smul]
    abel
  rw [hexp] at h4
  have hud : u3Op * d3Op = (1 / 2 : ℝ) • (1 + cl44Bivector 3 7) := by
    have h2 : (4 : ℝ) • (u3Op * d3Op) = (4 : ℝ) • ((1 / 2 : ℝ) • (1 + cl44Bivector 3 7)) := by
      rw [h4, smul_smul]; norm_num
    exact (smul_right_injective _ (by norm_num : (4 : ℝ) ≠ 0)) h2
  rw [hud, map_smul, map_add, rhoVec8_one, zero_add]

private lemma rhoVec8_ladder_prod
    (A B : Matrix Krein16Idx Krein16Idx ℝ) (a₁ a₂ b₁ b₂ : Fin 8)
    (hA : (2 : ℝ) • A = cl44Gen a₁ - cl44Gen a₂)
    (hB : (2 : ℝ) • B = cl44Gen b₁ + cl44Gen b₂) :
    rhoVec8 (A * B) = (1 / 4 : ℝ) • (rhoVec8 (cl44Bivector a₁ b₁) +
      rhoVec8 (cl44Bivector a₁ b₂) - rhoVec8 (cl44Bivector a₂ b₁) -
      rhoVec8 (cl44Bivector a₂ b₂)) := by
  have h4 : (4 : ℝ) • (A * B) = ((2 : ℝ) • A) * ((2 : ℝ) • B) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  rw [hA, hB, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add] at h4
  have hAB : A * B = (1 / 4 : ℝ) • (cl44Bivector a₁ b₁ + cl44Bivector a₁ b₂ -
      cl44Bivector a₂ b₁ - cl44Bivector a₂ b₂) := by
    have hs : (4 : ℝ) • (A * B) = (4 : ℝ) • ((1 / 4 : ℝ) • (cl44Bivector a₁ b₁ +
        cl44Bivector a₁ b₂ - cl44Bivector a₂ b₁ - cl44Bivector a₂ b₂)) := by
      rw [h4, smul_smul]
      simp only [cl44Bivector, show (4 : ℝ) * (1 / 4) = 1 by norm_num, one_smul]
      abel
    exact (smul_right_injective _ (by norm_num : (4 : ℝ) ≠ 0)) hs
  rw [hAB, map_smul, map_sub, map_sub, map_add]

private lemma rhoVec8_ladder_uu
    (A B : Matrix Krein16Idx Krein16Idx ℝ) (a₁ a₂ b₁ b₂ : Fin 8)
    (hA : (2 : ℝ) • A = cl44Gen a₁ - cl44Gen a₂)
    (hB : (2 : ℝ) • B = cl44Gen b₁ - cl44Gen b₂) :
    rhoVec8 (A * B) = (1 / 4 : ℝ) • (rhoVec8 (cl44Bivector a₁ b₁) -
      rhoVec8 (cl44Bivector a₁ b₂) - rhoVec8 (cl44Bivector a₂ b₁) +
      rhoVec8 (cl44Bivector a₂ b₂)) := by
  have h4 : (4 : ℝ) • (A * B) = ((2 : ℝ) • A) * ((2 : ℝ) • B) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  rw [hA, hB, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub] at h4
  have hAB : A * B = (1 / 4 : ℝ) • (cl44Bivector a₁ b₁ - cl44Bivector a₁ b₂ -
      cl44Bivector a₂ b₁ + cl44Bivector a₂ b₂) := by
    have hs : (4 : ℝ) • (A * B) = (4 : ℝ) • ((1 / 4 : ℝ) • (cl44Bivector a₁ b₁ -
        cl44Bivector a₁ b₂ - cl44Bivector a₂ b₁ + cl44Bivector a₂ b₂)) := by
      rw [h4, smul_smul]
      simp only [cl44Bivector, show (4 : ℝ) * (1 / 4) = 1 by norm_num, one_smul]
      abel
    exact (smul_right_injective _ (by norm_num : (4 : ℝ) ≠ 0)) hs
  rw [hAB, map_smul, map_add, map_sub, map_sub]

private lemma rhoVec8_ladder_dd
    (A B : Matrix Krein16Idx Krein16Idx ℝ) (a₁ a₂ b₁ b₂ : Fin 8)
    (hA : (2 : ℝ) • A = cl44Gen a₁ + cl44Gen a₂)
    (hB : (2 : ℝ) • B = cl44Gen b₁ + cl44Gen b₂) :
    rhoVec8 (A * B) = (1 / 4 : ℝ) • (rhoVec8 (cl44Bivector a₁ b₁) +
      rhoVec8 (cl44Bivector a₁ b₂) + rhoVec8 (cl44Bivector a₂ b₁) +
      rhoVec8 (cl44Bivector a₂ b₂)) := by
  have h4 : (4 : ℝ) • (A * B) = ((2 : ℝ) • A) * ((2 : ℝ) • B) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  rw [hA, hB, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add] at h4
  have hAB : A * B = (1 / 4 : ℝ) • (cl44Bivector a₁ b₁ + cl44Bivector a₁ b₂ +
      cl44Bivector a₂ b₁ + cl44Bivector a₂ b₂) := by
    have hs : (4 : ℝ) • (A * B) = (4 : ℝ) • ((1 / 4 : ℝ) • (cl44Bivector a₁ b₁ +
        cl44Bivector a₁ b₂ + cl44Bivector a₂ b₁ + cl44Bivector a₂ b₂)) := by
      rw [h4, smul_smul]
      simp only [cl44Bivector, show (4 : ℝ) * (1 / 4) = 1 by norm_num, one_smul]
      abel
    exact (smul_right_injective _ (by norm_num : (4 : ℝ) ≠ 0)) hs
  rw [hAB, map_smul, map_add, map_add, map_add]

private lemma rhoVec8_et0_d
    (B : Matrix Krein16Idx Krein16Idx ℝ) (b₁ b₂ : Fin 8)
    (hB : (2 : ℝ) • B = cl44Gen b₁ + cl44Gen b₂) :
    rhoVec8 (et0Op * B) =
      (1 / 2 : ℝ) • (rhoVec8 (cl44Bivector 4 b₁) + rhoVec8 (cl44Bivector 4 b₂)) := by
  have h2 : (2 : ℝ) • (et0Op * B) = cl44Gen 4 * ((2 : ℝ) • B) := by
    rw [Matrix.mul_smul]; rfl
  rw [hB, Matrix.mul_add] at h2
  have het : et0Op * B = (1 / 2 : ℝ) • (cl44Bivector 4 b₁ + cl44Bivector 4 b₂) := by
    have hs : (2 : ℝ) • (et0Op * B) =
        (2 : ℝ) • ((1 / 2 : ℝ) • (cl44Bivector 4 b₁ + cl44Bivector 4 b₂)) := by
      rw [h2, smul_smul]
      simp only [cl44Bivector, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
    exact (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) hs
  rw [het, map_smul, map_add]

private lemma rhoVec8_et0_u
    (B : Matrix Krein16Idx Krein16Idx ℝ) (b₁ b₂ : Fin 8)
    (hB : (2 : ℝ) • B = cl44Gen b₁ - cl44Gen b₂) :
    rhoVec8 (et0Op * B) =
      (1 / 2 : ℝ) • (rhoVec8 (cl44Bivector 4 b₁) - rhoVec8 (cl44Bivector 4 b₂)) := by
  have h2 : (2 : ℝ) • (et0Op * B) = cl44Gen 4 * ((2 : ℝ) • B) := by
    rw [Matrix.mul_smul]; rfl
  rw [hB, Matrix.mul_sub] at h2
  have het : et0Op * B = (1 / 2 : ℝ) • (cl44Bivector 4 b₁ - cl44Bivector 4 b₂) := by
    have hs : (2 : ℝ) • (et0Op * B) =
        (2 : ℝ) • ((1 / 2 : ℝ) • (cl44Bivector 4 b₁ - cl44Bivector 4 b₂)) := by
      rw [h2, smul_smul]
      simp only [cl44Bivector, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
    exact (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) hs
  rw [het, map_smul, map_sub]

private abbrev mkCD (c0 c1 c2 c3 c4 c5 c6 c7 : ℝ) : SplitOctCD :=
  ⟨⟨c0, c1, c2, c3⟩, ⟨c4, -c5, -c6, -c7⟩⟩

private def g2CdDerivAction (k : Fin 14) (x : SplitOctCD) : SplitOctCD :=
  let a1 := x.fst.imI; let a2 := x.fst.imJ; let a3 := x.fst.imK
  let b0 := x.snd.re; let b1 := -x.snd.imI; let b2 := -x.snd.imJ; let b3 := -x.snd.imK
  match k with
  | 0 => mkCD 0 ((a3 + b3) / 2) 0 ((-a1 + b1) / 2) 0 ((a3 + b3) / 2) 0 ((a1 - b1) / 2)
  | 1 => mkCD 0 ((a2 + b2) / 2) ((-a1 + b1) / 2) 0 0 ((a2 + b2) / 2) ((a1 - b1) / 2) 0
  | 2 => mkCD 0 0 ((a3 + b3) / 2) ((-a2 + b2) / 2) 0 0 ((a3 + b3) / 2) ((a2 - b2) / 2)
  | 3 => mkCD 0 ((a2 - b2) / 2) ((-a1 + b1) / 2) b0 (a3 + b3)
      ((a2 - b2) / 2) ((-a1 + b1) / 2) (-b0)
  | 4 => mkCD 0 (-b0) ((a3 + b3) / 2) ((-a2 - b2) / 2) (-a1 + b1)
      (-b0) ((-a3 - b3) / 2) ((a2 + b2) / 2)
  | 5 => mkCD 0 ((-a3 + b3) / 2) b0 ((a1 - b1) / 2) (a2 + b2)
      ((-a3 + b3) / 2) (-b0) ((a1 - b1) / 2)
  | 6 => mkCD 0 ((-a3 - b3) / 2) (-b0) ((a1 + b1) / 2) (-a2 + b2)
      ((a3 + b3) / 2) (-b0) ((-a1 - b1) / 2)
  | 7 => mkCD 0 ((-a2 + b2) / 2) ((a1 + b1) / 2) 0 0 ((a2 - b2) / 2) ((a1 + b1) / 2) 0
  | 8 => mkCD 0 0 ((-a3 + b3) / 2) ((a2 + b2) / 2) 0 0 ((a3 - b3) / 2) ((a2 + b2) / 2)
  | 9 => mkCD 0 b0 ((a3 - b3) / 2) ((-a2 + b2) / 2) (a1 + b1)
      (-b0) ((a3 - b3) / 2) ((-a2 + b2) / 2)
  | 10 => mkCD 0 ((a2 + b2) / 2) ((-a1 - b1) / 2) (-b0) (-a3 + b3)
      ((-a2 - b2) / 2) ((a1 + b1) / 2) (-b0)
  | 11 => mkCD 0 ((-a3 + b3) / 2) 0 ((a1 + b1) / 2) 0 ((a3 - b3) / 2) 0 ((a1 + b1) / 2)
  | 12 => mkCD 0 b1 0 (-b3) 0 a1 0 (-a3)
  | 13 => mkCD 0 0 b2 (-b3) 0 0 a2 (-a3)

private lemma g2CdDeriv_prop0 (x y : SplitOctCD) :
    g2CdDerivAction 0 (x * y) = g2CdDerivAction 0 x * y + x * g2CdDerivAction 0 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop1 (x y : SplitOctCD) :
    g2CdDerivAction 1 (x * y) = g2CdDerivAction 1 x * y + x * g2CdDerivAction 1 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop2 (x y : SplitOctCD) :
    g2CdDerivAction 2 (x * y) = g2CdDerivAction 2 x * y + x * g2CdDerivAction 2 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop3 (x y : SplitOctCD) :
    g2CdDerivAction 3 (x * y) = g2CdDerivAction 3 x * y + x * g2CdDerivAction 3 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop4 (x y : SplitOctCD) :
    g2CdDerivAction 4 (x * y) = g2CdDerivAction 4 x * y + x * g2CdDerivAction 4 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop5 (x y : SplitOctCD) :
    g2CdDerivAction 5 (x * y) = g2CdDerivAction 5 x * y + x * g2CdDerivAction 5 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop6 (x y : SplitOctCD) :
    g2CdDerivAction 6 (x * y) = g2CdDerivAction 6 x * y + x * g2CdDerivAction 6 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop7 (x y : SplitOctCD) :
    g2CdDerivAction 7 (x * y) = g2CdDerivAction 7 x * y + x * g2CdDerivAction 7 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop8 (x y : SplitOctCD) :
    g2CdDerivAction 8 (x * y) = g2CdDerivAction 8 x * y + x * g2CdDerivAction 8 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop9 (x y : SplitOctCD) :
    g2CdDerivAction 9 (x * y) = g2CdDerivAction 9 x * y + x * g2CdDerivAction 9 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop10 (x y : SplitOctCD) :
    g2CdDerivAction 10 (x * y) = g2CdDerivAction 10 x * y + x * g2CdDerivAction 10 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop11 (x y : SplitOctCD) :
    g2CdDerivAction 11 (x * y) = g2CdDerivAction 11 x * y + x * g2CdDerivAction 11 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop12 (x y : SplitOctCD) :
    g2CdDerivAction 12 (x * y) = g2CdDerivAction 12 x * y + x * g2CdDerivAction 12 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private lemma g2CdDeriv_prop13 (x y : SplitOctCD) :
    g2CdDerivAction 13 (x * y) = g2CdDerivAction 13 x * y + x * g2CdDerivAction 13 y := by
  rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
  rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
  dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring

private def g2CdDeriv (k : Fin 14) : cdDerivSubalgebra where
  val :=
    { toFun := g2CdDerivAction k
      map_add' := fun x y => by
        rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
        rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
        fin_cases k <;> (dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring)
      map_smul' := fun r x => by
        rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
        fin_cases k <;> (dsimp [g2CdDerivAction, mkCD]; ext <;> simp <;> ring) }
  property := fun x y => by
    fin_cases k
    · exact g2CdDeriv_prop0 x y
    · exact g2CdDeriv_prop1 x y
    · exact g2CdDeriv_prop2 x y
    · exact g2CdDeriv_prop3 x y
    · exact g2CdDeriv_prop4 x y
    · exact g2CdDeriv_prop5 x y
    · exact g2CdDeriv_prop6 x y
    · exact g2CdDeriv_prop7 x y
    · exact g2CdDeriv_prop8 x y
    · exact g2CdDeriv_prop9 x y
    · exact g2CdDeriv_prop10 x y
    · exact g2CdDeriv_prop11 x y
    · exact g2CdDeriv_prop12 x y
    · exact g2CdDeriv_prop13 x y

private lemma rhoVec8_biv_entry' (a b : Fin 8) (hab : a ≠ b) (i j : Fin 8) :
    rhoVec8 (cl44Bivector a b) i j =
      if i = a ∧ j = b then 2 * (if b.val < 4 then (1 : ℝ) else -1)
      else if i = b ∧ j = a then -(2 * (if a.val < 4 then (1 : ℝ) else -1))
      else 0 :=
  rhoVec8_bivector_entry hab i j

private lemma cdConj_entry (M : Matrix (Fin 8) (Fin 8) ℝ) (i j : Fin 8) :
    (cdG2SignMatrix * M * cdG2SignMatrix) i j =
      cdG2SignMatrix i i * M i j * cdG2SignMatrix j j := by
  simp only [cdG2SignMatrix, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte]
    rw [Finset.sum_eq_single i]
    · simp
    · intro r _ hri; simp [hri.symm]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · intro c _ hcj; simp [hcj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

private lemma cdDeriv_toMatrix_entry (D : cdDerivSubalgebra) (i j : Fin 8) :
    LinearMap.toMatrix basisCD basisCD D.1 i j = cdToFin8 (D.1 (basisCD j)) i := by
  rw [LinearMap.toMatrix_apply, basisCD_repr_apply]

private lemma rhoVec8_g2Basis_eq_0 :
    cdG2SignMatrix * rhoVec8 (g2Basis 0) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 0).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 0) = rhoVec8 (u1Op * d3Op) := rfl
  rw [rhoVec8_ladder_prod u1Op d3Op 1 5 3 7 hl.1 hl.2.2.2.2.2] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 1 3 (by decide), rhoVec8_biv_entry' 1 7 (by decide),
      rhoVec8_biv_entry' 5 3 (by decide), rhoVec8_biv_entry' 5 7 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_1 :
    cdG2SignMatrix * rhoVec8 (g2Basis 1) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 1).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 1) = rhoVec8 (u1Op * d2Op) := rfl
  rw [rhoVec8_ladder_prod u1Op d2Op 1 5 2 6 hl.1 hl.2.2.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 1 2 (by decide), rhoVec8_biv_entry' 1 6 (by decide),
      rhoVec8_biv_entry' 5 2 (by decide), rhoVec8_biv_entry' 5 6 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_2 :
    cdG2SignMatrix * rhoVec8 (g2Basis 2) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 2).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 2) = rhoVec8 (u2Op * d3Op) := rfl
  rw [rhoVec8_ladder_prod u2Op d3Op 2 6 3 7 hl.2.2.1 hl.2.2.2.2.2] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 2 3 (by decide), rhoVec8_biv_entry' 2 7 (by decide),
      rhoVec8_biv_entry' 6 3 (by decide), rhoVec8_biv_entry' 6 7 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_3 :
    cdG2SignMatrix * rhoVec8 (g2Basis 3) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 3).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 3) = rhoVec8 (u1Op * u2Op) + rhoVec8 (et0Op * d3Op) := by
    change rhoVec8 (u1Op * u2Op + et0Op * d3Op) = _
    rw [map_add]
  rw [rhoVec8_ladder_uu u1Op u2Op 1 5 2 6 hl.1 hl.2.2.1,
    rhoVec8_et0_d d3Op 3 7 hl.2.2.2.2.2] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 1 2 (by decide), rhoVec8_biv_entry' 1 6 (by decide),
      rhoVec8_biv_entry' 5 2 (by decide), rhoVec8_biv_entry' 5 6 (by decide),
      rhoVec8_biv_entry' 4 3 (by decide), rhoVec8_biv_entry' 4 7 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_4 :
    cdG2SignMatrix * rhoVec8 (g2Basis 4) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 4).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 4) = rhoVec8 (d2Op * d3Op) - rhoVec8 (et0Op * u1Op) := by
    change rhoVec8 (d2Op * d3Op - et0Op * u1Op) = _
    rw [map_sub]
  rw [rhoVec8_ladder_dd d2Op d3Op 2 6 3 7 hl.2.2.2.1 hl.2.2.2.2.2,
    rhoVec8_et0_u u1Op 1 5 hl.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 2 3 (by decide), rhoVec8_biv_entry' 2 7 (by decide),
      rhoVec8_biv_entry' 6 3 (by decide), rhoVec8_biv_entry' 6 7 (by decide),
      rhoVec8_biv_entry' 4 1 (by decide), rhoVec8_biv_entry' 4 5 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_5 :
    cdG2SignMatrix * rhoVec8 (g2Basis 5) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 5).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 5) = rhoVec8 (u3Op * u1Op) + rhoVec8 (et0Op * d2Op) := by
    change rhoVec8 (u3Op * u1Op + et0Op * d2Op) = _
    rw [map_add]
  rw [rhoVec8_ladder_uu u3Op u1Op 3 7 1 5 hl.2.2.2.2.1 hl.1,
    rhoVec8_et0_d d2Op 2 6 hl.2.2.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 3 1 (by decide), rhoVec8_biv_entry' 3 5 (by decide),
      rhoVec8_biv_entry' 7 1 (by decide), rhoVec8_biv_entry' 7 5 (by decide),
      rhoVec8_biv_entry' 4 2 (by decide), rhoVec8_biv_entry' 4 6 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_6 :
    cdG2SignMatrix * rhoVec8 (g2Basis 6) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 6).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 6) = rhoVec8 (d3Op * d1Op) - rhoVec8 (et0Op * u2Op) := by
    change rhoVec8 (d3Op * d1Op - et0Op * u2Op) = _
    rw [map_sub]
  rw [rhoVec8_ladder_dd d3Op d1Op 3 7 1 5 hl.2.2.2.2.2 hl.2.1,
    rhoVec8_et0_u u2Op 2 6 hl.2.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 3 1 (by decide), rhoVec8_biv_entry' 3 5 (by decide),
      rhoVec8_biv_entry' 7 1 (by decide), rhoVec8_biv_entry' 7 5 (by decide),
      rhoVec8_biv_entry' 4 2 (by decide), rhoVec8_biv_entry' 4 6 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_7 :
    cdG2SignMatrix * rhoVec8 (g2Basis 7) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 7).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 7) = rhoVec8 (u2Op * d1Op) := rfl
  rw [rhoVec8_ladder_prod u2Op d1Op 2 6 1 5 hl.2.2.1 hl.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 2 1 (by decide), rhoVec8_biv_entry' 2 5 (by decide),
      rhoVec8_biv_entry' 6 1 (by decide), rhoVec8_biv_entry' 6 5 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_8 :
    cdG2SignMatrix * rhoVec8 (g2Basis 8) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 8).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 8) = rhoVec8 (u3Op * d2Op) := rfl
  rw [rhoVec8_ladder_prod u3Op d2Op 3 7 2 6 hl.2.2.2.2.1 hl.2.2.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 3 2 (by decide), rhoVec8_biv_entry' 3 6 (by decide),
      rhoVec8_biv_entry' 7 2 (by decide), rhoVec8_biv_entry' 7 6 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_9 :
    cdG2SignMatrix * rhoVec8 (g2Basis 9) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 9).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 9) = rhoVec8 (u2Op * u3Op) + rhoVec8 (et0Op * d1Op) := by
    change rhoVec8 (u2Op * u3Op + et0Op * d1Op) = _
    rw [map_add]
  rw [rhoVec8_ladder_uu u2Op u3Op 2 6 3 7 hl.2.2.1 hl.2.2.2.2.1,
    rhoVec8_et0_d d1Op 1 5 hl.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 2 3 (by decide), rhoVec8_biv_entry' 2 7 (by decide),
      rhoVec8_biv_entry' 6 3 (by decide), rhoVec8_biv_entry' 6 7 (by decide),
      rhoVec8_biv_entry' 4 1 (by decide), rhoVec8_biv_entry' 4 5 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_10 :
    cdG2SignMatrix * rhoVec8 (g2Basis 10) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 10).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 10) = rhoVec8 (d1Op * d2Op) - rhoVec8 (et0Op * u3Op) := by
    change rhoVec8 (d1Op * d2Op - et0Op * u3Op) = _
    rw [map_sub]
  rw [rhoVec8_ladder_dd d1Op d2Op 1 5 2 6 hl.2.1 hl.2.2.2.1,
    rhoVec8_et0_u u3Op 3 7 hl.2.2.2.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 1 2 (by decide), rhoVec8_biv_entry' 1 6 (by decide),
      rhoVec8_biv_entry' 5 2 (by decide), rhoVec8_biv_entry' 5 6 (by decide),
      rhoVec8_biv_entry' 4 3 (by decide), rhoVec8_biv_entry' 4 7 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_11 :
    cdG2SignMatrix * rhoVec8 (g2Basis 11) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 11).1 := by
  have hl := ladder_ops_clifford_identities
  have hr : rhoVec8 (g2Basis 11) = rhoVec8 (u3Op * d1Op) := rfl
  rw [rhoVec8_ladder_prod u3Op d1Op 3 7 1 5 hl.2.2.2.2.1 hl.2.1] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 3 1 (by decide), rhoVec8_biv_entry' 3 5 (by decide),
      rhoVec8_biv_entry' 7 1 (by decide), rhoVec8_biv_entry' 7 5 (by decide)] <;>
    norm_num

private lemma rhoVec8_g2Basis_eq_12 :
    cdG2SignMatrix * rhoVec8 (g2Basis 12) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 12).1 := by
  have hr : rhoVec8 (g2Basis 12) = rhoVec8 (u1Op * d1Op) - rhoVec8 (u3Op * d3Op) := by
    change rhoVec8 (u1Op * d1Op - u3Op * d3Op) = _
    rw [map_sub]
  rw [rhoVec8_u1d1, rhoVec8_u3d3] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 1 5 (by decide), rhoVec8_biv_entry' 3 7 (by decide)]

private lemma rhoVec8_g2Basis_eq_13 :
    cdG2SignMatrix * rhoVec8 (g2Basis 13) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv 13).1 := by
  have hr : rhoVec8 (g2Basis 13) = rhoVec8 (u2Op * d2Op) - rhoVec8 (u3Op * d3Op) := by
    change rhoVec8 (u2Op * d2Op - u3Op * d3Op) = _
    rw [map_sub]
  rw [rhoVec8_u2d2, rhoVec8_u3d3] at hr
  ext i j
  rw [cdConj_entry, hr, cdDeriv_toMatrix_entry]
  fin_cases j <;> fin_cases i <;>
    simp [g2CdDeriv, g2CdDerivAction, mkCD, cdG2SignMatrix, cdToFin8, fin8ToCD, basisCD,
      rhoVec8_biv_entry' 2 6 (by decide), rhoVec8_biv_entry' 3 7 (by decide)]

private lemma rhoVec8_g2Basis_eq (k : Fin 14) :
    cdG2SignMatrix * rhoVec8 (g2Basis k) * cdG2SignMatrix =
      LinearMap.toMatrix basisCD basisCD (g2CdDeriv k).1 := by
  fin_cases k
  · exact rhoVec8_g2Basis_eq_0
  · exact rhoVec8_g2Basis_eq_1
  · exact rhoVec8_g2Basis_eq_2
  · exact rhoVec8_g2Basis_eq_3
  · exact rhoVec8_g2Basis_eq_4
  · exact rhoVec8_g2Basis_eq_5
  · exact rhoVec8_g2Basis_eq_6
  · exact rhoVec8_g2Basis_eq_7
  · exact rhoVec8_g2Basis_eq_8
  · exact rhoVec8_g2Basis_eq_9
  · exact rhoVec8_g2Basis_eq_10
  · exact rhoVec8_g2Basis_eq_11
  · exact rhoVec8_g2Basis_eq_12
  · exact rhoVec8_g2Basis_eq_13

section LieBracketHelpers

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Conjugated endomorphism on `SplitOctCD` induced by `B ∈ g2LieSubalgebra`. -/
def g2ToSplitOctEnd (B : g2LieSubalgebra) : Module.End ℝ SplitOctCD :=
  splitOctCDEndEquivMat8.symm (cdG2SignMatrix * g2RhoVec8LieHom B * cdG2SignMatrix)

private theorem g2ToSplitOctEnd_mem_cdDeriv (B : g2LieSubalgebra) :
    g2ToSplitOctEnd B ∈ cdDerivSubalgebra := by
  have hmem : ∀ Z ∈ g2Submodule,
      splitOctCDEndEquivMat8.symm (cdG2SignMatrix * rhoVec8 Z * cdG2SignMatrix) ∈
        cdDerivSubalgebra := by
    intro Z hZ
    refine Submodule.span_induction (hx := hZ) ?_ ?_ ?_ ?_
    · rintro _ ⟨k, rfl⟩
      rw [rhoVec8_g2Basis_eq k]
      change splitOctCDEndEquivMat8.symm (splitOctCDEndEquivMat8 (g2CdDeriv k).1) ∈
        cdDerivSubalgebra
      rw [splitOctCDEndEquivMat8.symm_apply_apply]
      exact (g2CdDeriv k).2
    · simp only [map_zero, Matrix.mul_zero, Matrix.zero_mul]
      exact cdDerivSubalgebra.zero_mem
    · intro X Y _ _ hX hY
      rw [map_add, Matrix.mul_add, Matrix.add_mul, map_add]
      exact cdDerivSubalgebra.add_mem hX hY
    · intro r X _ hX
      rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul]
      exact cdDerivSubalgebra.smul_mem r hX
  exact hmem B.1 B.2

/-- Injective Lie-algebra homomorphism `g2LieSubalgebra →ₗ⁅ℝ⁆ cdDerivSubalgebra`. -/
def g2ToCdDerivLieHom : g2LieSubalgebra →ₗ⁅ℝ⁆ cdDerivSubalgebra where
  toFun B := ⟨g2ToSplitOctEnd B, g2ToSplitOctEnd_mem_cdDeriv B⟩
  map_add' B₁ B₂ := by
    apply Subtype.ext
    change splitOctCDEndEquivMat8.symm
        (cdG2SignMatrix * (g2RhoVec8LieHom (B₁ + B₂)) * cdG2SignMatrix) =
      splitOctCDEndEquivMat8.symm
          (cdG2SignMatrix * g2RhoVec8LieHom B₁ * cdG2SignMatrix) +
        splitOctCDEndEquivMat8.symm
          (cdG2SignMatrix * g2RhoVec8LieHom B₂ * cdG2SignMatrix)
    rw [map_add, Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' r B := by
    apply Subtype.ext
    change splitOctCDEndEquivMat8.symm
        (cdG2SignMatrix * (g2RhoVec8LieHom (r • B)) * cdG2SignMatrix) =
      r • splitOctCDEndEquivMat8.symm
        (cdG2SignMatrix * g2RhoVec8LieHom B * cdG2SignMatrix)
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul]
  map_lie' {B₁ B₂} := by
    apply Subtype.ext
    change splitOctCDEndEquivMat8.symm
        (cdG2SignMatrix * g2RhoVec8LieHom ⁅B₁, B₂⁆ * cdG2SignMatrix) =
      g2ToSplitOctEnd B₁ * g2ToSplitOctEnd B₂ - g2ToSplitOctEnd B₂ * g2ToSplitOctEnd B₁
    apply splitOctCDEndEquivMat8.injective
    rw [splitOctCDEndEquivMat8.apply_symm_apply, map_sub, map_mul, map_mul]
    dsimp [g2ToSplitOctEnd]
    rw [splitOctCDEndEquivMat8.apply_symm_apply, splitOctCDEndEquivMat8.apply_symm_apply,
      g2RhoVec8LieHom.map_lie]
    have hbr : ⁅g2RhoVec8LieHom B₁, g2RhoVec8LieHom B₂⁆ =
        g2RhoVec8LieHom B₁ * g2RhoVec8LieHom B₂ -
          g2RhoVec8LieHom B₂ * g2RhoVec8LieHom B₁ := rfl
    rw [hbr, Matrix.mul_sub, Matrix.sub_mul]
    have hconj : ∀ X Y : Matrix (Fin 8) (Fin 8) ℝ,
        cdG2SignMatrix * (X * Y) * cdG2SignMatrix =
          (cdG2SignMatrix * X * cdG2SignMatrix) * (cdG2SignMatrix * Y * cdG2SignMatrix) := by
      intro X Y
      calc cdG2SignMatrix * (X * Y) * cdG2SignMatrix
          = cdG2SignMatrix * (X * (1 * Y)) * cdG2SignMatrix := by rw [Matrix.one_mul]
        _ = cdG2SignMatrix * (X * ((cdG2SignMatrix * cdG2SignMatrix) * Y)) * cdG2SignMatrix := by
            rw [cdG2SignMatrix_sq]
        _ = (cdG2SignMatrix * X * cdG2SignMatrix) * (cdG2SignMatrix * Y * cdG2SignMatrix) := by
            simp only [Matrix.mul_assoc]
    rw [hconj, hconj]

end LieBracketHelpers

theorem g2ToCdDerivLieHom_injective : Function.Injective g2ToCdDerivLieHom := by
  intro B₁ B₂ h
  apply g2RhoVec8LieHom_injective
  have he := congrArg (fun D : cdDerivSubalgebra =>
    cdG2SignMatrix * splitOctCDEndEquivMat8 D.1 * cdG2SignMatrix) h
  change cdG2SignMatrix * splitOctCDEndEquivMat8 (g2ToSplitOctEnd B₁) * cdG2SignMatrix =
    cdG2SignMatrix * splitOctCDEndEquivMat8 (g2ToSplitOctEnd B₂) * cdG2SignMatrix at he
  dsimp [g2ToSplitOctEnd] at he
  rw [splitOctCDEndEquivMat8.apply_symm_apply, splitOctCDEndEquivMat8.apply_symm_apply] at he
  have hsim : ∀ X : Matrix (Fin 8) (Fin 8) ℝ,
      cdG2SignMatrix * (cdG2SignMatrix * X * cdG2SignMatrix) * cdG2SignMatrix = X := by
    intro X
    calc cdG2SignMatrix * (cdG2SignMatrix * X * cdG2SignMatrix) * cdG2SignMatrix
        = (cdG2SignMatrix * cdG2SignMatrix) * X * (cdG2SignMatrix * cdG2SignMatrix) := by
            simp only [Matrix.mul_assoc]
      _ = X := by rw [cdG2SignMatrix_sq, Matrix.one_mul, Matrix.mul_one]
  simpa only [hsim] using he

private lemma splitOctCDEquivZornMatrix_symm_mul'
    (X Y : InfoGeometry.Canonical.ZornMatrix ℝ) :
    splitOctCDEquivZornMatrix.symm (X * Y) =
      splitOctCDEquivZornMatrix.symm X * splitOctCDEquivZornMatrix.symm Y := by
  apply splitOctCDEquivZornMatrix.injective
  rw [splitOctCDEquivZornMatrix_mul, splitOctCDEquivZornMatrix.apply_symm_apply,
    splitOctCDEquivZornMatrix.apply_symm_apply, splitOctCDEquivZornMatrix.apply_symm_apply]

/-- Public Lie algebra isomorphism `cdDerivSubalgebra ≃ₗ⁅ℝ⁆ canonicalZornDerivations`. -/
def cdDerivEquivCanonicalZorn :
    cdDerivSubalgebra ≃ₗ⁅ℝ⁆ CanonicalZornDerivation.canonicalZornDerivations where
  toFun D :=
    ⟨splitOctCDEquivZornMatrix.toLinearMap ∘ₗ D.1 ∘ₗ splitOctCDEquivZornMatrix.symm.toLinearMap,
      by
        intro X Y
        change splitOctCDEquivZornMatrix (D.1 (splitOctCDEquivZornMatrix.symm (X * Y))) =
          splitOctCDEquivZornMatrix (D.1 (splitOctCDEquivZornMatrix.symm X)) * Y +
            X * splitOctCDEquivZornMatrix (D.1 (splitOctCDEquivZornMatrix.symm Y))
        rw [splitOctCDEquivZornMatrix_symm_mul', D.2, map_add, splitOctCDEquivZornMatrix_mul,
          splitOctCDEquivZornMatrix_mul, splitOctCDEquivZornMatrix.apply_symm_apply,
          splitOctCDEquivZornMatrix.apply_symm_apply]⟩
  invFun E :=
    ⟨splitOctCDEquivZornMatrix.symm.toLinearMap ∘ₗ E.1 ∘ₗ splitOctCDEquivZornMatrix.toLinearMap,
      by
        intro x y
        change splitOctCDEquivZornMatrix.symm (E.1 (splitOctCDEquivZornMatrix (x * y))) =
          splitOctCDEquivZornMatrix.symm (E.1 (splitOctCDEquivZornMatrix x)) * y +
            x * splitOctCDEquivZornMatrix.symm (E.1 (splitOctCDEquivZornMatrix y))
        rw [splitOctCDEquivZornMatrix_mul, E.2, map_add, splitOctCDEquivZornMatrix_symm_mul',
          splitOctCDEquivZornMatrix_symm_mul', splitOctCDEquivZornMatrix.symm_apply_apply,
          splitOctCDEquivZornMatrix.symm_apply_apply]⟩
  left_inv D := by
    apply Subtype.ext; apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
  right_inv E := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply]
  map_add' D₁ D₂ := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    exact map_add splitOctCDEquivZornMatrix _ _
  map_smul' r D := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    exact map_smul splitOctCDEquivZornMatrix _ _
  map_lie' {D₁ D₂} := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    change splitOctCDEquivZornMatrix
        ((D₁.1 * D₂.1 - D₂.1 * D₁.1) (splitOctCDEquivZornMatrix.symm X)) =
      splitOctCDEquivZornMatrix (D₁.1 (splitOctCDEquivZornMatrix.symm
        (splitOctCDEquivZornMatrix (D₂.1 (splitOctCDEquivZornMatrix.symm X))))) -
      splitOctCDEquivZornMatrix (D₂.1 (splitOctCDEquivZornMatrix.symm
        (splitOctCDEquivZornMatrix (D₁.1 (splitOctCDEquivZornMatrix.symm X)))))
    simp only [LinearEquiv.symm_apply_apply, LinearMap.sub_apply, Module.End.mul_apply, map_sub]

theorem finrank_cdDerivSubalgebra : Module.finrank ℝ cdDerivSubalgebra = 14 := by
  rw [cdDerivEquivCanonicalZorn.toLinearEquiv.finrank_eq,
    SplitG2RealFormCapstone.parameter_model_is_fourteen_dimensional]

/-- Exact 14-dimensional Lie-algebra isomorphism
`g2LieSubalgebra ≃ₗ⁅ℝ⁆ cdDerivSubalgebra`. -/
def g2LieSubalgebraEquivCdDeriv : g2LieSubalgebra ≃ₗ⁅ℝ⁆ cdDerivSubalgebra := by
  have hrank : Module.finrank ℝ g2LieSubalgebra = Module.finrank ℝ cdDerivSubalgebra := by
    rw [finrank_g2LieSubalgebra, finrank_cdDerivSubalgebra]
  have hsurj : Function.Surjective g2ToCdDerivLieHom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := g2ToCdDerivLieHom.toLinearMap) hrank).mp g2ToCdDerivLieHom_injective
  exact LieEquiv.ofBijective g2ToCdDerivLieHom ⟨g2ToCdDerivLieHom_injective, hsurj⟩

/-- Composite Lie isomorphism `g2LieSubalgebra ≃ₗ⁅ℝ⁆ canonicalZornDerivations`. -/
def g2LieSubalgebraEquivCanonicalZorn :
    g2LieSubalgebra ≃ₗ⁅ℝ⁆ CanonicalZornDerivation.canonicalZornDerivations :=
  g2LieSubalgebraEquivCdDeriv.trans cdDerivEquivCanonicalZorn

/-- The 8 `et0Op`-commuting generators `{0, 1, 2, 7, 8, 11, 12, 13}` of `g2Basis`. -/
def g2EllStabilizerIndices : Finset (Fin 14) :=
  {0, 1, 2, 7, 8, 11, 12, 13}

theorem g2EllStabilizerIndices_card : g2EllStabilizerIndices.card = 8 := by decide

theorem g2ToCdDerivLieHom_basis_eq (k : Fin 14) :
    g2ToCdDerivLieHom ⟨g2Basis k, Submodule.subset_span ⟨k, rfl⟩⟩ = g2CdDeriv k := by
  apply Subtype.ext
  change splitOctCDEndEquivMat8.symm
    (cdG2SignMatrix * rhoVec8 (g2Basis k) * cdG2SignMatrix) = (g2CdDeriv k).1
  rw [rhoVec8_g2Basis_eq k]
  exact splitOctCDEndEquivMat8.symm_apply_apply (g2CdDeriv k).1

theorem g2ToCdDerivLieHom_et0_stabilizer (k : Fin 14) (hk : k ∈ g2EllStabilizerIndices) :
    (g2ToCdDerivLieHom ⟨g2Basis k, Submodule.subset_span ⟨k, rfl⟩⟩) ∈ cdEllDerivStabilizer ∧
    g2Basis k * et0Op = et0Op * g2Basis k := by
  rw [g2ToCdDerivLieHom_basis_eq k]
  have hell : (g2CdDeriv k).1 ellCD = 0 := by
    fin_cases k <;>
      first
      | exact absurd hk (by decide)
      | (ext <;> simp [g2CdDeriv, g2CdDerivAction, mkCD, ellCD])
  have hcomm : g2Basis k * et0Op = et0Op * g2Basis k := by
    fin_cases k
    · -- k = 0: g2Zpos2 = u1Op * d3Op
      simp only [g2Basis, g2Zpos2, et0Op, u1Op, d3Op, tensor4_mul, cl11Grad_sq,
        one_mul, mul_one]
    · -- k = 1: g2X1 = u1Op * d2Op
      simp only [g2Basis, g2X1, et0Op, u1Op, d2Op, tensor4_mul, cl11Grad_sq,
        one_mul, mul_one]
    · -- k = 2: g2X2 = u2Op * d3Op
      simp only [g2Basis, g2X2, et0Op, u2Op, d3Op, tensor4_mul, cl11Grad_sq,
        one_mul, mul_one]
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · -- k = 7: g2Y1 = u2Op * d1Op
      simp only [g2Basis, g2Y1, et0Op, u2Op, d1Op, tensor4_mul, cl11Grad_sq,
        one_mul, mul_one]
    · -- k = 8: g2Y2 = u3Op * d2Op
      simp only [g2Basis, g2Y2, et0Op, u3Op, d2Op, tensor4_mul, cl11Grad_sq,
        one_mul, mul_one]
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · -- k = 11: g2Zneg2 = u3Op * d1Op
      simp only [g2Basis, g2Zneg2, et0Op, u3Op, d1Op, tensor4_mul, cl11Grad_sq,
        one_mul, mul_one]
    · -- k = 12: g2H1 = u1Op * d1Op - u3Op * d3Op
      simp only [g2Basis, g2H1, et0Op, u1Op, d1Op, u3Op, d3Op, Matrix.sub_mul, Matrix.mul_sub,
        tensor4_mul, cl11Grad_sq, one_mul, mul_one]
    · -- k = 13: g2H2 = u2Op * d2Op - u3Op * d3Op
      simp only [g2Basis, g2H2, et0Op, u2Op, d2Op, u3Op, d3Op, Matrix.sub_mul, Matrix.mul_sub,
        tensor4_mul, cl11Grad_sq, one_mul, mul_one]
  exact ⟨hell, hcomm⟩

theorem g2ToCdDerivLieHom_J44_skew (B : g2LieSubalgebra) :
    (splitOctCDEndEquivMat8 (g2ToCdDerivLieHom B).1)ᵀ * J44 +
      J44 * (splitOctCDEndEquivMat8 (g2ToCdDerivLieHom B).1) = 0 := by
  rw [show splitOctCDEndEquivMat8 (g2ToCdDerivLieHom B).1 =
      cdG2SignMatrix * g2RhoVec8LieHom B * cdG2SignMatrix from
    splitOctCDEndEquivMat8.apply_symm_apply _]
  have hgr : (g2RhoVec8LieHom B : Matrix (Fin 8) (Fin 8) ℝ) = rhoVec8 B.1 := rfl
  rw [hgr]
  have hskew := rhoVec8_so44_skew B.1
  have hJ : J44 = cdG2SignMatrix * eta44 * cdG2SignMatrix := by
    have h := cdG2SignMatrix_preserves_J44
    rw [cdG2SignMatrix_transpose] at h
    calc J44 = 1 * J44 * 1 := by simp
      _ = (cdG2SignMatrix * cdG2SignMatrix) * J44 * (cdG2SignMatrix * cdG2SignMatrix) := by
          rw [cdG2SignMatrix_sq]
      _ = cdG2SignMatrix * (cdG2SignMatrix * J44 * cdG2SignMatrix) * cdG2SignMatrix := by
          simp only [Matrix.mul_assoc]
      _ = cdG2SignMatrix * eta44 * cdG2SignMatrix := by rw [h]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, cdG2SignMatrix_transpose]
  calc cdG2SignMatrix * ((rhoVec8 B.1)ᵀ * cdG2SignMatrix) * J44 +
        J44 * (cdG2SignMatrix * rhoVec8 B.1 * cdG2SignMatrix)
      = cdG2SignMatrix * ((rhoVec8 B.1)ᵀ * eta44 + eta44 * rhoVec8 B.1) * cdG2SignMatrix := by
          rw [hJ]
          simp only [Matrix.mul_assoc]
          have hc1 : cdG2SignMatrix * ((rhoVec8 B.1)ᵀ * (cdG2SignMatrix * (cdG2SignMatrix *
              (eta44 * cdG2SignMatrix)))) =
              cdG2SignMatrix * ((rhoVec8 B.1)ᵀ * eta44 * cdG2SignMatrix) := by
            rw [← Matrix.mul_assoc cdG2SignMatrix cdG2SignMatrix, cdG2SignMatrix_sq,
              Matrix.one_mul, Matrix.mul_assoc]
          have hc2 : cdG2SignMatrix * (eta44 * (cdG2SignMatrix * (cdG2SignMatrix *
              (rhoVec8 B.1 * cdG2SignMatrix)))) =
              cdG2SignMatrix * (eta44 * rhoVec8 B.1 * cdG2SignMatrix) := by
            rw [← Matrix.mul_assoc cdG2SignMatrix cdG2SignMatrix, cdG2SignMatrix_sq,
              Matrix.one_mul, ← Matrix.mul_assoc eta44]
          rw [hc1, hc2, ← Matrix.mul_add, ← Matrix.add_mul, ← Matrix.mul_assoc]
    _ = 0 := by rw [hskew, Matrix.mul_zero, Matrix.zero_mul]

private def matEntryLinear {n : Type*} [Fintype n] [DecidableEq n] (i j : n) :
    Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma ring_hasDerivAt_clm_exp {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (φ : 𝔸 →L[ℝ] ℝ) (X : 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (NormedSpace.exp (s • X)))
      (φ (NormedSpace.exp (t • X) * X)) t :=
  φ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)

private lemma hasDerivAt_exp_smul_entry {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (t : ℝ) (i j : n) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) i j)
      ((NormedSpace.exp (t • X) * X) i j) t := by
  open scoped Matrix.Norms.Operator in
  exact @ring_hasDerivAt_clm_exp (Matrix n n ℝ) _ _
    (NormedAlgebra.restrictScalars ℚ ℝ (Matrix n n ℝ)) _
    (LinearMap.toContinuousLinearMap (matEntryLinear i j)) X t

private def cdToV8 : SplitOctCD ≃ₗ[ℝ] CanonicalZornDerivationExponential.V8 :=
  splitOctCDEquivZornMatrix.trans InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.coordLE

private lemma zornFlow_cd_eq_exp_mat8 (D : cdDerivSubalgebra) (t : ℝ) :
    splitOctCDEndEquivMat8
      ((splitOctCDAutMulEquivRealSplitOctonionAut.symm
        (CanonicalZornDerivationRealAutBridge.zornFlowRealAut
          (cdDerivEquivCanonicalZorn D) t)).1.toLinearMap) =
      NormedSpace.exp (t • splitOctCDEndEquivMat8 D.1) := by
  let Dz := cdDerivEquivCanonicalZorn D
  let Φ : ℝ → (SplitOctCD →ₗ[ℝ] SplitOctCD) := fun s =>
    (splitOctCDAutMulEquivRealSplitOctonionAut.symm
      (CanonicalZornDerivationRealAutBridge.zornFlowRealAut Dz s)).1.toLinearMap
  have hΦ_apply : ∀ s x,
      Φ s x = splitOctCDEquivZornMatrix.symm
        (CanonicalZornDerivationExponential.zornFlowLinearEquiv Dz.1 s
          (splitOctCDEquivZornMatrix x)) := fun _ _ => rfl
  let M : Matrix (Fin 8) (Fin 8) ℝ := splitOctCDEndEquivMat8 D.1
  have hflow_deriv : ∀ (x : SplitOctCD) (s : ℝ) (i : Fin 8),
      HasDerivAt (fun τ : ℝ => cdToFin8 (Φ τ x) i)
        (cdToFin8 (D.1 (Φ s x)) i) s := by
    intro x s i
    let F_lin : CanonicalZornDerivationExponential.V8 →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.proj i).comp (cdLinearEquivFin8.toLinearMap.comp cdToV8.symm.toLinearMap))
    have horb := (ContinuousDerivationExponential.hasStrictDerivAt_orbit
      (CanonicalZornDerivationExponential.coordEnd Dz.1) (cdToV8 x) s).hasDerivAt
    have hcomp := F_lin.hasFDerivAt.comp_hasDerivAt s horb
    have hfun : (fun τ : ℝ => F_lin (ContinuousDerivationExponential.flow
        (CanonicalZornDerivationExponential.coordEnd Dz.1) τ (cdToV8 x))) =
        (fun τ : ℝ => cdToFin8 (Φ τ x) i) := by
      funext τ
      dsimp [F_lin, cdToV8, Φ]
      rfl
    have hder : F_lin (CanonicalZornDerivationExponential.coordEnd Dz.1
        (ContinuousDerivationExponential.flow
          (CanonicalZornDerivationExponential.coordEnd Dz.1) s (cdToV8 x))) =
        cdToFin8 (D.1 (Φ s x)) i := by
      dsimp [F_lin, cdToV8, Φ]
      change cdToFin8 (splitOctCDEquivZornMatrix.symm
        (InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.coordLE.symm
          (CanonicalZornDerivationExponential.coordEnd Dz.1
            (ContinuousDerivationExponential.flow
              (CanonicalZornDerivationExponential.coordEnd Dz.1) s
              (InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.coordLE
                (splitOctCDEquivZornMatrix x)))))) i = _
      rw [← CanonicalZornDerivationExponential.coordLE_zornFlowLinearEquiv,
        CanonicalZornDerivationExponential.coordEnd_apply_coordLE]
      change cdToFin8 (splitOctCDEquivZornMatrix.symm
        (splitOctCDEquivZornMatrix (D.1 (splitOctCDEquivZornMatrix.symm
          (CanonicalZornDerivationExponential.zornFlowLinearEquiv
            (cdDerivEquivCanonicalZorn D).1 s (splitOctCDEquivZornMatrix x)))))) i = _
      rw [splitOctCDEquivZornMatrix.symm_apply_apply, ← hΦ_apply s x]
      rfl
    change HasDerivAt (fun τ : ℝ => F_lin (ContinuousDerivationExponential.flow
        (CanonicalZornDerivationExponential.coordEnd Dz.1) τ (cdToV8 x))) _ s at hcomp
    rw [hfun, hder] at hcomp
    exact hcomp
  have hexp_eq : ∀ (x : SplitOctCD) (τ : ℝ),
      cdToFin8 (Φ τ x) = (NormedSpace.exp (τ • M)).mulVec (cdToFin8 x) := by
    intro x τ
    let g : ℝ → Fin 8 → ℝ := fun s =>
      (NormedSpace.exp ((τ - s) • M)).mulVec (cdToFin8 (Φ s x))
    have hg_deriv : ∀ s i, HasDerivAt (fun r => g r i) 0 s := by
      intro s i
      have hterm : ∀ j : Fin 8,
          HasDerivAt (fun r => NormedSpace.exp ((τ - r) • M) i j * cdToFin8 (Φ r x) j)
            (((-(NormedSpace.exp ((τ - s) • M) * M)) i j) * cdToFin8 (Φ s x) j +
              NormedSpace.exp ((τ - s) • M) i j * cdToFin8 (D.1 (Φ s x)) j) s := by
        intro j
        have hexp_r : HasDerivAt (fun r => NormedSpace.exp ((τ - r) • M) i j)
            ((-(NormedSpace.exp ((τ - s) • M) * M)) i j) s := by
          have hcomp := (hasDerivAt_exp_smul_entry M (τ - s) i j).comp s
            ((hasDerivAt_const s τ).sub (hasDerivAt_id s))
          refine hcomp.congr_deriv ?_
          rw [Matrix.neg_apply]
          ring
        exact hexp_r.mul (hflow_deriv x s j)
      have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hterm j
      refine hsum.congr_deriv ?_
      have hD_mulVec : cdToFin8 (D.1 (Φ s x)) = M.mulVec (cdToFin8 (Φ s x)) := by
        funext j
        change basisCD.repr (D.1 (Φ s x)) j =
          (LinearMap.toMatrix basisCD basisCD D.1).mulVec (basisCD.repr (Φ s x)) j
        rw [LinearMap.toMatrix_mulVec_repr]
      rw [hD_mulVec]
      simp only [Matrix.neg_apply, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      have h1 : (∑ j : Fin 8, (NormedSpace.exp ((τ - s) • M) * M) i j * cdToFin8 (Φ s x) j) =
          ((NormedSpace.exp ((τ - s) • M) * M).mulVec (cdToFin8 (Φ s x))) i := rfl
      have h2 : (∑ j : Fin 8, NormedSpace.exp ((τ - s) • M) i j * M.mulVec (cdToFin8 (Φ s x)) j) =
          (NormedSpace.exp ((τ - s) • M)).mulVec (M.mulVec (cdToFin8 (Φ s x))) i := rfl
      rw [h1, h2, Matrix.mulVec_mulVec, add_comm, add_neg_cancel]
    have hg_const : g τ = g 0 := by
      ext i
      exact is_const_of_deriv_eq_zero (fun s => (hg_deriv s i).differentiableAt)
        (fun s => (hg_deriv s i).deriv) τ 0
    have h0 : Φ 0 x = x := by
      rw [hΦ_apply, CanonicalZornDerivationExponential.zornFlowLinearEquiv_zero_apply,
        splitOctCDEquivZornMatrix.symm_apply_apply]
    dsimp [g] at hg_const
    simpa [sub_self, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, sub_zero, h0]
      using hg_const
  ext i j
  change (LinearMap.toMatrix basisCD basisCD (Φ t)) i j = NormedSpace.exp (t • M) i j
  rw [LinearMap.toMatrix_apply]
  change basisCD.repr (Φ t (basisCD j)) i = NormedSpace.exp (t • M) i j
  rw [basisCD_repr_apply, hexp_eq (basisCD j) t]
  have hbj : cdToFin8 (basisCD j) = Pi.single j 1 := by
    funext r
    rw [← basisCD_repr_apply, basisCD.repr_self, Finsupp.single_apply, Pi.single_apply]
    simp [eq_comm]
  rw [hbj, Matrix.mulVec_single]
  simp

/-- **Unified `KreinCl44SplitG2DerivationPosetSynthesis` Bridge**:
packages `eta44 = J44`, `cdG2SignMatrix` conjugation, `g2LieSubalgebra ≃ₗ⁅ℝ⁆ cdDerivSubalgebra`,
the 8-dimensional `cdEllDerivStabilizer` correspondence, `J44`-skewness, and 1-parameter
exponential intertwining `expMat16GL` in `SplitG2MatrixGroup` ↔ `SplitOctCDAut ⊂ SO44Subgroup`. -/
theorem bridge_to_KreinCl44SplitG2DerivationPosetSynthesis :
    (eta44 = J44 ∧ cdG2SignMatrixᵀ * J44 * cdG2SignMatrix = eta44) ∧
    Nonempty (g2LieSubalgebra ≃ₗ⁅ℝ⁆ cdDerivSubalgebra) ∧
    (∀ k ∈ g2EllStabilizerIndices,
      (g2ToCdDerivLieHom ⟨g2Basis k, Submodule.subset_span ⟨k, rfl⟩⟩) ∈ cdEllDerivStabilizer ∧
      g2Basis k * et0Op = et0Op * g2Basis k) ∧
    (∀ (B : g2LieSubalgebra) (t : ℝ),
      expMat16GL B.1 t ∈ SplitG2MatrixGroup ∧
      (∀ b : Fin 8,
        NormedSpace.exp (t • B.1) * cl44Gen b * NormedSpace.exp ((-t) • B.1) =
          ∑ a : Fin 8, (NormedSpace.exp (t • g2RhoVec8LieHom B) a b) • cl44Gen a) ∧
      ∃ φ : SplitOctCDAut,
        (splitOctCDAut_to_SO44 φ).1.val =
          cdG2SignMatrix * NormedSpace.exp (t • g2RhoVec8LieHom B) * cdG2SignMatrix ∧
        splitOctCDAutMulEquivRealSplitOctonionAut φ =
          CanonicalZornDerivationRealAutBridge.zornFlowRealAut
            (g2LieSubalgebraEquivCanonicalZorn B) t) := by
  refine ⟨⟨eta44_eq_J44, cdG2SignMatrix_preserves_J44⟩, ⟨g2LieSubalgebraEquivCdDeriv⟩,
    g2ToCdDerivLieHom_et0_stabilizer, ?_⟩
  intro B t
  refine ⟨expMat16GL_mem_splitG2MatrixGroup B.2 t,
    fun b => expMat16GL_cl44_intertwining B.2 t b, ?_⟩
  let D : cdDerivSubalgebra := g2ToCdDerivLieHom B
  let Dz := cdDerivEquivCanonicalZorn D
  let φ : SplitOctCDAut :=
    splitOctCDAutMulEquivRealSplitOctonionAut.symm
      (CanonicalZornDerivationRealAutBridge.zornFlowRealAut Dz t)
  refine ⟨φ, ?_, ?_⟩
  · have hφ_mat : (splitOctCDAut_to_SO44 φ).1.val =
        NormedSpace.exp (t • splitOctCDEndEquivMat8 D.1) :=
      zornFlow_cd_eq_exp_mat8 D t
    rw [hφ_mat]
    have hD_mat : splitOctCDEndEquivMat8 D.1 =
        cdG2SignMatrix * g2RhoVec8LieHom B * cdG2SignMatrix := by
      exact splitOctCDEndEquivMat8.apply_symm_apply _
    rw [hD_mat]
    have hconj : t • (cdG2SignMatrix * g2RhoVec8LieHom B * cdG2SignMatrix) =
        cdG2SignUnit.val * (t • g2RhoVec8LieHom B) * (cdG2SignUnit⁻¹).val := by
      change t • (cdG2SignMatrix * g2RhoVec8LieHom B * cdG2SignMatrix) =
        cdG2SignMatrix * (t • g2RhoVec8LieHom B) * cdG2SignMatrix
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hconj, Matrix.exp_units_conj cdG2SignUnit (t • g2RhoVec8LieHom B)]
    rfl
  · dsimp only [φ]
    rw [splitOctCDAutMulEquivRealSplitOctonionAut.apply_symm_apply]
    have hB : Dz = g2LieSubalgebraEquivCanonicalZorn B := rfl
    rw [hB]

/-! ## Section 6: `ZornDifferentialFormsCliffordBridge` & Exterior Fock Space (F14) -/

/-- Canonical `FormHodgeCliffordData` instance for `Q33` into `Matrix (Fin 8) (Fin 8) ℝ`,
with grade-raising differential `θ₀ ∧ ·` and `hodgeStar = id`. -/
def zornCl33FormHodgeData :
    FormHodgeCliffordData ℝ (Fin 6 → ℝ) (Matrix (Fin 8) (Fin 8) ℝ) where
  Q := Q33
  differential := LinearMap.mul ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ))
    (ExteriorAlgebra.ι ℝ (Pi.single 0 1))
  differential_sq := by
    refine LinearMap.ext fun ω => ?_
    change ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 6) 1) *
        (ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 6) 1) * ω) = 0
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  hodgeStar := LinearMap.id
  hodgeSquareSign := 1
  hodgeStar_sq := by
    refine LinearMap.ext fun ω => ?_
    simp
  generator := q33VecToMat
  generator_sq := q33VecToMat_sq

private def q33PlusIdx' : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

private def q33MinusIdx' : Fin 3 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5

/-- **Bridge to `ZornDifferentialFormsCliffordBridge`**:
`cliffordMorphism zornCl33FormHodgeData` coincides with `cliffordQ33ToMat8.toAlgHom`,
maps the chiral/Majorana generators to `carAnnihilateMat` / `carCreateMat` / `majoranaPlusMat` /
`majoranaMinusMat`, and `cliffordDifferential zornCl33FormHodgeData` raises exterior grade. -/
theorem bridge_to_ZornDifferentialFormsCliffordBridge :
    cliffordMorphism zornCl33FormHodgeData = cliffordQ33ToMat8.toAlgHom ∧
    Function.Bijective (cliffordMorphism zornCl33FormHodgeData) ∧
    (∀ k : Fin 3,
      cliffordMorphism zornCl33FormHodgeData ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx' k) 1) +
          CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx' k) 1))) = carAnnihilateMat k) ∧
    (∀ k : Fin 3,
      cliffordMorphism zornCl33FormHodgeData ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx' k) 1) -
          CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx' k) 1))) = carCreateMat k) ∧
    (∀ k : Fin 3,
      cliffordMorphism zornCl33FormHodgeData
        (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx' k) 1)) = majoranaPlusMat k) ∧
    (∀ k : Fin 3,
      cliffordMorphism zornCl33FormHodgeData
        (CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx' k) 1)) = majoranaMinusMat k) ∧
    (∀ k (x : CliffordAlgebra Q33),
      CliffordAlgebra.equivExterior Q33 x ∈
        ExteriorAlgebra.exteriorPower ℝ k (Fin 6 → ℝ) →
      CliffordAlgebra.equivExterior Q33
        (cliffordDifferential zornCl33FormHodgeData x) ∈
        ExteriorAlgebra.exteriorPower ℝ (k + 1) (Fin 6 → ℝ)) := by
  have hEq : cliffordMorphism zornCl33FormHodgeData = cliffordQ33ToMat8.toAlgHom :=
    AlgHom.ext fun _ => rfl
  refine ⟨hEq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEq]; exact cliffordQ33ToMat8.bijective
  · intro k
    rw [hEq]
    fin_cases k
    · exact cliffordQ33ToMat8_car_plus 0
    · exact cliffordQ33ToMat8_car_plus 1
    · exact cliffordQ33ToMat8_car_plus 2
  · intro k
    rw [hEq]
    fin_cases k
    · exact cliffordQ33ToMat8_car_minus 0
    · exact cliffordQ33ToMat8_car_minus 1
    · exact cliffordQ33ToMat8_car_minus 2
  · intro k
    rw [hEq]
    change cliffordQ33ToMat8Hom (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx' k) 1)) =
      majoranaPlusMat k
    rw [cliffordQ33ToMat8Hom_gen (q33PlusIdx' k)]
    fin_cases k <;> rfl
  · intro k
    rw [hEq]
    change cliffordQ33ToMat8Hom (CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx' k) 1)) =
      majoranaMinusMat k
    rw [cliffordQ33ToMat8Hom_gen (q33MinusIdx' k)]
    fin_cases k <;> rfl
  · intro k x hx
    let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
    have hed := equivExterior_cliffordDifferential zornCl33FormHodgeData x
    change CliffordAlgebra.equivExterior Q33 (cliffordDifferential zornCl33FormHodgeData x) =
      ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 6) 1) * CliffordAlgebra.equivExterior Q33 x at hed
    rw [hed, Nat.add_comm k 1, ExteriorAlgebra.exteriorPower, pow_add]
    have h1 : ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 6) 1) ∈
        (LinearMap.range (ExteriorAlgebra.ι ℝ : (Fin 6 → ℝ) →ₗ[ℝ] _)) ^ 1 := by
      rw [pow_one]
      exact LinearMap.mem_range_self _ _
    exact Submodule.mul_mem_mul h1 hx

private def ext3Basis : Module.Basis (Finset (Fin 3)) ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)) :=
  (Pi.basisFun ℝ (Fin 3)).ExteriorAlgebra

private def θ3 (k : Fin 3) : ExteriorAlgebra ℝ (Fin 3 → ℝ) :=
  ExteriorAlgebra.ι ℝ (Pi.single k 1)

private lemma θ3_eq_basisFun (k : Fin 3) :
    θ3 k = ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 3) k) := by
  simp [θ3, Pi.basisFun_apply]

private lemma ext3Basis_empty : ext3Basis ∅ = 1 := by
  change (Pi.basisFun ℝ (Fin 3)).ExteriorAlgebra (∅ : Finset (Fin 3)) = 1
  rw [ExteriorAlgebra.basis_apply_ofCard (Pi.basisFun ℝ (Fin 3)) Finset.card_empty]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]

private lemma orderIso_permOfDisjoint_val {m n : ℕ} {I : Type*} [LinearOrder I]
    {s : Set.powersetCard I m} {t : Set.powersetCard I n} (h : Disjoint s.val t.val)
    (i : Fin (m + n)) :
    ((Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion h))
        (Set.powersetCard.permOfDisjoint h i) : I) =
      ((Equiv.Finset.disjUnionEquiv s.val t.val h
        (((Set.powersetCard.orderIsoOfFin s).sumCongr (Set.powersetCard.orderIsoOfFin t))
          (finSumFinEquiv.symm i)) : ↥(Set.powersetCard.disjUnion h).val) : I) := by
  dsimp [Set.powersetCard.permOfDisjoint]
  exact congrArg Subtype.val
    ((Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion h)).apply_symm_apply _)

private lemma ext3Basis_singleton (k : Fin 3) : ext3Basis {k} = θ3 k := by
  change (Pi.basisFun ℝ (Fin 3)).ExteriorAlgebra ({k} : Finset (Fin 3)) = θ3 k
  rw [ExteriorAlgebra.basis_apply_ofCard (Pi.basisFun ℝ (Fin 3)) (Finset.card_singleton k),
    θ3_eq_basisFun]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, Function.comp_apply]
  rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  have hk_mem : ((Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton k)) 0) : Fin 3) = k :=
    Finset.mem_singleton.mp
      (Set.powersetCard.orderIsoOfFin (Set.powersetCard.ofCard (Finset.card_singleton k)) 0).2
  change ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 3)
    ((Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton k)) 0) : Fin 3)) = _
  rw [hk_mem]

private lemma ext3Basis_pair {j k : Fin 3} (hjk : j < k) :
    ext3Basis {j, k} = θ3 j * θ3 k := by
  rw [← ext3Basis_singleton j, ← ext3Basis_singleton k]
  let sj : Set.powersetCard (Fin 3) 1 := Set.powersetCard.ofCard (Finset.card_singleton j)
  let sk : Set.powersetCard (Fin 3) 1 := Set.powersetCard.ofCard (Finset.card_singleton k)
  have hdisj : Disjoint (sj : Finset (Fin 3)) (sk : Finset (Fin 3)) :=
    Finset.disjoint_singleton.mpr (ne_of_lt hjk)
  have hmul := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℝ (Fin 3)) sj sk hdisj
  change ext3Basis {j} * ext3Basis {k} = _ at hmul
  rw [hmul]
  have hdisjU : (Set.powersetCard.disjUnion hdisj).val = ({j, k} : Finset (Fin 3)) := by
    ext x; simp [Set.powersetCard.disjUnion, sj, sk]
  have h0eq : (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)
      (Set.powersetCard.permOfDisjoint hdisj 0) : Fin 3) = j := by
    rw [orderIso_permOfDisjoint_val,
      show finSumFinEquiv.symm (0 : Fin 2) = (Sum.inl 0 : Fin 1 ⊕ Fin 1) by decide]
    exact Finset.mem_singleton.mp (Set.powersetCard.orderIsoOfFin sj 0).2
  have h1eq : (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)
      (Set.powersetCard.permOfDisjoint hdisj 1) : Fin 3) = k := by
    rw [orderIso_permOfDisjoint_val,
      show finSumFinEquiv.symm (1 : Fin 2) = (Sum.inr 0 : Fin 1 ⊕ Fin 1) by decide]
    exact Finset.mem_singleton.mp (Set.powersetCard.orderIsoOfFin sk 0).2
  have hlt : Set.powersetCard.permOfDisjoint hdisj 0 <
      Set.powersetCard.permOfDisjoint hdisj 1 := by
    rw [← (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).lt_iff_lt]
    change (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)
        (Set.powersetCard.permOfDisjoint hdisj 0) : Fin 3) <
      (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)
        (Set.powersetCard.permOfDisjoint hdisj 1) : Fin 3)
    rw [h0eq, h1eq]
    exact hjk
  have hperm : Set.powersetCard.permOfDisjoint hdisj = 1 := by
    have h0lt1 : (Set.powersetCard.permOfDisjoint hdisj 0).val <
        (Set.powersetCard.permOfDisjoint hdisj 1).val := Fin.lt_def.mp hlt
    have h0b := (Set.powersetCard.permOfDisjoint hdisj 0).isLt
    have h1b := (Set.powersetCard.permOfDisjoint hdisj 1).isLt
    have h0 : (Set.powersetCard.permOfDisjoint hdisj 0).val = 0 := by omega
    have h1 : (Set.powersetCard.permOfDisjoint hdisj 1).val = 1 := by omega
    ext i
    simp only [Equiv.Perm.coe_one, id_eq]
    fin_cases i
    · exact h0
    · exact h1
  rw [hperm, Equiv.Perm.sign_one, one_smul]
  rw [hdisjU]; rfl

private lemma ext3Basis_univ : ext3Basis ({0, 1, 2} : Finset (Fin 3)) = θ3 0 * θ3 1 * θ3 2 := by
  rw [← ext3Basis_pair (by decide : (0 : Fin 3) < 1), ← ext3Basis_singleton 2]
  let p01 : Set.powersetCard (Fin 3) 2 :=
    Set.powersetCard.ofCard (by decide : ({0, 1} : Finset (Fin 3)).card = 2)
  let p2 : Set.powersetCard (Fin 3) 1 :=
    Set.powersetCard.ofCard (by decide : ({2} : Finset (Fin 3)).card = 1)
  have hdisj : Disjoint (p01 : Finset (Fin 3)) (p2 : Finset (Fin 3)) := by
    change Disjoint ({0, 1} : Finset (Fin 3)) {2}; decide
  have hmul := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℝ (Fin 3)) p01 p2 hdisj
  change ext3Basis {0, 1} * ext3Basis {2} = _ at hmul
  rw [hmul]
  have hdisjU : (Set.powersetCard.disjUnion hdisj).val = ({0, 1, 2} : Finset (Fin 3)) := by
    ext x; simp [Set.powersetCard.disjUnion, p01, p2]
  have hv0 : (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)
      (Set.powersetCard.permOfDisjoint hdisj 0) : Fin 3) =
      (Set.powersetCard.orderIsoOfFin p01 0 : Fin 3) := by
    rw [orderIso_permOfDisjoint_val,
      show finSumFinEquiv.symm (0 : Fin 3) = (Sum.inl 0 : Fin 2 ⊕ Fin 1) by decide]
    rfl
  have hv1 : (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)
      (Set.powersetCard.permOfDisjoint hdisj 1) : Fin 3) =
      (Set.powersetCard.orderIsoOfFin p01 1 : Fin 3) := by
    rw [orderIso_permOfDisjoint_val,
      show finSumFinEquiv.symm (1 : Fin 3) = (Sum.inl 1 : Fin 2 ⊕ Fin 1) by decide]
    rfl
  have hv2 : (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)
      (Set.powersetCard.permOfDisjoint hdisj 2) : Fin 3) = 2 := by
    rw [orderIso_permOfDisjoint_val,
      show finSumFinEquiv.symm (2 : Fin 3) = (Sum.inr 0 : Fin 2 ⊕ Fin 1) by decide]
    exact Finset.mem_singleton.mp (Set.powersetCard.orderIsoOfFin p2 0).2
  have h01_lt : (Set.powersetCard.orderIsoOfFin p01 0 : Fin 3) <
      (Set.powersetCard.orderIsoOfFin p01 1 : Fin 3) :=
    (Set.powersetCard.orderIsoOfFin p01).strictMono (by decide)
  have h0_mem : (Set.powersetCard.orderIsoOfFin p01 0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) :=
    (Set.powersetCard.orderIsoOfFin p01 0).2
  have h1_mem : (Set.powersetCard.orderIsoOfFin p01 1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) :=
    (Set.powersetCard.orderIsoOfFin p01 1).2
  have h0lt2 : (Set.powersetCard.orderIsoOfFin p01 0 : Fin 3) < 2 := by
    rcases Finset.mem_insert.mp h0_mem with h | h
    · rw [h]; decide
    · rw [Finset.mem_singleton.mp h]; decide
  have h1lt2 : (Set.powersetCard.orderIsoOfFin p01 1 : Fin 3) < 2 := by
    rcases Finset.mem_insert.mp h1_mem with h | h
    · rw [h]; decide
    · rw [Finset.mem_singleton.mp h]; decide
  have hlt01 : Set.powersetCard.permOfDisjoint hdisj 0 <
      Set.powersetCard.permOfDisjoint hdisj 1 := by
    rw [← (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).lt_iff_lt]
    change (_ : Fin 3) < _; rw [hv0, hv1]; exact h01_lt
  have hlt12 : Set.powersetCard.permOfDisjoint hdisj 1 <
      Set.powersetCard.permOfDisjoint hdisj 2 := by
    rw [← (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).lt_iff_lt]
    change (_ : Fin 3) < _; rw [hv1, hv2]; exact h1lt2
  have hperm : Set.powersetCard.permOfDisjoint hdisj = 1 := by
    have h01 := Fin.lt_def.mp hlt01
    have h12 := Fin.lt_def.mp hlt12
    have h0b := (Set.powersetCard.permOfDisjoint hdisj 0).isLt
    have h1b := (Set.powersetCard.permOfDisjoint hdisj 1).isLt
    have h2b := (Set.powersetCard.permOfDisjoint hdisj 2).isLt
    have h0 : (Set.powersetCard.permOfDisjoint hdisj 0).val = 0 := by omega
    have h1 : (Set.powersetCard.permOfDisjoint hdisj 1).val = 1 := by omega
    have h2 : (Set.powersetCard.permOfDisjoint hdisj 2).val = 2 := by omega
    ext i
    simp only [Equiv.Perm.coe_one, id_eq]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  rw [hperm, Equiv.Perm.sign_one, one_smul]
  rw [hdisjU]; rfl

private def ext3FockImage (s : Finset (Fin 3)) : SplitOctCD :=
  if s = ∅ then uPlusCD
  else if s = {0} then -eMinusCD 0
  else if s = {1} then -eMinusCD 1
  else if s = {2} then -eMinusCD 2
  else if s = {0, 1} then ePlusCD 2
  else if s = {1, 2} then ePlusCD 0
  else if s = {0, 2} then -ePlusCD 1
  else uMinusCD

private lemma ite_true_eq {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private lemma ite_false_eq {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

private lemma ext3FockImage_vals :
    ext3FockImage ∅ = uPlusCD ∧
    ext3FockImage {0} = -eMinusCD 0 ∧
    ext3FockImage {1} = -eMinusCD 1 ∧
    ext3FockImage {2} = -eMinusCD 2 ∧
    ext3FockImage {0, 1} = ePlusCD 2 ∧
    ext3FockImage {1, 2} = ePlusCD 0 ∧
    ext3FockImage {0, 2} = -ePlusCD 1 ∧
    ext3FockImage {0, 1, 2} = uMinusCD := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ext3FockImage; rw [ite_true_eq rfl]
  · unfold ext3FockImage; rw [ite_false_eq (by decide), ite_true_eq rfl]
  · unfold ext3FockImage; rw [ite_false_eq (by decide), ite_false_eq (by decide), ite_true_eq rfl]
  · unfold ext3FockImage
    rw [ite_false_eq (by decide), ite_false_eq (by decide), ite_false_eq (by decide),
      ite_true_eq rfl]
  · unfold ext3FockImage
    rw [ite_false_eq (by decide), ite_false_eq (by decide), ite_false_eq (by decide),
      ite_false_eq (by decide), ite_true_eq rfl]
  · unfold ext3FockImage
    rw [ite_false_eq (by decide), ite_false_eq (by decide), ite_false_eq (by decide),
      ite_false_eq (by decide), ite_false_eq (by decide), ite_true_eq rfl]
  · unfold ext3FockImage
    rw [ite_false_eq (by decide), ite_false_eq (by decide), ite_false_eq (by decide),
      ite_false_eq (by decide), ite_false_eq (by decide), ite_false_eq (by decide),
      ite_true_eq rfl]
  · unfold ext3FockImage
    rw [ite_false_eq (by decide), ite_false_eq (by decide), ite_false_eq (by decide),
      ite_false_eq (by decide), ite_false_eq (by decide), ite_false_eq (by decide),
      ite_false_eq (by decide)]

/-- Option A exterior Fock isomorphism `ExteriorAlgebra ℝ (Fin 3 → ℝ) ≃ₗ[ℝ] SplitOctCD`:
`∅ ↦ u_+`, `{k} ↦ -e_k^-`, `{0,1} ↦ e_2^+`, `{1,2} ↦ e_0^+`, `{0,2} ↦ -e_1^+`,
`{0,1,2} ↦ u_-`, mapping `Λ⁰ ⊕ Λ¹ ⊕ Λ² ⊕ Λ³` onto `1 ⊕ 3̄ ⊕ 3 ⊕ 1`. -/
def ext3ToSplitOctCD : ExteriorAlgebra ℝ (Fin 3 → ℝ) ≃ₗ[ℝ] SplitOctCD := by
  let f : ExteriorAlgebra ℝ (Fin 3 → ℝ) →ₗ[ℝ] SplitOctCD :=
    ext3Basis.constr ℝ ext3FockImage
  have hfin : Module.finrank ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)) =
      Module.finrank ℝ SplitOctCD := by
    rw [Module.finrank_eq_card_basis ext3Basis, Fintype.card_finset, Fintype.card_fin,
      Module.finrank_eq_card_basis basisCD, Fintype.card_fin]
    norm_num
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range ext3FockImage) := by
      have hspan : Submodule.span ℝ (Set.range ext3FockImage) = ⊤ := by
        rw [eq_top_iff]
        intro z _
        have hchiral : z = (chiralZornEquiv z).1 • uPlusCD + (chiralZornEquiv z).2.1 • uMinusCD +
            ∑ k : Fin 3, (chiralZornEquiv z).2.2.1 k • ePlusCD k +
            ∑ k : Fin 3, (chiralZornEquiv z).2.2.2 k • eMinusCD k := by
          have h := chiralZornEquiv.symm_apply_apply z
          exact h.symm
        rw [hchiral, Fin.sum_univ_three, Fin.sum_univ_three]
        have huP : uPlusCD ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
          Submodule.subset_span ⟨∅, ext3FockImage_vals.1⟩
        have huM : uMinusCD ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
          Submodule.subset_span ⟨{0, 1, 2}, ext3FockImage_vals.2.2.2.2.2.2.2⟩
        have heP0 : ePlusCD 0 ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
          Submodule.subset_span ⟨{1, 2}, ext3FockImage_vals.2.2.2.2.2.1⟩
        have heP1 : ePlusCD 1 ∈ Submodule.span ℝ (Set.range ext3FockImage) := by
          have h0 : -ePlusCD 1 ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
            Submodule.subset_span ⟨{0, 2}, ext3FockImage_vals.2.2.2.2.2.2.1⟩
          simpa using Submodule.neg_mem _ h0
        have heP2 : ePlusCD 2 ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
          Submodule.subset_span ⟨{0, 1}, ext3FockImage_vals.2.2.2.2.1⟩
        have heM0 : eMinusCD 0 ∈ Submodule.span ℝ (Set.range ext3FockImage) := by
          have h0 : -eMinusCD 0 ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
            Submodule.subset_span ⟨{0}, ext3FockImage_vals.2.1⟩
          simpa using Submodule.neg_mem _ h0
        have heM1 : eMinusCD 1 ∈ Submodule.span ℝ (Set.range ext3FockImage) := by
          have h0 : -eMinusCD 1 ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
            Submodule.subset_span ⟨{1}, ext3FockImage_vals.2.2.1⟩
          simpa using Submodule.neg_mem _ h0
        have heM2 : eMinusCD 2 ∈ Submodule.span ℝ (Set.range ext3FockImage) := by
          have h0 : -eMinusCD 2 ∈ Submodule.span ℝ (Set.range ext3FockImage) :=
            Submodule.subset_span ⟨{2}, ext3FockImage_vals.2.2.2.1⟩
          simpa using Submodule.neg_mem _ h0
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ huP) (Submodule.smul_mem _ _ huM))
          (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ heP0)
            (Submodule.smul_mem _ _ heP1)) (Submodule.smul_mem _ _ heP2)))
          (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ heM0)
            (Submodule.smul_mem _ _ heM1)) (Submodule.smul_mem _ _ heM2))
      rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    rcases hy with ⟨c, rfl⟩
    refine ⟨∑ s : Finset (Fin 3), c s • ext3Basis s, ?_⟩
    simp [f, map_sum, map_smul, ext3Basis.constr_basis]
  have hinj : Function.Injective f := by
    have : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)) :=
      Module.Basis.finiteDimensional_of_finite ext3Basis
    have : FiniteDimensional ℝ SplitOctCD :=
      Module.Basis.finiteDimensional_of_finite basisCD
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

@[simp] theorem ext3ToSplitOctCD_one : ext3ToSplitOctCD 1 = uPlusCD := by
  change ext3Basis.constr ℝ ext3FockImage 1 = uPlusCD
  rw [← ext3Basis_empty, ext3Basis.constr_basis]
  exact ext3FockImage_vals.1

@[simp] theorem ext3ToSplitOctCD_θ3 (k : Fin 3) :
    ext3ToSplitOctCD (θ3 k) = -eMinusCD k := by
  change ext3Basis.constr ℝ ext3FockImage (θ3 k) = -eMinusCD k
  rw [← ext3Basis_singleton k, ext3Basis.constr_basis]
  fin_cases k
  · exact ext3FockImage_vals.2.1
  · exact ext3FockImage_vals.2.2.1
  · exact ext3FockImage_vals.2.2.2.1

@[simp] theorem ext3ToSplitOctCD_pair_01 :
    ext3ToSplitOctCD (θ3 0 * θ3 1) = ePlusCD 2 := by
  change ext3Basis.constr ℝ ext3FockImage (θ3 0 * θ3 1) = ePlusCD 2
  rw [← ext3Basis_pair (by decide : (0 : Fin 3) < 1), ext3Basis.constr_basis]
  exact ext3FockImage_vals.2.2.2.2.1

@[simp] theorem ext3ToSplitOctCD_pair_12 :
    ext3ToSplitOctCD (θ3 1 * θ3 2) = ePlusCD 0 := by
  change ext3Basis.constr ℝ ext3FockImage (θ3 1 * θ3 2) = ePlusCD 0
  rw [← ext3Basis_pair (by decide : (1 : Fin 3) < 2), ext3Basis.constr_basis]
  exact ext3FockImage_vals.2.2.2.2.2.1

@[simp] theorem ext3ToSplitOctCD_pair_02 :
    ext3ToSplitOctCD (θ3 0 * θ3 2) = -ePlusCD 1 := by
  change ext3Basis.constr ℝ ext3FockImage (θ3 0 * θ3 2) = -ePlusCD 1
  rw [← ext3Basis_pair (by decide : (0 : Fin 3) < 2), ext3Basis.constr_basis]
  exact ext3FockImage_vals.2.2.2.2.2.2.1

@[simp] theorem ext3ToSplitOctCD_top :
    ext3ToSplitOctCD (θ3 0 * θ3 1 * θ3 2) = uMinusCD := by
  change ext3Basis.constr ℝ ext3FockImage (θ3 0 * θ3 1 * θ3 2) = uMinusCD
  rw [← ext3Basis_univ, ext3Basis.constr_basis]
  exact ext3FockImage_vals.2.2.2.2.2.2.2

private theorem ext3_basis_ind (P : ExteriorAlgebra ℝ (Fin 3 → ℝ) → Prop)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (r : ℝ) x, P x → P (r • x))
    (h0 : P 1) (h1 : P (θ3 0)) (h2 : P (θ3 1)) (h3 : P (θ3 2))
    (h01 : P (θ3 0 * θ3 1)) (h12 : P (θ3 1 * θ3 2)) (h02 : P (θ3 0 * θ3 2))
    (h012 : P (θ3 0 * θ3 1 * θ3 2)) (ω : ExteriorAlgebra ℝ (Fin 3 → ℝ)) : P ω := by
  rw [← ext3Basis.sum_repr ω]
  refine Finset.sum_induction _ P hadd (by simpa using hsmul 0 1 h0) ?_
  intro s _
  refine hsmul (ext3Basis.repr ω s) (ext3Basis s) ?_
  have hs : s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {2} ∨ s = {0, 1} ∨ s = {1, 2} ∨
      s = {0, 2} ∨ s = {0, 1, 2} := by
    revert s; decide
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ext3Basis_empty]; exact h0
  · rw [ext3Basis_singleton 0]; exact h1
  · rw [ext3Basis_singleton 1]; exact h2
  · rw [ext3Basis_singleton 2]; exact h3
  · rw [ext3Basis_pair (by decide : (0 : Fin 3) < 1)]; exact h01
  · rw [ext3Basis_pair (by decide : (1 : Fin 3) < 2)]; exact h12
  · rw [ext3Basis_pair (by decide : (0 : Fin 3) < 2)]; exact h02
  · rw [ext3Basis_univ]; exact h012

private lemma θ3_swap {j k : Fin 3} : θ3 j * θ3 k = -(θ3 k * θ3 j) := by
  have h := ExteriorAlgebra.ι_add_mul_swap (R := ℝ)
    (Pi.single j (1 : ℝ) : Fin 3 → ℝ) (Pi.single k (1 : ℝ) : Fin 3 → ℝ)
  exact eq_neg_of_add_eq_zero_left h

private lemma θ3_sq_zero (k : Fin 3) : θ3 k * θ3 k = 0 :=
  ExteriorAlgebra.ι_sq_zero _

private lemma ext3_contract_θ3 (i j : Fin 3) :
    exteriorContract (LinearMap.proj i) (θ3 j) = if j = i then 1 else 0 := by
  dsimp only [θ3]
  rw [exteriorContract_iota, LinearMap.proj_apply, Pi.single_apply]
  by_cases hij : i = j <;> simp [hij, eq_comm]

private lemma ext3_contract_mul_θ3 (i j : Fin 3) (x : ExteriorAlgebra ℝ (Fin 3 → ℝ)) :
    exteriorContract (LinearMap.proj i) (θ3 j * x) =
      (if j = i then x else 0) - θ3 j * exteriorContract (LinearMap.proj i) x := by
  have hw : θ3 j * x = exteriorWedge ℝ (Pi.single j (1 : ℝ)) x := rfl
  rw [hw, exteriorContract_wedge_apply, LinearMap.proj_apply, Pi.single_apply]
  simp only [exteriorWedge_apply, eq_comm (a := i) (b := j)]
  split_ifs <;> simp [θ3]

private lemma ext3_contract_01_0 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 0) (θ3 0 * θ3 1)) =
      ePlusCD 0 * ext3ToSplitOctCD (θ3 0 * θ3 1) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_01]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 3) ≠ 0 by decide, mul_zero, sub_zero,
    ext3ToSplitOctCD_θ3]
  ext <;> simp [ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_01_1 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 1) (θ3 0 * θ3 1)) =
      ePlusCD 1 * ext3ToSplitOctCD (θ3 0 * θ3 1) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_01]
  simp only [Fin.isValue, ↓reduceIte, show (0 : Fin 3) ≠ 1 by decide, mul_one, zero_sub,
    map_neg, ext3ToSplitOctCD_θ3, neg_neg]
  ext <;> simp [ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_01_2 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 2) (θ3 0 * θ3 1)) =
      ePlusCD 2 * ext3ToSplitOctCD (θ3 0 * θ3 1) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_01]
  simp only [Fin.isValue, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    ↓reduceIte, mul_zero, sub_zero, map_zero]
  ext <;> simp [ePlusCD_components, qBasis]

private lemma ext3_contract_01 (j : Fin 3) :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj j) (θ3 0 * θ3 1)) =
      ePlusCD j * ext3ToSplitOctCD (θ3 0 * θ3 1) := by
  fin_cases j
  · exact ext3_contract_01_0
  · exact ext3_contract_01_1
  · exact ext3_contract_01_2

private lemma ext3_contract_12_0 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 0) (θ3 1 * θ3 2)) =
      ePlusCD 0 * ext3ToSplitOctCD (θ3 1 * θ3 2) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_12]
  simp only [Fin.isValue, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    ↓reduceIte, mul_zero, sub_zero, map_zero]
  ext <;> simp [ePlusCD_components, qBasis]

private lemma ext3_contract_12_1 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 1) (θ3 1 * θ3 2)) =
      ePlusCD 1 * ext3ToSplitOctCD (θ3 1 * θ3 2) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_12]
  simp only [Fin.isValue, ↓reduceIte, show (2 : Fin 3) ≠ 1 by decide, mul_zero, sub_zero,
    ext3ToSplitOctCD_θ3]
  ext <;> simp [ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_12_2 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 2) (θ3 1 * θ3 2)) =
      ePlusCD 2 * ext3ToSplitOctCD (θ3 1 * θ3 2) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_12]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 3) ≠ 2 by decide, mul_one, zero_sub,
    map_neg, ext3ToSplitOctCD_θ3, neg_neg]
  ext <;> simp [ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_12 (j : Fin 3) :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj j) (θ3 1 * θ3 2)) =
      ePlusCD j * ext3ToSplitOctCD (θ3 1 * θ3 2) := by
  fin_cases j
  · exact ext3_contract_12_0
  · exact ext3_contract_12_1
  · exact ext3_contract_12_2

private lemma ext3_contract_02_0 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 0) (θ3 0 * θ3 2)) =
      ePlusCD 0 * ext3ToSplitOctCD (θ3 0 * θ3 2) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_02, mul_neg]
  simp only [Fin.isValue, ↓reduceIte, show (2 : Fin 3) ≠ 0 by decide, mul_zero, sub_zero,
    ext3ToSplitOctCD_θ3]
  ext <;> simp [ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_02_1 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 1) (θ3 0 * θ3 2)) =
      ePlusCD 1 * ext3ToSplitOctCD (θ3 0 * θ3 2) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_02, mul_neg]
  simp only [Fin.isValue, show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ↓reduceIte, mul_zero, sub_zero, map_zero]
  ext <;> simp [ePlusCD_components, qBasis]

private lemma ext3_contract_02_2 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 2) (θ3 0 * θ3 2)) =
      ePlusCD 2 * ext3ToSplitOctCD (θ3 0 * θ3 2) := by
  rw [ext3_contract_mul_θ3, ext3_contract_θ3, ext3ToSplitOctCD_pair_02, mul_neg]
  simp only [Fin.isValue, ↓reduceIte, show (0 : Fin 3) ≠ 2 by decide, mul_one, zero_sub,
    map_neg, ext3ToSplitOctCD_θ3, neg_neg]
  ext <;> simp [ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_02 (j : Fin 3) :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj j) (θ3 0 * θ3 2)) =
      ePlusCD j * ext3ToSplitOctCD (θ3 0 * θ3 2) := by
  fin_cases j
  · exact ext3_contract_02_0
  · exact ext3_contract_02_1
  · exact ext3_contract_02_2

private lemma ext3_contract_012_0 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 0) (θ3 0 * θ3 1 * θ3 2)) =
      ePlusCD 0 * ext3ToSplitOctCD (θ3 0 * θ3 1 * θ3 2) := by
  rw [ext3ToSplitOctCD_top, mul_assoc, ext3_contract_mul_θ3, ext3_contract_mul_θ3,
    ext3_contract_θ3]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, mul_zero, sub_zero, ext3ToSplitOctCD_pair_12]
  ext <;> simp [ePlusCD_components, uMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_012_1 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 1) (θ3 0 * θ3 1 * θ3 2)) =
      ePlusCD 1 * ext3ToSplitOctCD (θ3 0 * θ3 1 * θ3 2) := by
  rw [ext3ToSplitOctCD_top, mul_assoc, ext3_contract_mul_θ3, ext3_contract_mul_θ3,
    ext3_contract_θ3]
  simp only [Fin.isValue, ↓reduceIte, show (0 : Fin 3) ≠ 1 by decide,
    show (2 : Fin 3) ≠ 1 by decide, mul_zero, sub_zero, zero_sub, map_neg,
    ext3ToSplitOctCD_pair_02, neg_neg]
  ext <;> simp [ePlusCD_components, uMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_012_2 :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj 2) (θ3 0 * θ3 1 * θ3 2)) =
      ePlusCD 2 * ext3ToSplitOctCD (θ3 0 * θ3 1 * θ3 2) := by
  rw [ext3ToSplitOctCD_top, mul_assoc, ext3_contract_mul_θ3, ext3_contract_mul_θ3,
    ext3_contract_θ3]
  simp only [Fin.isValue, ↓reduceIte, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, mul_one, zero_sub, mul_neg, neg_neg,
    ext3ToSplitOctCD_pair_01]
  ext <;> simp [ePlusCD_components, uMinusCD_components, qBasis] <;> norm_num

private lemma ext3_contract_012 (j : Fin 3) :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj j) (θ3 0 * θ3 1 * θ3 2)) =
      ePlusCD j * ext3ToSplitOctCD (θ3 0 * θ3 1 * θ3 2) := by
  fin_cases j
  · exact ext3_contract_012_0
  · exact ext3_contract_012_1
  · exact ext3_contract_012_2

/-- Intertwining of exterior contraction `exteriorContract (proj j)` with left multiplication
by `ePlusCD j` (`carAnnihilateMat j`). -/
theorem ext3ToSplitOctCD_contract (j : Fin 3) (ω : ExteriorAlgebra ℝ (Fin 3 → ℝ)) :
    ext3ToSplitOctCD (exteriorContract (LinearMap.proj j) ω) =
      ePlusCD j * ext3ToSplitOctCD ω := by
  induction ω using ext3_basis_ind with
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, mul_add]
  | hsmul r x hx => rw [map_smul, map_smul, map_smul, hx, cdMul_smul_right]
  | h0 =>
      rw [exteriorContract_one, map_zero, ext3ToSplitOctCD_one]
      ext <;> simp [ePlusCD_components, uPlusCD_components]
      all_goals fin_cases j <;> simp [qBasis]
  | h1 =>
      change ext3ToSplitOctCD (exteriorContract (LinearMap.proj j)
          (ExteriorAlgebra.ι ℝ (Pi.single 0 1))) = ePlusCD j * ext3ToSplitOctCD (θ3 0)
      rw [exteriorContract_iota, LinearMap.proj_apply, map_smul, ext3ToSplitOctCD_one,
        ext3ToSplitOctCD_θ3, mul_neg]
      fin_cases j <;> ext <;> simp [ePlusCD_components, eMinusCD_components,
        uPlusCD_components, qBasis] <;> norm_num
  | h2 =>
      change ext3ToSplitOctCD (exteriorContract (LinearMap.proj j)
          (ExteriorAlgebra.ι ℝ (Pi.single 1 1))) = ePlusCD j * ext3ToSplitOctCD (θ3 1)
      rw [exteriorContract_iota, LinearMap.proj_apply, map_smul, ext3ToSplitOctCD_one,
        ext3ToSplitOctCD_θ3, mul_neg]
      fin_cases j <;> ext <;> simp [ePlusCD_components, eMinusCD_components,
        uPlusCD_components, qBasis] <;> norm_num
  | h3 =>
      change ext3ToSplitOctCD (exteriorContract (LinearMap.proj j)
          (ExteriorAlgebra.ι ℝ (Pi.single 2 1))) = ePlusCD j * ext3ToSplitOctCD (θ3 2)
      rw [exteriorContract_iota, LinearMap.proj_apply, map_smul, ext3ToSplitOctCD_one,
        ext3ToSplitOctCD_θ3, mul_neg]
      fin_cases j <;> ext <;> simp [ePlusCD_components, eMinusCD_components,
        uPlusCD_components, qBasis] <;> norm_num
  | h01 => exact ext3_contract_01 j
  | h12 => exact ext3_contract_12 j
  | h02 => exact ext3_contract_02 j
  | h012 => exact ext3_contract_012 j

private lemma ext3_wedge_01 (k : Fin 3) :
    ext3ToSplitOctCD (exteriorWedge ℝ (Pi.single k 1) (θ3 0 * θ3 1)) =
      (-eMinusCD k) * ext3ToSplitOctCD (θ3 0 * θ3 1) := by
  rw [exteriorWedge_apply]
  change ext3ToSplitOctCD (θ3 k * (θ3 0 * θ3 1)) =
    (-eMinusCD k) * ext3ToSplitOctCD (θ3 0 * θ3 1)
  rw [ext3ToSplitOctCD_pair_01]
  fin_cases k
  · change ext3ToSplitOctCD (θ3 0 * (θ3 0 * θ3 1)) = -eMinusCD 0 * ePlusCD 2
    rw [← mul_assoc, θ3_sq_zero 0, zero_mul, map_zero]
    ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis]
  · change ext3ToSplitOctCD (θ3 1 * (θ3 0 * θ3 1)) = -eMinusCD 1 * ePlusCD 2
    rw [← mul_assoc, θ3_swap (j := 1) (k := 0), neg_mul, mul_assoc, θ3_sq_zero 1,
      mul_zero, neg_zero, map_zero]
    ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis]
  · change ext3ToSplitOctCD (θ3 2 * (θ3 0 * θ3 1)) = -eMinusCD 2 * ePlusCD 2
    rw [← mul_assoc, θ3_swap (j := 2) (k := 0), neg_mul, mul_assoc,
      θ3_swap (j := 2) (k := 1), mul_neg, neg_neg, ← mul_assoc, ext3ToSplitOctCD_top]
    ext <;> simp [eMinusCD_components, ePlusCD_components, uMinusCD_components, qBasis] <;>
      norm_num

private lemma ext3_wedge_12 (k : Fin 3) :
    ext3ToSplitOctCD (exteriorWedge ℝ (Pi.single k 1) (θ3 1 * θ3 2)) =
      (-eMinusCD k) * ext3ToSplitOctCD (θ3 1 * θ3 2) := by
  rw [exteriorWedge_apply]
  change ext3ToSplitOctCD (θ3 k * (θ3 1 * θ3 2)) =
    (-eMinusCD k) * ext3ToSplitOctCD (θ3 1 * θ3 2)
  rw [ext3ToSplitOctCD_pair_12]
  fin_cases k
  · change ext3ToSplitOctCD (θ3 0 * (θ3 1 * θ3 2)) = -eMinusCD 0 * ePlusCD 0
    rw [← mul_assoc, ext3ToSplitOctCD_top]
    ext <;> simp [eMinusCD_components, ePlusCD_components, uMinusCD_components, qBasis] <;>
      norm_num
  · change ext3ToSplitOctCD (θ3 1 * (θ3 1 * θ3 2)) = -eMinusCD 1 * ePlusCD 0
    rw [← mul_assoc, θ3_sq_zero 1, zero_mul, map_zero]
    ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis]
  · change ext3ToSplitOctCD (θ3 2 * (θ3 1 * θ3 2)) = -eMinusCD 2 * ePlusCD 0
    rw [← mul_assoc, θ3_swap (j := 2) (k := 1), neg_mul, mul_assoc, θ3_sq_zero 2,
      mul_zero, neg_zero, map_zero]
    ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis]

private lemma ext3_wedge_02 (k : Fin 3) :
    ext3ToSplitOctCD (exteriorWedge ℝ (Pi.single k 1) (θ3 0 * θ3 2)) =
      (-eMinusCD k) * ext3ToSplitOctCD (θ3 0 * θ3 2) := by
  rw [exteriorWedge_apply]
  change ext3ToSplitOctCD (θ3 k * (θ3 0 * θ3 2)) =
    (-eMinusCD k) * ext3ToSplitOctCD (θ3 0 * θ3 2)
  rw [ext3ToSplitOctCD_pair_02]
  fin_cases k
  · change ext3ToSplitOctCD (θ3 0 * (θ3 0 * θ3 2)) = -eMinusCD 0 * -ePlusCD 1
    rw [← mul_assoc, θ3_sq_zero 0, zero_mul, map_zero]
    ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis]
  · change ext3ToSplitOctCD (θ3 1 * (θ3 0 * θ3 2)) = -eMinusCD 1 * -ePlusCD 1
    rw [← mul_assoc, θ3_swap (j := 1) (k := 0), neg_mul, map_neg, ext3ToSplitOctCD_top]
    ext <;> simp [eMinusCD_components, ePlusCD_components, uMinusCD_components, qBasis] <;>
      norm_num
  · change ext3ToSplitOctCD (θ3 2 * (θ3 0 * θ3 2)) = -eMinusCD 2 * -ePlusCD 1
    rw [← mul_assoc, θ3_swap (j := 2) (k := 0), neg_mul, mul_assoc, θ3_sq_zero 2,
      mul_zero, neg_zero, map_zero]
    ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis]

private lemma ext3_wedge_012 (k : Fin 3) :
    ext3ToSplitOctCD (exteriorWedge ℝ (Pi.single k 1) (θ3 0 * θ3 1 * θ3 2)) =
      (-eMinusCD k) * ext3ToSplitOctCD (θ3 0 * θ3 1 * θ3 2) := by
  rw [exteriorWedge_apply]
  change ext3ToSplitOctCD (θ3 k * (θ3 0 * θ3 1 * θ3 2)) =
    (-eMinusCD k) * ext3ToSplitOctCD (θ3 0 * θ3 1 * θ3 2)
  rw [ext3ToSplitOctCD_top]
  fin_cases k
  · change ext3ToSplitOctCD (θ3 0 * (θ3 0 * θ3 1 * θ3 2)) = -eMinusCD 0 * uMinusCD
    rw [← mul_assoc, ← mul_assoc, θ3_sq_zero 0, zero_mul, zero_mul, map_zero]
    ext <;> simp [eMinusCD_components, uMinusCD_components, qBasis]
  · change ext3ToSplitOctCD (θ3 1 * (θ3 0 * θ3 1 * θ3 2)) = -eMinusCD 1 * uMinusCD
    rw [← mul_assoc, ← mul_assoc, θ3_swap (j := 1) (k := 0), neg_mul, mul_assoc (θ3 0),
      θ3_sq_zero 1, mul_zero, neg_zero, zero_mul, map_zero]
    ext <;> simp [eMinusCD_components, uMinusCD_components, qBasis]
  · change ext3ToSplitOctCD (θ3 2 * (θ3 0 * θ3 1 * θ3 2)) = -eMinusCD 2 * uMinusCD
    have h21 : θ3 2 * (θ3 0 * θ3 1) = θ3 0 * θ3 1 * θ3 2 := by
      rw [← mul_assoc, θ3_swap (j := 2) (k := 0), neg_mul, mul_assoc,
        θ3_swap (j := 2) (k := 1), mul_neg, neg_neg, ← mul_assoc]
    rw [← mul_assoc, h21, mul_assoc, θ3_sq_zero 2, mul_zero, map_zero]
    ext <;> simp [eMinusCD_components, uMinusCD_components, qBasis]

/-- Intertwining of exterior wedge `exteriorWedge ℝ (Pi.single k 1)` with left multiplication
by `-eMinusCD k` (`carCreateMat k`). -/
theorem ext3ToSplitOctCD_wedge (k : Fin 3) (ω : ExteriorAlgebra ℝ (Fin 3 → ℝ)) :
    ext3ToSplitOctCD (exteriorWedge ℝ (Pi.single k 1) ω) =
      (-eMinusCD k) * ext3ToSplitOctCD ω := by
  induction ω using ext3_basis_ind with
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, mul_add]
  | hsmul r x hx => rw [map_smul, map_smul, map_smul, hx, cdMul_smul_right]
  | h0 =>
      rw [exteriorWedge_apply, mul_one, ext3ToSplitOctCD_one]
      change ext3ToSplitOctCD (θ3 k) = (-eMinusCD k) * uPlusCD
      rw [ext3ToSplitOctCD_θ3]
      fin_cases k <;> ext <;> simp [eMinusCD_components, uPlusCD_components, qBasis] <;> norm_num
  | h1 =>
      rw [exteriorWedge_apply]
      change ext3ToSplitOctCD (θ3 k * θ3 0) = (-eMinusCD k) * ext3ToSplitOctCD (θ3 0)
      rw [ext3ToSplitOctCD_θ3]
      fin_cases k
      · change ext3ToSplitOctCD (θ3 0 * θ3 0) = -eMinusCD 0 * -eMinusCD 0
        rw [θ3_sq_zero 0, map_zero]
        ext <;> simp [eMinusCD_components, qBasis]
      · change ext3ToSplitOctCD (θ3 1 * θ3 0) = -eMinusCD 1 * -eMinusCD 0
        rw [θ3_swap, map_neg, ext3ToSplitOctCD_pair_01]
        ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis] <;> norm_num
      · change ext3ToSplitOctCD (θ3 2 * θ3 0) = -eMinusCD 2 * -eMinusCD 0
        rw [θ3_swap, map_neg, ext3ToSplitOctCD_pair_02, neg_neg]
        ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis] <;> norm_num
  | h2 =>
      rw [exteriorWedge_apply]
      change ext3ToSplitOctCD (θ3 k * θ3 1) = (-eMinusCD k) * ext3ToSplitOctCD (θ3 1)
      rw [ext3ToSplitOctCD_θ3]
      fin_cases k
      · change ext3ToSplitOctCD (θ3 0 * θ3 1) = -eMinusCD 0 * -eMinusCD 1
        rw [ext3ToSplitOctCD_pair_01]
        ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis] <;> norm_num
      · change ext3ToSplitOctCD (θ3 1 * θ3 1) = -eMinusCD 1 * -eMinusCD 1
        rw [θ3_sq_zero 1, map_zero]
        ext <;> simp [eMinusCD_components, qBasis]
      · change ext3ToSplitOctCD (θ3 2 * θ3 1) = -eMinusCD 2 * -eMinusCD 1
        rw [θ3_swap, map_neg, ext3ToSplitOctCD_pair_12]
        ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis] <;> norm_num
  | h3 =>
      rw [exteriorWedge_apply]
      change ext3ToSplitOctCD (θ3 k * θ3 2) = (-eMinusCD k) * ext3ToSplitOctCD (θ3 2)
      rw [ext3ToSplitOctCD_θ3]
      fin_cases k
      · change ext3ToSplitOctCD (θ3 0 * θ3 2) = -eMinusCD 0 * -eMinusCD 2
        rw [ext3ToSplitOctCD_pair_02]
        ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis] <;> norm_num
      · change ext3ToSplitOctCD (θ3 1 * θ3 2) = -eMinusCD 1 * -eMinusCD 2
        rw [ext3ToSplitOctCD_pair_12]
        ext <;> simp [eMinusCD_components, ePlusCD_components, qBasis] <;> norm_num
      · change ext3ToSplitOctCD (θ3 2 * θ3 2) = -eMinusCD 2 * -eMinusCD 2
        rw [θ3_sq_zero 2, map_zero]
        ext <;> simp [eMinusCD_components, qBasis]
  | h01 => exact ext3_wedge_01 k
  | h12 => exact ext3_wedge_12 k
  | h02 => exact ext3_wedge_02 k
  | h012 => exact ext3_wedge_012 k

/-- Intertwining of `KahlerDiracWeitzenbockSynthesis.chevalleyAction` with `sCD` / `iCD`. -/
theorem ext3ToSplitOctCD_kahlerChevalley (k : Fin 3) (ω : ExteriorAlgebra ℝ (Fin 3 → ℝ)) :
    ext3ToSplitOctCD
        (InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.chevalleyAction
          (Pi.single k 1) (LinearMap.proj k) ω) =
      sCD k * ext3ToSplitOctCD ω ∧
    ext3ToSplitOctCD
        (InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.chevalleyAction
          (-Pi.single k 1) (LinearMap.proj k) ω) =
      iCD k * ext3ToSplitOctCD ω := by
  have hs : sCD k = ePlusCD k - eMinusCD k := by
    rw [ePlusCD_eq_half_add, eMinusCD_eq_half_sub]
    ext <;> simp [sCD_formula, iCD, qBasis] <;> ring
  have hi : iCD k = ePlusCD k + eMinusCD k := by
    rw [ePlusCD_eq_half_add, eMinusCD_eq_half_sub]
    ext <;> simp [sCD_formula, iCD, qBasis] <;> ring
  refine ⟨?_, ?_⟩
  · unfold InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.chevalleyAction
    rw [LinearMap.add_apply, map_add, ext3ToSplitOctCD_wedge, ext3ToSplitOctCD_contract, hs]
    rw [sub_eq_add_neg, add_mul, add_comm, neg_mul]
  · unfold InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.chevalleyAction
    have hw : exteriorWedge ℝ (-Pi.single k (1 : ℝ)) ω =
        -exteriorWedge ℝ (Pi.single k (1 : ℝ)) ω := by
      change ExteriorAlgebra.ι ℝ (-Pi.single k (1 : ℝ)) * ω =
        -(ExteriorAlgebra.ι ℝ (Pi.single k (1 : ℝ)) * ω)
      rw [map_neg, neg_mul]
    rw [LinearMap.add_apply, map_add, hw, map_neg, ext3ToSplitOctCD_wedge,
      ext3ToSplitOctCD_contract, hi, neg_mul, neg_neg, add_comm, add_mul]

private def fockMajoranaVec (c : Fin 6 → ℝ) :
    Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)) :=
  ∑ k : Fin 3, c (q33PlusIdx' k) •
      InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.chevalleyAction
        (Pi.single k 1) (LinearMap.proj k) +
    ∑ k : Fin 3, c (q33MinusIdx' k) •
      InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.chevalleyAction
        (-Pi.single k 1) (LinearMap.proj k)

private def fockMajoranaLinear :
    (Fin 6 → ℝ) →ₗ[ℝ] Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)) where
  toFun := fockMajoranaVec
  map_add' c d := by
    simp only [fockMajoranaVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' r c := by
    simp only [fockMajoranaVec, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      Finset.smul_sum, smul_smul]

private lemma zornCl33_morphism_eq :
    cliffordMorphism zornCl33FormHodgeData = cliffordQ33ToMat8.toAlgHom :=
  AlgHom.ext fun _ => rfl

private lemma fockMajorana_intertwine (c : Fin 6 → ℝ) (ω : ExteriorAlgebra ℝ (Fin 3 → ℝ)) :
    cdToFin8 (ext3ToSplitOctCD (fockMajoranaVec c ω)) =
      (q33VecToMat c) *ᵥ cdToFin8 (ext3ToSplitOctCD ω) := by
  have hL : ext3ToSplitOctCD (fockMajoranaVec c ω) =
      (∑ k : Fin 3, c (q33PlusIdx' k) • sCD k +
        ∑ k : Fin 3, c (q33MinusIdx' k) • iCD k) * ext3ToSplitOctCD ω := by
    simp only [fockMajoranaVec, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_add, map_sum, map_smul]
    simp_rw [fun k => (ext3ToSplitOctCD_kahlerChevalley k ω).1,
      fun k => (ext3ToSplitOctCD_kahlerChevalley k ω).2, ← cdMul_smul_left, ← Finset.sum_mul,
      ← add_mul]
  have hM : q33VecToMat c =
      leftMulMat (∑ k : Fin 3, c (q33PlusIdx' k) • sCD k +
        ∑ k : Fin 3, c (q33MinusIdx' k) • iCD k) := by
    rw [leftMulMat_add, Fin.sum_univ_three, Fin.sum_univ_three,
      leftMulMat_add, leftMulMat_add, leftMulMat_add, leftMulMat_add]
    simp_rw [leftMulMat_smul, ← majoranaPlusMat_eq_leftMulMat_sCD,
      ← majoranaMinusMat_eq_leftMulMat_iCD]
    unfold q33VecToMat
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_six,
      q33PlusIdx', q33MinusIdx', q33GenMat]
    abel
  have hL_fin : cdToFin8 ((∑ k : Fin 3, c (q33PlusIdx' k) • sCD k +
      ∑ k : Fin 3, c (q33MinusIdx' k) • iCD k) * ext3ToSplitOctCD ω) =
      leftMulFin8 (∑ k : Fin 3, c (q33PlusIdx' k) • sCD k +
        ∑ k : Fin 3, c (q33MinusIdx' k) • iCD k) (cdToFin8 (ext3ToSplitOctCD ω)) := by
    change cdToFin8 (_ * ext3ToSplitOctCD ω) =
      cdToFin8 (_ * fin8ToCD (cdToFin8 (ext3ToSplitOctCD ω)))
    rw [← cdLinearEquivFin8_symm_apply,
      show cdToFin8 (ext3ToSplitOctCD ω) = cdLinearEquivFin8 (ext3ToSplitOctCD ω) from rfl,
      cdLinearEquivFin8.symm_apply_apply]
  rw [hL, hM, hL_fin]
  funext i
  change ((Pi.basisFun ℝ (Fin 8)).repr
    (leftMulFin8 (∑ k : Fin 3, c (q33PlusIdx' k) • sCD k +
        ∑ k : Fin 3, c (q33MinusIdx' k) • iCD k) (cdToFin8 (ext3ToSplitOctCD ω)))) i = _
  rw [← LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (leftMulFin8 _)]
  rfl

private lemma fockMajorana_sq (c : Fin 6 → ℝ) :
    fockMajoranaVec c * fockMajoranaVec c =
      algebraMap ℝ (Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ))) (Q33 c) := by
  apply LinearMap.ext; intro ω
  apply ext3ToSplitOctCD.injective
  apply cdLinearEquivFin8.injective
  change cdLinearEquivFin8 (ext3ToSplitOctCD (fockMajoranaVec c (fockMajoranaVec c ω))) =
    cdLinearEquivFin8 (ext3ToSplitOctCD (Q33 c • ω))
  change cdToFin8 (ext3ToSplitOctCD (fockMajoranaVec c (fockMajoranaVec c ω))) =
    cdLinearEquivFin8 (ext3ToSplitOctCD (Q33 c • ω))
  rw [fockMajorana_intertwine, fockMajorana_intertwine, Matrix.mulVec_mulVec,
    q33VecToMat_sq, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    map_smul, map_smul]
  rfl

private lemma fockMajoranaLinear_sq (c : Fin 6 → ℝ) :
    fockMajoranaLinear c * fockMajoranaLinear c =
      algebraMap ℝ (Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ))) (Q33 c) :=
  fockMajorana_sq c

/-- 8D exterior Fock representation `Cl(3,3) →ₐ[ℝ] End(Λ• ℝ³)` intertwining `cliffordMorphism`
on `SplitOctCD`. -/
def fockCliffordRep :
    CliffordAlgebra Q33 →ₐ[ℝ] Module.End ℝ (ExteriorAlgebra ℝ (Fin 3 → ℝ)) :=
  CliffordAlgebra.lift Q33 ⟨fockMajoranaLinear, fockMajoranaLinear_sq⟩

private lemma cliffordMorphism_zornCl33_apply (a : CliffordAlgebra Q33) :
    cliffordMorphism zornCl33FormHodgeData a = cliffordQ33ToMat8 a := rfl

theorem fockCliffordRep_intertwines (a : CliffordAlgebra Q33)
    (ω : ExteriorAlgebra ℝ (Fin 3 → ℝ)) :
    cdToFin8 (ext3ToSplitOctCD (fockCliffordRep a ω)) =
      (cliffordMorphism zornCl33FormHodgeData a) *ᵥ cdToFin8 (ext3ToSplitOctCD ω) := by
  rw [cliffordMorphism_zornCl33_apply]
  induction a using CliffordAlgebra.induction generalizing ω with
  | algebraMap r =>
      rw [AlgHom.commutes, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      change cdLinearEquivFin8 (ext3ToSplitOctCD (r • ω)) =
        r • cdLinearEquivFin8 (ext3ToSplitOctCD ω)
      rw [map_smul, map_smul]
  | ι v =>
      have hi : fockCliffordRep (CliffordAlgebra.ι Q33 v) = fockMajoranaLinear v :=
        CliffordAlgebra.lift_ι_apply fockMajoranaLinear fockMajoranaLinear_sq v
      rw [hi]
      simp only [fockMajoranaLinear, LinearMap.coe_mk, AddHom.coe_mk]
      have hgen : cliffordQ33ToMat8 (CliffordAlgebra.ι Q33 v) = q33VecToMat v :=
        cliffordMorphism_generator zornCl33FormHodgeData v
      rw [hgen]
      exact fockMajorana_intertwine v ω
  | mul a b ha hb =>
      rw [map_mul, map_mul, Module.End.mul_apply, ha, hb, Matrix.mulVec_mulVec]
  | add a b ha hb =>
      rw [map_add, map_add, LinearMap.add_apply]
      change cdLinearEquivFin8 (ext3ToSplitOctCD (fockCliffordRep a ω + fockCliffordRep b ω)) =
        (cliffordQ33ToMat8 a + cliffordQ33ToMat8 b) *ᵥ cdToFin8 (ext3ToSplitOctCD ω)
      rw [map_add, map_add]
      exact (congrArg₂ (· + ·) (ha ω) (hb ω)).trans (Matrix.add_mulVec _ _ _).symm

/-- Surjective 64D-to-8D vacuum readout map `Λ• ℝ⁶ →ₗ[ℝ] SplitOctCD` intertwining the
64D `ZornDifferentialFormsCliffordBridge.chevalleyAction` with `cliffordMorphism` / `leftMulMat`. -/
def chevalleyFockEval : ExteriorAlgebra ℝ (Fin 6 → ℝ) →ₗ[ℝ] SplitOctCD where
  toFun ω :=
    cdLinearEquivFin8.symm
      ((cliffordQ33ToMat8 ((CliffordAlgebra.equivExterior Q33).symm ω)) *ᵥ cdToFin8 uPlusCD)
  map_add' ω₁ ω₂ := by
    rw [map_add, map_add, Matrix.add_mulVec, map_add]
  map_smul' r ω := by
    rw [map_smul, map_smul, Matrix.smul_mulVec, map_smul, RingHom.id_apply]

theorem chevalleyFockEval_one : chevalleyFockEval 1 = uPlusCD := by
  have h1 : (CliffordAlgebra.equivExterior Q33).symm (1 : ExteriorAlgebra ℝ (Fin 6 → ℝ)) = 1 := by
    let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
    apply (CliffordAlgebra.equivExterior Q33).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (InfoGeometry.Clifford.GradedGraceContraction.equivExterior_algebraMap Q33 (1 : ℝ)).symm
  change cdLinearEquivFin8.symm ((cliffordQ33ToMat8 _) *ᵥ cdToFin8 uPlusCD) = uPlusCD
  rw [h1, map_one, Matrix.one_mulVec]
  exact cdLinearEquivFin8.symm_apply_apply uPlusCD

theorem chevalleyFockEval_intertwines (a : CliffordAlgebra Q33)
    (ω : ExteriorAlgebra ℝ (Fin 6 → ℝ)) :
    chevalleyFockEval
        (InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge.chevalleyAction
          zornCl33FormHodgeData a ω) =
      cdLinearEquivFin8.symm
        ((cliffordMorphism zornCl33FormHodgeData a) *ᵥ cdToFin8 (chevalleyFockEval ω)) := by
  rw [zornCl33_morphism_eq]
  change cdLinearEquivFin8.symm
    ((cliffordQ33ToMat8
      ((CliffordAlgebra.equivExterior Q33).symm
        (CliffordAlgebra.equivExterior Q33
          (a * (CliffordAlgebra.equivExterior Q33).symm ω)))) *ᵥ cdToFin8 uPlusCD) = _
  rw [LinearEquiv.symm_apply_apply, map_mul, ← Matrix.mulVec_mulVec]
  simp only [chevalleyFockEval, LinearMap.coe_mk, AddHom.coe_mk, cdLinearEquivFin8_symm_apply,
    cdToFin8_fin8ToCD]
  rfl

theorem chevalleyFockEval_surjective : Function.Surjective chevalleyFockEval := by
  intro y
  have hy : ∃ a : CliffordAlgebra Q33,
      cliffordMorphism zornCl33FormHodgeData a =
        Matrix.of fun i j => if j = 0 then 2 * cdToFin8 y i else 0 :=
    bridge_to_ZornDifferentialFormsCliffordBridge.2.1.2 _
  rcases hy with ⟨a, ha⟩
  rw [zornCl33_morphism_eq] at ha
  change cliffordQ33ToMat8 a = _ at ha
  refine ⟨CliffordAlgebra.equivExterior Q33 a, ?_⟩
  change cdLinearEquivFin8.symm
    ((cliffordQ33ToMat8
      ((CliffordAlgebra.equivExterior Q33).symm (CliffordAlgebra.equivExterior Q33 a))) *ᵥ
      cdToFin8 uPlusCD) = y
  rw [LinearEquiv.symm_apply_apply, ha]
  have hu0 : (cdToFin8 uPlusCD 0) = 1 / 2 := by
    simp [cdToFin8, uPlusCD_components]
  have hmul : (Matrix.of fun i j : Fin 8 => if j = 0 then 2 * cdToFin8 y i else 0).mulVec
      (cdToFin8 uPlusCD) = cdToFin8 y := by
    funext i
    simp [Matrix.mulVec, dotProduct, hu0]
    ring
  rw [hmul]
  exact cdLinearEquivFin8.symm_apply_apply y

/-! ## Section 7: Bridge to `InfoGeometry.Krein.DoubledSpace` (Feature F15) -/

/-- Canonical 4D Euclidean space matching `RealDoubledChiralKreinFrame.FourSpace`. -/
abbrev FourSpace := EuclideanSpace ℝ (Fin 4)

/-- Canonical 8D doubled Krein frame matching `RealDoubledChiralKreinFrame.KreinFrame4`. -/
abbrev KreinFrame4 := DoubledSpace FourSpace

/-- Standard orthonormal frame basis on `FourSpace`. -/
def frameBasis (i : Fin 4) : FourSpace :=
  EuclideanSpace.basisFun (Fin 4) ℝ i

/-- Positive sheet frame vector `(eᵢ, 0)` in `KreinFrame4`. -/
def plusFrame (i : Fin 4) : KreinFrame4 :=
  to_doubled (frameBasis i) 0

/-- Negative sheet frame vector `(0, eᵢ)` in `KreinFrame4`. -/
def minusFrame (i : Fin 4) : KreinFrame4 :=
  to_doubled 0 (frameBasis i)

/-- Cayley–Dickson `ℤ₂`-grading automorphism `σ(a, b) = (a, -b)` on `SplitOctCD`. -/
def cdGradingInvolution : SplitOctCD ≃ₗ[ℝ] SplitOctCD where
  toFun x := ⟨x.fst, -x.snd⟩
  invFun x := ⟨x.fst, -x.snd⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by
    rcases x with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
    rcases y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
    ext <;> simp <;> abel
  map_smul' r x := by ext <;> simp

theorem cdGradingInvolution_mul (x y : SplitOctCD) :
    cdGradingInvolution (x * y) = cdGradingInvolution x * cdGradingInvolution y := by
  ext <;> simp [cdGradingInvolution] <;> ring

theorem cdGradingInvolution_one : cdGradingInvolution 1 = 1 := by
  ext <;> simp [cdGradingInvolution]

/-- Canonical split complex-like operator `I_CD = σ ∘ L_ℓ` on `SplitOctCD`,
satisfying `cdComplexI² = -id`. -/
def cdComplexI : SplitOctCD ≃ₗ[ℝ] SplitOctCD where
  toFun x := cdGradingInvolution (ellCD * x)
  invFun x := -(cdGradingInvolution (ellCD * x))
  left_inv x := by
    rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
    ext <;> simp [cdGradingInvolution, ellCD]
  right_inv x := by
    rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
    ext <;> simp [cdGradingInvolution, ellCD]
  map_add' x y := by
    rw [mul_add, map_add]
  map_smul' r x := by
    rw [cdMul_smul_right, map_smul]; rfl

private def coordsToFourSpace (c0 : ℝ) (v : Fin 3 → ℝ) : FourSpace :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![c0, v 0, v 1, v 2]

private lemma inner_coordsToFourSpace (c0 d0 : ℝ) (v w : Fin 3 → ℝ) :
    inner ℝ (coordsToFourSpace c0 v) (coordsToFourSpace d0 w) =
      c0 * d0 + ∑ k : Fin 3, v k * w k := by
  have hev : ∀ (u : Fin 4 → ℝ) (i : Fin 4),
      ((EuclideanSpace.equiv (Fin 4) ℝ).symm u) i = u i := fun _ _ => rfl
  rw [PiLp.inner_apply]
  simp only [coordsToFourSpace, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_three]
  simp_rw [hev]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

private lemma chiralZornEquiv_reconstruct (αP αM : ℝ) (a b : Fin 3 → ℝ) :
    chiralZornEquiv (chiralZornReconstruct αP αM a b) = (αP, αM, a, b) :=
  chiralZornEquiv.apply_symm_apply (αP, αM, a, b)

/-- Unit-scale Krein isometry `SplitOctCD ≃ₗ[ℝ] KreinFrame4` mapping `𝒩_+`/`𝒩_-` to
`plusFrame`/`minusFrame`, `cdKreinForm` to `DoubledSpace.nullPairing`, `ellCD * ·` to
`spectral_epsilon`, `cdGradingInvolution` to `modular_j`, and `cdComplexI` to `complex_i`. -/
def cdToDoubledChiralEquiv : SplitOctCD ≃ₗ[ℝ] KreinFrame4 where
  toFun X :=
    let p := chiralZornEquiv X
    let s := (1 / Real.sqrt 2 : ℝ)
    to_doubled (s • coordsToFourSpace p.1 p.2.2.1) (s • coordsToFourSpace p.2.1 p.2.2.2)
  invFun u :=
    let x := (EuclideanSpace.equiv (Fin 4) ℝ) (WithLp.fst u)
    let ξ := (EuclideanSpace.equiv (Fin 4) ℝ) (WithLp.snd u)
    let r := Real.sqrt 2
    chiralZornReconstruct (r * x 0) (r * ξ 0)
      (fun k => r * x k.succ) (fun k => r * ξ k.succ)
  left_inv X := by
    have hs : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
      have hne : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hne]
    dsimp only
    have hfst : (fun k : Fin 3 => Real.sqrt 2 * ((1 / Real.sqrt 2) *
        coordsToFourSpace (chiralZornEquiv X).1 (chiralZornEquiv X).2.2.1 k.succ)) =
        (chiralZornEquiv X).2.2.1 := by
      funext k
      fin_cases k <;> simp [coordsToFourSpace]
    have hsnd : (fun k : Fin 3 => Real.sqrt 2 * ((1 / Real.sqrt 2) *
        coordsToFourSpace (chiralZornEquiv X).2.1 (chiralZornEquiv X).2.2.2 k.succ)) =
        (chiralZornEquiv X).2.2.2 := by
      funext k
      fin_cases k <;> simp [coordsToFourSpace]
    change chiralZornReconstruct
      (Real.sqrt 2 * ((1 / Real.sqrt 2) * (chiralZornEquiv X).1))
      (Real.sqrt 2 * ((1 / Real.sqrt 2) * (chiralZornEquiv X).2.1))
      (fun k => Real.sqrt 2 * ((1 / Real.sqrt 2) *
        coordsToFourSpace (chiralZornEquiv X).1 (chiralZornEquiv X).2.2.1 k.succ))
      (fun k => Real.sqrt 2 * ((1 / Real.sqrt 2) *
        coordsToFourSpace (chiralZornEquiv X).2.1 (chiralZornEquiv X).2.2.2 k.succ)) = X
    rw [hfst, hsnd, ← mul_assoc, ← mul_assoc, hs, one_mul, one_mul]
    exact chiralZornEquiv.left_inv X
  right_inv u := by
    dsimp only
    rw [chiralZornEquiv_reconstruct]
    dsimp only
    apply DoubledSpace.ext
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i
      fin_cases i <;> simp [coordsToFourSpace]
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i
      fin_cases i <;> simp [coordsToFourSpace]
  map_add' X Y := by
    apply DoubledSpace.ext
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i
      fin_cases i <;>
        simp [map_add, coordsToFourSpace, mul_add]
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i
      fin_cases i <;>
        simp [map_add, coordsToFourSpace, mul_add]
  map_smul' c X := by
    apply DoubledSpace.ext
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i
      fin_cases i <;>
        simp [map_smul, coordsToFourSpace, smul_eq_mul] <;> ring
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i
      fin_cases i <;>
        simp [map_smul, coordsToFourSpace, smul_eq_mul] <;> ring

private def quatToFour (q : Quaternion ℝ) : FourSpace :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![q.re, q.imI, q.imJ, q.imK]

/-- Rational split-diagonal Krein isometry `SplitOctCD ≃ₗ[ℝ] KreinFrame4` sending `⟨q, r⟩` to
`to_doubled (quatToFour q) (quatToFour r)` and matching `KreinSpace.kreinInner` identically. -/
def cdToDoubledSplitEquiv : SplitOctCD ≃ₗ[ℝ] KreinFrame4 where
  toFun X := to_doubled (quatToFour X.fst) (quatToFour X.snd)
  invFun u :=
    let x := (EuclideanSpace.equiv (Fin 4) ℝ) (WithLp.fst u)
    let ξ := (EuclideanSpace.equiv (Fin 4) ℝ) (WithLp.snd u)
    ⟨⟨x 0, x 1, x 2, x 3⟩, ⟨ξ 0, ξ 1, ξ 2, ξ 3⟩⟩
  left_inv X := by
    rcases X with ⟨⟨q0, q1, q2, q3⟩, ⟨r0, r1, r2, r3⟩⟩
    ext <;> simp [quatToFour]
  right_inv u := by
    apply DoubledSpace.ext
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i; fin_cases i <;> simp [quatToFour]
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i; fin_cases i <;> simp [quatToFour]
  map_add' X Y := by
    apply DoubledSpace.ext
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i; fin_cases i <;> simp [quatToFour]
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i; fin_cases i <;> simp [quatToFour]
  map_smul' c X := by
    apply DoubledSpace.ext
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i; fin_cases i <;> simp [quatToFour]
    · apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      ext i; fin_cases i <;> simp [quatToFour]

private lemma cdToDoubledChiralEquiv_coords (X : SplitOctCD) :
    cdToDoubledChiralEquiv X =
      to_doubled
        ((1 / Real.sqrt 2 : ℝ) •
          coordsToFourSpace (chiralZornEquiv X).1 (chiralZornEquiv X).2.2.1)
        ((1 / Real.sqrt 2 : ℝ) •
          coordsToFourSpace (chiralZornEquiv X).2.1 (chiralZornEquiv X).2.2.2) := rfl

private lemma cdToDoubledSplitEquiv_grading (X : SplitOctCD) :
    cdToDoubledSplitEquiv (cdGradingInvolution X) =
      spectral_epsilon (cdToDoubledSplitEquiv X) := by
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
    simp [cdToDoubledSplitEquiv, quatToFour, cdGradingInvolution, spectral_epsilon]

private lemma cdToDoubledSplitEquiv_ell (X : SplitOctCD) :
    cdToDoubledSplitEquiv (X * ellCD) =
      modular_j (cdToDoubledSplitEquiv X) := by
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
    simp [cdToDoubledSplitEquiv, quatToFour, ellCD, modular_j]

private lemma cdToDoubledSplitEquiv_complexI (X : SplitOctCD) :
    cdToDoubledSplitEquiv ⟨-X.snd, X.fst⟩ =
      complex_i (cdToDoubledSplitEquiv X) := by
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
    simp [cdToDoubledSplitEquiv, quatToFour, complex_i, modular_j, spectral_epsilon]

/-- **Bridge to `InfoGeometry.Krein.DoubledSpace` (`KreinFrame4`)**:
connects `SplitOctCD` and `cdKreinForm` isometrically to `DoubledSpace.nullPairing`
(definitionally equal to `RealDoubledChiralKrein.chiralKreinForm`), `KreinSpace.kreinInner`,
`plusFrame`/`minusFrame`, `spectral_epsilon`, `modular_j`, and `complex_i`. -/
theorem bridge_to_DoubledSpace :
    (∀ X Y : SplitOctCD,
      nullPairing (cdToDoubledChiralEquiv X) (cdToDoubledChiralEquiv Y) = cdKreinForm X Y ∧
      nullPairing (cdToDoubledChiralEquiv X) (cdToDoubledChiralEquiv X) = cdNorm X) ∧
    (cdToDoubledChiralEquiv uPlusCD = (1 / Real.sqrt 2 : ℝ) • plusFrame 0 ∧
      cdToDoubledChiralEquiv uMinusCD = (1 / Real.sqrt 2 : ℝ) • minusFrame 0 ∧
      (∀ k : Fin 3,
        cdToDoubledChiralEquiv (ePlusCD k) = (1 / Real.sqrt 2 : ℝ) • plusFrame k.succ ∧
        cdToDoubledChiralEquiv (eMinusCD k) = (1 / Real.sqrt 2 : ℝ) • minusFrame k.succ) ∧
      (∀ X : SplitOctCD,
        (X ∈ nullSpacePlus ↔ WithLp.snd (cdToDoubledChiralEquiv X) = 0) ∧
        (X ∈ nullSpaceMinus ↔ WithLp.fst (cdToDoubledChiralEquiv X) = 0))) ∧
    (∀ X : SplitOctCD,
      cdToDoubledChiralEquiv (ellCD * X) = spectral_epsilon (cdToDoubledChiralEquiv X) ∧
      cdToDoubledChiralEquiv (cdGradingInvolution X) = modular_j (cdToDoubledChiralEquiv X) ∧
      cdToDoubledChiralEquiv (cdComplexI X) = complex_i (cdToDoubledChiralEquiv X)) ∧
    (∀ X Y : SplitOctCD,
      KreinSpace.kreinInner (H := KreinFrame4)
          (cdToDoubledSplitEquiv X) (cdToDoubledSplitEquiv Y) = cdKreinForm X Y ∧
      cdToDoubledSplitEquiv (cdGradingInvolution X) =
        spectral_epsilon (cdToDoubledSplitEquiv X) ∧
      cdToDoubledSplitEquiv (X * ellCD) = modular_j (cdToDoubledSplitEquiv X) ∧
      cdToDoubledSplitEquiv ⟨-X.snd, X.fst⟩ = complex_i (cdToDoubledSplitEquiv X)) := by
  have hsq2 : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    field_simp [show Real.sqrt 2 ≠ 0 by positivity]
    rw [Real.sq_sqrt (by norm_num)]
  have hnorm_formula : ∀ X : SplitOctCD,
      cdNorm X = (chiralZornEquiv X).1 * (chiralZornEquiv X).2.1 +
        ∑ k : Fin 3, (chiralZornEquiv X).2.2.1 k * (chiralZornEquiv X).2.2.2 k := by
    intro X
    have h := cdNorm_chiralZorn_cross_pairing (chiralZornEquiv X).1 (chiralZornEquiv X).2.1
      (chiralZornEquiv X).2.2.1 (chiralZornEquiv X).2.2.2
    have hre : chiralZornReconstruct (chiralZornEquiv X).1 (chiralZornEquiv X).2.1
        (chiralZornEquiv X).2.2.1 (chiralZornEquiv X).2.2.2 = X := chiralZornEquiv.left_inv X
    rw [hre] at h
    exact h
  have hnull : ∀ X Y : SplitOctCD,
      nullPairing (cdToDoubledChiralEquiv X) (cdToDoubledChiralEquiv Y) = cdKreinForm X Y := by
    intro X Y
    rw [cdToDoubledChiralEquiv_coords, cdToDoubledChiralEquiv_coords]
    simp only [nullPairing, fst_to_doubled, snd_to_doubled, real_inner_smul_left,
      real_inner_smul_right, inner_coordsToFourSpace]
    have hfactor : ∀ u v : ℝ,
        (1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * u) +
          (1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * v) = (u + v) / 2 := by
      intro u v
      calc (1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * u) +
            (1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * v)
          = ((1 / Real.sqrt 2) * (1 / Real.sqrt 2)) * (u + v) := by ring
        _ = (u + v) / 2 := by rw [hsq2]; ring
    rw [hfactor]
    unfold cdKreinForm
    rw [hnorm_formula (X + Y), hnorm_formula X, hnorm_formula Y]
    simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp only [Fin.sum_univ_three]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y
    refine ⟨hnull X Y, ?_⟩
    rw [hnull X X]
    unfold cdKreinForm
    have h2 : cdNorm (X + X) = 4 * cdNorm X := by
      have h := cdNorm_smul (2 : ℝ) X
      rw [two_smul] at h
      norm_num at h
      exact h
    rw [h2]; ring
  · refine ⟨?_, ?_, ?_, ?_⟩
    · (apply DoubledSpace.ext <;>
        apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
        simp [cdToDoubledChiralEquiv, plusFrame, frameBasis, coordsToFourSpace,
          uPlusCD_components]); norm_num
    · (apply DoubledSpace.ext <;>
        apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
        simp [cdToDoubledChiralEquiv, minusFrame, frameBasis, coordsToFourSpace,
          uMinusCD_components]); norm_num
    · intro k
      constructor
      · apply DoubledSpace.ext <;>
          apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;>
          fin_cases k <;> fin_cases i <;>
          simp [cdToDoubledChiralEquiv, plusFrame, frameBasis, coordsToFourSpace,
            ePlusCD_components, qBasis] <;> norm_num
      · apply DoubledSpace.ext <;>
          apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;>
          fin_cases k <;> fin_cases i <;>
          simp [cdToDoubledChiralEquiv, minusFrame, frameBasis, coordsToFourSpace,
            eMinusCD_components, qBasis] <;> norm_num
    · intro X
      have hne : (1 / Real.sqrt 2 : ℝ) ≠ 0 := by positivity
      refine ⟨?_, ?_⟩
      · rw [mem_nullSpacePlus_iff]
        constructor
        · intro hx
          apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
          ext i; fin_cases i <;>
            simp [cdToDoubledChiralEquiv, coordsToFourSpace, hx]
        · intro hx
          have h0 := congrArg (fun v : FourSpace => v 0) hx
          have h1 := congrArg (fun v : FourSpace => v 1) hx
          have h2 := congrArg (fun v : FourSpace => v 2) hx
          have h3 := congrArg (fun v : FourSpace => v 3) hx
          simp [cdToDoubledChiralEquiv, coordsToFourSpace, mul_eq_zero] at h0 h1 h2 h3
          rcases X with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
          ext <;> dsimp at h0 h1 h2 h3 ⊢ <;> linarith
      · rw [mem_nullSpaceMinus_iff]
        constructor
        · intro hx
          apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
          ext i; fin_cases i <;>
            simp [cdToDoubledChiralEquiv, coordsToFourSpace, hx]
        · intro hx
          have h0 := congrArg (fun v : FourSpace => v 0) hx
          have h1 := congrArg (fun v : FourSpace => v 1) hx
          have h2 := congrArg (fun v : FourSpace => v 2) hx
          have h3 := congrArg (fun v : FourSpace => v 3) hx
          simp [cdToDoubledChiralEquiv, coordsToFourSpace, mul_eq_zero] at h0 h1 h2 h3
          rcases X with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
          ext <;> dsimp at h0 h1 h2 h3 ⊢ <;> linarith
  · intro X
    refine ⟨?_, ?_, ?_⟩
    · apply DoubledSpace.ext <;>
        apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
        simp [cdToDoubledChiralEquiv, coordsToFourSpace, ellCD, spectral_epsilon] <;> ring
    · apply DoubledSpace.ext <;>
        apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
        simp [cdToDoubledChiralEquiv, coordsToFourSpace, cdGradingInvolution, modular_j] <;> ring
    · apply DoubledSpace.ext <;>
        apply (EuclideanSpace.equiv (Fin 4) ℝ).injective <;> ext i <;> fin_cases i <;>
        simp [cdToDoubledChiralEquiv, coordsToFourSpace, cdComplexI, cdGradingInvolution,
          ellCD, complex_i, modular_j, spectral_epsilon] <;> ring
  · intro X Y
    refine ⟨?_, cdToDoubledSplitEquiv_grading X, cdToDoubledSplitEquiv_ell X,
        cdToDoubledSplitEquiv_complexI X⟩
    change KreinSpace.kreinInner (H := KreinFrame4)
      (to_doubled (quatToFour X.fst) (quatToFour X.snd))
      (to_doubled (quatToFour Y.fst) (quatToFour Y.snd)) = cdKreinForm X Y
    rw [kreinInner_to_doubled]
    have hev : ∀ (v : Fin 4 → ℝ) (i : Fin 4),
        ((EuclideanSpace.equiv (Fin 4) ℝ).symm v) i = v i := fun _ _ => rfl
    simp only [quatToFour, PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply,
      conj_trivial]
    simp_rw [hev]
    rcases X with ⟨⟨x0, x1, x2, x3⟩, ⟨u0, u1, u2, u3⟩⟩
    rcases Y with ⟨⟨y0, y1, y2, y3⟩, ⟨v0, v1, v2, v3⟩⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      cdKreinForm, cdNorm, Quaternion.normSq_def']
    dsimp
    ring

end InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge
