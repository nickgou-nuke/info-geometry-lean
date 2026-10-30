/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.PrimitiveCoprimeSimplicity
public import InfoGeometry.Exceptional.CFSGPort.SuzukiBruhatFactorization

/-!
# Simplicity of the finite Suzuki operator group

This assembles the proved ovoid action, local point-stabilizer recognition,
solvability of the root–torus subgroup, and perfectness criterion into a
conditional simplicity theorem for the actual generated Suzuki matrix group.
-/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Suzuki

open InfoGeometry.Exceptional.CFSGPort.Chevalley
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K]

/-- Under the finite Suzuki field and Tits endomorphism hypotheses, the
upper-orientation Suzuki operator group is simple. The proof uses its actual
faithful two-transitive action on the projective ovoid, identifies the point
stabilizer with the root–torus subgroup, and applies the primitive-action
criterion to the proved perfectness and solvability results. -/
theorem suzukiUpperMatrixGroup_isSimple
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1))) :
    IsSimpleGroup (Chevalley.suzukiUpperMatrixGroup a K) := by
  let G := Chevalley.suzukiUpperMatrixGroup a K
  let ρ : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp G.subtype
  letI : MulAction G (ℙ K (Fin 4 → K)) := MulAction.compHom _ ρ
  let Ω : SubMulAction G (ℙ K (Fin 4 → K)) :=
    { carrier := ovoid pi
      smul_mem' := by
        intro g z hz
        exact suzukiUpperMatrixGroup_smul_mem_ovoid
          a pi hpi_sq hpi_formula
          (ovoidNorm_eq_zero_only_at_origin a hK pi hpi_formula) g z hz }
  letI : MulAction G Ω := {
    smul g z := ⟨ρ g • z.1, Ω.smul_mem' g z.2⟩
    one_smul z := by
      apply Subtype.ext
      simp
    mul_smul g h z := by
      apply Subtype.ext
      change ρ (g * h) • (z : ℙ K (Fin 4 → K)) =
        ρ g • (ρ h • (z : ℙ K (Fin 4 → K)))
      rw [map_mul]
      exact mul_smul _ _ _
  }
  letI : FaithfulSMul G Ω :=
    suzukiUpperMatrixGroup_faithful_ovoid
      (K := K) a pi hpi_sq hpi_formula
      (ovoidNorm_eq_zero_only_at_origin a hK pi hpi_formula)
  letI : MulAction.IsMultiplyPretransitive G Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro x y z w hxy hzw
    obtain ⟨g, hg₁, hg₂⟩ :=
      suzukiUpperMatrixGroup_two_transitive_on_ovoid_of_field
        (K := K) a hK pi hpi_sq hpi_formula
        x.1 y.1 z.1 w.1 x.2 y.2 z.2 w.2
        (Subtype.val_injective.ne hxy) (Subtype.val_injective.ne hzw)
    refine ⟨g, ?_, ?_⟩
    · exact Subtype.ext hg₁
    · exact Subtype.ext hg₂
  letI : MulAction.IsPreprimitive G Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive
      (G := G) (α := Ω) inferInstance

  let ω : Ω := ⟨ovoidInfinity (K := K), Or.inl rfl⟩
  let B := suzukiPointStabilizerOperatorGroup (K := K) a
  have hBG : B ≤ G := by
    exact suzukiPointStabilizerOperatorGroup_le_suzukiUpperMatrixGroup
      (K := K) a
  let B' := B.subgroupOf G
  have hstabilizer : MulAction.stabilizer G ω = B' := by
    ext g
    change g ∈ MulAction.stabilizer G ω ↔ (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈ B
    rw [MulAction.mem_stabilizer_iff]
    rw [Subtype.ext_iff]
    change ((ρ g).toLinearEquiv • ovoidInfinity (K := K) =
      ovoidInfinity (K := K)) ↔ _
    exact (suzukiUpperMatrixGroup_mem_pointStabilizer_iff
      (K := K) a hK pi hpi_sq hpi_formula g).symm
  have hBsolv : Group.IsSolvable B :=
    suzukiPointStabilizerOperatorGroup_isSolvable
      (K := K) a hK pi hpi_sq hpi_formula
  have hB'solv : Group.IsSolvable B' := by
    let e : B' ≃* B := Subgroup.subgroupOfEquivOfLe hBG
    exact Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
  have hstabilizersolvable :
      Group.IsSolvable (MulAction.stabilizer G ω) := by
    rw [hstabilizer]
    exact hB'solv

  obtain ⟨g, h, hne⟩ := suzukiUpperMatrixGroup_noncommuting_pair (K := K) a
  letI : Nontrivial G := ⟨⟨g, h, fun hgh => hne (by rw [hgh])⟩⟩
  letI : Group.IsPerfect G :=
    suzukiUpperMatrixGroup_isPerfect (K := K) a ha hK pi hpi_sq hpi_formula
  exact _root_.InfoGeometry.Exceptional.CFSGPort.GroupActions.isSimpleGroup_of_isPreprimitive_of_isSolvable_stabilizer
      (G := G) (Ω := Ω) inferInstance ω hstabilizersolvable

/-- The same simplicity result on the locally defined Suzuki subgroup of
linear endomorphism units. It transports through the proved inverse-transpose
and matrix-to-linear-operator group equivalences. -/
theorem suzukiGroup_isSimple
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1))) :
    IsSimpleGroup (Chevalley.suzukiGroup a K) := by
  let G := Chevalley.suzukiUpperMatrixGroup a K
  have hG : IsSimpleGroup G :=
    suzukiUpperMatrixGroup_isSimple (K := K) a ha hK pi hpi_sq hpi_formula
  let invT : Matrix.GeneralLinearGroup (Fin 4) K ≃*
      Matrix.GeneralLinearGroup (Fin 4) K :=
    Matrix.GeneralLinearGroup.inverseTranspose
  let e₁ := Subgroup.equivMapOfInjective G invT.toMonoidHom invT.injective
  have hmatrix : IsSimpleGroup (G.map invT.toMonoidHom) :=
    e₁.isSimpleGroup_congr.mp hG
  rw [Chevalley.suzukiUpperMatrixGroup_inverseTranspose] at hmatrix
  let e₂ : Matrix.GeneralLinearGroup (Fin 4) K ≃*
      LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
  let e₃ := Subgroup.equivMapOfInjective
    (Chevalley.suzukiMatrixGroup a K) e₂.toMonoidHom e₂.injective
  have hoperator : IsSimpleGroup
      ((Chevalley.suzukiMatrixGroup a K).map e₂.toMonoidHom) :=
    e₃.isSimpleGroup_congr.mp hmatrix
  change IsSimpleGroup (Chevalley.suzukiGroup a K)
  exact hoperator

/-- The finite-field Tits endomorphism used by the Suzuki family: the
`(a+1)`-fold absolute Frobenius in characteristic two. -/
noncomputable def suzukiTitsEndomorphism [Finite K] [CharP K 2]
    (a : ℕ) : K ≃+* K :=
  iterateFrobeniusEquiv K 2 (a + 1)

/-- Evaluation formula for the canonical Suzuki Tits endomorphism. -/
theorem suzukiTitsEndomorphism_apply [Finite K] [CharP K 2]
    (a : ℕ) (x : K) : suzukiTitsEndomorphism (K := K) a x = x ^ (2 ^ (a + 1)) := by
  rw [suzukiTitsEndomorphism, iterateFrobeniusEquiv_def]

/-- Squaring the canonical Suzuki Tits endomorphism gives the field
Frobenius when the field has the Suzuki cardinality. -/
theorem suzukiTitsEndomorphism_sq [Finite K] [CharP K 2]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : K) :
    suzukiTitsEndomorphism (K := K) a
        (suzukiTitsEndomorphism (K := K) a x) = x ^ 2 := by
  haveI := Fintype.ofFinite K
  rw [suzukiTitsEndomorphism_apply, suzukiTitsEndomorphism_apply]
  have hexp : 2 ^ (a + 1) * 2 ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
    calc
      2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ ((a + 1) + (a + 1)) := by rw [← pow_add]
      _ = 2 ^ (2 * a + 2) := by congr 1 <;> omega
      _ = 2 * 2 ^ (2 * a + 1) := by
        rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega, pow_succ]
        simp [Nat.mul_comm]
  calc
    (x ^ (2 ^ (a + 1))) ^ (2 ^ (a + 1)) =
        x ^ (2 ^ (a + 1) * 2 ^ (a + 1)) := by rw [← pow_mul]
    _ = x ^ (2 * 2 ^ (2 * a + 1)) := by rw [hexp]
    _ = x ^ (2 ^ (2 * a + 1) * 2) := by
      exact congrArg (fun n : ℕ => x ^ n) (Nat.mul_comm _ _)
    _ = (x ^ (2 ^ (2 * a + 1))) ^ 2 := by rw [pow_mul]
    _ = (x ^ Nat.card K) ^ 2 := by rw [← hK]
    _ = (x ^ Fintype.card K) ^ 2 := by rw [← Nat.card_eq_fintype_card]
    _ = x ^ 2 := by rw [FiniteField.pow_card]

/-- The canonical finite-field Suzuki upper-matrix group is simple: the
required Tits endomorphism is the `(a+1)`-fold Frobenius, whose square is the
field Frobenius by the cardinality hypothesis. -/
theorem suzukiUpperMatrixGroup_isSimple_of_field
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (Chevalley.suzukiUpperMatrixGroup a K) := by
  let pi := suzukiTitsEndomorphism (K := K) a
  apply suzukiUpperMatrixGroup_isSimple (K := K) a ha hK pi
  · exact suzukiTitsEndomorphism_sq (K := K) a hK
  · exact suzukiTitsEndomorphism_apply (K := K) a

/-- The canonical finite-field Suzuki operator group is simple under the same
field hypotheses. -/
theorem suzukiGroup_isSimple_of_field
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (Chevalley.suzukiGroup a K) := by
  let pi := suzukiTitsEndomorphism (K := K) a
  apply suzukiGroup_isSimple (K := K) a ha hK pi
  · exact suzukiTitsEndomorphism_sq (K := K) a hK
  · exact suzukiTitsEndomorphism_apply (K := K) a

/-- Simplicity on the external CFSG matrix-coordinate carrier, transported
from the faithful local endomorphism-unit realization. This is the same
four-dimensional root/torus/Weyl matrix subgroup used by the external
`SuzukiModel`; the proof stays in the pinned root project and does not import
the external dependency graph. -/
theorem suzukiMatrixGroup_isSimple_of_field
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (Chevalley.suzukiMatrixGroup a K) := by
  let e : Chevalley.suzukiMatrixGroup a K ≃* Chevalley.suzukiGroup a K :=
    Subgroup.equivMapOfInjective (Chevalley.suzukiMatrixGroup a K)
      (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))).toMonoidHom
      (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))).injective
  exact e.isSimpleGroup_congr.mpr
    (suzukiGroup_isSimple_of_field (K := K) a ha hK)

/-- Root-pinned port of the external `fam_2b2_simplicity` model conclusion.
Its hypothesis has the external `SuzukiModel` shape, with the local matrix
subgroup generated by the same root, torus, and Weyl matrices. -/
theorem isSimpleGroup_of_SuzukiMatrixModel
    {G : Type} [Group G] {p f : ℕ}
    (hmodel : p = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K),
        f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧
          Nonempty (G ≃* ↥(Chevalley.suzukiMatrixGroup a K))) :
    IsSimpleGroup G := by
  rcases hmodel with ⟨rfl, a, ha, K, hField, hFinite, hf, hcard, ⟨e⟩⟩
  letI : Field K := hField
  letI : Finite K := hFinite
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by
    calc
      Nat.card K = 2 ^ f := hcard
      _ = 2 ^ (2 * a + 1) := by rw [hf]
  haveI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP K 2 := charP_of_card_eq_prime_pow hcard'
  exact e.isSimpleGroup_congr.mpr
    (suzukiMatrixGroup_isSimple_of_field (K := K) a (by omega) hK)

end InfoGeometry.Exceptional.CFSGPort.Suzuki
