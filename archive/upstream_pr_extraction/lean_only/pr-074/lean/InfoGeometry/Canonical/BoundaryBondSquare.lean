import InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Canonical.CantorKMSState
import InfoGeometry.Canonical.FiniteCantorCuntzBranches
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness

noncomputable section

namespace InfoGeometry.Canonical.BoundaryBondSquare

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.FiniteCantorCuntzBranches
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness

private theorem extendBitWord_eq_extendSucc (n : ℕ) (w : BitWord n) (b : Bool) :
    extendBitWord n w b = extendSucc n w b := by
  funext i
  by_cases hi : i.1 < n
  · simp [extendBitWord, bitWordEquiv, extendSucc, hi]
  · have hi' : i.1 = n := by omega
    simp [extendBitWord, bitWordEquiv, extendSucc, hi']

private theorem extendSucc_eq_iff (n : ℕ) (u : BitWord n) (b : Bool)
    (x : BitWord (n + 1)) :
    extendSucc n u b = x ↔
      u = prefixSucc n x ∧ x ⟨n, Nat.lt_succ_self n⟩ = b := by
  constructor
  · intro h
    subst x
    exact ⟨(prefixSucc_extendSucc n u b).symm, by
      simp [extendSucc]
      ⟩
  · rintro ⟨hu, hb⟩
    subst u
    funext i
    by_cases hi : i.1 < n
    · simp [extendSucc, prefixSucc, hi]
    · have hi' : i.1 = n := by omega
      have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
      rw [hi_eq]
      simp [extendSucc, hb]

private theorem bondFun_single (n : ℕ) (u v : BitWord n) (c : ℂ) :
    bondFun n (Matrix.single u v c) =
      c • (Matrix.single (extendSucc n u false) (extendSucc n v false) 1 +
        Matrix.single (extendSucc n u true) (extendSucc n v true) 1) := by
  ext x y
  cases hx : x ⟨n, Nat.lt_succ_self n⟩ <;>
    cases hy : y ⟨n, Nat.lt_succ_self n⟩ <;>
      simp [bondFun, Matrix.single, extendSucc, prefixSucc,
        extendSucc_eq_iff, hx, hy]

theorem bondFun_eq_dyadicMatrixEmbedding
    (n : ℕ) (A : Matrix (BitWord n) (BitWord n) ℂ) :
    bondFun n A = dyadicMatrixEmbedding n A := by
  change bond n A = dyadicMatrixEmbedding n A
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  unfold dyadicMatrixEmbedding
  have hb (u v : BitWord n) (c : ℂ) :
      bond n (Matrix.single u v c) =
        c • (Matrix.single (extendSucc n u false) (extendSucc n v false) 1 +
          Matrix.single (extendSucc n u true) (extendSucc n v true) 1) := by
    exact bondFun_single n u v c
  simp_rw [hb]
  have hA (u v : BitWord n) :
      (∑ i, ∑ j, Matrix.single i j (A i j)) u v = A u v := by
    exact congrArg (fun M => M u v) (Matrix.matrix_eq_sum_single A).symm
  simp_rw [hA, extendBitWord_eq_extendSucc]

theorem boundaryRep_canonical_bond_compatible
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    boundaryRep n A =
      boundaryRep (n + 1) (ComplexMatrixStage.bondFun n A) := by
  rw [bondFun_eq_dyadicMatrixEmbedding]
  exact boundaryRep_bond_compatible n A

def boundaryRepColimitCone :
    ∀ n : ℕ,
      ComplexMatrixStage.Stage n →+*
        CuntzBoundaryMatrixStageBridge.BoundaryOperator :=
  fun n => (boundaryRep n).toRingHom

theorem boundaryRepColimitCone_compatible :
    CompatibleCone ComplexMatrixStage.bond boundaryRepColimitCone := by
  intro n A
  exact (boundaryRep_canonical_bond_compatible n A).symm

noncomputable def boundaryRepColimit :
    ComplexMatrixStage.Colimit →+*
      CuntzBoundaryMatrixStageBridge.BoundaryOperator :=
  directLimitLift ComplexMatrixStage.bond boundaryRepColimitCone
    boundaryRepColimitCone_compatible

@[simp] theorem boundaryRepColimit_stage
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    boundaryRepColimit (ComplexMatrixStage.toColimit n A) =
      boundaryRep n A := by
  rfl

noncomputable def boundaryRepStarColimit :
    ComplexMatrixStage.Colimit →⋆ₐ[ℂ]
      CuntzBoundaryMatrixStageBridge.BoundaryOperator where
  toFun := boundaryRepColimit
  map_one' := boundaryRepColimit.map_one
  map_mul' := boundaryRepColimit.map_mul
  map_zero' := boundaryRepColimit.map_zero
  map_add' := boundaryRepColimit.map_add
  commutes' := by
    intro c
    change boundaryRepColimit (c • (1 : ComplexMatrixStage.Colimit)) =
      c • (1 : CuntzBoundaryMatrixStageBridge.BoundaryOperator)
    rw [DirectLimit.one_def 0, colimit_smul_mk]
    change boundaryRep 0 (c • (1 : ComplexMatrixStage.Stage 0)) =
      c • (1 : CuntzBoundaryMatrixStageBridge.BoundaryOperator)
    rw [map_smul, map_one]
  map_star' := by
    intro x
    induction x using DirectLimit.induction with
    | _ n A =>
        change boundaryRep n (star A) = star (boundaryRep n A)
        exact map_star (boundaryRep n) A

@[simp] theorem boundaryRepStarColimit_stage
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    boundaryRepStarColimit (ComplexMatrixStage.toColimit n A) =
      boundaryRep n A := rfl

def normalizedTraceLinear (n : ℕ) :
    ComplexMatrixStage.Stage n →ₗ[ℂ] ℂ where
  toFun := normalizedTrace n
  map_add' := by
    intro A B
    simp [normalizedTrace, Matrix.trace_add]
    ring
  map_smul' := by
    intro c A
    simp [normalizedTrace, Matrix.trace_smul]
    ring

theorem matrixTrace_star_mul_self_re_eq_sum_normSq
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    (Matrix.trace (star A * A)).re =
      ∑ i : BitWord n, ∑ k : BitWord n, Complex.normSq (A k i) := by
  dsimp [Matrix.trace, Matrix.mul_apply, star, Matrix.conjTranspose_apply]
  have h_elem (k i : BitWord n) :
      (starRingEnd ℂ (A k i) * A k i).re = Complex.normSq (A k i) := by
    rw [mul_comm, Complex.mul_conj]
    rfl
  have h_sum (i : BitWord n) :
      (∑ k : BitWord n, starRingEnd ℂ (A k i) * A k i).re =
        ∑ k : BitWord n, Complex.normSq (A k i) := by
    have h_map := map_sum Complex.reAddGroupHom
      (fun k : BitWord n => starRingEnd ℂ (A k i) * A k i) Finset.univ
    change Complex.reAddGroupHom
        (∑ k : BitWord n, starRingEnd ℂ (A k i) * A k i) =
      ∑ k : BitWord n, Complex.normSq (A k i)
    rw [h_map]
    congr 1
    ext k
    exact h_elem k i
  have h_map := map_sum Complex.reAddGroupHom
    (fun i : BitWord n => ∑ k : BitWord n,
      starRingEnd ℂ (A k i) * A k i) Finset.univ
  change Complex.reAddGroupHom
      (∑ i : BitWord n, ∑ k : BitWord n,
        starRingEnd ℂ (A k i) * A k i) =
    ∑ i : BitWord n, ∑ k : BitWord n, Complex.normSq (A k i)
  rw [h_map]
  congr 1
  ext i
  exact h_sum i

theorem normalizedTrace_stage_star_mul_self_re_nonneg
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    0 ≤ (normalizedTrace n (star A * A)).re := by
  rw [normalizedTrace_apply, Complex.mul_re]
  have hcast : (1 / (2 ^ n : ℂ)) =
      (((1 / (2 ^ n : ℝ) : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [matrixTrace_star_mul_self_re_eq_sum_normSq]
  have hcoeff : 0 ≤ (1 / (2 ^ n : ℝ)) := by positivity
  have hsum : 0 ≤ ∑ i : BitWord n,
      ∑ k : BitWord n, Complex.normSq (A k i) :=
    Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  exact mul_nonneg hcoeff hsum

theorem normalizedTrace_reindex
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    normalizedTrace n A =
      matrixTraceState n (bitWordStageStarAlgEquiv n A) := by
  simpa [normalizedTrace, matrixTraceState,
    bitWordMatrixTraceFunctional_apply, matrixTraceFunctional_apply] using
    (bitWordStageTrace_transport n A)

theorem normalizedTrace_stage_star_mul_self_eq_zero_iff
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    normalizedTrace n (star A * A) = 0 ↔ A = 0 := by
  let E := bitWordStageStarAlgEquiv n
  constructor
  · intro h
    have htransport := normalizedTrace_reindex n (star A * A)
    rw [map_mul, map_star] at htransport
    have hfin : matrixTraceState n (star (E A) * E A) = 0 := by
      rw [← htransport, h]
    have hE : E A = 0 :=
      (matrixTraceState_star_mul_self_eq_zero_iff n (E A)).mp hfin
    exact E.injective hE
  · intro h
    subst A
    simp

noncomputable def normalizedTraceColimit :
    ComplexMatrixStage.Colimit →ₗ[ℂ] ℂ where
  toFun := DirectLimit.lift
    (fun _ _ h => bondMap ComplexMatrixStage.bond _ _ h)
    (fun n A => normalizedTrace n A)
    (by
      intro m n h A
      change normalizedTrace m A =
        normalizedTrace n (bondMap ComplexMatrixStage.bond m n h A)
      induction h with
      | refl => simp [bondMap_refl]
      | @step n h ih =>
          rw [bondMap_succ ComplexMatrixStage.bond m n h]
          change normalizedTrace m A =
            normalizedTrace (n + 1)
              (ComplexMatrixStage.bond n
                (bondMap ComplexMatrixStage.bond m n h A))
          rw [show ComplexMatrixStage.bond n =
              ComplexMatrixStage.bondFun n by rfl]
          rw [normalizedTrace_bond]
          exact ih)
  map_add' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
        simp only [DirectLimit.add_def, DirectLimit.lift_def]
        exact (normalizedTraceLinear n).map_add A B
  map_smul' := by
    intro c x
    induction x using DirectLimit.induction with
    | _ n A =>
        simp only [DirectLimit.smul_def, DirectLimit.lift_def]
        exact (normalizedTraceLinear n).map_smul c A

@[simp] theorem normalizedTraceColimit_stage
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    normalizedTraceColimit (ComplexMatrixStage.toColimit n A) =
    normalizedTrace n A := rfl

theorem normalizedTraceColimit_positive
    (x : ComplexMatrixStage.Colimit) :
    0 ≤ (normalizedTraceColimit (star x * x)).re := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [colimit_star_mk, DirectLimit.mul_def]
      change 0 ≤ (normalizedTrace n (star A * A)).re
      exact normalizedTrace_stage_star_mul_self_re_nonneg n A

theorem normalizedTraceColimit_cyclic
    (x y : ComplexMatrixStage.Colimit) :
    normalizedTraceColimit (x * y) =
      normalizedTraceColimit (y * x) := by
  induction x, y using DirectLimit.induction₂ with
  | _ n A B =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def]
      change normalizedTrace n (A * B) = normalizedTrace n (B * A)
      unfold normalizedTrace
      rw [Matrix.trace_mul_comm]

theorem normalizedTraceColimit_star
    (x : ComplexMatrixStage.Colimit) :
    normalizedTraceColimit (star x) =
      starRingEnd ℂ (normalizedTraceColimit x) := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [colimit_star_mk]
      change normalizedTrace n (star A) =
        starRingEnd ℂ (normalizedTrace n A)
      unfold normalizedTrace
      have htrace : Matrix.trace (star A) =
          starRingEnd ℂ (Matrix.trace A) := by
        dsimp [Matrix.trace]
        simp
      have hcoef : starRingEnd ℂ (1 / (2 ^ n : ℂ)) =
          1 / (2 ^ n : ℂ) := by
        have h2 : starRingEnd ℂ (2 : ℂ) = 2 := by
          exact Complex.conj_natCast 2
        rw [map_div₀, map_one, map_pow, h2]
      rw [htrace, map_mul, hcoef]

theorem normalizedTraceColimit_one :
    normalizedTraceColimit (1 : ComplexMatrixStage.Colimit) = 1 := by
  rw [DirectLimit.one_def 0]
  change normalizedTrace 0 (1 : ComplexMatrixStage.Stage 0) = 1
  unfold normalizedTrace
  simp [Matrix.trace]

theorem normalizedTraceColimit_commutator_zero
    (x y : ComplexMatrixStage.Colimit) :
    normalizedTraceColimit (x * y - y * x) = 0 := by
  rw [map_sub, normalizedTraceColimit_cyclic]
  exact sub_self _

theorem normalizedTraceColimit_faithful
    {x : ComplexMatrixStage.Colimit}
    (h : normalizedTraceColimit (star x * x) = 0) :
    x = 0 := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [colimit_star_mk, DirectLimit.mul_def] at h
      change normalizedTrace n (star A * A) = 0 at h
      have hA : A = 0 :=
        (normalizedTrace_stage_star_mul_self_eq_zero_iff n A).mp h
      subst A
      rw [DirectLimit.zero_def n]

end InfoGeometry.Canonical.BoundaryBondSquare
