/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic
import InfoGeometry.Cosmology.ParabolicCosetSingularityResolution
import InfoGeometry.Cosmology.GNSQuotientCosetEquivalence
import InfoGeometry.Clifford.SolderingIsomorphism

/-!
# Finite Matrix Models for a Vacuum Annihilator and a Parabolic Ray Stabilizer

This module proves finite-dimensional identities in `Matrix (Fin 2) (Fin 2) ℝ`:
the explicitly defined bilinear radical is equivalent to annihilating a fixed
vacuum vector, the stabilizer of that vector's projective ray in `SL(2, ℝ)` is
the upper-triangular subgroup, and normalized rank-one projectors satisfy
elementary Frobenius and commutator bounds.

The finite quotient is identified with the vacuum spinor space by Mathlib's
first isomorphism theorem. Its projectivization is then identified with the
native `SL₂(ℝ)` quotient by the vacuum-ray stabilizer. This does not construct
the general positive-state C*-GNS space, modular flow, or a singularity-
resolution theorem.
-/

namespace InfoGeometry.Cosmology.SpacetimeParabolicQuotient

open Matrix
open scoped Matrix LinearAlgebra.Projectivization

/-! ### 1. Conformal Group G = SL(2, ℝ) & Explicit Inverses -/

/-- Predicate for membership in the conformal symmetry group SL(2, ℝ). -/
def IsSL2 (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  g.det = 1

/-- Explicit, computable two-sided inverse for SL(2, ℝ).
    For g = [[a, b], [c, d]], the inverse is [[d, -b], [-c, a]] since det = 1. -/
def sl2Inv (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g 1 1, -g 0 1;
     -g 1 0, g 0 0]

/-- The explicit inverse is a true left inverse for SL(2, ℝ) elements. -/
theorem sl2Inv_mul_eq_one (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g) :
    sl2Inv g * g = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Inv, IsSL2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two] at hg ⊢ <;>
    nlinarith

/-- The explicit inverse is a true right inverse for SL(2, ℝ) elements. -/
theorem mul_sl2Inv_eq_one (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g) :
    g * sl2Inv g = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Inv, IsSL2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two] at hg ⊢ <;>
    nlinarith


/-! ### 2. The Vacuum State & GNS Null Radical 𝒩_ω -/

/-- The cyclic vacuum state vector |Ω⟩. -/
def cyclicVacuum : Fin 2 → ℝ := ![1, 0]

/-- Matrix-vector multiplication by the vacuum spinor extracts the first column. -/
theorem mulVec_cyclicVacuum (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mulVec M cyclicVacuum = ![M 0 0, M 1 0] := by
  ext i
  fin_cases i <;> simp [mulVec, cyclicVacuum, dotProduct, Fin.sum_univ_two]

/-- The vacuum vector is annihilated exactly when the first column vanishes. -/
theorem mulVec_cyclicVacuum_eq_zero (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mulVec M cyclicVacuum = 0 ↔ M 0 0 = 0 ∧ M 1 0 = 0 := by
  rw [mulVec_cyclicVacuum]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h₀, h₁⟩
    ext i
    fin_cases i <;> simp [h₀, h₁]

/-- The evaluation functional corresponding to the cyclic vacuum state: ω(A) = A₀₀. -/
def vacuumState (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A 0 0

/-- The left radical of the finite matrix pairing, defined by
`ω(Bᵀ * A) = 0` for every test matrix `B`. This is a concrete bilinear
radical; it is not the general positive-state GNS null set. -/
def InGNSNull (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ B : Matrix (Fin 2) (Fin 2) ℝ, vacuumState (Bᵀ * A) = 0

/-- The finite matrix pairing radical equals the annihilator of the chosen
cyclic vacuum vector.
-/
theorem inGNSNull_iff_mulVec_vacuum (A : Matrix (Fin 2) (Fin 2) ℝ) :
    InGNSNull A ↔ mulVec A cyclicVacuum = 0 := by
  constructor
  · intro h
    have h₁ : A 0 0 = 0 := by
      have h₁ := h (!![1, 0; 0, 0])
      simpa [vacuumState, mul_apply, transpose_apply, Fin.sum_univ_two] using h₁
    have h₂ : A 1 0 = 0 := by
      have h₂ := h (!![0, 0; 1, 0])
      simpa [vacuumState, mul_apply, transpose_apply, Fin.sum_univ_two] using h₂
    have h₃ : mulVec A cyclicVacuum = 0 := by
      ext i
      fin_cases i <;>
        simp [mulVec, cyclicVacuum, dotProduct, Fin.sum_univ_two, Fin.isValue, h₁, h₂]
    exact h₃
  · intro h B
    have h₀ : A 0 0 = 0 := by
      have h₀ := congr_fun h 0
      simpa [mulVec, cyclicVacuum, dotProduct, Fin.sum_univ_two] using h₀
    have h₁ : A 1 0 = 0 := by
      have h₁ := congr_fun h 1
      simpa [mulVec, cyclicVacuum, dotProduct, Fin.sum_univ_two] using h₁
    simp [vacuumState, mul_apply, Fin.sum_univ_two, transpose_apply, h₀, h₁]

/-! ### 3. The finite null quotient as the vacuum spinor space -/

/-- The vacuum-column map is the existing evaluation map owned by
`GNSQuotientCoset`; reusing it keeps the finite quotient construction unique. -/
abbrev vacuumColumnMap :=
  InfoGeometry.Cosmology.GNSQuotientCoset.evalVacuum

/-- The kernel of the vacuum-column map is exactly the concrete null set above. -/
theorem mem_vacuumColumnMap_ker_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ∈ LinearMap.ker vacuumColumnMap ↔ InGNSNull A := by
  change A ∈ InfoGeometry.Cosmology.GNSQuotientCoset.gnsRadicalSubmodule ↔
    InGNSNull A
  rw [InfoGeometry.Cosmology.GNSQuotientCoset.mem_gnsRadicalSubmodule_iff]
  rw [← mulVec_cyclicVacuum_eq_zero A, inGNSNull_iff_mulVec_vacuum]

/-- The soldering owner's raising CAR root is killed by the chosen vacuum, so it
lies in the kernel defining this finite vacuum quotient. -/
theorem solderingRootPlus_mem_vacuumColumnMap_ker :
    InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus ∈
      LinearMap.ker vacuumColumnMap := by
  change InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus ∈
    InfoGeometry.Cosmology.GNSQuotientCoset.gnsRadicalSubmodule
  rw [InfoGeometry.Cosmology.GNSQuotientCoset.mem_gnsRadicalSubmodule_iff]
  rw [InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus_eq_matrix]
  norm_num

/-- Equivalently, this finite matrix-pairing radical annihilates the soldered
raising root; the statement does not identify it with a completed GNS null set. -/
theorem solderingRootPlus_mem_InGNSNull :
    InGNSNull InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus :=
  (mem_vacuumColumnMap_ker_iff _).mp solderingRootPlus_mem_vacuumColumnMap_ker

/-- The soldering root has zero class in the finite vacuum-column quotient.
This is the quotient-level form of its vacuum annihilation; it is not a claim
about the null class of the faithful filtered C⋆-GNS construction. -/
theorem solderingRootPlus_class_eq_zero :
    (Submodule.Quotient.mk
      InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus :
        Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact solderingRootPlus_mem_vacuumColumnMap_ker

/-- The opposite soldering root is also null in `Vec22`, but it is not
annihilated by the chosen vacuum: its first matrix column is nonzero. This
distinguishes the spacetime null cone from the state-dependent finite GNS
radical instead of identifying the two sets. -/
theorem solderingRootMinus_not_mem_vacuumColumnMap_ker :
    InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus ∉
      LinearMap.ker vacuumColumnMap := by
  intro h
  change InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus ∈
    InfoGeometry.Cosmology.GNSQuotientCoset.gnsRadicalSubmodule at h
  have hcol :=
    (InfoGeometry.Cosmology.GNSQuotientCoset.mem_gnsRadicalSubmodule_iff
      InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus).mp h
  rw [InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus_eq_matrix]
    at hcol
  norm_num at hcol

/-- The opposite null root survives as a nonzero class in the finite vacuum
quotient. -/
theorem solderingRootMinus_class_ne_zero :
    (Submodule.Quotient.mk
      InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus :
        Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≠ 0 := by
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  exact solderingRootMinus_not_mem_vacuumColumnMap_ker h

/-- Under the quotient-to-spinor equivalence, the surviving null root is the
second standard basis vector. -/
theorem solderingRootMinus_quotient_eq_second_basis :
    InfoGeometry.Cosmology.GNSQuotientCoset.gnsQuotientEquiv
      (Submodule.Quotient.mk
        InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus) =
      ![0, 1] := by
  rw [InfoGeometry.Cosmology.GNSQuotientCoset.gnsQuotientEquiv_mk,
    InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus_eq_matrix]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      InfoGeometry.Cosmology.GNSQuotientCoset.cyclicVacuum]

/-- The two soldered CAR roots are both spacetime-null, while the selected
vacuum quotient kills the raising root and retains the lowering root. This is
the explicit compatibility statement between the soldering and finite GNS
lanes; it records the state dependence of the quotient. -/
theorem soldering_null_roots_have_distinct_vacuum_classes :
    InfoGeometry.Clifford.Soldering.q22
        InfoGeometry.Clifford.SolderingIsomorphism.vecRootPlus = 0 ∧
      InfoGeometry.Clifford.Soldering.q22
        InfoGeometry.Clifford.SolderingIsomorphism.vecRootMinus = 0 ∧
      (Submodule.Quotient.mk
        InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus :
          Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) = 0 ∧
      (Submodule.Quotient.mk
        InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus :
          Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≠ 0 :=
  ⟨InfoGeometry.Clifford.SolderingIsomorphism.rootPlus_null,
    InfoGeometry.Clifford.SolderingIsomorphism.rootMinus_null,
    solderingRootPlus_class_eq_zero, solderingRootMinus_class_ne_zero⟩

/-- Every real two-spinor is the first column of a real two-by-two matrix. -/
theorem vacuumColumnMap_surjective : Function.Surjective vacuumColumnMap := by
  exact InfoGeometry.Cosmology.GNSQuotientCoset.evalVacuum_surjective

/-- The quotient by the vacuum null set is linearly equivalent to the vacuum spinor space.

This is the first isomorphism theorem for the explicit finite matrix model.
Its projectivization, rather than this vector-space quotient itself, is related
to the parabolic coset below. It is not a completed C*-GNS construction. -/
noncomputable def vacuumNullQuotientEquiv :
    (Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≃ₗ[ℝ]
      (Fin 2 → ℝ) :=
  InfoGeometry.Cosmology.GNSQuotientCoset.gnsQuotientEquiv

@[simp] theorem vacuumNullQuotientEquiv_mk (A : Matrix (Fin 2) (Fin 2) ℝ) :
    vacuumNullQuotientEquiv (Submodule.Quotient.mk A) =
      fun i => A i 0 := by
  change InfoGeometry.Cosmology.GNSQuotientCoset.gnsQuotientEquiv
      (Submodule.Quotient.mk A) = fun i => A i 0
  rw [InfoGeometry.Cosmology.GNSQuotientCoset.gnsQuotientEquiv_mk]
  change mulVec A cyclicVacuum = fun i => A i 0
  rw [mulVec_cyclicVacuum]
  ext i
  fin_cases i <;> simp

/-- The finite quotient equivalence transports left multiplication of operators
to the standard matrix action on the vacuum spinor. This reuses the GNS
quotient owner's intertwining theorem and supplies the operator-action leg of
the finite quotient/projective-coset bridge. -/
theorem vacuumNullQuotient_left_action_intertwining
    (A X : Matrix (Fin 2) (Fin 2) ℝ) :
    vacuumNullQuotientEquiv (Submodule.Quotient.mk (A * X)) =
      mulVec A (vacuumNullQuotientEquiv (Submodule.Quotient.mk X)) := by
  exact InfoGeometry.Cosmology.GNSQuotientCoset.gns_quotient_left_action_intertwining
    A X

theorem vacuumNullQuotientEquiv_mk_eq_zero_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    vacuumNullQuotientEquiv (Submodule.Quotient.mk A) = 0 ↔
      InGNSNull A := by
  rw [vacuumNullQuotientEquiv_mk]
  have hcol : (fun i : Fin 2 => A i 0) = 0 ↔ A 0 0 = 0 ∧ A 1 0 = 0 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h₀, h₁⟩
      ext i
      fin_cases i <;> assumption
  rw [hcol, ← mulVec_cyclicVacuum_eq_zero, inGNSNull_iff_mulVec_vacuum]

/-- The projective line of the finite vacuum-null quotient. -/
abbrev VacuumNullProjectiveLine :=
  ℙ ℝ (Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap)

/-- The canonical projectivization of the quotient's linear equivalence with the spinor space. -/
noncomputable def vacuumNullProjectiveMap :
    VacuumNullProjectiveLine → ℙ ℝ (Fin 2 → ℝ) :=
  Projectivization.map vacuumNullQuotientEquiv.toLinearMap
    vacuumNullQuotientEquiv.injective

/-- Projectivizing the finite null quotient gives the native real projective line. -/
noncomputable def vacuumNullProjectiveEquiv :
    VacuumNullProjectiveLine ≃ ℙ ℝ (Fin 2 → ℝ) := by
  apply Equiv.ofBijective vacuumNullProjectiveMap
  constructor
  · exact Projectivization.map_injective
      vacuumNullQuotientEquiv.toLinearMap vacuumNullQuotientEquiv.injective
  · intro p
    induction p using Projectivization.ind with
    | h v hv =>
      refine ⟨Projectivization.mk ℝ (vacuumNullQuotientEquiv.symm v) ?_, ?_⟩
      · intro hzero
        apply hv
        have := congrArg vacuumNullQuotientEquiv hzero
        simpa using this
      · rw [vacuumNullProjectiveMap, Projectivization.map_mk]
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _
          (by simpa using hv) hv).2
        exact ⟨1, by simp⟩

/-- On representatives, the projective quotient equivalence is induced by the quotient map. -/
theorem vacuumNullProjectiveMap_mk
    (x : Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) (hx : x ≠ 0) :
    vacuumNullProjectiveMap (Projectivization.mk ℝ x hx) =
      Projectivization.mk ℝ (vacuumNullQuotientEquiv x)
        (by
          intro hzero
          apply hx
          exact vacuumNullQuotientEquiv.injective (by simpa using hzero)) := by
  exact Projectivization.map_mk _ _ _ _

/-- The native special linear group acting on the native real projective line. -/
abbrev RealSL2 := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The projective ray represented by the chosen vacuum spinor. -/
noncomputable def vacuumProjectivePoint : ℙ ℝ (Fin 2 → ℝ) :=
  Projectivization.mk ℝ cyclicVacuum (by simp [cyclicVacuum])

/-- The parabolic subgroup is defined natively as the ray stabilizer in `SL₂(ℝ)`. -/
noncomputable def vacuumRayStabilizer : Subgroup RealSL2 :=
  MulAction.stabilizer RealSL2 vacuumProjectivePoint

/-- The orbit of the vacuum ray is the entire native projective line.

This uses Mathlib's pretransitivity instance for the special linear group action. -/
noncomputable def vacuumProjectiveOrbitEquiv :
    MulAction.orbit RealSL2 vacuumProjectivePoint ≃ ℙ ℝ (Fin 2 → ℝ) := by
  apply Equiv.ofBijective Subtype.val
  constructor
  · exact Subtype.val_injective
  · intro y
    have hpre : MulAction.IsPretransitive RealSL2 (ℙ ℝ (Fin 2 → ℝ)) := inferInstance
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq vacuumProjectivePoint y
    exact ⟨⟨g • vacuumProjectivePoint, ⟨g, rfl⟩⟩, hg⟩

/-- The native homogeneous-space description `SL₂(ℝ)/P ≃ ℙ¹(ℝ)`,
where `P` is the exact stabilizer of the vacuum ray. -/
noncomputable def vacuumRayCosetEquivProjectiveLine :
    (RealSL2 ⧸ vacuumRayStabilizer) ≃ ℙ ℝ (Fin 2 → ℝ) :=
  (MulAction.orbitEquivQuotientStabilizer RealSL2 vacuumProjectivePoint).symm.trans
    vacuumProjectiveOrbitEquiv

/-- The finite vacuum-null quotient and the native parabolic coset have
isomorphic projectivizations. This is a finite-dimensional `SL₂(ℝ)` result. -/
noncomputable def vacuumRayCosetEquivProjectiveNullQuotient :
    (RealSL2 ⧸ vacuumRayStabilizer) ≃ VacuumNullProjectiveLine :=
  vacuumRayCosetEquivProjectiveLine.trans vacuumNullProjectiveEquiv.symm

/-- Every point of the projectivized vacuum quotient is represented by the
`SL(2, ℝ)` orbit of the canonical spinor. This explicit representative
statement complements the native group-action quotient equivalence above. -/
theorem vacuumNullProjectivePoint_is_sl2_orbit
    (p : VacuumNullProjectiveLine) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℝ,
      InfoGeometry.Cosmology.ParabolicResolution.IsSL2 g ∧
        ∃ hv : Matrix.mulVec g
            InfoGeometry.Cosmology.ParabolicResolution.canonicalSpinor ≠ 0,
          vacuumNullProjectiveEquiv p =
            Projectivization.mk ℝ
              (Matrix.mulVec g
                InfoGeometry.Cosmology.ParabolicResolution.canonicalSpinor) hv := by
  induction p using Projectivization.ind with
  | h q hq =>
    have hvec : vacuumNullQuotientEquiv q ≠ 0 := by
      intro h
      exact hq (vacuumNullQuotientEquiv.injective (by simpa using h))
    obtain ⟨g, hg, hact⟩ :=
      InfoGeometry.Cosmology.ParabolicResolution.sl2_transitive_on_spinors
        (vacuumNullQuotientEquiv q) hvec
    have hnonzero : Matrix.mulVec g
        InfoGeometry.Cosmology.ParabolicResolution.canonicalSpinor ≠ 0 := by
      rw [hact]
      exact hvec
    refine ⟨g, hg, hnonzero, ?_⟩
    change vacuumNullProjectiveMap (Projectivization.mk ℝ q hq) = _
    rw [vacuumNullProjectiveMap_mk]
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    exact ⟨1, by rw [hact]; simp⟩


/-! ### 3. Parabolic Stabilizer of the Vacuum Ray -/

/-- The Parabolic Subgroup P (upper-triangular in this chart). -/
def IsParabolicUpper (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  g 1 0 = 0

/-- A transformation stabilizes the vacuum projective ray if it acts as a non-zero scaling. -/
def StabilizesVacuumRay (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  IsSL2 g ∧ ∃ (lambdaVal : ℝ), lambdaVal ≠ 0 ∧ mulVec g cyclicVacuum = lambdaVal • cyclicVacuum

/--
  The stabilizer of the cyclic vacuum ray in `SL(2, ℝ)` consists exactly of
  the matrices with vanishing lower-left entry.
-/
theorem stabilizesVacuumRay_iff_parabolic (g : Matrix (Fin 2) (Fin 2) ℝ) :
    StabilizesVacuumRay g ↔ IsSL2 g ∧ IsParabolicUpper g := by
  constructor
  · rintro ⟨hSL, c, ⟨_hc, h_ray⟩⟩
    refine ⟨hSL, ?_⟩
    change g 1 0 = 0
    have h1 : (mulVec g cyclicVacuum) 1 = (c • cyclicVacuum) 1 :=
      congrArg (fun v : Fin 2 → ℝ => v 1) h_ray
    rw [mulVec_cyclicVacuum] at h1
    simpa [cyclicVacuum] using h1
  · rintro ⟨hSL, hP⟩
    refine ⟨hSL, g 0 0, ?_, ?_⟩
    · intro hc
      have hdet : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
      have : g.det = 0 := by
        rw [hdet, hc, hP]
        ring
      rw [hSL] at this
      norm_num at this
    · rw [mulVec_cyclicVacuum]
      ext i
      fin_cases i
      · simp [cyclicVacuum]
      · simpa [cyclicVacuum, IsParabolicUpper] using hP

/-- The finite vacuum-ray stabilizer is definitionally the same predicate as
the canonical spinor-ray stabilizer owned by the parabolic development. -/
theorem stabilizesVacuumRay_agrees_with_parabolic_owner
    (g : Matrix (Fin 2) (Fin 2) ℝ) :
    StabilizesVacuumRay g ↔
      InfoGeometry.Cosmology.ParabolicResolution.StabilizesSpinorRaySL2 g := by
  rfl

/-- The local ray-stabilizer calculation is the existing parabolic stabilizer
theorem after identifying the two definitions of the vacuum spinor. -/
theorem stabilizesVacuumRay_iff_parabolic_owner
    (g : Matrix (Fin 2) (Fin 2) ℝ) :
    StabilizesVacuumRay g ↔
      InfoGeometry.Cosmology.ParabolicResolution.IsSL2 g ∧
        InfoGeometry.Cosmology.ParabolicResolution.IsParabolicUpper g := by
  simpa [StabilizesVacuumRay, IsSL2, IsParabolicUpper, cyclicVacuum,
    InfoGeometry.Cosmology.ParabolicResolution.StabilizesSpinorRaySL2,
    InfoGeometry.Cosmology.ParabolicResolution.IsSL2,
    InfoGeometry.Cosmology.ParabolicResolution.IsParabolicUpper,
    InfoGeometry.Cosmology.ParabolicResolution.canonicalSpinor] using
      (InfoGeometry.Cosmology.ParabolicResolution.stabilizesSpinorRaySL2_iff g)


/-! ### 4. Finite-Dimensional Projector and Commutator Bounds -/

/-- The rank-one matrix projector associated to a real two-vector. -/
noncomputable def projector (u : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u 0 * u 0, u 0 * u 1;
     u 1 * u 0, u 1 * u 1]

/-- The Frobenius norm squared of an operator. -/
def frobNormSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A 0 0)^2 + (A 0 1)^2 + (A 1 0)^2 + (A 1 1)^2

/-- The vacuum matrix coefficient of a normalized rank-one projector is bounded by one. -/
theorem vacuumState_projector_bound (u : Fin 2 → ℝ) (hu : (u 0)^2 + (u 1)^2 = 1) :
    |vacuumState (projector u)| ≤ 1 := by
  dsimp [vacuumState, projector]
  have h_abs : |u 0 * u 0| = (u 0)^2 := by
    rw [← sq]
    exact abs_of_nonneg (sq_nonneg _)
  rw [h_abs]
  have h_u1_sq : 0 ≤ (u 1)^2 := sq_nonneg (u 1)
  linarith

/-- A normalized rank-one projector has Frobenius norm squared one. -/
theorem projector_frobNormSq (u : Fin 2 → ℝ) (hu : (u 0)^2 + (u 1)^2 = 1) :
    frobNormSq (projector u) = 1 := by
  dsimp [frobNormSq, projector]
  calc
    (u 0 * u 0)^2 + (u 0 * u 1)^2 + (u 1 * u 0)^2 + (u 1 * u 1)^2
      = (u 0)^4 + 2 * (u 0)^2 * (u 1)^2 + (u 1)^4 := by ring
    _ = ((u 0)^2 + (u 1)^2)^2 := by ring
    _ = 1^2 := by rw [hu]
    _ = 1 := by ring

/-- The Lorentz boost generator K in the spinor representation. -/
noncomputable def boostGenerator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1/2 : ℝ), 0;
     0, -(1/2 : ℝ)]

/-- Matrix commutator [A, B] = A B - B A. -/
def commutator (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A * B - B * A

/--
  For every normalized vector, the explicitly defined matrix commutator has
  Frobenius norm squared at most one half.
-/
theorem commutator_boost_projector_bound (u : Fin 2 → ℝ) (hu : (u 0)^2 + (u 1)^2 = 1) :
    frobNormSq (commutator boostGenerator (projector u)) ≤ 1/2 := by
  dsimp [frobNormSq, commutator, boostGenerator, projector] at *
  simp [mul_apply, Fin.sum_univ_two, Fin.isValue] at *
  ring_nf at *
  nlinarith [sq_nonneg ((u 0 : ℝ) ^ 2 - (u 1 : ℝ) ^ 2)]

end InfoGeometry.Cosmology.SpacetimeParabolicQuotient
