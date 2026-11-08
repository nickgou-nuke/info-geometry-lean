/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.OperatorAlgebra.SuperTKK
import InfoGeometry.Quantum.CliffordDictionary
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# TKK adjoint grading on the Cl(5,5) vacuum spinor ideal

The grading element below acts on the same 32-dimensional vacuum ideal used
by the Cl(5,5) spinor representation. It is transported from a diagonal
endomorphism in the owner's `Fin 32` coordinates. Its adjoint eigenspaces
are independent of the CAR operator-number grading.

We prove the bracket grade-addition law. The repository's `SuperTKKStructure` API records a tripotent
polynomial; it does not itself construct a Jordan-pair TKK algebra. This file
therefore claims the concrete tripotent adjoint grading and its bracket law,
not an unprovided Jordan-pair construction.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SuperTKK

open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Krein InfoGeometry.Quantum

abbrev V := cl55VacuumIdeal
abbrev EndV := Module.End ℝ V
abbrev Coord := Fin 32 → ℝ
abbrev EndCoord := Module.End ℝ Coord

abbrev KreinBase := EuclideanSpace ℝ (Fin 16)
abbrev KreinDouble := InfoGeometry.Krein.DoubledSpace KreinBase

/-- The vacuum-ideal identification followed by the exterior spinor
coordinate readout. -/
def coordinates : V ≃ₗ[ℝ] Coord :=
  cl55VacuumIdealSpinorEquiv.trans spinorCoordinateEquiv

/-- The pair-interleaved coordinate reindexing of the 32-dimensional
spinor: coordinate `2*i` is in the first real sheet and `2*i+1` in the
second. -/
private def pairIndex : Fin 16 × Fin 2 ≃ Fin 32 := finProdFinEquiv

/-- Split the pair-interleaved coordinate functions into the two real sheets. -/
private def splitPairCoordinates : (Fin 16 × Fin 2 → ℝ) ≃ₗ[ℝ]
    (Fin 16 → ℝ) × (Fin 16 → ℝ) where
  toFun f := (fun i => f (i, 0), fun i => f (i, 1))
  invFun p ij := if ij.2 = 0 then p.1 ij.1 else p.2 ij.1
  left_inv f := by
    funext ij
    rcases ij with ⟨i, b⟩
    fin_cases b <;> simp
  right_inv p := by
    rcases p with ⟨x, y⟩
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp
  map_add' f g := by
    apply Prod.ext <;> funext i <;> simp
  map_smul' c f := by
    apply Prod.ext <;> funext i <;> simp

/-- Coordinate realization of the two-sheeted real Krein carrier on the
same 32-dimensional spinor coordinates. -/
noncomputable def coordinateToKreinDouble : Coord ≃ₗ[ℝ] KreinDouble :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin 32 => ℝ) pairIndex.symm).trans
    (((splitPairCoordinates.trans
        ((EuclideanSpace.equiv (Fin 16) ℝ).toLinearEquiv.symm.prodCongr
          (EuclideanSpace.equiv (Fin 16) ℝ).toLinearEquiv.symm)).trans
      (WithLp.linearEquiv (2 : ENNReal) ℝ
        (KreinBase × KreinBase)).symm))

/-- The vacuum ideal, in its exterior-spinor coordinates, is the canonical
two-sheeted real Krein carrier with sixteen coordinates on each sheet. -/
noncomputable def idealKreinEquiv : V ≃ₗ[ℝ] KreinDouble :=
  coordinates.trans coordinateToKreinDouble

/-- Transport modular conjugation from the canonical doubled real carrier to
the Cl(5,5) vacuum ideal. -/
noncomputable def idealModularConjugation : EndV :=
  (idealKreinEquiv.conjAlgEquiv ℝ).symm
    (Cl11Dictionary.canonical (E := KreinBase)).J.toLinearMap

/-- Transport the fundamental sign symmetry from the canonical doubled real
carrier to the Cl(5,5) vacuum ideal. -/
noncomputable def idealFundamentalSymmetry : EndV :=
  (idealKreinEquiv.conjAlgEquiv ℝ).symm
    (Cl11Dictionary.canonical (E := KreinBase)).ε.toLinearMap

/-- The coordinate TKK grading read on the doubled carrier is supported on
the first coordinate of each sheet with opposite signs. -/
def doubledTKKGrading : Module.End ℝ KreinDouble where
  toFun u := to_doubled
    (WithLp.toLp (2 : ENNReal)
      (Pi.single (0 : Fin 16) ((WithLp.fst u) 0)))
    (WithLp.toLp (2 : ENNReal)
      (Pi.single (0 : Fin 16) (-((WithLp.snd u) 0))))
  map_add' u v := by
    apply DoubledSpace.ext
    · apply WithLp.ofLp_injective
      ext i
      by_cases hi : i = 0 <;> simp [Pi.single_apply, hi, WithLp.add_fst]
    · apply WithLp.ofLp_injective
      ext i
      by_cases hi : i = 0 <;> simp [Pi.single_apply, hi, WithLp.add_snd] <;> ring
  map_smul' c u := by
    apply DoubledSpace.ext
    · apply WithLp.ofLp_injective
      ext i
      by_cases hi : i = 0 <;> simp [Pi.single_apply, hi, WithLp.smul_fst]
    · apply WithLp.ofLp_injective
      ext i
      by_cases hi : i = 0 <;> simp [hi, WithLp.smul_snd]

/-- A diagonal operator with vector-space eigenvalues `1`, `-1`, and `0`.
Its adjoint action on endomorphisms realizes weights `-2` through `2`. -/
def coordinateGradingOperator : EndCoord where
  toFun f i := (if i = 0 then (1 : ℝ) else if i = 1 then -1 else 0) * f i
  map_add' f g := by
    ext i
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

theorem coordinateGradingOperator_cube :
    coordinateGradingOperator ^ 3 = coordinateGradingOperator := by
  apply LinearMap.ext
  intro f
  ext i
  change coordinateGradingOperator
      (coordinateGradingOperator (coordinateGradingOperator f)) i =
    coordinateGradingOperator f i
  by_cases h0 : i = 0
  · subst i
    simp [coordinateGradingOperator]
  · by_cases h1 : i = 1
    · subst i
      simp [coordinateGradingOperator]
    · simp [coordinateGradingOperator, h0, h1]

/-- The coordinate-to-doubled equivalence reads the even and odd coordinates
as the first and second real sheets, respectively. -/
theorem coordinateToKreinDouble_fst (f : Coord) (i : Fin 16) :
    WithLp.fst (coordinateToKreinDouble f) i = f (pairIndex (i, 0)) := by
  simp [coordinateToKreinDouble, pairIndex, splitPairCoordinates]

theorem coordinateToKreinDouble_snd (f : Coord) (i : Fin 16) :
    WithLp.snd (coordinateToKreinDouble f) i = f (pairIndex (i, 1)) := by
  simp [coordinateToKreinDouble, pairIndex, splitPairCoordinates]

theorem coordinateToKreinDouble_symm_pair0 (u : KreinDouble) (i : Fin 16) :
    coordinateToKreinDouble.symm u (pairIndex (i, 0)) = (WithLp.fst u) i := by
  have h := congrArg (fun z : KreinDouble => WithLp.fst z i)
    (coordinateToKreinDouble.apply_symm_apply u)
  simpa only [coordinateToKreinDouble_fst] using h

theorem coordinateToKreinDouble_symm_pair1 (u : KreinDouble) (i : Fin 16) :
    coordinateToKreinDouble.symm u (pairIndex (i, 1)) = (WithLp.snd u) i := by
  have h := congrArg (fun z : KreinDouble => WithLp.snd z i)
    (coordinateToKreinDouble.apply_symm_apply u)
  simpa only [coordinateToKreinDouble_snd] using h

private theorem pairIndex_zero_iff (i : Fin 16) :
    pairIndex (i, 0) = 0 ↔ i = 0 := by
  constructor
  · intro h
    have h00 : pairIndex (0, 0) = 0 := by decide
    have h' : pairIndex (i, 0) = pairIndex (0, 0) := by
      rw [h00]
      exact h
    have h' := pairIndex.injective h'
    exact congrArg Prod.fst h'
  · rintro rfl
    decide

private theorem pairIndex_one_iff (i : Fin 16) :
    pairIndex (i, 0) = 1 ↔ False := by
  constructor
  · intro h
    have h01 : pairIndex (0, 1) = 1 := by decide
    have h' : pairIndex (i, 0) = pairIndex (0, 1) := by
      rw [h01]
      exact h
    have h' := pairIndex.injective h'
    have hs : (0 : Fin 2) = 1 := by
      simpa using congrArg Prod.snd h'
    exact (by decide : (0 : Fin 2) ≠ 1) hs
  · exact False.elim

private theorem pairIndex1_zero_iff (i : Fin 16) :
    pairIndex (i, 1) = 0 ↔ False := by
  constructor
  · intro h
    have h00 : pairIndex (0, 0) = 0 := by decide
    have h' : pairIndex (i, 1) = pairIndex (0, 0) := by
      rw [h00]
      exact h
    have h' := pairIndex.injective h'
    have hs : (1 : Fin 2) = 0 := by
      simpa using congrArg Prod.snd h'
    exact (by decide : (1 : Fin 2) ≠ 0) hs
  · exact False.elim

private theorem pairIndex1_one_iff (i : Fin 16) :
    pairIndex (i, 1) = 1 ↔ i = 0 := by
  constructor
  · intro h
    have h01 : pairIndex (0, 1) = 1 := by decide
    have h' : pairIndex (i, 1) = pairIndex (0, 1) := by
      rw [h01]
      exact h
    have h' := pairIndex.injective h'
    exact congrArg Prod.fst h'
  · rintro rfl
    decide

/-- The grading element on endomorphisms of the actual vacuum ideal. -/
def tkkGradingElement : EndV :=
  (coordinates.conjAlgEquiv ℝ).symm coordinateGradingOperator

private theorem coordinateGradingOperator_pair0 (f : Coord) (i : Fin 16) :
    coordinateGradingOperator f (pairIndex (i, 0)) =
      if i = 0 then f (pairIndex (i, 0)) else 0 := by
  by_cases hi : i = 0
  · subst i
    have hzero : pairIndex (0, 0) = 0 := by decide
    have hone : pairIndex (0, 0) ≠ 1 := by decide
    simp [coordinateGradingOperator, hzero, hone]
  · simp [coordinateGradingOperator, pairIndex_zero_iff,
      pairIndex_one_iff, hi]

private theorem coordinateGradingOperator_pair1 (f : Coord) (i : Fin 16) :
    coordinateGradingOperator f (pairIndex (i, 1)) =
      if i = 0 then -f (pairIndex (i, 1)) else 0 := by
  by_cases hi : i = 0
  · subst i
    have hzero : pairIndex (0, 1) ≠ 0 := by decide
    have hone : pairIndex (0, 1) = 1 := by decide
    simp [coordinateGradingOperator, hzero, hone]
  · simp [coordinateGradingOperator, pairIndex1_zero_iff,
      pairIndex1_one_iff, hi]

private theorem tkkGradingElement_krein_apply (u : KreinDouble) :
    ((idealKreinEquiv.conjAlgEquiv ℝ) tkkGradingElement) u =
      coordinateToKreinDouble
        (coordinateGradingOperator (coordinateToKreinDouble.symm u)) := by
  simp [idealKreinEquiv, coordinates, tkkGradingElement,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

/-- Under the explicit two-sheet coordinate equivalence, the TKK grading
operator is the signed first-coordinate operator on the doubled carrier. -/
theorem tkkGradingElement_kreinDouble :
    (idealKreinEquiv.conjAlgEquiv ℝ) tkkGradingElement = doubledTKKGrading := by
  apply LinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext
  · apply WithLp.ofLp_injective
    ext i
    rw [tkkGradingElement_krein_apply, coordinateToKreinDouble_fst]
    by_cases hi : i = 0
    · subst i
      simp [coordinateGradingOperator_pair0, coordinateToKreinDouble_symm_pair0,
        doubledTKKGrading, to_doubled]
    · simp [coordinateGradingOperator_pair0, coordinateToKreinDouble_symm_pair0,
        doubledTKKGrading, to_doubled, hi]
  · apply WithLp.ofLp_injective
    ext i
    rw [tkkGradingElement_krein_apply, coordinateToKreinDouble_snd]
    by_cases hi : i = 0
    · subst i
      simp [coordinateGradingOperator_pair1, coordinateToKreinDouble_symm_pair1,
        doubledTKKGrading, to_doubled]
    · simp [coordinateGradingOperator_pair1, coordinateToKreinDouble_symm_pair1,
        doubledTKKGrading, to_doubled, hi]

private abbrev doubledJ : Module.End ℝ KreinDouble :=
  (Cl11Dictionary.canonical (E := KreinBase)).J.toLinearMap

private abbrev doubledEpsilon : Module.End ℝ KreinDouble :=
  (Cl11Dictionary.canonical (E := KreinBase)).ε.toLinearMap

/-- The modular sheet swap reverses the signed TKK grading operator. -/
theorem doubled_modular_conjugation_reverses_tkk :
    doubledJ * doubledTKKGrading * doubledJ = -doubledTKKGrading := by
  apply LinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  simp [doubledJ, doubledTKKGrading, to_doubled,
    Cl11Dictionary.canonical_J_to_doubled, WithLp.add_fst,
    WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd] <;>
    ext i <;> by_cases hi : i = 0 <;> simp [hi, Pi.single_apply] <;> ring

/-- The transported modular conjugation is an involution on the vacuum-ideal
endomorphism algebra. -/
theorem idealModularConjugation_sq :
    idealModularConjugation * idealModularConjugation = 1 := by
  let e := idealKreinEquiv.conjAlgEquiv ℝ
  let J := (Cl11Dictionary.canonical (E := KreinBase)).J
  apply e.injective
  simp only [map_mul, map_one, idealModularConjugation, e,
    AlgEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro u
  change J (J u) = u
  exact congrArg (fun f : KreinDouble →L[ℝ] KreinDouble => f u)
    Cl11Dictionary.canonical_J_sq

/-- The transported modular conjugation reverses the concrete TKK grading
element on the vacuum ideal. -/
theorem idealModularConjugation_conjugates_tkkGradingElement :
    idealModularConjugation * tkkGradingElement * idealModularConjugation =
      -tkkGradingElement := by
  let e := idealKreinEquiv.conjAlgEquiv ℝ
  have hJ : e idealModularConjugation = doubledJ := by
    simp [e, idealModularConjugation]
  have hP : e tkkGradingElement = doubledTKKGrading :=
    tkkGradingElement_kreinDouble
  apply e.injective
  calc
    e (idealModularConjugation * tkkGradingElement *
        idealModularConjugation) =
      (e idealModularConjugation) * (e tkkGradingElement) *
        (e idealModularConjugation) := by simp only [map_mul]
    _ = -(e tkkGradingElement) := by
      rw [hJ, hP]
      exact doubled_modular_conjugation_reverses_tkk
    _ = e (-tkkGradingElement) := (map_neg e tkkGradingElement).symm

/-- The fundamental sign symmetry preserves the signed TKK grading operator. -/
theorem doubled_fundamental_symmetry_preserves_tkk :
    doubledEpsilon * doubledTKKGrading * doubledEpsilon =
      doubledTKKGrading := by
  apply LinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  simp [doubledEpsilon, doubledTKKGrading, to_doubled,
    Cl11Dictionary.canonical_eps_to_doubled, WithLp.add_fst,
    WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd] <;>
    ext i <;> by_cases hi : i = 0 <;> simp [hi, Pi.single_apply] <;> ring

theorem tkkGradingElement_cube :
    tkkGradingElement ^ 3 = tkkGradingElement := by
  apply (coordinates.conjAlgEquiv ℝ).injective
  simp only [tkkGradingElement, AlgEquiv.apply_symm_apply, map_pow]
  exact coordinateGradingOperator_cube

/-- The tripotent structure required by the repository's TKK adjoint
polynomial, instantiated on endomorphisms of the vacuum ideal. -/
def tkkStructure : InfoGeometry.OperatorAlgebra.TKK.SuperTKKStructure EndV where
  P := tkkGradingElement
  tripotent_P := tkkGradingElement_cube

/-- The associative commutator on the endomorphism algebra. -/
def tkkBracket (X Y : EndV) : EndV := X * Y - Y * X

/-- The adjoint action, packaged as a linear endomorphism of the Lie carrier. -/
def tkkAdjointLinear : EndV →ₗ[ℝ] EndV where
  toFun X := tkkBracket tkkGradingElement X
  map_add' X Y := by
    simp only [tkkBracket, mul_add, add_mul]
    abel
  map_smul' c X := by
    simp only [tkkBracket, smul_mul_assoc, mul_smul_comm]
    exact (smul_sub c (tkkGradingElement * X) (X * tkkGradingElement)).symm

/-- The adjoint action that defines the TKK weights. -/
def tkkAdjoint (X : EndV) : EndV := tkkAdjointLinear X

/-- Integer-weight eigenspace of the tripotent adjoint action. -/
def tkkGrade (k : ℤ) : Submodule ℝ EndV where
  carrier := {X | tkkAdjoint X = (k : ℝ) • X}
  zero_mem' := by simp [tkkAdjoint]
  add_mem' := by
    intro X Y hX hY
    change tkkAdjointLinear X = (k : ℝ) • X at hX
    change tkkAdjointLinear Y = (k : ℝ) • Y at hY
    change tkkAdjointLinear (X + Y) = (k : ℝ) • (X + Y)
    rw [map_add, hX, hY]
    exact (smul_add (k : ℝ) X Y).symm
  smul_mem' := by
    intro c X hX
    change tkkAdjointLinear X = (k : ℝ) • X at hX
    change tkkAdjointLinear (c • X) = (k : ℝ) • (c • X)
    rw [map_smul, hX, smul_smul, smul_smul]
    congr 1
    ring

set_option maxRecDepth 10000 in
private theorem adjoint_bracket_identity (X Y : EndV) :
    tkkAdjoint (tkkBracket X Y) =
      tkkBracket (tkkAdjoint X) Y + tkkBracket X (tkkAdjoint Y) := by
  ext x
  simp [tkkAdjoint, tkkAdjointLinear, tkkBracket,
    Module.End.mul_apply, map_sub]
  abel_nf

private theorem bracket_smul_left (r : ℝ) (X Y : EndV) :
    tkkBracket (r • X) Y = r • tkkBracket X Y := by
  simp only [tkkBracket]
  rw [smul_mul_assoc, mul_smul_comm]
  exact (smul_sub r (X * Y) (Y * X)).symm

private theorem bracket_smul_right (r : ℝ) (X Y : EndV) :
    tkkBracket X (r • Y) = r • tkkBracket X Y := by
  simp only [tkkBracket]
  rw [mul_smul_comm, smul_mul_assoc]
  exact (smul_sub r (X * Y) (Y * X)).symm

/-- The bracket adds TKK adjoint grades: `[gᵢ,gⱼ] ⊆ g_(i+j)`. -/
theorem tkk_bracket_grade_add {i j k : ℤ} (hij : i + j = k)
    {X Y : EndV} (hX : X ∈ tkkGrade i) (hY : Y ∈ tkkGrade j) :
    tkkBracket X Y ∈ tkkGrade k := by
  change tkkAdjoint X = (i : ℝ) • X at hX
  change tkkAdjoint Y = (j : ℝ) • Y at hY
  change tkkAdjoint (tkkBracket X Y) = (k : ℝ) • tkkBracket X Y
  rw [adjoint_bracket_identity, hX, hY]
  rw [bracket_smul_left, bracket_smul_right]
  rw [← add_smul]
  rw [← Int.cast_add, hij]

/-- Coordinate matrix unit `Eᵢⱼ`. -/
def coordinateMatrixUnit (i j : Fin 32) : EndCoord where
  toFun f := Pi.single i (f j)
  map_add' f g := by
    ext n
    by_cases hn : n = i <;> simp [hn]
  map_smul' c f := by
    ext n
    simp [Pi.single_apply, smul_eq_mul]

/-- The matrix unit transported to the vacuum ideal. -/
def matrixUnit (i j : Fin 32) : EndV :=
  (coordinates.conjAlgEquiv ℝ).symm (coordinateMatrixUnit i j)

/-- The diagonal weight assigned to a spinor coordinate by the grading
operator. -/
def coordinateWeight (i : Fin 32) : ℝ :=
  if i = 0 then 1 else if i = 1 then -1 else 0

/-- The adjoint action on a coordinate matrix unit is the difference of its
row and column weights. This computes the TKK weight on the represented
endomorphism, rather than identifying it with operator-number degree. -/
theorem coordinateGradingOperator_commutator_matrixUnit (i j : Fin 32) :
    coordinateGradingOperator * coordinateMatrixUnit i j -
        coordinateMatrixUnit i j * coordinateGradingOperator =
      (coordinateWeight i - coordinateWeight j) • coordinateMatrixUnit i j := by
  apply LinearMap.ext
  intro f
  ext n
  by_cases h : n = i
  · subst n
    simp [coordinateGradingOperator, coordinateMatrixUnit, coordinateWeight,
      Module.End.mul_apply, Pi.single_apply]
    split_ifs <;> ring
  · simp [coordinateGradingOperator, coordinateMatrixUnit, coordinateWeight,
      Module.End.mul_apply, Pi.single_apply, h]

/-- Coordinate matrix units are nonzero, as witnessed by their action on the
`j`-th coordinate vector. -/
theorem coordinateMatrixUnit_ne_zero (i j : Fin 32) :
    coordinateMatrixUnit i j ≠ 0 := by
  intro h
  have hval := congrArg (fun T : EndCoord => T (Pi.single j (1 : ℝ)) i) h
  have hone : (1 : ℝ) = 0 := by
    simpa [coordinateMatrixUnit, Pi.single_apply] using hval
  exact one_ne_zero hone


theorem coordinate_five_weights_nonempty :
    (∃ X : EndCoord,
        coordinateGradingOperator * X - X * coordinateGradingOperator = (-2 : ℝ) • X ∧ X ≠ 0) ∧
    (∃ X : EndCoord,
        coordinateGradingOperator * X - X * coordinateGradingOperator = (-1 : ℝ) • X ∧ X ≠ 0) ∧
    (∃ X : EndCoord,
        coordinateGradingOperator * X - X * coordinateGradingOperator = (0 : ℝ) • X ∧ X ≠ 0) ∧
    (∃ X : EndCoord,
        coordinateGradingOperator * X - X * coordinateGradingOperator = (1 : ℝ) • X ∧ X ≠ 0) ∧
    (∃ X : EndCoord,
        coordinateGradingOperator * X - X * coordinateGradingOperator = (2 : ℝ) • X ∧ X ≠ 0) := by
  refine ⟨⟨coordinateMatrixUnit 1 0, ?_, coordinateMatrixUnit_ne_zero 1 0⟩,
    ⟨coordinateMatrixUnit 2 0, ?_, coordinateMatrixUnit_ne_zero 2 0⟩,
    ⟨coordinateMatrixUnit 2 2, ?_, coordinateMatrixUnit_ne_zero 2 2⟩,
    ⟨coordinateMatrixUnit 0 2, ?_, coordinateMatrixUnit_ne_zero 0 2⟩,
    ⟨coordinateMatrixUnit 0 1, ?_, coordinateMatrixUnit_ne_zero 0 1⟩⟩
  · rw [coordinateGradingOperator_commutator_matrixUnit]
    norm_num [coordinateWeight]
  · rw [coordinateGradingOperator_commutator_matrixUnit]
    norm_num [coordinateWeight]
  · rw [coordinateGradingOperator_commutator_matrixUnit]
    norm_num [coordinateWeight]
  · rw [coordinateGradingOperator_commutator_matrixUnit]
    norm_num [coordinateWeight]
  · rw [coordinateGradingOperator_commutator_matrixUnit]
    norm_num [coordinateWeight]

/-- The conjugation algebra equivalence induced by `coordinates` preserves
pointwise subtraction. This is proved extensionally because its generic API
only assumes additive monoids. -/
private theorem coordinates_conj_map_sub (A B : EndV) :
    (coordinates.conjAlgEquiv ℝ) (A - B) =
      (coordinates.conjAlgEquiv ℝ) A - (coordinates.conjAlgEquiv ℝ) B := by
  apply LinearMap.ext
  intro f
  ext i
  simp [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, map_sub]

/-- The TKK adjoint action on an ideal matrix unit is the difference of its
row and column weights, transported through the vacuum-ideal coordinates. -/
theorem tkkAdjoint_matrixUnit (i j : Fin 32) :
    tkkAdjoint (matrixUnit i j) =
      (coordinateWeight i - coordinateWeight j) • matrixUnit i j := by
  let e := coordinates.conjAlgEquiv ℝ
  apply e.injective
  change e (tkkGradingElement * matrixUnit i j -
      matrixUnit i j * tkkGradingElement) =
    e ((coordinateWeight i - coordinateWeight j) • matrixUnit i j)
  have hP : e tkkGradingElement = coordinateGradingOperator := by
    simp [e, tkkGradingElement]
  have hE : e (matrixUnit i j) = coordinateMatrixUnit i j := by
    simp [e, matrixUnit]
  have hsub := coordinates_conj_map_sub
    (tkkGradingElement * matrixUnit i j) (matrixUnit i j * tkkGradingElement)
  have hmulLeft : e (tkkGradingElement * matrixUnit i j) =
      e tkkGradingElement * e (matrixUnit i j) := e.map_mul _ _
  have hmulRight : e (matrixUnit i j * tkkGradingElement) =
      e (matrixUnit i j) * e tkkGradingElement := e.map_mul _ _
  have hleft :
      e (tkkGradingElement * matrixUnit i j - matrixUnit i j * tkkGradingElement) =
        coordinateGradingOperator * coordinateMatrixUnit i j -
          coordinateMatrixUnit i j * coordinateGradingOperator := by
    calc
      _ = e (tkkGradingElement * matrixUnit i j) -
            e (matrixUnit i j * tkkGradingElement) := hsub
      _ = _ := by rw [hmulLeft, hmulRight, hP, hE]
  have hright :
      e ((coordinateWeight i - coordinateWeight j) • matrixUnit i j) =
        (coordinateWeight i - coordinateWeight j) • coordinateMatrixUnit i j := by
    change e.toLinearEquiv ((coordinateWeight i - coordinateWeight j) • matrixUnit i j) = _
    rw [e.toLinearEquiv.map_smul]
    exact congrArg ((coordinateWeight i - coordinateWeight j) • ·) hE
  exact hleft.trans
    ((coordinateGradingOperator_commutator_matrixUnit i j).trans hright.symm)

/-- The coordinate matrix units are the endomorphism basis induced by the
standard basis of the spinor coordinate module. -/
noncomputable def coordinateEndBasis :
    Module.Basis (Fin 32 × Fin 32) ℝ EndCoord :=
  (Pi.basisFun ℝ (Fin 32)).end

theorem coordinateMatrixUnit_eq_basis (i j : Fin 32) :
    coordinateMatrixUnit i j = coordinateEndBasis (i, j) := by
  apply (Pi.basisFun ℝ (Fin 32)).ext
  intro k
  rw [coordinateEndBasis, Module.Basis.end_apply_apply]
  by_cases hjk : j = k
  · subst k
    simp [coordinateMatrixUnit, Pi.basisFun_apply]
  · simp [coordinateMatrixUnit, Pi.basisFun_apply, hjk]

/-- The coordinate matrix-unit basis transported to the actual vacuum-ideal
endomorphisms. -/
noncomputable def tkkMatrixUnitBasis :
    Module.Basis (Fin 32 × Fin 32) ℝ EndV :=
  coordinateEndBasis.map (coordinates.conjAlgEquiv ℝ).toLinearEquiv.symm

theorem tkkMatrixUnitBasis_apply (i j : Fin 32) :
    tkkMatrixUnitBasis (i, j) = matrixUnit i j := by
  simp [tkkMatrixUnitBasis, matrixUnit, coordinateEndBasis,
    coordinateMatrixUnit_eq_basis]

/-- The actual five TKK eigenspaces inside the vacuum-ideal endomorphisms. -/
noncomputable def tkkFiveGradeCarrier : Submodule ℝ EndV :=
  (((tkkGrade (-2) ⊔ tkkGrade (-1)) ⊔ tkkGrade 0) ⊔
    tkkGrade 1) ⊔ tkkGrade 2

/-- Integer form of the three coordinate weights `1`, `-1`, and `0`. -/
def coordinateWeightInt (i : Fin 32) : ℤ :=
  if i = 0 then 1 else if i = 1 then -1 else 0

theorem coordinateWeightInt_range (i : Fin 32) :
    coordinateWeightInt i = -1 ∨ coordinateWeightInt i = 0 ∨
      coordinateWeightInt i = 1 := by
  by_cases h0 : i = 0
  · simp [coordinateWeightInt, h0]
  · by_cases h1 : i = 1
    · simp [coordinateWeightInt, h1]
    · simp [coordinateWeightInt, h0, h1]

theorem coordinateWeight_eq_int (i : Fin 32) :
    coordinateWeight i = (coordinateWeightInt i : ℝ) := by
  simp [coordinateWeight, coordinateWeightInt]

theorem coordinateWeightInt_sub_range (i j : Fin 32) :
    coordinateWeightInt i - coordinateWeightInt j = -2 ∨
    coordinateWeightInt i - coordinateWeightInt j = -1 ∨
    coordinateWeightInt i - coordinateWeightInt j = 0 ∨
    coordinateWeightInt i - coordinateWeightInt j = 1 ∨
    coordinateWeightInt i - coordinateWeightInt j = 2 := by
  rcases coordinateWeightInt_range i with hi | hi | hi <;>
    rcases coordinateWeightInt_range j with hj | hj | hj <;>
    simp [hi, hj]

theorem matrixUnit_mem_grade (i j : Fin 32) :
    matrixUnit i j ∈ tkkGrade (coordinateWeightInt i - coordinateWeightInt j) := by
  change tkkAdjoint (matrixUnit i j) =
    ((coordinateWeightInt i - coordinateWeightInt j : ℤ) : ℝ) • matrixUnit i j
  rw [tkkAdjoint_matrixUnit, coordinateWeight_eq_int i,
    coordinateWeight_eq_int j, Int.cast_sub]

theorem matrixUnit_mem_tkkFiveGradeCarrier (i j : Fin 32) :
    matrixUnit i j ∈ tkkFiveGradeCarrier := by
  have h := matrixUnit_mem_grade i j
  rcases coordinateWeightInt_sub_range i j with hneg2 | hneg1 | hzero | hpos1 | hpos2
  · change matrixUnit i j ∈
      (((tkkGrade (-2) ⊔ tkkGrade (-1)) ⊔ tkkGrade 0) ⊔ tkkGrade 1) ⊔ tkkGrade 2
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_sup_left
        (by simpa only [hneg2] using h))))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_sup_right
        (by simpa only [hneg1] using h))))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (by simpa only [hzero] using h)))
  · exact Submodule.mem_sup_left
      (Submodule.mem_sup_right (by simpa only [hpos1] using h))
  · exact Submodule.mem_sup_right (by simpa only [hpos2] using h)

/-- Every endomorphism of the actual vacuum ideal is a sum of its five TKK
grade subspaces, since the coordinate matrix units each have weight in
`{-2,-1,0,1,2}`. -/
theorem tkkFiveGradeCarrier_eq_top : tkkFiveGradeCarrier = ⊤ := by
  apply top_unique
  intro X hX
  rw [← tkkMatrixUnitBasis.sum_repr X]
  apply Submodule.sum_mem
  intro ij hij
  rcases ij with ⟨i, j⟩
  rw [tkkMatrixUnitBasis_apply]
  exact Submodule.smul_mem tkkFiveGradeCarrier
    (tkkMatrixUnitBasis.repr X (i, j)) (matrixUnit_mem_tkkFiveGradeCarrier i j)

/-- Every endomorphism of the vacuum ideal decomposes as a sum of elements in
the five TKK adjoint eigenspaces. -/
theorem tkkFiveGrade_decomposition (X : EndV) :
    ∃ xNeg2 xNeg1 x0 x1 x2 : EndV,
      xNeg2 ∈ tkkGrade (-2) ∧ xNeg1 ∈ tkkGrade (-1) ∧
      x0 ∈ tkkGrade 0 ∧ x1 ∈ tkkGrade 1 ∧
      x2 ∈ tkkGrade 2 ∧
      X = xNeg2 + xNeg1 + x0 + x1 + x2 := by
  have hX : X ∈ tkkFiveGradeCarrier := by
    rw [tkkFiveGradeCarrier_eq_top]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hX with ⟨y1, hy1, x2, hx2, heq2⟩
  rcases Submodule.mem_sup.mp hy1 with ⟨y0, hy0, x1, hx1, heq1⟩
  rcases Submodule.mem_sup.mp hy0 with ⟨yNeg, hyNeg, x0, hx0, heq0⟩
  rcases Submodule.mem_sup.mp hyNeg with ⟨xNeg2, hNeg2, xNeg1, hNeg1, heqNeg⟩
  refine ⟨xNeg2, xNeg1, x0, x1, x2, hNeg2, hNeg1, hx0, hx1, hx2, ?_⟩
  rw [← heq2, ← heq1, ← heq0, ← heqNeg]

/-- All five adjoint weights occur as nonzero endomorphisms of the actual
Cl(5,5) vacuum ideal. -/
theorem tkk_five_weights_nonempty :
    (∃ X ∈ tkkGrade (-2), X ≠ 0) ∧
    (∃ X ∈ tkkGrade (-1), X ≠ 0) ∧
    (∃ X ∈ tkkGrade 0, X ≠ 0) ∧
    (∃ X ∈ tkkGrade 1, X ≠ 0) ∧
    (∃ X ∈ tkkGrade 2, X ≠ 0) := by
  refine ⟨⟨matrixUnit 1 0, ?_, ?_⟩,
    ⟨matrixUnit 2 0, ?_, ?_⟩,
    ⟨matrixUnit 2 2, ?_, ?_⟩,
    ⟨matrixUnit 0 2, ?_, ?_⟩,
    ⟨matrixUnit 0 1, ?_, ?_⟩⟩
  · change tkkAdjoint (matrixUnit 1 0) = ((-2 : ℤ) : ℝ) • matrixUnit 1 0
    rw [tkkAdjoint_matrixUnit]
    norm_num [coordinateWeight]
  · intro hzero
    apply coordinateMatrixUnit_ne_zero 1 0
    have h := congrArg (coordinates.conjAlgEquiv ℝ) hzero
    simpa [matrixUnit] using h
  · change tkkAdjoint (matrixUnit 2 0) = ((-1 : ℤ) : ℝ) • matrixUnit 2 0
    rw [tkkAdjoint_matrixUnit]
    norm_num [coordinateWeight]
  · intro hzero
    apply coordinateMatrixUnit_ne_zero 2 0
    have h := congrArg (coordinates.conjAlgEquiv ℝ) hzero
    simpa [matrixUnit] using h
  · change tkkAdjoint (matrixUnit 2 2) = ((0 : ℤ) : ℝ) • matrixUnit 2 2
    rw [tkkAdjoint_matrixUnit]
    norm_num [coordinateWeight]
  · intro hzero
    apply coordinateMatrixUnit_ne_zero 2 2
    have h := congrArg (coordinates.conjAlgEquiv ℝ) hzero
    simpa [matrixUnit] using h
  · change tkkAdjoint (matrixUnit 0 2) = ((1 : ℤ) : ℝ) • matrixUnit 0 2
    rw [tkkAdjoint_matrixUnit]
    norm_num [coordinateWeight]
  · intro hzero
    apply coordinateMatrixUnit_ne_zero 0 2
    have h := congrArg (coordinates.conjAlgEquiv ℝ) hzero
    simpa [matrixUnit] using h
  · change tkkAdjoint (matrixUnit 0 1) = ((2 : ℤ) : ℝ) • matrixUnit 0 1
    rw [tkkAdjoint_matrixUnit]
    norm_num [coordinateWeight]
  · intro hzero
    apply coordinateMatrixUnit_ne_zero 0 1
    have h := congrArg (coordinates.conjAlgEquiv ℝ) hzero
    simpa [matrixUnit] using h

end InfoGeometry.Clifford.Cl55SuperTKK

end
