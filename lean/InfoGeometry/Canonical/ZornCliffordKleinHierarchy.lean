/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Canonical.TetractysCliffordLorentzAction
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Real split-octonion Clifford dimensions, parity, and bivector action

This owner uses the existing real specialization of the genuine Zorn gamma
representation.  Its module is `ZornMatrix ℝ × ZornMatrix ℝ`, of real dimension
sixteen.  The two eight-dimensional summands are the chiral spinor spaces;
they are not the two four-dimensional Peirce summands of one Zorn matrix.

The representation is a native `CliffordAlgebra` algebra homomorphism.  Here
we prove the dimension obstruction to replacing its target by endomorphisms
of a single Zorn matrix, and establish chirality and the infinitesimal action
of antisymmetric products of vectors.  No faithfulness or surjectivity of the
full representation, identification of chirality with an oriented volume
element, or differential-geometric gauge connection is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornClifford

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-! ## Actual real dimensions -/

/-- One real Zorn matrix has eight real coordinates. -/
theorem realZorn_finrank : Module.finrank ℝ (ZornMatrix ℝ) = 8 := by
  rw [(coordLinearEquiv (R := ℝ)).finrank_eq]
  simp [Coord, Module.finrank_prod]

/-- The full real spinor module has two eight-dimensional summands. -/
theorem realDiracSpinor_finrank :
    Module.finrank ℝ (DiracSpinor16 (R := ℝ)) = 16 := by
  let : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    (coordLinearEquiv (R := ℝ)).symm.finiteDimensional
  rw [Module.finrank_prod, realZorn_finrank]

/-- Endomorphisms of one Zorn matrix have dimension sixty-four. -/
theorem realZornEnd_finrank :
    Module.finrank ℝ (Module.End ℝ (ZornMatrix ℝ)) = 64 := by
  let : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    (coordLinearEquiv (R := ℝ)).symm.finiteDimensional
  rw [Module.finrank_linearMap, realZorn_finrank]

/-- Endomorphisms of the real Dirac module have dimension two hundred fifty-six. -/
theorem realDiracEnd_finrank :
    Module.finrank ℝ (Module.End ℝ (DiracSpinor16 (R := ℝ))) = 256 := by
  let : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    (coordLinearEquiv (R := ℝ)).symm.finiteDimensional
  rw [Module.finrank_linearMap, realDiracSpinor_finrank]

/-- The native full Clifford algebra has dimension `2^8 = 256`. -/
theorem realZornClifford_finrank :
    Module.finrank ℝ (CliffordAlgebra (zornNorm (R := ℝ))) = 256 := by
  let : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    (coordLinearEquiv (R := ℝ)).symm.finiteDimensional
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let b : Module.Basis (Fin 8) ℝ (ZornMatrix ℝ) :=
    Module.finBasisOfFinrankEq ℝ (ZornMatrix ℝ) realZorn_finrank
  rw [(CliffordAlgebra.equivExterior (zornNorm (R := ℝ))).finrank_eq,
    Module.finrank_eq_card_basis b.ExteriorAlgebra]
  norm_num [Fintype.card_finset]

/-- A full Clifford algebra cannot be identified linearly with the
endomorphisms of just one eight-dimensional Zorn copy. -/
theorem no_realZornClifford_end8_linearEquiv :
    ¬ Nonempty (CliffordAlgebra (zornNorm (R := ℝ)) ≃ₗ[ℝ]
      Module.End ℝ (ZornMatrix ℝ)) := by
  rintro ⟨e⟩
  have h := e.finrank_eq
  rw [realZornClifford_finrank, realZornEnd_finrank] at h
  norm_num at h

/-! ## Readback to the existing `ZornVectorMatrix` carrier -/

@[simp] theorem canonicalVectorEquiv_zornConj (x : ZornMatrix ℝ) :
    canonicalVectorEquiv (zornConj x) =
      InfoGeometry.Algebra.ZornVectorMatrix.conj (canonicalVectorEquiv x) := rfl

/-- The quadratic form used by the Clifford lift is the original Zorn norm. -/
theorem zornNorm_eq_vectorNorm (x : ZornMatrix ℝ) :
    zornNorm x =
      InfoGeometry.Algebra.ZornVectorMatrix.norm (canonicalVectorEquiv x) := by
  simp [zornNorm_apply, zornNormFun,
    InfoGeometry.Algebra.ZornVectorMatrix.norm,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]

/-- On the two real spinor blocks, the gamma operator is exactly the existing
left product by `x` and by its conjugate. -/
theorem diracGamma_vectorReadback (x s t : ZornMatrix ℝ) :
    (canonicalVectorEquiv (diracGamma x (s, t)).1,
      canonicalVectorEquiv (diracGamma x (s, t)).2) =
    (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (canonicalVectorEquiv x) (canonicalVectorEquiv t),
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.conj (canonicalVectorEquiv x))
        (canonicalVectorEquiv s)) := by
  change (canonicalVectorEquiv (x * t), canonicalVectorEquiv (zornConj x * s)) = _
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_zornConj]

/-! ## Chirality is a grading of the sixteen-dimensional module -/

/-- `+1` on the first real Zorn spinor and `-1` on the second. -/
def diracChirality :
    DiracSpinor16 (R := ℝ) ≃ₗ[ℝ] DiracSpinor16 (R := ℝ) where
  toFun Ψ := (Ψ.1, -Ψ.2)
  invFun Ψ := (Ψ.1, -Ψ.2)
  left_inv Ψ := by simp
  right_inv Ψ := by simp
  map_add' Ψ Φ := by apply Prod.ext <;> simp [add_comm]
  map_smul' r Ψ := by
    apply Prod.ext
    · rfl
    · change -(r • Ψ.2) = r • (-Ψ.2)
      exact (smul_neg r Ψ.2).symm

@[simp] theorem diracChirality_apply (s t : ZornMatrix ℝ) :
    diracChirality (s, t) = (s, -t) := rfl

@[simp] theorem diracChirality_sq (Ψ : DiracSpinor16 (R := ℝ)) :
    diracChirality (diracChirality Ψ) = Ψ := by
  simp [diracChirality]

/-- A vector acts between the two chiral summands. -/
theorem diracChirality_gamma (x : ZornMatrix ℝ)
    (Ψ : DiracSpinor16 (R := ℝ)) :
    diracChirality (diracGamma x Ψ) =
      -diracGamma x (diracChirality Ψ) := by
  rcases Ψ with ⟨s, t⟩
  have hneg : cliffordMinus x (-t) = -cliffordMinus x t := by
    exact congrArg Prod.fst (map_neg (diracGamma x) (0, t))
  apply Prod.ext
  · change cliffordMinus x t = -cliffordMinus x (-t)
    rw [hneg, neg_neg]
  · rfl

/-- Chirality implements Mathlib's native Clifford grade involution. -/
theorem diracChirality_clifford_involute
    (a : CliffordAlgebra (zornNorm (R := ℝ)))
    (Ψ : DiracSpinor16 (R := ℝ)) :
    diracChirality (zornCliffordRepresentation a Ψ) =
      zornCliffordRepresentation (CliffordAlgebra.involute a)
        (diracChirality Ψ) := by
  induction a using CliffordAlgebra.induction generalizing Ψ with
  | algebraMap r => simp
  | ι x =>
      rw [zornCliffordRepresentation_ι, CliffordAlgebra.involute_ι,
        map_neg, zornCliffordRepresentation_ι]
      exact diracChirality_gamma x Ψ
  | mul a b ha hb =>
      rw [map_mul, map_mul, map_mul]
      change diracChirality
        (zornCliffordRepresentation a (zornCliffordRepresentation b Ψ)) = _
      rw [ha, hb]
      rfl
  | add a b ha hb =>
      rw [map_add, map_add, map_add]
      change diracChirality
        (zornCliffordRepresentation a Ψ + zornCliffordRepresentation b Ψ) = _
      rw [map_add, ha, hb]
      rfl

/-- Real spin operators commute with chirality. -/
theorem spinDirac_commutes_chirality
    (g : spinGroup (zornNorm (R := ℝ)))
    (Ψ : DiracSpinor16 (R := ℝ)) :
    diracChirality
        ((spinDiracRepresentation g : Module.End ℝ (DiracSpinor16 (R := ℝ))) Ψ) =
      (spinDiracRepresentation g : Module.End ℝ (DiracSpinor16 (R := ℝ)))
        (diracChirality Ψ) := by
  rw [spinDiracRepresentation_val, diracChirality_clifford_involute,
    spinGroup.involute_eq g.2]

/-- The null cone gives square-zero gamma operators on the full Dirac module. -/
theorem diracGamma_sq_eq_zero_of_null (x : ZornMatrix ℝ)
    (hx : zornNorm x = 0) :
    diracGammaLinear x * diracGammaLinear x = 0 := by
  rw [diracGamma_sq, hx, map_zero]

/-! ## Antisymmetric vector products and their operator action -/

/-- The antisymmetrized Clifford product corresponding to a simple bivector. -/
def realCliffordBivector (x y : ZornMatrix ℝ) :
    CliffordAlgebra (zornNorm (R := ℝ)) :=
  (1 / 2 : ℝ) •
    (CliffordAlgebra.ι zornNorm x * CliffordAlgebra.ι zornNorm y -
      CliffordAlgebra.ι zornNorm y * CliffordAlgebra.ι zornNorm x)

/-- The actual Dirac operator associated with the antisymmetric product. -/
def realDiracBivector (x y : ZornMatrix ℝ) :
    Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  zornCliffordRepresentation (realCliffordBivector x y)

theorem realDiracBivector_eq (x y : ZornMatrix ℝ) :
    realDiracBivector x y =
      (1 / 2 : ℝ) • (diracGammaLinear x * diracGammaLinear y -
        diracGammaLinear y * diracGammaLinear x) := by
  simp [realDiracBivector, realCliffordBivector]

/-- Antisymmetric vector products belong to the native even Clifford submodule. -/
theorem realCliffordBivector_mem_even (x y : ZornMatrix ℝ) :
    realCliffordBivector x y ∈ CliffordAlgebra.evenOdd zornNorm 0 := by
  exact (CliffordAlgebra.evenOdd zornNorm 0).smul_mem _
    ((CliffordAlgebra.evenOdd zornNorm 0).sub_mem
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero zornNorm x y)
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero zornNorm y x))

/-- The antisymmetric Clifford product is exactly the exterior two-vector
under Mathlib's Clifford-to-exterior linear equivalence. -/
theorem realCliffordBivector_exterior [Invertible (2 : ℝ)]
    (x y : ZornMatrix ℝ) :
    CliffordAlgebra.equivExterior (zornNorm (R := ℝ)) (realCliffordBivector x y) =
      ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y := by
  change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
    ((1 / 2 : ℝ) •
      (CliffordAlgebra.ι zornNorm x * CliffordAlgebra.ι zornNorm y -
        CliffordAlgebra.ι zornNorm y * CliffordAlgebra.ι zornNorm x)) = _
  rw [map_smul, map_sub, CliffordAlgebra.changeForm_ι_mul_ι,
    CliffordAlgebra.changeForm_ι_mul_ι]
  have hsymm := QuadraticMap.associated_isSymm ℝ (-(zornNorm (R := ℝ))) x y
  rw [hsymm]
  have hyx : ExteriorAlgebra.ι ℝ y * ExteriorAlgebra.ι ℝ x =
      -(ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using (ExteriorAlgebra.ι_add_mul_swap (R := ℝ) x y)
  rw [hyx]
  module

/-- Every antisymmetric vector product preserves chirality. -/
theorem diracChirality_bivector (x y : ZornMatrix ℝ)
    (Ψ : DiracSpinor16 (R := ℝ)) :
    diracChirality (realDiracBivector x y Ψ) =
      realDiracBivector x y (diracChirality Ψ) := by
  unfold realDiracBivector
  rw [diracChirality_clifford_involute]
  congr 1
  simp [realCliffordBivector]

/-- The commutator with a simple bivector closes on the vector image.  The
polar form is twice the associated symmetric bilinear form. -/
theorem realDiracBivector_commutator_gamma (x y z : ZornMatrix ℝ) :
    realDiracBivector x y * diracGammaLinear z -
        diracGammaLinear z * realDiracBivector x y =
      diracGammaLinear
        (QuadraticMap.polar zornNorm y z • x -
          QuadraticMap.polar zornNorm x z • y) := by
  have hxy := congrArg (zornCliffordRepresentation (R := ℝ))
    (TetractysCliffordLorentzAction.bivector_commutator_preserves_vectors
      zornNorm x y z)
  have hyx := congrArg (zornCliffordRepresentation (R := ℝ))
    (TetractysCliffordLorentzAction.bivector_commutator_preserves_vectors
      zornNorm y x z)
  simp only [map_sub, map_mul, zornCliffordRepresentation_ι,
    TetractysCliffordLorentzAction.bivectorAction, map_smul] at hxy hyx
  rw [realDiracBivector_eq]
  calc
    ((1 / 2 : ℝ) • (diracGammaLinear x * diracGammaLinear y -
        diracGammaLinear y * diracGammaLinear x)) * diracGammaLinear z -
        diracGammaLinear z * ((1 / 2 : ℝ) •
          (diracGammaLinear x * diracGammaLinear y -
            diracGammaLinear y * diracGammaLinear x)) =
      (1 / 2 : ℝ) •
        ((diracGammaLinear x * diracGammaLinear y * diracGammaLinear z -
            diracGammaLinear z * diracGammaLinear x * diracGammaLinear y) -
          (diracGammaLinear y * diracGammaLinear x * diracGammaLinear z -
            diracGammaLinear z * diracGammaLinear y * diracGammaLinear x)) := by
      simp only [smul_mul_assoc, mul_smul_comm, _root_.sub_mul,
        _root_.mul_sub, smul_sub, _root_.mul_assoc]
      abel
    _ = diracGammaLinear
        (QuadraticMap.polar zornNorm y z • x -
          QuadraticMap.polar zornNorm x z • y) := by
      rw [hxy, hyx, map_sub, map_smul, map_smul]
      module

/-- Commutators of simple bivector operators are sums of simple bivector
operators.  The vector action is the already constructed polar-form action;
no commutativity of endomorphisms is assumed. -/
theorem realDiracBivector_commutator_bivector
    (x y u v : ZornMatrix ℝ) :
    realDiracBivector x y * realDiracBivector u v -
        realDiracBivector u v * realDiracBivector x y =
      realDiracBivector
        (TetractysCliffordLorentzAction.bivectorAction zornNorm x y u) v +
      realDiracBivector u
        (TetractysCliffordLorentzAction.bivectorAction zornNorm x y v) := by
  have hu := realDiracBivector_commutator_gamma x y u
  have hv := realDiracBivector_commutator_gamma x y v
  rw [realDiracBivector_eq u v, realDiracBivector_eq
    (TetractysCliffordLorentzAction.bivectorAction zornNorm x y u) v,
    realDiracBivector_eq u
      (TetractysCliffordLorentzAction.bivectorAction zornNorm x y v)]
  calc
    realDiracBivector x y *
        ((1 / 2 : ℝ) • (diracGammaLinear u * diracGammaLinear v -
          diracGammaLinear v * diracGammaLinear u)) -
        ((1 / 2 : ℝ) • (diracGammaLinear u * diracGammaLinear v -
          diracGammaLinear v * diracGammaLinear u)) * realDiracBivector x y =
      (1 / 2 : ℝ) •
        ((realDiracBivector x y * diracGammaLinear u -
            diracGammaLinear u * realDiracBivector x y) * diracGammaLinear v +
          diracGammaLinear u * (realDiracBivector x y * diracGammaLinear v -
            diracGammaLinear v * realDiracBivector x y) -
          (realDiracBivector x y * diracGammaLinear v -
            diracGammaLinear v * realDiracBivector x y) * diracGammaLinear u -
          diracGammaLinear v * (realDiracBivector x y * diracGammaLinear u -
            diracGammaLinear u * realDiracBivector x y)) := by
      simp only [smul_mul_assoc, mul_smul_comm, _root_.sub_mul,
        _root_.mul_sub, smul_add, smul_sub, _root_.mul_assoc]
      abel
    _ = _ := by
      rw [hu, hv]
      unfold TetractysCliffordLorentzAction.bivectorAction
      module

end InfoGeometry.Canonical.ZornClifford

end
