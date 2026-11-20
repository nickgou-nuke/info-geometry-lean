/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills
import InfoGeometry.Canonical.GradedConnectionBianchiBridge
import InfoGeometry.Clifford.CliffordExteriorLift

/-!
# Nonzero Graded and Even Differential Compatibility for Circular Chiral Yang–Mills

This module resolves the nonzero differential compatibility problem left open by
`InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge`:

1. **Peirce-Preserving Differential and the Strong Eigencondition No-Go**:
   For `P = chiralExteriorProj4 V` and `A = circularGaugeConnection4 ω`, the
   strong eigencondition
   `matrixExteriorDerivative d A = peirceGradingDeriv P A` holds if and only
   if `d (ω i) = ω i` for `i < 4` and `d (ω i) = -ω i` for `i ≥ 4`.
   Consequently, any square-zero differential (`d.comp d = 0`) satisfying this
   eigencondition forces `A = 0`. The compatibility contract used below is
   instead that `d` commute with the Peirce grading map; it does not prescribe
   eigenvalues for the connection coefficients.
2. **Nonzero Odd Graded Derivation (`d ≠ 0`, `A ≠ 0`, `F ≠ 0`)**:
   Constructs `circularGradedDiff : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))`
   via an upper-triangular `2 × 2` matrix lift in `ExteriorAlgebra.lift`, proves
   `circularGradedDiff ≠ 0` and `IsGradedDerivation circularGradedDiff`, exhibits
   eigenforms `uPlusForm` (`+1`) and `uMinusForm` (`-1`), proves the strong
   eigencondition on `circularGradedOmega x`, and separately obtains
   Peirce-preservation from `matrixExteriorDerivative_peirceCompatible`.
   It instantiates `circularGaugeConnection4_yang_mills_bridge`,
   and constructs an explicit nondegenerate witness with `A ≠ 0` and
   `curvatureFromConnection circularGradedDiff A ≠ 0`.
3. **Complementary Homogeneous 1-Form Even Derivation**:
   Constructs `circularEvenDiff := exteriorLift circularEvenMap` on
   `ExteriorAlgebra ℂ (Fin 4 → ℂ)`, proves `circularEvenDiff ≠ 0`,
   `MatrixIsHomogeneous 1 (circularGaugeConnection4 (circularEvenOmega x))`,
   its strong eigencondition with `peirceGradingDeriv P`, covariant vanishing
   `covariantDerivative A circularEvenDiff (genV P A A) = 0`, and a nondegenerate
   witness (`A ≠ 0`, `genV P A A ≠ 0`, `P * A ≠ A * P`).
-/

noncomputable section

open scoped BigOperators Matrix

namespace InfoGeometry.Lie

open ExteriorAlgebra
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
  (frame coordinateEquiv coordinateEquiv_apply_frame)
open InfoGeometry.Lie.SplitOctonionEllCrossChannel (uPlus uMinus)
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian (idempotencyDefect)
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge (curvatureFromConnection)
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.GradedConnectionBianchiBridge
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills
  (extBasisOneForm blade2Coeff blade2Coeff_eval chiralHodgeStar4)
open InfoGeometry.CliffordExteriorLift

/-! ## 0. Explicit Matrix Non-Commutativity Witnesses (T16) -/

/-- Explicit `2 × 2` non-commutativity witness over `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
theorem mat2_exterior_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)), A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) := !![0, 0; 1, 0]
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Explicit `4 × 4` non-commutativity witness over `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
theorem mat4_exterior_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)), A * B ≠ B * A := by
  let P := chiralExteriorProj4 (Fin 4 → ℂ)
  let B := chiralOffBlock4 (1 : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) 1
  refine ⟨P, B, ?_⟩
  intro h
  have h02 := congrFun (congrFun h 0) 2
  simp [P, B, chiralExteriorProj4, chiralProj4, chiralDiagBlock4, chiralOffBlock4,
    Matrix.mul_apply, Fin.sum_univ_four] at h02

/-! ## 1. Structural Equivalence & Square-Zero No-Go -/

/-- Two `chiralOffBlock4` matrices coincide if and only if their upper and lower `2 × 2`
blocks coincide. -/
theorem chiralOffBlock4_eq_iff {R : Type*} [Ring R]
    (U L U' L' : Matrix (Fin 2) (Fin 2) R) :
    chiralOffBlock4 U L = chiralOffBlock4 U' L' ↔ U = U' ∧ L = L' := by
  constructor
  · intro h
    constructor
    · ext i j
      fin_cases i <;> fin_cases j
      · exact congrFun (congrFun h 0) 2
      · exact congrFun (congrFun h 0) 3
      · exact congrFun (congrFun h 1) 2
      · exact congrFun (congrFun h 1) 3
    · ext i j
      fin_cases i <;> fin_cases j
      · exact congrFun (congrFun h 2) 0
      · exact congrFun (congrFun h 2) 1
      · exact congrFun (congrFun h 3) 0
      · exact congrFun (congrFun h 3) 1
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Applying `matrixExteriorDerivative d` to a `chiralOffBlock4` matrix acts blockwise. -/
theorem matrixExteriorDerivative_chiralOffBlock4
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (d : Module.End R (ExteriorAlgebra R V))
    (U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V)) :
    matrixExteriorDerivative d (chiralOffBlock4 U L) =
      chiralOffBlock4 (U.map d) (L.map d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixExteriorDerivative, chiralOffBlock4, LinearMap.map_zero]

/-- The Peirce grading derivation `[P, ·]` at `P = chiralExteriorProj4 V` fixes the upper
block `U` and negates the lower block `L` of `chiralOffBlock4 U L`. -/
theorem chiralExteriorProj4_peirceGradingDeriv_offBlock
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ V)) :
    peirceGradingDeriv (chiralExteriorProj4 V) (chiralOffBlock4 U L) =
      chiralOffBlock4 U (-L) := by
  unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralExteriorProj4, chiralProj4, chiralDiagBlock4, chiralOffBlock4]

/-- A differential is Peirce-compatible on the chiral off-diagonal sector when
it commutes with the inner grading `X ↦ [P, X]` there. This is a preservation
condition, not the strong coefficient eigencondition `d A = [P, A]`. -/
def PeirceCompatibleDifferential
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : Module.End ℂ (ExteriorAlgebra ℂ V)) : Prop :=
  ∀ U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ V),
    matrixExteriorDerivative d
        (peirceGradingDeriv (chiralExteriorProj4 V) (chiralOffBlock4 U L)) =
      peirceGradingDeriv (chiralExteriorProj4 V)
        (matrixExteriorDerivative d (chiralOffBlock4 U L))

/-- Any componentwise linear differential commutes with the chiral Peirce
grading on the entire off-diagonal sector. The proof uses the block formula
`δ_P(U,L) = (U,-L)` and the fact that `Matrix.map` preserves negation. -/
theorem matrixExteriorDerivative_peirceCompatible
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : Module.End ℂ (ExteriorAlgebra ℂ V)) :
    PeirceCompatibleDifferential d := by
  intro U L
  calc
    matrixExteriorDerivative d
        (peirceGradingDeriv (chiralExteriorProj4 V) (chiralOffBlock4 U L)) =
        chiralOffBlock4 (U.map d) ((-L).map d) := by
          rw [chiralExteriorProj4_peirceGradingDeriv_offBlock,
            matrixExteriorDerivative_chiralOffBlock4]
    _ = chiralOffBlock4 (U.map d) (-(L.map d)) := by
          congr 1
          ext i j
          simp
    _ = peirceGradingDeriv (chiralExteriorProj4 V)
          (matrixExteriorDerivative d (chiralOffBlock4 U L)) := by
          rw [matrixExteriorDerivative_chiralOffBlock4,
            chiralExteriorProj4_peirceGradingDeriv_offBlock]

/-- On the same circular connection, Peirce preservation and the ordinary
graded-connection Bianchi identity coexist for a genuine square-zero
`ExteriorDifferentialData`. The only connection-specific input is its
homogeneous one-form proof; the curvature is `dA + A²`. -/
theorem circularGaugeConnection4_peirce_preservation_and_bianchi
    (D : ExteriorDifferentialData ℂ (Fin 4 → ℂ))
    (ω : Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (hA : MatrixIsHomogeneous 1 (circularGaugeConnection4 ω)) :
    PeirceCompatibleDifferential D.d ∧
      covariantDerivative (circularGaugeConnection4 ω) D.d
        (curvatureFromConnection D.d (circularGaugeConnection4 ω)) = 0 := by
  exact ⟨matrixExteriorDerivative_peirceCompatible D.d,
    graded_connection_curvature_bianchi D (circularGaugeConnection4 ω) hA⟩

/-- Block characterization of the strong derivative eigencondition on
`chiralOffBlock4 U L`. -/
theorem chiralOffBlock4_eigencondition_iff
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : Module.End ℂ (ExteriorAlgebra ℂ V))
    (U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ V)) :
    matrixExteriorDerivative d (chiralOffBlock4 U L) =
        peirceGradingDeriv (chiralExteriorProj4 V) (chiralOffBlock4 U L) ↔
      (U.map d = U ∧ L.map d = -L) := by
  rw [matrixExteriorDerivative_chiralOffBlock4, chiralExteriorProj4_peirceGradingDeriv_offBlock]
  exact chiralOffBlock4_eq_iff (U.map d) (L.map d) U (-L)

private lemma add_eq_and_sub_eq_resolve {V : Type*} [AddCommGroup V] [Module ℂ V]
    {x y a b : ExteriorAlgebra ℂ V}
    (hadd : x + y = a + b) (hsub : x - y = a - b) :
    x = a ∧ y = b := by
  have h2x : (2 : ℂ) • x = (2 : ℂ) • a := by
    have hsum : x + x = a + a := by
      calc
        x + x = (x + y) + (x - y) := by abel
        _ = (a + b) + (a - b) := by rw [hadd, hsub]
        _ = a + a := by abel
    rw [← one_add_one_eq_two, add_smul, one_smul, add_smul, one_smul]
    exact hsum
  have hx : x = a := by
    have h := congrArg (fun z => (2 : ℂ)⁻¹ • z) h2x
    simpa [smul_smul] using h
  have hy : y = b := by
    rw [hx] at hadd
    exact add_left_cancel hadd
  exact ⟨hx, hy⟩

private lemma complex_I_smul_cancel {V : Type*} [AddCommGroup V] [Module ℂ V]
    {x y : ExteriorAlgebra ℂ V}
    (h : Complex.I • x = Complex.I • y) : x = y := by
  have h' := congrArg (fun z => (-Complex.I) • z) h
  simpa [smul_smul] using h'

/-- Exact component characterization of the strong derivative eigencondition
`matrixExteriorDerivative d A = peirceGradingDeriv P A` for
`A = circularGaugeConnection4 ω` and `P = chiralExteriorProj4 V`. -/
theorem circularGaugeConnection4_eigencondition_iff
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : Module.End ℂ (ExteriorAlgebra ℂ V))
    (ω : Fin 8 → ExteriorAlgebra ℂ V) :
    matrixExteriorDerivative d (circularGaugeConnection4 ω) =
        peirceGradingDeriv (chiralExteriorProj4 V) (circularGaugeConnection4 ω) ↔
      (∀ i : Fin 8, d (ω i) = if i.val < 4 then ω i else -ω i) := by
  unfold circularGaugeConnection4
  rw [chiralOffBlock4_eigencondition_iff]
  constructor
  · rintro ⟨hU, hL⟩
    have hU00 : d (ω 0) + d (ω 3) = ω 0 + ω 3 := by
      have h := congrFun (congrFun hU 0) 0
      simpa [weylUpperExt, map_add] using h
    have hU11 : d (ω 0) - d (ω 3) = ω 0 - ω 3 := by
      have h := congrFun (congrFun hU 1) 1
      simpa [weylUpperExt, map_sub] using h
    have hU01 : d (ω 1) - Complex.I • d (ω 2) = ω 1 - Complex.I • ω 2 := by
      have h := congrFun (congrFun hU 0) 1
      simpa [weylUpperExt, map_sub, map_smul] using h
    have hU10 : d (ω 1) + Complex.I • d (ω 2) = ω 1 + Complex.I • ω 2 := by
      have h := congrFun (congrFun hU 1) 0
      simpa [weylUpperExt, map_add, map_smul] using h
    have hL00 : d (ω 4) - d (ω 7) = -(ω 4) - -(ω 7) := by
      have h := congrFun (congrFun hL 0) 0
      simp only [weylLowerExt, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply,
        Matrix.cons_val_zero, map_sub] at h
      rw [h]
      abel
    have hL11 : d (ω 4) + d (ω 7) = -(ω 4) + -(ω 7) := by
      have h := congrFun (congrFun hL 1) 1
      simp only [weylLowerExt, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero, map_add] at h
      rw [h]
      abel
    have hL01 : -d (ω 5) + Complex.I • d (ω 6) = ω 5 + Complex.I • -(ω 6) := by
      have h := congrFun (congrFun hL 0) 1
      simp only [weylLowerExt, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_neg, map_smul] at h
      rw [h]
      simp only [smul_neg]
      abel
    have hL10 : -d (ω 5) - Complex.I • d (ω 6) = ω 5 - Complex.I • -(ω 6) := by
      have h := congrFun (congrFun hL 1) 0
      simp only [weylLowerExt, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero, map_sub, map_neg, map_smul] at h
      rw [h]
      simp only [smul_neg]
      abel
    rcases add_eq_and_sub_eq_resolve hU00 hU11 with ⟨h0, h3⟩
    rcases add_eq_and_sub_eq_resolve hU10 hU01 with ⟨h1, hI2⟩
    have h2 : d (ω 2) = ω 2 := complex_I_smul_cancel hI2
    rcases add_eq_and_sub_eq_resolve hL11 hL00 with ⟨h4, h7⟩
    rcases add_eq_and_sub_eq_resolve hL01 hL10 with ⟨hn5, hI6⟩
    have h5 : d (ω 5) = -ω 5 := neg_eq_iff_eq_neg.mp hn5
    have h6 : d (ω 6) = -ω 6 := complex_I_smul_cancel hI6
    intro i
    fin_cases i <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · intro hω
    have h0 : d (ω 0) = ω 0 := by simpa using hω 0
    have h1 : d (ω 1) = ω 1 := by simpa using hω 1
    have h2 : d (ω 2) = ω 2 := by simpa using hω 2
    have h3 : d (ω 3) = ω 3 := by simpa using hω 3
    have h4 : d (ω 4) = -ω 4 := by simpa using hω 4
    have h5 : d (ω 5) = -ω 5 := by simpa using hω 5
    have h6 : d (ω 6) = -ω 6 := by simpa using hω 6
    have h7 : d (ω 7) = -ω 7 := by simpa using hω 7
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [weylUpperExt, map_add, map_sub, map_smul, h0, h1, h2, h3]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [weylLowerExt, map_add, map_sub, map_neg, map_smul, h4, h5, h6, h7] <;>
        abel

/-- Square-zero no-go theorem for the strong derivative eigencondition: if `d² = 0`
and `d A = [P,A]` for `P = chiralExteriorProj4 V` and
`A = circularGaugeConnection4 ω`, then `A = 0`. This is not the
Peirce-preservation compatibility condition `PeirceCompatibleDifferential`. -/
theorem circularGaugeConnection4_sq_zero_eigencondition_forces_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : Module.End ℂ (ExteriorAlgebra ℂ V))
    (ω : Fin 8 → ExteriorAlgebra ℂ V)
    (hd2 : d.comp d = 0)
    (hcompat : matrixExteriorDerivative d (circularGaugeConnection4 ω) =
      peirceGradingDeriv (chiralExteriorProj4 V) (circularGaugeConnection4 ω)) :
    circularGaugeConnection4 ω = 0 := by
  have hd_zero : ∀ z : ExteriorAlgebra ℂ V, d (d z) = 0 := by
    intro z
    have h := congrArg (fun f : Module.End ℂ (ExteriorAlgebra ℂ V) => f z) hd2
    simpa [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hblocks := (chiralOffBlock4_eigencondition_iff d
    (weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3))
    (weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7))).mp hcompat
  rcases hblocks with ⟨hU, hL⟩
  have hU0 : weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3) = 0 := by
    ext i j
    have hij : d (weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3) i j) =
        weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3) i j := congrFun (congrFun hU i) j
    calc
      weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3) i j
        = d (weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3) i j) := hij.symm
      _ = d (d (weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3) i j)) := congrArg d hij.symm
      _ = 0 := hd_zero _
  have hL0 : weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) = 0 := by
    ext i j
    have hij : d (weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) i j) =
        -(weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) i j) := congrFun (congrFun hL i) j
    have hneg : weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) i j =
        -(d (weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) i j)) := by
      rw [hij, neg_neg]
    calc
      weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) i j
        = d (-(weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) i j)) := by rw [map_neg, ← hneg]
      _ = d (d (weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7) i j)) := congrArg d hij.symm
      _ = 0 := hd_zero _
  change chiralOffBlock4 (weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3))
    (weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7)) = 0
  rw [hU0, hL0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

/-! ## 2. Nonzero Odd Graded Derivation (`d ≠ 0`, `A ≠ 0`, `F ≠ 0`) -/

private lemma ι_comm_ι_mul_ι (v a b : Fin 4 → ℂ) :
    ι ℂ v * (ι ℂ a * ι ℂ b) = (ι ℂ a * ι ℂ b) * ι ℂ v := by
  have h1 : ι ℂ v * ι ℂ a = -(ι ℂ a * ι ℂ v) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v a)
  have h2 : ι ℂ v * ι ℂ b = -(ι ℂ b * ι ℂ v) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v b)
  calc
    ι ℂ v * (ι ℂ a * ι ℂ b) = (ι ℂ v * ι ℂ a) * ι ℂ b := (mul_assoc _ _ _).symm
    _ = -(ι ℂ a * ι ℂ v) * ι ℂ b := by rw [h1]
    _ = -(ι ℂ a * (ι ℂ v * ι ℂ b)) := by rw [neg_mul, mul_assoc]
    _ = -(ι ℂ a * -(ι ℂ b * ι ℂ v)) := by rw [h2]
    _ = (ι ℂ a * ι ℂ b) * ι ℂ v := by rw [mul_neg, neg_neg, mul_assoc]

/-- Target linear map `(Fin 4 → ℂ) →ₗ[ℂ] ExteriorAlgebra ℂ (Fin 4 → ℂ)` defining
`circularGradedDiff` on degree-1 generators `ι ℂ v`. -/
noncomputable def circularGradedTargetMap :
    (Fin 4 → ℂ) →ₗ[ℂ] ExteriorAlgebra ℂ (Fin 4 → ℂ) where
  toFun v :=
    v 0 • (1 : ExteriorAlgebra ℂ (Fin 4 → ℂ)) +
    v 1 • (ι ℂ (Pi.single 0 (1 : ℂ)) * ι ℂ (Pi.single 1 (1 : ℂ))) +
    v 2 • (1 : ExteriorAlgebra ℂ (Fin 4 → ℂ)) +
    v 3 • (ι ℂ (Pi.single 2 (1 : ℂ)) * ι ℂ (Pi.single 3 (1 : ℂ)))
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c x := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]

private lemma ι_mul_circularGradedTargetMap (v : Fin 4 → ℂ) :
    ι ℂ v * circularGradedTargetMap v = circularGradedTargetMap v * ι ℂ v := by
  dsimp [circularGradedTargetMap]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
    ι_comm_ι_mul_ι]

private noncomputable def circularGradedLiftMatrix :
    (Fin 4 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) where
  toFun v := !![-(ι ℂ v), circularGradedTargetMap v; 0, ι ℂ v]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [map_add]; try abel)
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_smul, smul_neg]

private lemma circularGradedLiftMatrix_sq_zero (v : Fin 4 → ℂ) :
    circularGradedLiftMatrix v * circularGradedLiftMatrix v = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularGradedLiftMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      neg_mul, ι_mul_circularGradedTargetMap]

private noncomputable def circularGradedLift :
    ExteriorAlgebra ℂ (Fin 4 → ℂ) →ₐ[ℂ]
      Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  ExteriorAlgebra.lift ℂ ⟨circularGradedLiftMatrix, circularGradedLiftMatrix_sq_zero⟩

private lemma circularGradedLift_lower_row (y : ExteriorAlgebra ℂ (Fin 4 → ℂ)) :
    (circularGradedLift y) 1 1 = y ∧ (circularGradedLift y) 1 0 = 0 := by
  refine ExteriorAlgebra.induction (C := fun y =>
    (circularGradedLift y) 1 1 = y ∧ (circularGradedLift y) 1 0 = 0) ?_ ?_ ?_ ?_ y
  · intro r
    simp [circularGradedLift, Matrix.algebraMap_matrix_apply]
  · intro m
    rw [circularGradedLift, ExteriorAlgebra.lift_ι_apply]
    simp [circularGradedLiftMatrix]
  · intro a b ha hb
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [ha.1, ha.2, hb.1, hb.2]
  · intro a b ha hb
    rw [map_add]
    simp [ha.1, ha.2, hb.1, hb.2]

private lemma circularGradedLift_zero_zero_prod :
    ∀ (k : ℕ) (v : Fin k → (Fin 4 → ℂ)),
      (circularGradedLift (List.prod (List.ofFn (fun i => ι ℂ (v i))))) 0 0 =
        ((-1 : ℂ) ^ k) • List.prod (List.ofFn (fun i => ι ℂ (v i)))
  | 0, v => by
    simp [circularGradedLift]
  | k + 1, v => by
    rw [List.ofFn_succ, List.prod_cons, map_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have htail_row := (circularGradedLift_lower_row
      (List.prod (List.ofFn (fun i : Fin k => ι ℂ (v i.succ))))).2
    have ih := circularGradedLift_zero_zero_prod k (fun i => v i.succ)
    have hhead : (circularGradedLift (ι ℂ (v 0))) 0 0 = -(ι ℂ (v 0)) := by
      rw [circularGradedLift, ExteriorAlgebra.lift_ι_apply]
      simp [circularGradedLiftMatrix]
    rw [htail_row, mul_zero, add_zero, hhead, ih]
    rw [neg_mul, mul_smul_comm, ← neg_one_smul ℂ, smul_smul, pow_succ']

private lemma circularGradedLift_zero_zero_of_homogeneous (k : ℕ)
    (x : ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (hx : IsHomogeneousExteriorDegree k x) :
    (circularGradedLift x) 0 0 = ((-1 : ℂ) ^ k) • x := by
  change x ∈ Submodule.span ℂ
    (Set.range (fun (v : Fin k → (Fin 4 → ℂ)) => List.prod (List.ofFn (fun i => ι ℂ (v i)))))
    at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨v, rfl⟩
    exact circularGradedLift_zero_zero_prod k v
  · simp [map_zero]
  · intro a b _ _ ha hb
    rw [map_add, Matrix.add_apply, ha, hb, smul_add]
  · intro c a _ ha
    rw [map_smul, Matrix.smul_apply, ha, smul_comm]

/-- Nonzero odd graded exterior derivation on `ExteriorAlgebra ℂ (Fin 4 → ℂ)` constructed
via the `(0, 1)` entry of the upper-triangular `2 × 2` algebra lift `circularGradedLift`. -/
noncomputable def circularGradedDiff : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) where
  toFun x := (circularGradedLift x) 0 1
  map_add' x y := by simp [map_add]
  map_smul' c x := by simp [map_smul]

/-- Action of `circularGradedDiff` on degree-1 generators `ι ℂ v`. -/
theorem circularGradedDiff_ι (v : Fin 4 → ℂ) :
    circularGradedDiff (ι ℂ v) = circularGradedTargetMap v := by
  change (circularGradedLift (ι ℂ v)) 0 1 = circularGradedTargetMap v
  rw [circularGradedLift, ExteriorAlgebra.lift_ι_apply]
  simp [circularGradedLiftMatrix]

/-- `circularGradedDiff` is nonzero: it sends `dx₀ = ι ℂ (Pi.single 0 1)` to `1 ≠ 0`. -/
theorem circularGradedDiff_ne_zero : circularGradedDiff ≠ 0 := by
  intro hz
  have h0 := congrArg (fun d : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) =>
    d (ι ℂ (Pi.single 0 (1 : ℂ)))) hz
  rw [circularGradedDiff_ι] at h0
  have h1 : (1 : ExteriorAlgebra ℂ (Fin 4 → ℂ)) = 0 := by
    simp [circularGradedTargetMap] at h0
  exact one_ne_zero h1

/-- `circularGradedDiff` satisfies the full graded Leibniz rule `IsGradedDerivation`. -/
theorem circularGradedDiff_isGradedDerivation :
    IsGradedDerivation circularGradedDiff := by
  intro k x y hx
  change (circularGradedLift (x * y)) 0 1 =
    (circularGradedLift x) 0 1 * y + ((-1 : ℂ) ^ k) • (x * (circularGradedLift y) 0 1)
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [circularGradedLift_zero_zero_of_homogeneous k x hx]
  rw [(circularGradedLift_lower_row y).1]
  rw [smul_mul_assoc, add_comm]

/-- Plus-eigenform `dx₀ ∧ dx₁ + dx₁` with eigenvalue `+1` under `circularGradedDiff`. -/
noncomputable def uPlusForm : ExteriorAlgebra ℂ (Fin 4 → ℂ) :=
  ι ℂ (Pi.single 0 (1 : ℂ)) * ι ℂ (Pi.single 1 (1 : ℂ)) + ι ℂ (Pi.single 1 (1 : ℂ))

/-- Minus-eigenform `dx₂ ∧ dx₃ - dx₃` with eigenvalue `-1` under `circularGradedDiff`. -/
noncomputable def uMinusForm : ExteriorAlgebra ℂ (Fin 4 → ℂ) :=
  ι ℂ (Pi.single 2 (1 : ℂ)) * ι ℂ (Pi.single 3 (1 : ℂ)) - ι ℂ (Pi.single 3 (1 : ℂ))

theorem circularGradedDiff_uPlusForm :
    circularGradedDiff uPlusForm = uPlusForm := by
  have hdeg0 :
      IsHomogeneousExteriorDegree 1 (ι ℂ (Pi.single (0 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)) :=
    (homogeneous_one_iff_exists_generator _).mpr ⟨_, rfl⟩
  have hd0 : circularGradedDiff (ι ℂ (Pi.single (0 : Fin 4) (1 : ℂ))) = 1 := by
    rw [circularGradedDiff_ι]
    simp [circularGradedTargetMap]
  have hd1 : circularGradedDiff (ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ))) =
      ι ℂ (Pi.single 0 (1 : ℂ)) * ι ℂ (Pi.single 1 (1 : ℂ)) := by
    rw [circularGradedDiff_ι]
    simp [circularGradedTargetMap]
  have hd01 : circularGradedDiff (ι ℂ (Pi.single 0 (1 : ℂ)) * ι ℂ (Pi.single 1 (1 : ℂ))) =
      ι ℂ (Pi.single 1 (1 : ℂ)) := by
    rw [circularGradedDiff_isGradedDerivation 1 _ _ hdeg0, hd0, hd1, one_mul, pow_one,
      neg_one_smul, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
    simp
  unfold uPlusForm
  rw [map_add, hd01, hd1, add_comm]

theorem circularGradedDiff_uMinusForm :
    circularGradedDiff uMinusForm = -uMinusForm := by
  have hdeg2 :
      IsHomogeneousExteriorDegree 1 (ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)) :=
    (homogeneous_one_iff_exists_generator _).mpr ⟨_, rfl⟩
  have hd2 : circularGradedDiff (ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ))) = 1 := by
    rw [circularGradedDiff_ι]
    simp [circularGradedTargetMap]
  have hd3 : circularGradedDiff (ι ℂ (Pi.single (3 : Fin 4) (1 : ℂ))) =
      ι ℂ (Pi.single 2 (1 : ℂ)) * ι ℂ (Pi.single 3 (1 : ℂ)) := by
    rw [circularGradedDiff_ι]
    simp [circularGradedTargetMap]
  have hd23 : circularGradedDiff (ι ℂ (Pi.single 2 (1 : ℂ)) * ι ℂ (Pi.single 3 (1 : ℂ))) =
      ι ℂ (Pi.single 3 (1 : ℂ)) := by
    rw [circularGradedDiff_isGradedDerivation 1 _ _ hdeg2, hd2, hd3, one_mul, pow_one,
      neg_one_smul, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
    simp
  unfold uMinusForm
  rw [map_sub, hd23, hd3]
  abel

/-- Circular 8-component mixed-degree form assignment driving the strong derivative
eigencondition for `circularGradedDiff` on `circularGaugeConnection4`. -/
noncomputable def circularGradedOmega (x : Coordinate) :
    Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ) :=
  fun i => if i.val < 4 then (x i : ℂ) • uPlusForm else (x i : ℂ) • uMinusForm

/-- For every `x : Coordinate`, `circularGradedDiff` satisfies the strong derivative
eigencondition `matrixExteriorDerivative circularGradedDiff A = peirceGradingDeriv P A`. -/
theorem circularGradedDiff_eigencondition (x : Coordinate) :
    matrixExteriorDerivative circularGradedDiff
        (circularGaugeConnection4 (circularGradedOmega x)) =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularGradedOmega x)) := by
  rw [circularGaugeConnection4_eigencondition_iff]
  intro i
  by_cases hi : i.val < 4
  · simp only [circularGradedOmega, hi, ↓reduceIte, LinearMap.map_smul,
      circularGradedDiff_uPlusForm]
  · simp only [circularGradedOmega, hi, ↓reduceIte, LinearMap.map_smul,
      circularGradedDiff_uMinusForm, smul_neg]

/-- General instantiation of `circularGaugeConnection4_yang_mills_bridge` for `circularGradedDiff`
with its strong derivative eigencondition discharged. -/
theorem circularGradedDiff_yang_mills_bridge_general
    (star : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    (x : Coordinate)
    (X : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularGradedOmega x)
    genPhi P A A = A ∧
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X ∧
    curvatureFromConnection circularGradedDiff A = genJ P A A + genV P A A ∧
    evenGrade P (curvatureFromConnection circularGradedDiff A) = genV P A A ∧
    curvatureFromConnection 0 A = genV P A A ∧
    covariantDerivative A 0 (genV P A A) = 0 ∧
    (isSelfDualCurvature star (genV P A A) →
      covariantDerivative A 0 (matrixHodgeStar star (curvatureFromConnection 0 A)) = 0) := by
  intro P A
  have hBridge := circularGaugeConnection4_yang_mills_bridge
    star circularGradedDiff (circularGradedOmega x) X
  dsimp only at hBridge
  have hEigencondition := circularGradedDiff_eigencondition x
  have hCurv := hBridge.2.2.1 hEigencondition
  exact ⟨hBridge.1, hBridge.2.1, hCurv.1, hCurv.2,
    hBridge.2.2.2.1, hBridge.2.2.2.2.1, hBridge.2.2.2.2.2⟩

/-- Specialized instantiation of `circularGaugeConnection4_yang_mills_bridge` with
`star := chiralHodgeStar4` and `X := circularGaugeConnection4 (circularGradedOmega x)`. -/
theorem circularGradedDiff_yang_mills_bridge (x : Coordinate) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularGradedOmega x)
    genPhi P A A = A ∧
    evenGrade P (idempotencyDefect A) - idempotencyDefect (evenGrade P A) = genV P A A ∧
    curvatureFromConnection circularGradedDiff A = genJ P A A + genV P A A ∧
    evenGrade P (curvatureFromConnection circularGradedDiff A) = genV P A A ∧
    curvatureFromConnection 0 A = genV P A A ∧
    covariantDerivative A 0 (genV P A A) = 0 ∧
    (isSelfDualCurvature chiralHodgeStar4 (genV P A A) →
      covariantDerivative A 0
        (matrixHodgeStar chiralHodgeStar4 (curvatureFromConnection 0 A)) = 0) :=
  circularGradedDiff_yang_mills_bridge_general chiralHodgeStar4 x
    (circularGaugeConnection4 (circularGradedOmega x))

private def proj13 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![0, v 1, 0, v 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

private lemma proj13_single (μ : Fin 4) :
    proj13 (Pi.single μ (1 : ℂ)) =
      if μ = 1 ∨ μ = 3 then Pi.single μ (1 : ℂ) else 0 := by
  ext i
  fin_cases μ <;> fin_cases i <;> simp [proj13]

private lemma uPlusForm_ne_zero : uPlusForm ≠ 0 := by
  intro h
  have hc := congrArg (blade2Coeff 0 1) h
  have hev01 := (blade2Coeff_eval 0 1 0 1 0).1
  have hev1 := (blade2Coeff_eval 0 1 1 0 0).2.1
  rw [map_zero] at hc
  unfold uPlusForm at hc
  change blade2Coeff 0 1 (extBasisOneForm 0 * extBasisOneForm 1 + extBasisOneForm 1) = 0 at hc
  rw [map_add, hev01, hev1] at hc
  norm_num at hc

private lemma uPlusForm_mul_uMinusForm_ne_zero :
    uPlusForm * uMinusForm ≠ 0 := by
  intro h
  have hmap := congrArg (ExteriorAlgebra.map proj13) h
  have hp : ExteriorAlgebra.map proj13 uPlusForm = extBasisOneForm 1 := by
    unfold uPlusForm
    rw [map_add, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
      proj13_single 0, proj13_single 1]
    simp [extBasisOneForm]
  have hm : ExteriorAlgebra.map proj13 uMinusForm = -(extBasisOneForm 3) := by
    unfold uMinusForm
    rw [map_sub, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
      proj13_single 2, proj13_single 3]
    simp [extBasisOneForm]
  rw [map_mul, hp, hm, map_zero, mul_neg] at hmap
  have hc := congrArg (blade2Coeff 1 3) hmap
  have hev := (blade2Coeff_eval 1 3 1 3 0).1
  rw [map_neg, map_zero, hev] at hc
  norm_num at hc

/-- Nondegenerate witness at `x₀ = coordinateEquiv (uPlus + uMinus)` showing `A ≠ 0`,
`curvatureFromConnection circularGradedDiff A ≠ 0`, `genJ P A A ≠ 0`, `genV P A A ≠ 0`,
and the strong derivative eigencondition simultaneously. -/
theorem circularGradedDiff_nondegenerate_witness :
    ∃ x : Coordinate,
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let A := circularGaugeConnection4 (circularGradedOmega x)
      A ≠ 0 ∧
      curvatureFromConnection circularGradedDiff A ≠ 0 ∧
      matrixExteriorDerivative circularGradedDiff A = peirceGradingDeriv P A ∧
      genJ P A A ≠ 0 ∧
      genV P A A ≠ 0 := by
  let x₀ : Coordinate := coordinateEquiv (uPlus + uMinus)
  refine ⟨x₀, ?_⟩
  have hx0 : x₀ = Pi.single 0 1 + Pi.single 4 1 := by
    have h0 : coordinateEquiv uPlus = Pi.single 0 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 0
    have h4 : coordinateEquiv uMinus = Pi.single 4 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 4
    calc
      x₀ = coordinateEquiv (uPlus + uMinus) := rfl
      _ = coordinateEquiv uPlus + coordinateEquiv uMinus :=
        LinearEquiv.map_add coordinateEquiv uPlus uMinus
      _ = Pi.single 0 1 + Pi.single 4 1 := by rw [h0, h4]
  have hω : ∀ i : Fin 8, circularGradedOmega x₀ i =
      if i = 0 then uPlusForm else if i = 4 then uMinusForm else 0 := by
    intro i
    fin_cases i <;> simp [circularGradedOmega, hx0]
  have hA02 : circularGaugeConnection4 (circularGradedOmega x₀) 0 2 = uPlusForm := by
    simp [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 0, hω 3]
  have hA20 : circularGaugeConnection4 (circularGradedOmega x₀) 2 0 = uMinusForm := by
    simp [circularGaugeConnection4, chiralOffBlock4, weylLowerExt, hω 4, hω 7]
  have hA_ne : circularGaugeConnection4 (circularGradedOmega x₀) ≠ 0 := by
    intro hz
    have h02 := congrFun (congrFun hz 0) 2
    rw [hA02, Matrix.zero_apply] at h02
    exact uPlusForm_ne_zero h02
  have hEigencondition := circularGradedDiff_eigencondition x₀
  have hBridge := circularGradedDiff_yang_mills_bridge x₀
  dsimp only at hBridge
  have hGenJ02 : genJ (chiralExteriorProj4 (Fin 4 → ℂ))
      (circularGaugeConnection4 (circularGradedOmega x₀))
      (circularGaugeConnection4 (circularGradedOmega x₀)) 0 2 = uPlusForm := by
    unfold circularGaugeConnection4 chiralExteriorProj4
    rw [genJ, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4]
    simp [chiralOffBlock4, weylUpperExt, hω 0, hω 3]
  have hGenJ_ne : genJ (chiralExteriorProj4 (Fin 4 → ℂ))
      (circularGaugeConnection4 (circularGradedOmega x₀))
      (circularGaugeConnection4 (circularGradedOmega x₀)) ≠ 0 := by
    intro hz
    have h02 := congrFun (congrFun hz 0) 2
    rw [hGenJ02, Matrix.zero_apply] at h02
    exact uPlusForm_ne_zero h02
  have hGenV_eq : genV (chiralExteriorProj4 (Fin 4 → ℂ))
      (circularGaugeConnection4 (circularGradedOmega x₀))
      (circularGaugeConnection4 (circularGradedOmega x₀)) =
      circularGaugeConnection4 (circularGradedOmega x₀) *
        circularGaugeConnection4 (circularGradedOmega x₀) := by
    unfold circularGaugeConnection4 chiralExteriorProj4
    rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hAA00 : (circularGaugeConnection4 (circularGradedOmega x₀) *
      circularGaugeConnection4 (circularGradedOmega x₀)) 0 0 = uPlusForm * uMinusForm := by
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    have hA00 : circularGaugeConnection4 (circularGradedOmega x₀) 0 0 = 0 := by
      simp [circularGaugeConnection4, chiralOffBlock4]
    have hA01 : circularGaugeConnection4 (circularGradedOmega x₀) 0 1 = 0 := by
      simp [circularGaugeConnection4, chiralOffBlock4]
    have hA03 : circularGaugeConnection4 (circularGradedOmega x₀) 0 3 = 0 := by
      simp [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 1, hω 2]
    rw [hA00, hA01, hA02, hA03, hA20]
    simp
  have hGenV_ne : genV (chiralExteriorProj4 (Fin 4 → ℂ))
      (circularGaugeConnection4 (circularGradedOmega x₀))
      (circularGaugeConnection4 (circularGradedOmega x₀)) ≠ 0 := by
    intro hz
    rw [hGenV_eq] at hz
    have h00 := congrFun (congrFun hz 0) 0
    rw [hAA00, Matrix.zero_apply] at h00
    exact uPlusForm_mul_uMinusForm_ne_zero h00
  have hCurv_ne : curvatureFromConnection circularGradedDiff
      (circularGaugeConnection4 (circularGradedOmega x₀)) ≠ 0 := by
    intro hz
    have h00 := congrFun (congrFun hz 0) 0
    rw [hBridge.2.2.1] at h00
    have h00' : (genJ (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularGradedOmega x₀))
        (circularGaugeConnection4 (circularGradedOmega x₀)) +
        genV (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularGradedOmega x₀))
        (circularGaugeConnection4 (circularGradedOmega x₀))) 0 0 = 0 := by
      simpa using h00
    have hJ00 : genJ (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularGradedOmega x₀))
        (circularGaugeConnection4 (circularGradedOmega x₀)) 0 0 = 0 := by
      unfold circularGaugeConnection4 chiralExteriorProj4
      rw [genJ, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4]
      simp [chiralOffBlock4]
    rw [Matrix.add_apply, hJ00, zero_add, hGenV_eq, hAA00] at h00'
    exact uPlusForm_mul_uMinusForm_ne_zero h00'
  exact ⟨hA_ne, hCurv_ne, hEigencondition, hGenJ_ne, hGenV_ne⟩

/-! ## 3. Complementary Homogeneous 1-Form Even Derivation -/

/-- Diagonal involution `diag(1, 1, -1, -1)` on `Fin 4 → ℂ`. -/
def circularEvenMap : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := fun i => if i.val < 2 then v i else -v i
  map_add' x y := by
    ext i
    fin_cases i <;> (simp; try abel)
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

/-- Even exterior derivation `CliffordExteriorLift.exteriorLift circularEvenMap`. -/
noncomputable def circularEvenDiff : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  exteriorLift circularEvenMap

/-- Action of `circularEvenDiff` on degree-1 generators `ι ℂ v`. -/
theorem circularEvenDiff_ι (v : Fin 4 → ℂ) :
    circularEvenDiff (ι ℂ v) = ι ℂ (circularEvenMap v) := by
  dsimp [circularEvenDiff]
  exact exteriorLift_ι circularEvenMap v

private lemma circularEvenMap_single0 :
    circularEvenMap (Pi.single (0 : Fin 4) (1 : ℂ)) = Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [circularEvenMap]

private lemma circularEvenMap_single2 :
    circularEvenMap (Pi.single (2 : Fin 4) (1 : ℂ)) = -Pi.single 2 1 := by
  ext i
  fin_cases i <;> simp [circularEvenMap]

/-- `circularEvenDiff` is nonzero on `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
theorem circularEvenDiff_ne_zero : circularEvenDiff ≠ 0 := by
  intro hz
  have h0 := congrArg (fun d : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) =>
    d (ι ℂ (Pi.single (0 : Fin 4) (1 : ℂ)))) hz
  have hev : circularEvenDiff (ι ℂ (Pi.single (0 : Fin 4) (1 : ℂ))) =
      ι ℂ (Pi.single (0 : Fin 4) (1 : ℂ)) := by
    dsimp [circularEvenDiff]
    rw [exteriorLift_ι, circularEvenMap_single0]
  rw [hev, LinearMap.zero_apply] at h0
  have hsingle : (Pi.single (0 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) = 0 :=
    (ExteriorAlgebra.ι_eq_zero_iff (R := ℂ) (Pi.single (0 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)).mp h0
  have h1 := congrFun hsingle 0
  simp at h1

/-- Homogeneous 1-form circular connection components driven by `circularEvenDiff`. -/
noncomputable def circularEvenOmega (x : Coordinate) :
    Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ) :=
  fun i =>
    if i.val < 4 then (x i : ℂ) • ι ℂ (Pi.single 0 (1 : ℂ))
    else (x i : ℂ) • ι ℂ (Pi.single 2 (1 : ℂ))

private lemma circularEvenOmega_deg1 (x : Coordinate) (i : Fin 8) :
    IsHomogeneousExteriorDegree 1 (circularEvenOmega x i) := by
  by_cases hi : i.val < 4
  · refine (homogeneous_one_iff_exists_generator _).mpr
      ⟨(x i : ℂ) • (Pi.single (0 : Fin 4) (1 : ℂ) : Fin 4 → ℂ), ?_⟩
    simp only [circularEvenOmega, hi, ↓reduceIte, LinearMap.map_smul]
  · refine (homogeneous_one_iff_exists_generator _).mpr
      ⟨(x i : ℂ) • (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ), ?_⟩
    simp only [circularEvenOmega, hi, ↓reduceIte, LinearMap.map_smul]

private lemma isHomogeneous_sub_mem {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {k : ℕ} {a b : ExteriorAlgebra R V}
    (ha : IsHomogeneousExteriorDegree k a) (hb : IsHomogeneousExteriorDegree k b) :
    IsHomogeneousExteriorDegree k (a - b) :=
  Submodule.sub_mem _ ha hb

private lemma isHomogeneous_add_mem {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {k : ℕ} {a b : ExteriorAlgebra R V}
    (ha : IsHomogeneousExteriorDegree k a) (hb : IsHomogeneousExteriorDegree k b) :
    IsHomogeneousExteriorDegree k (a + b) :=
  Submodule.add_mem _ ha hb

private lemma isHomogeneous_neg_mem {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {k : ℕ} {a : ExteriorAlgebra R V}
    (ha : IsHomogeneousExteriorDegree k a) :
    IsHomogeneousExteriorDegree k (-a) :=
  Submodule.neg_mem _ ha

private lemma isHomogeneous_smul_mem {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {k : ℕ} (c : R) {a : ExteriorAlgebra R V}
    (ha : IsHomogeneousExteriorDegree k a) :
    IsHomogeneousExteriorDegree k (c • a) :=
  Submodule.smul_mem _ c ha

private lemma isHomogeneous_zero_mem {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (k : ℕ) : IsHomogeneousExteriorDegree k (0 : ExteriorAlgebra R V) :=
  Submodule.zero_mem _

/-- Every entry of `circularGaugeConnection4 (circularEvenOmega x)` is a homogeneous 1-form. -/
theorem circularEvenOmega_homogeneous (x : Coordinate) :
    InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1
      (circularGaugeConnection4 (circularEvenOmega x)) := by
  intro i j
  have hd : ∀ m : Fin 8, IsHomogeneousExteriorDegree 1 (circularEvenOmega x m) :=
    circularEvenOmega_deg1 x
  fin_cases i <;> fin_cases j <;>
    simp only [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, weylLowerExt,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact isHomogeneous_zero_mem 1
  · exact isHomogeneous_zero_mem 1
  · exact isHomogeneous_add_mem (hd 0) (hd 3)
  · exact isHomogeneous_sub_mem (hd 1) (isHomogeneous_smul_mem Complex.I (hd 2))
  · exact isHomogeneous_zero_mem 1
  · exact isHomogeneous_zero_mem 1
  · exact isHomogeneous_add_mem (hd 1) (isHomogeneous_smul_mem Complex.I (hd 2))
  · exact isHomogeneous_sub_mem (hd 0) (hd 3)
  · exact isHomogeneous_sub_mem (hd 4) (hd 7)
  · exact isHomogeneous_add_mem (isHomogeneous_neg_mem (hd 5))
      (isHomogeneous_smul_mem Complex.I (hd 6))
  · exact isHomogeneous_zero_mem 1
  · exact isHomogeneous_zero_mem 1
  · exact isHomogeneous_sub_mem (isHomogeneous_neg_mem (hd 5))
      (isHomogeneous_smul_mem Complex.I (hd 6))
  · exact isHomogeneous_add_mem (hd 4) (hd 7)
  · exact isHomogeneous_zero_mem 1
  · exact isHomogeneous_zero_mem 1

/-- For every `x : Coordinate`, `circularEvenDiff` satisfies the strong derivative
eigencondition on
`circularGaugeConnection4 (circularEvenOmega x)`. -/
theorem circularEvenDiff_eigencondition (x : Coordinate) :
    matrixExteriorDerivative circularEvenDiff
        (circularGaugeConnection4 (circularEvenOmega x)) =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularEvenOmega x)) := by
  rw [circularGaugeConnection4_eigencondition_iff]
  intro i
  by_cases hi : i.val < 4
  · simp only [circularEvenOmega, hi, ↓reduceIte, LinearMap.map_smul]
    dsimp [circularEvenDiff]
    rw [exteriorLift_ι, circularEvenMap_single0]
  · simp only [circularEvenOmega, hi, ↓reduceIte, LinearMap.map_smul]
    dsimp [circularEvenDiff]
    rw [exteriorLift_ι, circularEvenMap_single2, map_neg, smul_neg]

private lemma matrixExteriorDerivative_even_mul
    (X Y : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) :
    matrixExteriorDerivative circularEvenDiff (X * Y) =
      matrixExteriorDerivative circularEvenDiff X * Y +
        X * matrixExteriorDerivative circularEvenDiff Y := by
  ext i j
  simp only [matrixExteriorDerivative, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
    map_sum, circularEvenDiff, exteriorLift_even_derivation]
  rw [Finset.sum_add_distrib]

/-- Unconditional covariant vanishing of the quadratic Peirce curvature `genV P A A` under the
even derivation `circularEvenDiff`. -/
theorem circularEvenDiff_covariant_vanishing (x : Coordinate) :
    covariantDerivative (circularGaugeConnection4 (circularEvenOmega x)) circularEvenDiff
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genV (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularEvenOmega x))
        (circularGaugeConnection4 (circularEvenOmega x))) = 0 := by
  let P := chiralExteriorProj4 (Fin 4 → ℂ)
  let A := circularGaugeConnection4 (circularEvenOmega x)
  have hP : P * P = P := chiralProj4_idempotent (ExteriorAlgebra ℂ (Fin 4 → ℂ))
  have hGenV : genV P A A = A * A := by
    dsimp [P, A]
    unfold circularGaugeConnection4 chiralExteriorProj4
    rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hEigencondition : matrixExteriorDerivative circularEvenDiff A =
      peirceGradingDeriv P A :=
    circularEvenDiff_eigencondition x
  have hDerivV : matrixExteriorDerivative circularEvenDiff (genV P A A) = 0 := by
    rw [hGenV, matrixExteriorDerivative_even_mul A A, hEigencondition]
    have hPeirce :=
      (peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP A A A A).2.2.2.2.2.2.2.1
    calc
      peirceGradingDeriv P A * A + A * peirceGradingDeriv P A
        = (P * A - A * P) * A + A * (P * A - A * P) := rfl
      _ = P * (A * A) - (A * A) * P := by noncomm_ring
      _ = peirceGradingDeriv P (A * A) := rfl
      _ = peirceGradingDeriv P (genV P A A) := by rw [hGenV]
      _ = 0 := hPeirce
  have hCommV : matrixCommutator A (genV P A A) = 0 := by
    rw [hGenV, matrixCommutator, mul_assoc, sub_self]
  change matrixExteriorDerivative circularEvenDiff (genV P A A) +
    matrixCommutator A (genV P A A) = 0
  rw [hDerivV, hCommV, add_zero]

/-- Self-dual Yang–Mills corollary for `circularEvenDiff`: for any Hodge star making
`genV P A A` self-dual,
`covariantDerivative A circularEvenDiff (matrixHodgeStar star (genV P A A)) = 0`. -/
theorem circularEvenDiff_self_dual_covariant_vanishing
    (star : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    (x : Coordinate)
    (hsd : isSelfDualCurvature star
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genV (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularEvenOmega x))
        (circularGaugeConnection4 (circularEvenOmega x)))) :
    covariantDerivative (circularGaugeConnection4 (circularEvenOmega x)) circularEvenDiff
      (matrixHodgeStar star
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genV (chiralExteriorProj4 (Fin 4 → ℂ))
          (circularGaugeConnection4 (circularEvenOmega x))
          (circularGaugeConnection4 (circularEvenOmega x)))) = 0 :=
  self_dual_solves_yang_mills star _ circularEvenDiff _ hsd
    (circularEvenDiff_covariant_vanishing x)

/-- Nondegenerate witness at `x₀ = coordinateEquiv (uPlus + uMinus)` for `circularEvenDiff`
and `circularEvenOmega`, establishing `A ≠ 0`, `genV P A A ≠ 0`, `P * A ≠ A * P`, and
`matrixTraceForm (A * A) = 0`. -/
theorem circularEvenDiff_nondegenerate_witness :
    ∃ x : Coordinate,
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let A := circularGaugeConnection4 (circularEvenOmega x)
      A ≠ 0 ∧
      genV P A A ≠ 0 ∧
      P * A ≠ A * P ∧
      matrixTraceForm (A * A) = 0 := by
  let x₀ : Coordinate := coordinateEquiv (uPlus + uMinus)
  refine ⟨x₀, ?_⟩
  have hx0 : x₀ = Pi.single 0 1 + Pi.single 4 1 := by
    have h0 : coordinateEquiv uPlus = Pi.single 0 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 0
    have h4 : coordinateEquiv uMinus = Pi.single 4 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 4
    calc
      x₀ = coordinateEquiv (uPlus + uMinus) := rfl
      _ = coordinateEquiv uPlus + coordinateEquiv uMinus :=
        LinearEquiv.map_add coordinateEquiv uPlus uMinus
      _ = Pi.single 0 1 + Pi.single 4 1 := by rw [h0, h4]
  have hω : ∀ i : Fin 8, circularEvenOmega x₀ i =
      if i = 0 then extBasisOneForm 0 else if i = 4 then extBasisOneForm 2 else 0 := by
    intro i
    fin_cases i <;> simp [circularEvenOmega, extBasisOneForm, hx0]
  have hA02 : circularGaugeConnection4 (circularEvenOmega x₀) 0 2 = extBasisOneForm 0 := by
    simp [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 0, hω 3]
  have hA20 : circularGaugeConnection4 (circularEvenOmega x₀) 2 0 = extBasisOneForm 2 := by
    simp [circularGaugeConnection4, chiralOffBlock4, weylLowerExt, hω 4, hω 7]
  have he0_ne : extBasisOneForm 0 ≠ 0 := by
    intro hz
    unfold extBasisOneForm at hz
    have hsingle : (Pi.single (0 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) = 0 :=
      (ExteriorAlgebra.ι_eq_zero_iff (R := ℂ) (Pi.single (0 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)).mp hz
    have h1 := congrFun hsingle 0
    simp at h1
  have hA_ne : circularGaugeConnection4 (circularEvenOmega x₀) ≠ 0 := by
    intro hz
    have h02 := congrFun (congrFun hz 0) 2
    rw [hA02, Matrix.zero_apply] at h02
    exact he0_ne h02
  have hGenV_eq : genV (chiralExteriorProj4 (Fin 4 → ℂ))
      (circularGaugeConnection4 (circularEvenOmega x₀))
      (circularGaugeConnection4 (circularEvenOmega x₀)) =
      circularGaugeConnection4 (circularEvenOmega x₀) *
        circularGaugeConnection4 (circularEvenOmega x₀) := by
    unfold circularGaugeConnection4 chiralExteriorProj4
    rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hAA00 : (circularGaugeConnection4 (circularEvenOmega x₀) *
      circularGaugeConnection4 (circularEvenOmega x₀)) 0 0 =
      extBasisOneForm 0 * extBasisOneForm 2 := by
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    have hA00 : circularGaugeConnection4 (circularEvenOmega x₀) 0 0 = 0 := by
      simp [circularGaugeConnection4, chiralOffBlock4]
    have hA01 : circularGaugeConnection4 (circularEvenOmega x₀) 0 1 = 0 := by
      simp [circularGaugeConnection4, chiralOffBlock4]
    have hA03 : circularGaugeConnection4 (circularEvenOmega x₀) 0 3 = 0 := by
      simp [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 1, hω 2]
    rw [hA00, hA01, hA02, hA03, hA20]
    simp
  have hGenV_ne : genV (chiralExteriorProj4 (Fin 4 → ℂ))
      (circularGaugeConnection4 (circularEvenOmega x₀))
      (circularGaugeConnection4 (circularEvenOmega x₀)) ≠ 0 := by
    intro hz
    rw [hGenV_eq] at hz
    have h00 := congrFun (congrFun hz 0) 0
    rw [hAA00, Matrix.zero_apply] at h00
    have hc := congrArg (blade2Coeff 0 2) h00
    have hev := (blade2Coeff_eval 0 2 0 2 0).1
    rw [map_zero, hev] at hc
    norm_num at hc
  have hNoncomm : chiralExteriorProj4 (Fin 4 → ℂ) *
      circularGaugeConnection4 (circularEvenOmega x₀) ≠
      circularGaugeConnection4 (circularEvenOmega x₀) * chiralExteriorProj4 (Fin 4 → ℂ) := by
    intro h
    have hPsub : peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularEvenOmega x₀)) = 0 :=
      sub_eq_zero.mpr h
    have h02 := congrFun (congrFun hPsub 0) 2
    unfold circularGaugeConnection4 at h02
    rw [chiralExteriorProj4_peirceGradingDeriv_offBlock] at h02
    have h02' : weylUpperExt (circularEvenOmega x₀ 0) (circularEvenOmega x₀ 1)
        (circularEvenOmega x₀ 2) (circularEvenOmega x₀ 3) 0 0 = 0 := by
      simpa [chiralOffBlock4] using h02
    have h02'' : extBasisOneForm 0 = 0 := by
      simpa [weylUpperExt, hω 0, hω 3] using h02'
    exact he0_ne h02''
  have hTrZero : matrixTraceForm
      (circularGaugeConnection4 (circularEvenOmega x₀) *
        circularGaugeConnection4 (circularEvenOmega x₀)) = 0 :=
    matrixTrace_one_form_square_eq_zero _ (circularEvenOmega_homogeneous x₀)
  exact ⟨hA_ne, hGenV_ne, hNoncomm, hTrZero⟩

end InfoGeometry.Lie
