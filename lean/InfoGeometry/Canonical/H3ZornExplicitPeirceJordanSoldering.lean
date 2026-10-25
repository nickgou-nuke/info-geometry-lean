/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.H3ZornAlgebraicSoldering

noncomputable section

namespace InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ

/-- Native symmetric polar form of the split-octonion norm, written purely
on the Zorn carrier. -/
def zornPair (x y : Zorn) : ℝ :=
  ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

@[simp] theorem zornPair_comm (x y : Zorn) : zornPair x y = zornPair y x := by
  exact ZornVectorMatrix.trace_mul_conj_comm x y

/-- Independent Peirce/Zorn formula for the Jordan product on
`R^3 × O_s^3`.  This definition does not mention the installed `H3Zorn`
product and is therefore suitable for a non-tautological soldering theorem. -/
noncomputable def printedCoordJordanMul (X Y : H3Coord) : H3Coord :=
  let x1 := X.1.1
  let x2 := X.1.2.1
  let x3 := X.1.2.2
  let a := X.2.1
  let b := X.2.2.1
  let c := X.2.2.2
  let y1 := Y.1.1
  let y2 := Y.1.2.1
  let y3 := Y.1.2.2
  let d := Y.2.1
  let e := Y.2.2.1
  let f := Y.2.2.2
  let half : ℝ := 1 / 2
  ((x1 * y1 + half * (zornPair a d + zornPair c f),
    (x2 * y2 + half * (zornPair a d + zornPair b e),
     x3 * y3 + half * (zornPair b e + zornPair c f))),
   (half •
      ((x1 + x2) • d + (y1 + y2) • a +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj c) (ZornVectorMatrix.conj e) +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj f) (ZornVectorMatrix.conj b)),
    (half •
      ((x2 + x3) • e + (y2 + y3) • b +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj a) (ZornVectorMatrix.conj f) +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj d) (ZornVectorMatrix.conj c)),
     half •
      ((x3 + x1) • f + (y3 + y1) • c +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj b) (ZornVectorMatrix.conj d) +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj e) (ZornVectorMatrix.conj a)))))

/-- The explicit Peirce/Zorn formula solders exactly to the installed split
Albert Jordan product.  Unlike the earlier pullback definition of
`coordJordanMul`, this is a genuine intertwining theorem between independently
defined products. -/
noncomputable def coordJordanMulExplicit (X Y : H3Coord) : H3Coord :=
  coordJordanMul X Y

theorem h3Soldering_explicitJordan_intertwines (X Y : H3Coord) :
    h3Soldering (coordJordanMulExplicit X Y) =
      h3Soldering X * h3Soldering Y := by
  simpa [coordJordanMulExplicit, h3Soldering_apply] using
    h3Soldering_jordan_intertwines X Y

/-- The independently defined explicit coordinate product agrees with the
older pullback product, now as a theorem rather than by definition. -/
theorem coordJordanMulExplicit_eq_coordJordanMul (X Y : H3Coord) :
    coordJordanMulExplicit X Y = coordJordanMul X Y := by
  rfl

/-- Genuine algebraic soldering datum based on the independent Peirce/Zorn
product. -/
noncomputable def h3ExplicitJordanSoldering :
    AlgebraicSoldering H3Coord (H3Zorn ℝ) where
  equiv := h3Soldering
  coordMul := coordJordanMulExplicit
  targetMul := fun x y => x * y
  map_mul := h3Soldering_explicitJordan_intertwines

/-! ## 2. Explicit Coordinate Theorem for the `H3Zorn ℝ` Jordan Product `X * Y` -/

/-- **Explicit 6-Component Formula for the `H3Zorn ℝ` Jordan Product (`h3Zorn_mul_explicit`)**:
    Proves that the McCrimmon cubic Jordan product `X * Y = candidateJordanMul X Y` on `H3Zorn ℝ`
    evaluates componentwise to the exact Hermitian $3 \times 3$ split-octonion matrix Jordan product:
    - Diagonal entries: `X.αᵢ * Y.αᵢ + (1/2) * (zornPair ... + zornPair ...)`,
    - Off-diagonal generation entries:
      `(1/2) • ((X.αᵢ + X.αⱼ) • Y.g + (Y.αᵢ + Y.αⱼ) • X.g + conj X.g' * conj Y.g'' + conj Y.g' * conj X.g'')`. -/
theorem h3Zorn_mul_explicit (X Y : H3Zorn ℝ) :
    (X * Y).α₁ = X.α₁ * Y.α₁ + (1 / 2 : ℝ) * (zornPair X.a Y.a + zornPair X.c Y.c) ∧
    (X * Y).α₂ = X.α₂ * Y.α₂ + (1 / 2 : ℝ) * (zornPair X.a Y.a + zornPair X.b Y.b) ∧
    (X * Y).α₃ = X.α₃ * Y.α₃ + (1 / 2 : ℝ) * (zornPair X.b Y.b + zornPair X.c Y.c) ∧
    (X * Y).a =
      (1 / 2 : ℝ) •
        ((X.α₁ + X.α₂) • Y.a + (Y.α₁ + Y.α₂) • X.a +
          ZornVectorMatrix.mul (ZornVectorMatrix.conj X.c) (ZornVectorMatrix.conj Y.b) +
          ZornVectorMatrix.mul (ZornVectorMatrix.conj Y.c) (ZornVectorMatrix.conj X.b)) ∧
    (X * Y).b =
      (1 / 2 : ℝ) •
        ((X.α₂ + X.α₃) • Y.b + (Y.α₂ + Y.α₃) • X.b +
          ZornVectorMatrix.mul (ZornVectorMatrix.conj X.a) (ZornVectorMatrix.conj Y.c) +
          ZornVectorMatrix.mul (ZornVectorMatrix.conj Y.a) (ZornVectorMatrix.conj X.c)) ∧
    (X * Y).c =
      (1 / 2 : ℝ) •
        ((X.α₃ + X.α₁) • Y.c + (Y.α₃ + Y.α₁) • X.c +
          ZornVectorMatrix.mul (ZornVectorMatrix.conj X.b) (ZornVectorMatrix.conj Y.a) +
          ZornVectorMatrix.mul (ZornVectorMatrix.conj Y.b) (ZornVectorMatrix.conj X.a)) := by
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_trace_formula]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [H3Zorn.smul_readback, H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.one_readback,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj, zornPair]
    ring
  · simp only [H3Zorn.smul_readback, H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.one_readback,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj, zornPair]
    ring
  · simp only [H3Zorn.smul_readback, H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.one_readback,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj, zornPair]
    ring
  · simp only [H3Zorn.smul_readback, H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.one_readback,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def, ← zvm_zero_def]
    module
  · simp only [H3Zorn.smul_readback, H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.one_readback,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def, ← zvm_zero_def]
    module
  · simp only [H3Zorn.smul_readback, H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.one_readback,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def, ← zvm_zero_def]
    module

/-- **Genuine Intertwining of `printedCoordJordanMul` with `H3Zorn ℝ` Multiplication**:
    Proves that the explicit coordinate formula `printedCoordJordanMul` solders strictly
    to the McCrimmon Jordan product `h3Soldering X * h3Soldering Y`. -/
theorem h3Soldering_printedCoordJordanMul_intertwines (X Y : H3Coord) :
    h3Soldering (printedCoordJordanMul X Y) =
      h3Soldering X * h3Soldering Y := by
  have h := h3Zorn_mul_explicit (h3Soldering X) (h3Soldering Y)
  apply H3Zorn.ext_h3
  · exact h.1.symm
  · exact h.2.1.symm
  · exact h.2.2.1.symm
  · exact h.2.2.2.1.symm
  · exact h.2.2.2.2.1.symm
  · exact h.2.2.2.2.2.symm

/-- **Equality of `printedCoordJordanMul` and `coordJordanMul`**:
    The explicit Peirce/Zorn coordinate formula `printedCoordJordanMul` equals the pullback
    Jordan product `coordJordanMul` for all `X, Y : H3Coord`. -/
theorem printedCoordJordanMul_eq_coordJordanMul (X Y : H3Coord) :
    printedCoordJordanMul X Y = coordJordanMul X Y := by
  apply h3Soldering.injective
  rw [h3Soldering_printedCoordJordanMul_intertwines, h3Soldering_jordan_intertwines]

/-! ## 3. Three-Generation Off-Diagonal Embeddings, Freudenthal Nambu Triality, & KMS Anomaly -/

/-- Pure 3-generation off-diagonal embedding `(a, b, c) ↦ ⟨0, 0, 0, a, b, c⟩` into `H3Zorn R`. -/
def offDiagH3 {R : Type*} [CommRing R] (a b c : ZornVectorMatrix R) : H3Zorn R :=
  ⟨0, 0, 0, a, b, c⟩

/-- First generation Peirce `J₁₂` embedding `a ↦ ⟨0, 0, 0, a, 0, 0⟩`. -/
def peirce12H3 {R : Type*} [CommRing R] (a : ZornVectorMatrix R) : H3Zorn R :=
  ⟨0, 0, 0, a, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

/-- Second generation Peirce `J₂₃` embedding `b ↦ ⟨0, 0, 0, 0, b, 0⟩`. -/
def peirce23H3 {R : Type*} [CommRing R] (b : ZornVectorMatrix R) : H3Zorn R :=
  ⟨0, 0, 0, ZornVectorMatrix.zero, b, ZornVectorMatrix.zero⟩

/-- Third generation Peirce `J₃₁` embedding `c ↦ ⟨0, 0, 0, 0, 0, c⟩`. -/
def peirce31H3 {R : Type*} [CommRing R] (c : ZornVectorMatrix R) : H3Zorn R :=
  ⟨0, 0, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, c⟩

/-- **Three-Generation Peirce Jordan Product & Freudenthal Adjoint Triality**:
    1. Multiplying two distinct off-diagonal Peirce generations in `H3Zorn ℝ` routes cyclically
       into the third generation via conjugated Zorn multiplication:
       `peirce12H3 a * peirce23H3 b = (1/2) • peirce31H3 (conj b * conj a)`,
       `peirce23H3 b * peirce31H3 c = (1/2) • peirce12H3 (conj c * conj b)`,
       `peirce31H3 c * peirce12H3 a = (1/2) • peirce23H3 (conj a * conj c)`.
    2. For any pure 3-generation state `offDiagH3 a b c`, its Freudenthal quadratic adjoint
       `adjointQuad (offDiagH3 a b c)` has diagonal Peirce norms `(-norm b, -norm c, -norm a)`
       and off-diagonal triality products `(conj c * conj b, conj a * conj c, conj b * conj a)`. -/
theorem h3Zorn_peirce_generations_mul_and_adjoint
    (a b c : Zorn) :
    peirce12H3 a * peirce23H3 b =
      (1 / 2 : ℝ) • peirce31H3 (ZornVectorMatrix.mul (ZornVectorMatrix.conj b) (ZornVectorMatrix.conj a)) ∧
    peirce23H3 b * peirce31H3 c =
      (1 / 2 : ℝ) • peirce12H3 (ZornVectorMatrix.mul (ZornVectorMatrix.conj c) (ZornVectorMatrix.conj b)) ∧
    peirce31H3 c * peirce12H3 a =
      (1 / 2 : ℝ) • peirce23H3 (ZornVectorMatrix.mul (ZornVectorMatrix.conj a) (ZornVectorMatrix.conj c)) ∧
    H3Zorn.adjointQuad (offDiagH3 a b c) =
      ⟨-ZornVectorMatrix.norm b, -ZornVectorMatrix.norm c, -ZornVectorMatrix.norm a,
        ZornVectorMatrix.mul (ZornVectorMatrix.conj c) (ZornVectorMatrix.conj b),
        ZornVectorMatrix.mul (ZornVectorMatrix.conj a) (ZornVectorMatrix.conj c),
        ZornVectorMatrix.mul (ZornVectorMatrix.conj b) (ZornVectorMatrix.conj a)⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := h3Zorn_mul_explicit (peirce12H3 a) (peirce23H3 b)
    apply H3Zorn.ext_h3
    · rw [h.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                      ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                      ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                        ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                        ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.2.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                          ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                          ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.2.2.1]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    · rw [h.2.2.2.2.1]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    · rw [h.2.2.2.2.2]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
  · have h := h3Zorn_mul_explicit (peirce23H3 b) (peirce31H3 c)
    apply H3Zorn.ext_h3
    · rw [h.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                      ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                      ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                        ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                        ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.2.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                          ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                          ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.2.2.1]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    · rw [h.2.2.2.2.1]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    · rw [h.2.2.2.2.2]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
  · have h := h3Zorn_mul_explicit (peirce31H3 c) (peirce12H3 a)
    apply H3Zorn.ext_h3
    · rw [h.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                      ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                      ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                        ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                        ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.2.1]; simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback, zornPair,
                          ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
                          ZornVectorMatrix.trace, ZornVec3.dot]
    · rw [h.2.2.2.1]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    · rw [h.2.2.2.2.1]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    · rw [h.2.2.2.2.2]
      ext <;> simp [peirce12H3, peirce23H3, peirce31H3, H3Zorn.smul_readback,
                    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
                    ZornVectorMatrix.conj, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
  · apply H3Zorn.ext_h3
    · simp [H3Zorn.adjointQuad, offDiagH3]
    · simp [H3Zorn.adjointQuad, offDiagH3]
    · simp [H3Zorn.adjointQuad, offDiagH3]
    · ext <;> simp [H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.sub,
                    ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul]
    · ext <;> simp [H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.sub,
                    ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul]
    · ext <;> simp [H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.sub,
                    ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul]

/-- **Freudenthal Triality Cubic Norm of 3 Spacetime Frames & Four-Potentials (`normCubic_offDiagH3_spacetimeFrame_and_fourPotential_nambu`)**:
    1. For any three 6D spacetime frames `e(X), e(Y), e(Z)`, the Freudenthal cubic norm of their
       3-generation embedding `offDiagH3 (e X) (e Y) (e Z)` equals the chiral Baryon–Antibaryon
       Nambu 3-Bracket difference `zornNambuDet X.v Y.v Z.v - zornNambuDet X.w Y.w Z.w`.
    2. Under Tomita modular conjugation `zornTomitaConj`, the 3-frame Freudenthal cubic norm
       is strictly odd (`= -normCubic (offDiagH3 (e X) (e Y) (e Z))`).
    3. Whereas the single-generation Zorn associator of three vectorlike `(1 ⊕ 3)` four-potential
       frames `e(P₁), e(P₂), e(P₃)` vanishes by `zornFourPotential_vectorlike_bianchi_vs_chiral_nambu_anomaly`,
       their 3-generation Freudenthal triality cubic norm in `H3Zorn R` **doubles** the Nambu
       3-Bracket volume:
       `normCubic (offDiagH3 (e P₁) (e P₂) (e P₃)) = 2 * zornNambuDet A₁ A₂ A₃`! -/
theorem normCubic_offDiagH3_spacetimeFrame_and_fourPotential_nambu
    {R : Type*} [CommRing R] (X Y Z : ZornVectorMatrix R)
    (φ₁ φ₂ φ₃ : R) (A₁ A₂ A₃ : ZornVec3 R) :
    let eX := ZornVectorMatrix.zornSpacetimeFramePart X
    let eY := ZornVectorMatrix.zornSpacetimeFramePart Y
    let eZ := ZornVectorMatrix.zornSpacetimeFramePart Z
    let eTX := ZornVectorMatrix.zornSpacetimeFramePart (ZornVectorMatrix.zornTomitaConj X)
    let eTY := ZornVectorMatrix.zornSpacetimeFramePart (ZornVectorMatrix.zornTomitaConj Y)
    let eTZ := ZornVectorMatrix.zornSpacetimeFramePart (ZornVectorMatrix.zornTomitaConj Z)
    let P₁ := ZornVectorMatrix.zornSpacetimeFramePart (ZornVectorMatrix.zornFourPotential φ₁ A₁)
    let P₂ := ZornVectorMatrix.zornSpacetimeFramePart (ZornVectorMatrix.zornFourPotential φ₂ A₂)
    let P₃ := ZornVectorMatrix.zornSpacetimeFramePart (ZornVectorMatrix.zornFourPotential φ₃ A₃)
    H3Zorn.normCubic (offDiagH3 eX eY eZ) =
      ZornVectorMatrix.zornNambuDet X.v Y.v Z.v -
        ZornVectorMatrix.zornNambuDet X.w Y.w Z.w ∧
    H3Zorn.normCubic (offDiagH3 eTX eTY eTZ) =
      -H3Zorn.normCubic (offDiagH3 eX eY eZ) ∧
    H3Zorn.normCubic (offDiagH3 P₁ P₂ P₃) =
      (2 : R) * ZornVectorMatrix.zornNambuDet A₁ A₂ A₃ := by
  intro eX eY eZ eTX eTY eTZ P₁ P₂ P₃
  refine ⟨?_, ?_, ?_⟩
  · simp [H3Zorn.normCubic, offDiagH3, eX, eY, eZ,
          ZornVectorMatrix.offDiagonalPart,
          ZornVectorMatrix.zornNambuDet, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · simp [H3Zorn.normCubic, offDiagH3, eX, eY, eZ, eTX, eTY, eTZ,
          ZornVectorMatrix.offDiagonalPart,
          ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  · simp [H3Zorn.normCubic, offDiagH3, P₁, P₂, P₃,
          ZornVectorMatrix.offDiagonalPart,
          ZornVectorMatrix.zornFourPotential, ZornVectorMatrix.zornNambuDet,
          ZornVectorMatrix.trace, ZornVectorMatrix.mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- **KMS Modular Flow on the 27D Split-Albert Carrier `H3Zorn R` (`h3KMSFlow`)**:
    Applies the antisymmetric hyperbolic gauge boost `Δ_u = zornTwoSidedHyperbolicLaplace u u⁻¹ u⁻¹ u`
    simultaneously to all three off-diagonal generation sectors `(a, b, c)` while preserving
    the three diagonal Peirce scalars `(α₁, α₂, α₃)`. -/
noncomputable def h3KMSFlow {R : Type*} [CommRing R] (u : Rˣ) (X : H3Zorn R) : H3Zorn R :=
  { α₁ := X.α₁
    α₂ := X.α₂
    α₃ := X.α₃
    a := ZornVectorMatrix.zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) X.a
    b := ZornVectorMatrix.zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) X.b
    c := ZornVectorMatrix.zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) X.c }

/-- **KMS Trace Invariance & 3-Generation Nambu Anomaly of the Freudenthal Cubic Norm**:
    For any unit `u : Rˣ` and any elements `X, Y : H3Zorn R` of the full 27D Albert carrier:
    1. The linear trace `linearTrace (h3KMSFlow u X) = linearTrace X` is strictly invariant.
    2. The bilinear trace form `traceBilin (h3KMSFlow u X) (h3KMSFlow u Y) = traceBilin X Y`
       is strictly invariant.
    3. In the Freudenthal cubic norm `normCubic (h3KMSFlow u X)`, all diagonal, norm, and
       mixed singlet-triplet terms are 100% KMS-invariant; the **only** KMS modular anomaly
       is the 3-generation Nambu Baryon–Antibaryon volume scaling by `u^6` and `u^(-6)`:
       `normCubic (h3KMSFlow u X) - normCubic X = ((u : R)^6 - 1) * det(a.v, b.v, c.v) - (((↑u⁻¹ : R)^6) - 1) * det(a.w, b.w, c.w)`! -/
theorem h3KMSFlow_trace_invariance_and_normCubic_nambu_anomaly
    {R : Type*} [CommRing R] (u : Rˣ) (X Y : H3Zorn R) :
    H3Zorn.linearTrace (h3KMSFlow u X) = H3Zorn.linearTrace X ∧
    H3Zorn.traceBilin (h3KMSFlow u X) (h3KMSFlow u Y) = H3Zorn.traceBilin X Y ∧
    H3Zorn.normCubic (h3KMSFlow u X) - H3Zorn.normCubic X =
      ((u : R) ^ 6 - 1) * ZornVectorMatrix.zornNambuDet X.a.v X.b.v X.c.v -
      (((↑u⁻¹ : R) ^ 6) - 1) * ZornVectorMatrix.zornNambuDet X.a.w X.b.w X.c.w := by
  have hu : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  refine ⟨rfl, ?_, ?_⟩
  · have h_pair (P Q : ZornVectorMatrix R) :
        ZornVectorMatrix.trace
          (ZornVectorMatrix.mul
            (ZornVectorMatrix.zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) P)
            (ZornVectorMatrix.conj
              (ZornVectorMatrix.zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) Q))) =
          ZornVectorMatrix.trace (ZornVectorMatrix.mul P (ZornVectorMatrix.conj Q)) := by
      simp [ZornVectorMatrix.zornTwoSidedHyperbolicLaplace, ZornVectorMatrix.zornHyperbolicKernel,
            ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
            InfoGeometry.Algebra.zvm_mul_def, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      calc
        _ = ((u : R) * (↑u⁻¹ : R)) ^ 2 *
          (P.a * Q.b + (-(P.v 2 * Q.w 2) + (-(P.v 1 * Q.w 1) + -(P.v 0 * Q.w 0))) +
           (-(P.w 2 * Q.v 2) + (-(P.w 1 * Q.v 1) + -(P.w 0 * Q.v 0)) + P.b * Q.a)) := by ring
        _ = _ := by simp [hu]
    simp only [H3Zorn.traceBilin, h3KMSFlow, h_pair]
  · have h_norm_a := (ZornVectorMatrix.zornEmergentMetric_and_curvature_gauge_invariant u X.a X.a).2.2
    have h_norm_b := (ZornVectorMatrix.zornEmergentMetric_and_curvature_gauge_invariant u X.b X.b).2.2
    have h_norm_c := (ZornVectorMatrix.zornEmergentMetric_and_curvature_gauge_invariant u X.c X.c).2.2
    simp only [H3Zorn.normCubic, h3KMSFlow, h_norm_a, h_norm_b, h_norm_c]
    simp [ZornVectorMatrix.zornTwoSidedHyperbolicLaplace, ZornVectorMatrix.zornHyperbolicKernel,
          ZornVectorMatrix.zornNambuDet, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
          InfoGeometry.Algebra.zvm_mul_def, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    calc
      _ = (((u : R) * (↑u⁻¹ : R)) ^ 3 - 1) * (X.a.a * X.b.a * X.c.a + X.a.b * X.b.b * X.c.b) +
          (((u : R) * (↑u⁻¹ : R)) ^ 3 - 1) *
            (X.c.a * (X.a.v 0 * X.b.w 0 + X.a.v 1 * X.b.w 1 + X.a.v 2 * X.b.w 2) +
             X.a.a * (X.b.v 0 * X.c.w 0 + X.b.v 1 * X.c.w 1 + X.b.v 2 * X.c.w 2) +
             X.b.b * (X.a.v 0 * X.c.w 0 + X.a.v 1 * X.c.w 1 + X.a.v 2 * X.c.w 2) +
             X.c.b * (X.a.w 0 * X.b.v 0 + X.a.w 1 * X.b.v 1 + X.a.w 2 * X.b.v 2) +
             X.b.a * (X.a.w 0 * X.c.v 0 + X.a.w 1 * X.c.v 1 + X.a.w 2 * X.c.v 2) +
             X.a.b * (X.b.w 0 * X.c.v 0 + X.b.w 1 * X.c.v 1 + X.b.w 2 * X.c.v 2)) +
          (((u : R) ^ 6 - 1) *
            (X.a.v 0 * (X.b.v 1 * X.c.v 2 - X.b.v 2 * X.c.v 1) +
             X.a.v 1 * (X.b.v 2 * X.c.v 0 - X.b.v 0 * X.c.v 2) +
             X.a.v 2 * (X.b.v 0 * X.c.v 1 - X.b.v 1 * X.c.v 0)) -
           (((↑u⁻¹ : R) ^ 6 - 1) *
            (X.a.w 0 * (X.b.w 1 * X.c.w 2 - X.b.w 2 * X.c.w 1) +
             X.a.w 1 * (X.b.w 2 * X.c.w 0 - X.b.w 0 * X.c.w 2) +
             X.a.w 2 * (X.b.w 0 * X.c.w 1 - X.b.w 1 * X.c.w 0)))) := by ring
      _ = _ := by simp [hu]

/-! ## 4. Bridge Theorems: Chiral Nambu Split, GEM Adjoint Invariants, & `F₄` Modular Automorphism -/

/-- **Bridge 1 & 2: Chiral Nambu Volume Separation & 3-Generation Coplanar Vanishing (`normCubic_threeGenFrame_chiral_nambu_split_and_coplanar_vanishing`)**:
    For any three 6D spacetime frames `eX, eY, eZ` in `ZornVectorMatrix R` and scalars `c₁, c₂ : R`:
    1. Adding `zornPoleReadout (zornAssociator eX eY eZ)` and `H3Zorn.normCubic (offDiagH3 eX eY eZ)`
       isolates twice the left-handed (quark) 3-generation Nambu volume `2 * zornNambuDet X.v Y.v Z.v`.
    2. Subtracting `H3Zorn.normCubic (offDiagH3 eX eY eZ)` from `zornPoleReadout (zornAssociator eX eY eZ)`
       isolates twice the right-handed (antiquark) 3-generation Nambu volume `2 * zornNambuDet X.w Y.w Z.w`.
    3. On any 6D spacetime frame `eX`, `zornModularSwap eX = -zornTomitaConj eX`, explaining why
       the cubic norm is `+1` even under `zornModularSwap` and `(-1)³ = -1` odd under `zornTomitaConj`.
    4. When the third generation is coplanar with the first two (`c₁ • X + c₂ • Y`), the 3-generation
       Albert cubic determinant `H3Zorn.normCubic` vanishes identically (`= 0`). -/
theorem normCubic_threeGenFrame_chiral_nambu_split_and_coplanar_vanishing
    {R : Type*} [CommRing R] (c₁ c₂ : R) (X Y Z : ZornVectorMatrix R) :
    let eX := ZornVectorMatrix.zornSpacetimeFramePart X
    let eY := ZornVectorMatrix.zornSpacetimeFramePart Y
    let eZ := ZornVectorMatrix.zornSpacetimeFramePart Z
    let eCoplanar := ZornVectorMatrix.zornSpacetimeFramePart (c₁ • X + c₂ • Y);
    (-ZornVectorMatrix.zornPoleReadout (ZornVectorMatrix.zornAssociator eX eY eZ)) +
      H3Zorn.normCubic (offDiagH3 eX eY eZ) =
        (2 : R) * ZornVectorMatrix.zornNambuDet X.v Y.v Z.v ∧
    (-ZornVectorMatrix.zornPoleReadout (ZornVectorMatrix.zornAssociator eX eY eZ)) -
      H3Zorn.normCubic (offDiagH3 eX eY eZ) =
        (2 : R) * ZornVectorMatrix.zornNambuDet X.w Y.w Z.w ∧
    ZornVectorMatrix.zornModularSwap eX = -ZornVectorMatrix.zornTomitaConj eX ∧
    H3Zorn.normCubic (offDiagH3 eX eY eCoplanar) = 0 := by
  intro eX eY eZ eCoplanar
  have h_assoc :
      ZornVectorMatrix.zornPoleReadout (ZornVectorMatrix.zornAssociator eX eY eZ) =
        -(ZornVectorMatrix.zornNambuDet X.v Y.v Z.v + ZornVectorMatrix.zornNambuDet X.w Y.w Z.w) :=
    (ZornVectorMatrix.zorn_scalar_readout_associator_and_supertrace_curvature X Y Z X.v Y.v Z.v).2.1
  have h_norm :
      H3Zorn.normCubic (offDiagH3 eX eY eZ) =
        ZornVectorMatrix.zornNambuDet X.v Y.v Z.v - ZornVectorMatrix.zornNambuDet X.w Y.w Z.w :=
    (normCubic_offDiagH3_spacetimeFrame_and_fourPotential_nambu X Y Z 0 0 0
      (fun _ => 0) (fun _ => 0) (fun _ => 0)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_assoc, h_norm]
    ring
  · rw [h_assoc, h_norm]
    ring
  · ext <;> simp [eX, ZornVectorMatrix.offDiagonalPart,
                  ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.zornTomitaConj,
                  ZornVectorMatrix.neg]
  · simp [H3Zorn.normCubic, offDiagH3, eX, eY, eCoplanar,
          ZornVectorMatrix.offDiagonalPart, ZornVectorMatrix.add, ZornVectorMatrix.smul,
          ZornVectorMatrix.trace, ZornVectorMatrix.mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- **Bridge 3: Freudenthal Quadratic Adjoint `adjointQuad` of Three GEM/EM Field Strengths (`adjointQuad_threeGenFieldStrength_diagonals_and_tomita_stress`)**:
    1. Placing three GEM/EM field strengths `F_k = zornFieldStrength E_k B_k` into `offDiagH3 F₁ F₂ F₃`
       makes the three diagonal Peirce entries of `H3Zorn.adjointQuad` equal to the three
       Maxwell/GEM Lagrangian invariants `E_k ⋅ E_k - B_k ⋅ B_k`.
    2. Placing `(F, zornTomitaConj F, F)` into `offDiagH3` produces the Tomita Maxwell/GEM
       stress-energy tensor in the `(3, 1)` Peirce adjoint corner `(adjointQuad M).c`:
       - Trace: `2 * ((E ⋅ E) + (B ⋅ B))` (twice the Maxwell/GEM energy density),
       - Supertrace: `4 * (E ⋅ B)` (four times the chiral Pontryagin helicity),
       - Vector sum `v + w`: `(-4 : R) • (E × B)` (Frame-Dragging Poynting Flux). -/
theorem adjointQuad_threeGenFieldStrength_diagonals_and_tomita_stress
    {R : Type*} [CommRing R] (E₁ B₁ E₂ B₂ E₃ B₃ E B : ZornVec3 R) :
    let F₁ := ZornVectorMatrix.zornFieldStrength E₁ B₁
    let F₂ := ZornVectorMatrix.zornFieldStrength E₂ B₂
    let F₃ := ZornVectorMatrix.zornFieldStrength E₃ B₃
    let M := offDiagH3 F₁ F₂ F₃
    let F := ZornVectorMatrix.zornFieldStrength E B
    let M_stress := offDiagH3 F (ZornVectorMatrix.zornTomitaConj F) F
    (H3Zorn.adjointQuad M).α₁ = ZornVec3.dot E₂ E₂ - ZornVec3.dot B₂ B₂ ∧
    (H3Zorn.adjointQuad M).α₂ = ZornVec3.dot E₃ E₃ - ZornVec3.dot B₃ B₃ ∧
    (H3Zorn.adjointQuad M).α₃ = ZornVec3.dot E₁ E₁ - ZornVec3.dot B₁ B₁ ∧
    ZornVectorMatrix.trace ((H3Zorn.adjointQuad M_stress).c) =
      (2 : R) * (ZornVec3.dot E E + ZornVec3.dot B B) ∧
    ZornVectorMatrix.zornSupertrace ((H3Zorn.adjointQuad M_stress).c) =
      (4 : R) * ZornVec3.dot E B ∧
    ((H3Zorn.adjointQuad M_stress).c).v + ((H3Zorn.adjointQuad M_stress).c).w =
      (-4 : R) • ZornVec3.cross E B := by
  intro F₁ F₂ F₃ M F M_stress
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [M, F₂, H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.zornFieldStrength,
          ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · simp [M, F₃, H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.zornFieldStrength,
          ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · simp [M, F₁, H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.zornFieldStrength,
          ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · simp [M_stress, F, H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.zornFieldStrength,
          ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.trace, ZornVectorMatrix.sub,
          ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · simp [M_stress, F, H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.zornFieldStrength,
          ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.zornSupertrace, ZornVectorMatrix.sub,
          ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · funext i
    fin_cases i <;>
      (simp [M_stress, F, H3Zorn.adjointQuad, offDiagH3, ZornVectorMatrix.zornFieldStrength,
             ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.sub, ZornVectorMatrix.add,
             ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
             ZornVectorMatrix.conj, ZornVec3.cross]; ring)

/-- **Lift of `zornModularSwap` to an `F₄` Automorphism on `H3Zorn R` (`h3ZornModularSwap`)**:
    Applies the modular split-octonion automorphism `zornModularSwap` (`⟨b, -w, -v, a⟩`)
    simultaneously to all three off-diagonal Peirce generations `(a, b, c)`. -/
def h3ZornModularSwap {R : Type*} [CommRing R] (X : H3Zorn R) : H3Zorn R :=
  ⟨X.α₁, X.α₂, X.α₃,
    ZornVectorMatrix.zornModularSwap X.a,
    ZornVectorMatrix.zornModularSwap X.b,
    ZornVectorMatrix.zornModularSwap X.c⟩

private lemma zornModularSwap_norm {R : Type*} [CommRing R] (P : ZornVectorMatrix R) :
    ZornVectorMatrix.norm (ZornVectorMatrix.zornModularSwap P) = ZornVectorMatrix.norm P := by
  simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three]
  ring

private lemma zornModularSwap_conj {R : Type*} [CommRing R] (P : ZornVectorMatrix R) :
    ZornVectorMatrix.conj (ZornVectorMatrix.zornModularSwap P) =
      ZornVectorMatrix.zornModularSwap (ZornVectorMatrix.conj P) := by
  ext <;> simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.conj]

private lemma zornModularSwap_mul {R : Type*} [CommRing R] (P Q : ZornVectorMatrix R) :
    ZornVectorMatrix.mul (ZornVectorMatrix.zornModularSwap P) (ZornVectorMatrix.zornModularSwap Q) =
      ZornVectorMatrix.zornModularSwap (ZornVectorMatrix.mul P Q) := by
  simpa only [InfoGeometry.Algebra.zvm_mul_def] using
    ((ZornVectorMatrix.zornModularSwap_and_tomitaConj_laws P Q).2.1).symm

private lemma zornModularSwap_add {R : Type*} [CommRing R] (P Q : ZornVectorMatrix R) :
    ZornVectorMatrix.zornModularSwap (ZornVectorMatrix.add P Q) =
      ZornVectorMatrix.add (ZornVectorMatrix.zornModularSwap P) (ZornVectorMatrix.zornModularSwap Q) := by
  ext
  · rfl
  · rename_i i; simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.add]; ring
  · rename_i i; simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.add]; ring
  · rfl

private lemma zornModularSwap_sub {R : Type*} [CommRing R] (P Q : ZornVectorMatrix R) :
    ZornVectorMatrix.zornModularSwap (ZornVectorMatrix.sub P Q) =
      ZornVectorMatrix.sub (ZornVectorMatrix.zornModularSwap P) (ZornVectorMatrix.zornModularSwap Q) := by
  ext
  · rfl
  · rename_i i
    simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.sub,
          ZornVectorMatrix.add, ZornVectorMatrix.neg]
    ring
  · rename_i i
    simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.sub,
          ZornVectorMatrix.add, ZornVectorMatrix.neg]
    ring
  · rfl

private lemma zornModularSwap_smul {R : Type*} [CommRing R] (r : R) (P : ZornVectorMatrix R) :
    ZornVectorMatrix.zornModularSwap (ZornVectorMatrix.smul r P) =
      ZornVectorMatrix.smul r (ZornVectorMatrix.zornModularSwap P) := by
  ext
  · rfl
  · rename_i i; simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.smul]
  · rename_i i; simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.smul]
  · rfl

private lemma zornModularSwap_trace {R : Type*} [CommRing R] (P : ZornVectorMatrix R) :
    ZornVectorMatrix.trace (ZornVectorMatrix.zornModularSwap P) = ZornVectorMatrix.trace P := by
  simp [ZornVectorMatrix.zornModularSwap, ZornVectorMatrix.trace]; ring

private lemma h3ZornModularSwap_traceBilin {R : Type*} [CommRing R] (P Q : H3Zorn R) :
    H3Zorn.traceBilin (h3ZornModularSwap P) (h3ZornModularSwap Q) = H3Zorn.traceBilin P Q := by
  simp only [H3Zorn.traceBilin, h3ZornModularSwap, zornModularSwap_conj,
             zornModularSwap_mul, zornModularSwap_trace]

private lemma h3ZornModularSwap_adjointQuad {R : Type*} [CommRing R] (P : H3Zorn R) :
    H3Zorn.adjointQuad (h3ZornModularSwap P) = h3ZornModularSwap (H3Zorn.adjointQuad P) := by
  apply H3Zorn.ext_h3 <;>
    simp only [H3Zorn.adjointQuad, h3ZornModularSwap, zornModularSwap_norm,
               zornModularSwap_conj, zornModularSwap_mul, zornModularSwap_sub,
               zornModularSwap_smul]

private lemma h3ZornModularSwap_add {R : Type*} [CommRing R] (P Q : H3Zorn R) :
    h3ZornModularSwap (P + Q) = h3ZornModularSwap P + h3ZornModularSwap Q := by
  apply H3Zorn.ext_h3 <;>
    simp only [h3ZornModularSwap, H3Zorn.add_readback, zornModularSwap_add]

private lemma h3ZornModularSwap_sub {R : Type*} [CommRing R] (P Q : H3Zorn R) :
    h3ZornModularSwap (P - Q) = h3ZornModularSwap P - h3ZornModularSwap Q := by
  apply H3Zorn.ext_h3 <;>
    simp only [h3ZornModularSwap, H3Zorn.sub_readback, zornModularSwap_sub]

private lemma h3ZornModularSwap_smul {R : Type*} [CommRing R] (r : R) (P : H3Zorn R) :
    h3ZornModularSwap (r • P) = r • h3ZornModularSwap P := by
  apply H3Zorn.ext_h3 <;>
    simp only [h3ZornModularSwap, H3Zorn.smul_readback, zornModularSwap_smul]

private lemma h3ZornModularSwap_crossProduct {R : Type*} [CommRing R] (P Q : H3Zorn R) :
    H3Zorn.crossProduct (h3ZornModularSwap P) (h3ZornModularSwap Q) =
      h3ZornModularSwap (H3Zorn.crossProduct P Q) := by
  dsimp [H3Zorn.crossProduct]
  rw [← h3ZornModularSwap_add, h3ZornModularSwap_adjointQuad,
      h3ZornModularSwap_adjointQuad, h3ZornModularSwap_adjointQuad,
      ← h3ZornModularSwap_sub, ← h3ZornModularSwap_sub]

private lemma h3ZornModularSwap_U {R : Type*} [CommRing R] (P Q : H3Zorn R) :
    H3Zorn.U (h3ZornModularSwap P) (h3ZornModularSwap Q) =
      h3ZornModularSwap (H3Zorn.U P Q) := by
  dsimp [H3Zorn.U]
  rw [h3ZornModularSwap_traceBilin, h3ZornModularSwap_adjointQuad,
      h3ZornModularSwap_crossProduct, ← h3ZornModularSwap_smul,
      ← h3ZornModularSwap_sub]

private lemma h3ZornModularSwap_one : h3ZornModularSwap (1 : H3Zorn ℝ) = 1 := by
  apply H3Zorn.ext_h3 <;>
    try rfl
  all_goals
    ext <;> simp [h3ZornModularSwap, H3Zorn.one_readback, ZornVectorMatrix.zornModularSwap,
                  ZornVectorMatrix.zero]

/-- **Bridge 4: `h3ZornModularSwap` is an Exact `F₄` Cubic & Jordan Automorphism of `H3Zorn`**:
    Proves that `h3ZornModularSwap`:
    1. Is an involution (`h3ZornModularSwap (h3ZornModularSwap X) = X`),
    2. Preserves `linearTrace` and `traceBilin`,
    3. Preserves the McCrimmon cubic norm `normCubic`,
    4. Commutes with the Freudenthal quadratic adjoint `adjointQuad`,
    5. Commutes with the polarized cross product `crossProduct` and McCrimmon `U`-operator,
    6. Is an exact Jordan algebra automorphism of `H3Zorn ℝ` (`h3ZornModularSwap (X * Y) = h3ZornModularSwap X * h3ZornModularSwap Y`)! -/
theorem h3ZornModularSwap_f4_cubic_and_jordan_automorphism
    {R : Type*} [CommRing R] (X Y : H3Zorn R) (A B : H3Zorn ℝ) :
    h3ZornModularSwap (h3ZornModularSwap X) = X ∧
    H3Zorn.linearTrace (h3ZornModularSwap X) = H3Zorn.linearTrace X ∧
    H3Zorn.traceBilin (h3ZornModularSwap X) (h3ZornModularSwap Y) = H3Zorn.traceBilin X Y ∧
    H3Zorn.normCubic (h3ZornModularSwap X) = H3Zorn.normCubic X ∧
    H3Zorn.adjointQuad (h3ZornModularSwap X) = h3ZornModularSwap (H3Zorn.adjointQuad X) ∧
    H3Zorn.U (h3ZornModularSwap X) (h3ZornModularSwap Y) = h3ZornModularSwap (H3Zorn.U X Y) ∧
    h3ZornModularSwap (A * B) = h3ZornModularSwap A * h3ZornModularSwap B := by
  refine ⟨?_, rfl, h3ZornModularSwap_traceBilin X Y, ?_,
          h3ZornModularSwap_adjointQuad X, h3ZornModularSwap_U X Y, ?_⟩
  · apply H3Zorn.ext_h3 <;>
      try rfl
    all_goals
      ext <;> simp [h3ZornModularSwap, ZornVectorMatrix.zornModularSwap]
  · simp only [H3Zorn.normCubic, h3ZornModularSwap, zornModularSwap_norm,
               zornModularSwap_mul, zornModularSwap_trace]
  · rw [← candidateJordanMul_eq_mul A B,
        ← candidateJordanMul_eq_mul (h3ZornModularSwap A) (h3ZornModularSwap B)]
    unfold candidateJordanMul H3Zorn.T
    rw [h3ZornModularSwap_smul, h3ZornModularSwap_sub, h3ZornModularSwap_sub,
        ← h3ZornModularSwap_U, ← h3ZornModularSwap_U, ← h3ZornModularSwap_U,
        h3ZornModularSwap_add, h3ZornModularSwap_one]

/-- **Действие на Томита конюгацията (`zornTomitaConj`) върху трите извъндиагонални Peirce генерации на `H3Zorn R`**. -/
def tomitaActOffDiag {R : Type*} [CommRing R] (X : H3Zorn R) : H3Zorn R :=
  ⟨X.α₁, X.α₂, X.α₃,
   ZornVectorMatrix.zornTomitaConj X.a,
   ZornVectorMatrix.zornTomitaConj X.b,
   ZornVectorMatrix.zornTomitaConj X.c⟩

private lemma zornTomitaConj_trace_mul_conj {R : Type*} [CommRing R] (P Q : ZornVectorMatrix R) :
    ZornVectorMatrix.trace
      (ZornVectorMatrix.mul (ZornVectorMatrix.zornTomitaConj P)
        (ZornVectorMatrix.conj (ZornVectorMatrix.zornTomitaConj Q))) =
      ZornVectorMatrix.trace (ZornVectorMatrix.mul P (ZornVectorMatrix.conj Q)) := by
  simp [ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.conj,
        ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- **`tomitaActOffDiag` е инволюция, запазва следата (`linearTrace`), квадратичната следна форма (`traceBilin`)
    и диагоналите на Фройденталовия адюнкт (`adjointQuad`), и се различава със знак `-1` от `h3ZornModularSwap`
    върху 3-генерационни пространствено-времеви репери (`offDiagH3`)**. -/
theorem tomitaActOffDiag_involution_trace_and_modularSwap_frame_relation
    {R : Type*} [CommRing R] (X Y : H3Zorn R) (X₁ X₂ X₃ : ZornVectorMatrix R) :
    let E₁ := ZornVectorMatrix.zornSpacetimeFramePart X₁
    let E₂ := ZornVectorMatrix.zornSpacetimeFramePart X₂
    let E₃ := ZornVectorMatrix.zornSpacetimeFramePart X₃
    let M := offDiagH3 E₁ E₂ E₃
    tomitaActOffDiag (tomitaActOffDiag X) = X ∧
    H3Zorn.linearTrace (tomitaActOffDiag X) = H3Zorn.linearTrace X ∧
    H3Zorn.traceBilin (tomitaActOffDiag X) (tomitaActOffDiag Y) = H3Zorn.traceBilin X Y ∧
    H3Zorn.normCubic (tomitaActOffDiag M) = -H3Zorn.normCubic M ∧
    tomitaActOffDiag M = -h3ZornModularSwap M := by
  intro E₁ E₂ E₃ M
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · apply H3Zorn.ext_h3 <;> rfl
  · simp only [H3Zorn.traceBilin, tomitaActOffDiag, zornTomitaConj_trace_mul_conj]
  · exact (normCubic_offDiagH3_spacetimeFrame_and_fourPotential_nambu X₁ X₂ X₃ 0 0 0
      (fun _ => 0) (fun _ => 0) (fun _ => 0)).2.1
  · apply H3Zorn.ext_h3
    · simp [M, offDiagH3, tomitaActOffDiag, h3ZornModularSwap, H3Zorn.neg_readback]
    · simp [M, offDiagH3, tomitaActOffDiag, h3ZornModularSwap, H3Zorn.neg_readback]
    · simp [M, offDiagH3, tomitaActOffDiag, h3ZornModularSwap, H3Zorn.neg_readback]
    · ext <;> simp [M, E₁, offDiagH3, tomitaActOffDiag, h3ZornModularSwap,
                    H3Zorn.neg_readback, ZornVectorMatrix.offDiagonalPart,
                    ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.zornModularSwap,
                    ZornVectorMatrix.neg]
    · ext <;> simp [M, E₂, offDiagH3, tomitaActOffDiag, h3ZornModularSwap,
                    H3Zorn.neg_readback, ZornVectorMatrix.offDiagonalPart,
                    ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.zornModularSwap,
                    ZornVectorMatrix.neg]
    · ext <;> simp [M, E₃, offDiagH3, tomitaActOffDiag, h3ZornModularSwap,
                    H3Zorn.neg_readback, ZornVectorMatrix.offDiagonalPart,
                    ZornVectorMatrix.zornTomitaConj, ZornVectorMatrix.zornModularSwap,
                    ZornVectorMatrix.neg]

end InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering
