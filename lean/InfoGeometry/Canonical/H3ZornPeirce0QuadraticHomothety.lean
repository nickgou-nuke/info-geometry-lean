import Mathlib
import InfoGeometry.Canonical.H3ZornPeirce0QuadraticRepresentation
import InfoGeometry.Algebra.H3ZornCoordinateReadback
import InfoGeometry.Algebra.ZornAlternativeLaws

/-!
# Quadratic homothety on the ten-dimensional split Peirce-0 block

This file proves the determinant/quadratic-form similarity law for the actual
repository-native `H3Zorn.U` restricted to `V₀(e₁)`.

For the native layout

```
[ α₁   a    c* ]
[ a*   α₂   b  ]
[ c    b*   α₃ ]
```

the first Peirce-zero block has coordinates `(α₂, α₃, b)` and quadratic form

`Q(X) = α₂ α₃ - N(b)`.

The key reduction is native: on this block `X# = Q(X) e₁`.  Therefore the
existing cubic quadratic representation

`U_X(Y) = T(X,Y) X - X# × Y`

reduces to the usual spin-factor formula, from which the homothety
`Q(U_X Y) = Q(X)^2 Q(Y)` follows by the already-established polarization of
the split-octonion norm.
-/

noncomputable section

namespace InfoGeometry.Canonical.H3ZornPeirce0QuadraticHomothety

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.H3ZornCoordinateReadback
open InfoGeometry.Canonical.H3ZornPeirce0QuadraticRepresentation

/-- First primitive diagonal idempotent in the native H3 layout. -/
def e1 : H3Zorn ℝ :=
  { α₁ := 1
    α₂ := 0
    α₃ := 0
    a := ZornVectorMatrix.zero
    b := ZornVectorMatrix.zero
    c := ZornVectorMatrix.zero }

/-- Symmetric composition-algebra pairing on the native Zorn block. -/
def zornPair (x y : ZornVectorMatrix ℝ) : ℝ :=
  ZornVectorMatrix.trace
    (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

@[simp] theorem zornPair_comm (x y : ZornVectorMatrix ℝ) :
    zornPair x y = zornPair y x := by
  exact ZornVectorMatrix.trace_mul_conj_comm x y

/-- Polarization of the split-octonion norm for arbitrary real scalars. -/
theorem zorn_norm_smul_add_smul
    (α β : ℝ) (x y : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.norm
        (ZornVectorMatrix.add
          (ZornVectorMatrix.smul α x)
          (ZornVectorMatrix.smul β y)) =
      α ^ 2 * ZornVectorMatrix.norm x +
      β ^ 2 * ZornVectorMatrix.norm y +
      α * β * zornPair x y := by
  rw [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
    ZornVectorMatrix.norm_smul, ZornVectorMatrix.norm_smul,
    ZornVectorMatrix.conj_smul, ZornVectorMatrix.smul_mul,
    ZornVectorMatrix.mul_smul, ZornVectorMatrix.trace_smul]
  simp [zornPair]
  ring

/-- Quadratic determinant form on the lower-right `H₂(O_s)` block. -/
def QPeirce (X : H3Zorn ℝ) : ℝ :=
  X.α₂ * X.α₃ - ZornVectorMatrix.norm X.b

/-- Polar pairing associated with `QPeirce`. -/
def BPeirce (X Y : H3Zorn ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (X.α₂ * Y.α₃ + X.α₃ * Y.α₂ - zornPair X.b Y.b)

@[simp] theorem BPeirce_comm (X Y : H3Zorn ℝ) :
    BPeirce X Y = BPeirce Y X := by
  simp [BPeirce, zornPair_comm]
  ring

@[simp] theorem zornPair_self (x : ZornVectorMatrix ℝ) :
    zornPair x x = 2 * ZornVectorMatrix.norm x := by
  simp [zornPair, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.norm, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

@[simp] theorem BPeirce_self (X : H3Zorn ℝ) :
    BPeirce X X = QPeirce X := by
  rw [BPeirce, zornPair_self]
  simp [QPeirce]
  ring

/-- On `V₀(e₁)`, the cubic adjoint is purely the first diagonal component:
`X# = Q(X)e₁`. -/
theorem adjointQuad_eq_QPeirce_smul_e1
    {X : H3Zorn ℝ} (hX : InPeirce0E1 X) :
    H3Zorn.adjointQuad X = QPeirce X • e1 := by
  rcases hX with ⟨h1, ha, hc⟩
  have hzero_neg : ZornVectorMatrix.neg (ZornVectorMatrix.zero : ZornVectorMatrix ℝ) =
      ZornVectorMatrix.zero := by
    ext i <;> simp [ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  apply H3Zorn.ext_h3
  · rw [H3ZornCoordinateReadback.adjointQuad_α₁,
      H3ZornCoordinateReadback.smul_α₁]
    simp [QPeirce, e1]
  · rw [H3ZornCoordinateReadback.adjointQuad_α₂,
      H3ZornCoordinateReadback.smul_α₂]
    simp [h1, hc, e1]
  · rw [H3ZornCoordinateReadback.adjointQuad_α₃,
      H3ZornCoordinateReadback.smul_α₃]
    simp [h1, ha, e1]
  · rw [H3ZornCoordinateReadback.adjointQuad_a,
      H3ZornCoordinateReadback.smul_a]
    ext i <;> simp [ha, hc, e1, ZornVectorMatrix.sub,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.neg,
      hzero_neg]
  · rw [H3ZornCoordinateReadback.adjointQuad_b,
      H3ZornCoordinateReadback.smul_b]
    ext i <;> simp [h1, ha, hc, e1, ZornVectorMatrix.sub,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.neg,
      hzero_neg]
  · rw [H3ZornCoordinateReadback.adjointQuad_c,
      H3ZornCoordinateReadback.smul_c]
    ext i <;> simp [h1, ha, hc, e1, ZornVectorMatrix.sub,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.neg,
      hzero_neg]

/-- The cross product by `e₁` swaps the two scalar light-cone coordinates and
negates the surviving split-octonion block. -/
def e1CrossReadout (Y : H3Zorn ℝ) : H3Zorn ℝ :=
  { α₁ := 0
    α₂ := Y.α₃
    α₃ := Y.α₂
    a := ZornVectorMatrix.zero
    b := ZornVectorMatrix.neg Y.b
    c := ZornVectorMatrix.zero }

/-- Exact cross-product readout on the first Peirce-zero block. -/
theorem crossProduct_e1_of_peirce0
    {Y : H3Zorn ℝ} (hY : InPeirce0E1 Y) :
    H3Zorn.crossProduct e1 Y = e1CrossReadout Y := by
  rcases hY with ⟨h1, ha, hc⟩
  apply H3Zorn.ext_h3
  · rw [H3ZornCoordinateReadback.crossProduct_α₁,
      H3ZornCoordinateReadback.adjointQuad_α₁]
    simp [h1, e1CrossReadout, H3Zorn.add_readback,
      H3Zorn.adjointQuad, e1, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three] <;> ring
  · rw [H3ZornCoordinateReadback.crossProduct_α₂,
      H3ZornCoordinateReadback.adjointQuad_α₂]
    simp [h1, ha, hc, e1CrossReadout, H3Zorn.add_readback,
      H3Zorn.adjointQuad, e1, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three] <;> ring
  · rw [H3ZornCoordinateReadback.crossProduct_α₃,
      H3ZornCoordinateReadback.adjointQuad_α₃]
    simp [h1, ha, hc, e1CrossReadout, H3Zorn.add_readback,
      H3Zorn.adjointQuad, e1, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three] <;> ring
  · rw [H3ZornCoordinateReadback.crossProduct_a,
      H3ZornCoordinateReadback.adjointQuad_a]
    ext i <;> simp [h1, ha, hc, e1CrossReadout, H3Zorn.add_readback,
      H3Zorn.adjointQuad, e1, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three] <;> ring
  · rw [H3ZornCoordinateReadback.crossProduct_b,
      H3ZornCoordinateReadback.adjointQuad_b]
    ext i <;> simp [h1, ha, hc, e1CrossReadout, H3Zorn.add_readback,
      H3Zorn.adjointQuad, e1, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three] <;> ring
  · rw [H3ZornCoordinateReadback.crossProduct_c,
      H3ZornCoordinateReadback.adjointQuad_c]
    ext i <;> simp [h1, ha, hc, e1CrossReadout, H3Zorn.add_readback,
      H3Zorn.adjointQuad, e1, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three] <;> ring

/-- Scalar coefficient `T(X,Y)` appearing in the restricted spin-factor
quadratic representation. -/
def KPeirce (X Y : H3Zorn ℝ) : ℝ :=
  X.α₂ * Y.α₂ + X.α₃ * Y.α₃ + zornPair X.b Y.b

/-- Restriction of the native trace pairing to `V₀(e₁)`. -/
theorem traceBilin_eq_KPeirce
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    H3Zorn.traceBilin X Y = KPeirce X Y := by
  rcases hX with ⟨hX1, hXa, hXc⟩
  rcases hY with ⟨hY1, hYa, hYc⟩
  simp [H3Zorn.traceBilin, KPeirce, zornPair,
    hX1, hXa, hXc, hY1, hYa, hYc,
    ZornVectorMatrix.zero_mul, ZornVectorMatrix.trace_zero]

/-- Native spin-factor normal form of the quadratic representation on
`V₀(e₁)`. -/
theorem U_peirce0_normal_form
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    H3Zorn.U X Y =
      KPeirce X Y • X - QPeirce X • e1CrossReadout Y := by
  rw [H3Zorn.U, traceBilin_eq_KPeirce hX hY,
    adjointQuad_eq_QPeirce_smul_e1 hX,
    H3Zorn.crossProduct_smul_left,
    crossProduct_e1_of_peirce0 hY]

/-- Scalar `α₂` coordinate of the restricted quadratic representation. -/
theorem U_peirce0_α₂
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    (H3Zorn.U X Y).α₂ =
      X.α₂ ^ 2 * Y.α₂ + X.α₂ * zornPair X.b Y.b +
        Y.α₃ * ZornVectorMatrix.norm X.b := by
  rw [U_peirce0_normal_form hX hY]
  simp [KPeirce, QPeirce, e1CrossReadout, H3Zorn.sub_readback,
    H3Zorn.smul_readback]
  ring

/-- Scalar `α₃` coordinate of the restricted quadratic representation. -/
theorem U_peirce0_α₃
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    (H3Zorn.U X Y).α₃ =
      X.α₃ ^ 2 * Y.α₃ + X.α₃ * zornPair X.b Y.b +
        Y.α₂ * ZornVectorMatrix.norm X.b := by
  rw [U_peirce0_normal_form hX hY]
  simp [KPeirce, QPeirce, e1CrossReadout, H3Zorn.sub_readback,
    H3Zorn.smul_readback]
  ring

/-- Surviving split-octonion coordinate of the restricted quadratic
representation. -/
theorem U_peirce0_b
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    (H3Zorn.U X Y).b =
      ZornVectorMatrix.add
        (ZornVectorMatrix.smul (QPeirce X) Y.b)
        (ZornVectorMatrix.smul (KPeirce X Y) X.b) := by
  rw [U_peirce0_normal_form hX hY]
  simp [e1CrossReadout, H3Zorn.sub_readback, H3Zorn.smul_readback,
    ZornVectorMatrix.sub_eq_add_neg, ZornVectorMatrix.neg,
    ZornVectorMatrix.add, ZornVectorMatrix.smul]
  constructor
  · ring
  constructor
  · funext i
    ring
  constructor
  · funext i
    ring
  · ring

/-- Main homothety theorem on the actual native quadratic representation. -/
theorem QPeirce_U_homothety
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    QPeirce (H3Zorn.U X Y) = QPeirce X ^ 2 * QPeirce Y := by
  have hb := U_peirce0_b hX hY
  rw [QPeirce, U_peirce0_α₂ hX hY, U_peirce0_α₃ hX hY, hb,
    zorn_norm_smul_add_smul, zornPair_comm Y.b X.b]
  simp [QPeirce, KPeirce]
  ring

/-- Ten-dimensional quadratic form transported through the explicit embedding. -/
def Q10 (v : Minkowski10) : ℝ :=
  QPeirce (toH3 v)

/-- Polarized ten-dimensional metric. -/
def BQ10 (u v : Minkowski10) : ℝ :=
  BPeirce (toH3 u) (toH3 v)

@[simp] theorem BQ10_self (v : Minkowski10) :
    BQ10 v v = Q10 v := by
  exact BPeirce_self (toH3 v)

/-- Requested quadratic homothety for the induced native ten-dimensional
quadratic representation. -/
theorem Q10_P10_homothety (u v : Minkowski10) :
    Q10 (P10 u v) = Q10 u ^ 2 * Q10 v := by
  unfold Q10
  rw [toH3_intertwines_U]
  exact QPeirce_U_homothety
    (toH3_in_peirce0E1 u) (toH3_in_peirce0E1 v)

/-- Unit positive norm gives an exact isometry of the quadratic form. -/
theorem P10_isometry_of_Q_eq_one
    (u v : Minkowski10) (hu : Q10 u = 1) :
    Q10 (P10 u v) = Q10 v := by
  rw [Q10_P10_homothety, hu]
  ring

/-- Unit negative norm also gives an exact quadratic-form isometry because the
similarity multiplier is `Q(u)^2`. -/
theorem P10_isometry_of_Q_eq_neg_one
    (u v : Minkowski10) (hu : Q10 u = -1) :
    Q10 (P10 u v) = Q10 v := by
  rw [Q10_P10_homothety, hu]
  ring

/-- A null parameter maps every argument into the null cone.  This theorem
asserts nullity of the image, not rank-one collapse onto a fixed ray. -/
theorem P10_null_image
    (u v : Minkowski10) (hu : Q10 u = 0) :
    Q10 (P10 u v) = 0 := by
  rw [Q10_P10_homothety, hu]
  ring

end InfoGeometry.Canonical.H3ZornPeirce0QuadraticHomothety
