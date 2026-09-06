import Mathlib

/-!
# Pauli-Zorn Trifactor Bridge

This module connects three finite algebraic layers.

* `OP^3 = OP` factors as `OP(OP-1)(OP+1)=0`.
* A Hermitian Pauli 4-vector has determinant
  `t^2 - x^2 - y^2 - z^2`, giving the determinant trichotomy.
* The same quadratic form is the Zorn determinant of
  `[[t, p], [p, t]]`, so Pauli null vectors map to determinant-null Zorn
  paravectors.

The non-associative Zorn product and square-zero pure paravectors are handled
in `ZornOPParavector.lean`; this file focuses on the determinant bridge.
-/

noncomputable section

namespace PauliZornTrifactor

open Matrix

/-- Complex Hermitian Pauli representative of a Minkowski 4-vector. -/
def pauliHermitian (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(t + z : ℂ), (x : ℂ) - Complex.I * (y : ℂ);
     (x : ℂ) + Complex.I * (y : ℂ), (t - z : ℂ)]

/-- Minkowski quadratic form with signature `(1,3)`. -/
def minkowskiNorm (t x y z : ℝ) : ℝ :=
  t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2

theorem pauliHermitian_det (t x y z : ℝ) :
    (pauliHermitian t x y z).det = (minkowskiNorm t x y z : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [pauliHermitian, minkowskiNorm]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- Determinant-sign sectors for the Pauli/Zorn quadratic form. -/
inductive DetSector where
  | ellipticTimelike
  | hyperbolicSpacelike
  | parabolicNull
  deriving DecidableEq, Repr

def detSector (q : ℝ) : DetSector :=
  if 0 < q then DetSector.ellipticTimelike
  else if q < 0 then DetSector.hyperbolicSpacelike
  else DetSector.parabolicNull

theorem detSector_positive {q : ℝ} (h : 0 < q) :
    detSector q = DetSector.ellipticTimelike := by
  simp [detSector, h]

theorem detSector_negative {q : ℝ} (h : q < 0) :
    detSector q = DetSector.hyperbolicSpacelike := by
  have hn : ¬ 0 < q := by linarith
  simp [detSector, hn, h]

theorem detSector_zero {q : ℝ} (h : q = 0) :
    detSector q = DetSector.parabolicNull := by
  subst h
  simp [detSector]

/-- Scalar trifactor/cubic projector condition. -/
def CubicProjector (op : ℝ) : Prop :=
  op ^ 3 = op

theorem cubic_projector_iff_trifactor (op : ℝ) :
    CubicProjector op ↔ op * (op - 1) * (op + 1) = 0 := by
  unfold CubicProjector
  constructor
  · intro h
    calc
      op * (op - 1) * (op + 1) = op ^ 3 - op := by ring
      _ = 0 := by rw [h, sub_self]
  · intro h
    have hz : op ^ 3 - op = 0 := by
      calc
        op ^ 3 - op = op * (op - 1) * (op + 1) := by ring
        _ = 0 := h
    exact sub_eq_zero.mp hz

theorem cubic_roots :
    CubicProjector (-1) ∧ CubicProjector 0 ∧ CubicProjector 1 := by
  norm_num [CubicProjector]

/-- Real three-vector dot product. -/
def dot3 (p q : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, p i * q i

/-- Real Zorn vector matrix container for determinant bridge. -/
structure RZorn where
  alpha : ℝ
  p : Fin 3 → ℝ
  q : Fin 3 → ℝ
  beta : ℝ

/-- Zorn determinant/norm form. -/
def zornDet (Z : RZorn) : ℝ :=
  Z.alpha * Z.beta - dot3 Z.p Z.q

/-- Spatial part of a Pauli 4-vector as a `Fin 3` vector. -/
def spatial (x y z : ℝ) : Fin 3 → ℝ
  | 0 => x
  | 1 => y
  | 2 => z

/-- Pauli 4-vector embedded in the symmetric Zorn paravector lane. -/
def pauliToZorn (t x y z : ℝ) : RZorn :=
  ⟨t, spatial x y z, spatial x y z, t⟩

theorem dot3_spatial (x y z : ℝ) :
    dot3 (spatial x y z) (spatial x y z) = x ^ 2 + y ^ 2 + z ^ 2 := by
  simp [dot3, spatial, Fin.sum_univ_three]
  ring

theorem zornDet_pauliToZorn (t x y z : ℝ) :
    zornDet (pauliToZorn t x y z) = minkowskiNorm t x y z := by
  simp [zornDet, pauliToZorn, dot3_spatial, minkowskiNorm]
  ring

/-- Null Pauli vectors map to determinant-null Zorn paravectors. -/
theorem zorn_null_of_pauli_null {t x y z : ℝ}
    (h : minkowskiNorm t x y z = 0) :
    zornDet (pauliToZorn t x y z) = 0 := by
  rw [zornDet_pauliToZorn, h]

/-- Pure upper Zorn parafermion lane is determinant-null. -/
def pureUpper (p : Fin 3 → ℝ) : RZorn :=
  ⟨0, p, 0, 0⟩

/-- Pure lower Zorn parafermion lane is determinant-null. -/
def pureLower (q : Fin 3 → ℝ) : RZorn :=
  ⟨0, 0, q, 0⟩

theorem zornDet_pureUpper (p : Fin 3 → ℝ) :
    zornDet (pureUpper p) = 0 := by
  simp [zornDet, pureUpper, dot3]

theorem zornDet_pureLower (q : Fin 3 → ℝ) :
    zornDet (pureLower q) = 0 := by
  simp [zornDet, pureLower, dot3]

/--
Consolidated bridge: trifactor roots, Pauli determinant grading, and Zorn
determinant-null embedding of the parabolic/null sector.
-/
theorem pauli_zorn_trifactor_synthesis :
    (∀ op : ℝ, CubicProjector op ↔ op * (op - 1) * (op + 1) = 0) ∧
    CubicProjector (-1) ∧
    CubicProjector 0 ∧
    CubicProjector 1 ∧
    (∀ t x y z : ℝ,
      (pauliHermitian t x y z).det = (minkowskiNorm t x y z : ℂ)) ∧
    (∀ t x y z : ℝ,
      zornDet (pauliToZorn t x y z) = minkowskiNorm t x y z) ∧
    (∀ t x y z : ℝ, minkowskiNorm t x y z = 0 →
      zornDet (pauliToZorn t x y z) = 0) ∧
    (∀ p : Fin 3 → ℝ, zornDet (pureUpper p) = 0) ∧
    (∀ q : Fin 3 → ℝ, zornDet (pureLower q) = 0) := by
  exact ⟨cubic_projector_iff_trifactor,
    cubic_roots.1,
    cubic_roots.2.1,
    cubic_roots.2.2,
    pauliHermitian_det,
    zornDet_pauliToZorn,
    fun t x y z h => zorn_null_of_pauli_null h,
    zornDet_pureUpper,
    zornDet_pureLower⟩

end PauliZornTrifactor

end noncomputable section
