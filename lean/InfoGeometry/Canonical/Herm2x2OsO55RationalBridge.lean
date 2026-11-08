import InfoGeometry.Algebra.JordanCayleyInversionOsQ
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Pin55Formal
import Mathlib.Tactic

open InfoGeometry.Algebra.SplitOctonionQ
open InfoGeometry.Algebra.JordanCayleyInversionOsQ
open InfoGeometry.Algebra.SplitOctonionQ.SplitO

namespace InfoGeometry.Canonical.Herm2x2OsO55RationalBridge

/-- Determinant-aligned `(4,4)` coordinates for the rational Zorn block. -/
def toVec44ForDet (Z : SplitO) : Fin 8 → ℚ :=
  ![(Z.a - Z.b) / 2,
    (Z.x0 + Z.y0) / 2,
    (Z.x1 + Z.y1) / 2,
    (Z.x2 + Z.y2) / 2,
    (Z.a + Z.b) / 2,
    (Z.x0 - Z.y0) / 2,
    (Z.x1 - Z.y1) / 2,
    (Z.x2 - Z.y2) / 2]

/-- The diagonal `(4,4)` form in the determinant-aligned ordering. -/
def q44Det (v : Fin 8 → ℚ) : ℚ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 -
    v 4 ^ 2 - v 5 ^ 2 - v 6 ^ 2 - v 7 ^ 2

def swap04Vec44 (v : Fin 8 → ℚ) : Fin 8 → ℚ :=
  fun i => if i = 0 then v 4 else if i = 4 then v 0 else v i

theorem toVec44ForDet_eq_swap04 (Z : SplitO) :
    toVec44ForDet Z = swap04Vec44 (SplitO.toVec44 Z) := by
  funext i
  fin_cases i <;>
    simp [toVec44ForDet, swap04Vec44, SplitO.toVec44]

theorem q44Det_swap04 (v : Fin 8 → ℚ) :
    q44Det (swap04Vec44 v) = -SplitO.q44 v := by
  simp [q44Det, swap04Vec44, SplitO.q44]
  ring

/-- In the determinant-aligned ordering, the transverse form is `-norm`. -/
theorem q44_toVec44ForDet_eq_neg_norm (Z : SplitO) :
    q44Det (toVec44ForDet Z) = -Z.norm := by
  simp [q44Det, toVec44ForDet, SplitO.norm]
  ring

/-- The light-plane `(1,1)` quadratic form in null coordinates. -/
def q11 (xp xm : ℚ) : ℚ :=
  ((xp + xm) / 2) ^ 2 - ((xp - xm) / 2) ^ 2

theorem q11_eq_mul (xp xm : ℚ) :
    q11 xp xm = xp * xm := by
  simp [q11]
  ring

/-- The light-plane embedding in the diagonal `(5,5)` coordinates. -/
def lightEmbed55 (xp xm : ℚ) : Fin 10 → ℚ :=
  fun i => if i = 0 then (xp + xm) / 2
    else if i = 5 then (xp - xm) / 2 else 0

/-- The determinant-aligned transverse `(4,4)` embedding in `(5,5)`. -/
def transverseEmbed55 (w : Fin 8 → ℚ) : Fin 10 → ℚ :=
  fun i =>
    if i = 1 then w 0
    else if i = 2 then w 1
    else if i = 3 then w 2
    else if i = 4 then w 3
    else if i = 6 then w 4
    else if i = 7 then w 5
    else if i = 8 then w 6
    else if i = 9 then w 7
    else 0

theorem q55_lightEmbed55 (xp xm : ℚ) :
    InfoGeometry.Physics.Pin55Formal.q55 (lightEmbed55 xp xm) = xp * xm := by
  simp [InfoGeometry.Physics.Pin55Formal.q55, lightEmbed55,
    QuadraticMap.proj]
  ring

theorem q55_transverseEmbed55 (w : Fin 8 → ℚ) :
    InfoGeometry.Physics.Pin55Formal.q55 (transverseEmbed55 w) =
      q44Det w := by
  simp [InfoGeometry.Physics.Pin55Formal.q55, transverseEmbed55,
    q44Det, QuadraticMap.proj]
  ring

/-- The rational `(5,5)` coordinates of the pure rational Jordan carrier. -/
def toVec55Q (X : Herm2x2OsQ) : Fin 10 → ℚ :=
  ![(X.xp + X.xm) / 2,
    (X.z.a - X.z.b) / 2,
    (X.z.x0 + X.z.y0) / 2,
    (X.z.x1 + X.z.y1) / 2,
    (X.z.x2 + X.z.y2) / 2,
    (X.xp - X.xm) / 2,
    (X.z.a + X.z.b) / 2,
    (X.z.x0 - X.z.y0) / 2,
    (X.z.x1 - X.z.y1) / 2,
    (X.z.x2 - X.z.y2) / 2]

def ofVec55Q (v : Fin 10 → ℚ) : Herm2x2OsQ :=
  { xp := v 0 + v 5
    xm := v 0 - v 5
    z :=
      { a := v 6 + v 1
        b := v 6 - v 1
        x0 := v 2 + v 7
        y0 := v 2 - v 7
        x1 := v 3 + v 8
        y1 := v 3 - v 8
        x2 := v 4 + v 9
        y2 := v 4 - v 9 } }

@[simp] theorem ofVec55Q_toVec55Q (X : Herm2x2OsQ) :
    ofVec55Q (toVec55Q X) = X := by
  cases X
  apply Herm2x2OsQ.ext <;>
    simp [ofVec55Q, toVec55Q, ofVec44] <;>
    ring_nf

@[simp] theorem toVec55Q_ofVec55Q (v : Fin 10 → ℚ) :
    toVec55Q (ofVec55Q v) = v := by
  funext i
  fin_cases i <;>
    simp [ofVec55Q, toVec55Q]

def vec55Equiv : Herm2x2OsQ ≃ (Fin 10 → ℚ) where
  toFun := toVec55Q
  invFun := ofVec55Q
  left_inv := ofVec55Q_toVec55Q
  right_inv := toVec55Q_ofVec55Q

def conj44Vec (v : Fin 8 → ℚ) : Fin 8 → ℚ :=
  fun i => if i = 0 then v 0 else -v i

theorem toVec44_conj (Z : SplitO) :
    SplitO.toVec44 (SplitO.conj Z) = conj44Vec (SplitO.toVec44 Z) := by
  funext i
  fin_cases i <;>
    simp [conj44Vec, SplitO.conj, SplitO.toVec44] <;>
    ring

theorem conj44Vec_preserves_q44 (v : Fin 8 → ℚ) :
    SplitO.q44 (conj44Vec v) = SplitO.q44 v := by
  simp [conj44Vec, SplitO.q44]

def conjugateTransverse (X : Herm2x2OsQ) : Herm2x2OsQ :=
  { xp := X.xp
    xm := X.xm
    z := SplitO.conj X.z }

def conjugateTransverse55Vec (v : Fin 10 → ℚ) : Fin 10 → ℚ :=
  fun i => if i = 0 then v i else if i = 5 then v i else if i = 6 then v i else -v i

theorem toVec55Q_conjugateTransverse (X : Herm2x2OsQ) :
    toVec55Q (conjugateTransverse X) =
      conjugateTransverse55Vec (toVec55Q X) := by
  funext i
  fin_cases i <;>
    simp [toVec55Q, conjugateTransverse, conjugateTransverse55Vec,
      SplitO.conj] <;>
    ring

theorem conjugateTransverse55Vec_preserves_q55 (v : Fin 10 → ℚ) :
    InfoGeometry.Physics.Pin55Formal.q55 (conjugateTransverse55Vec v) =
      InfoGeometry.Physics.Pin55Formal.q55 v := by
  simp [InfoGeometry.Physics.Pin55Formal.q55, conjugateTransverse55Vec,
    QuadraticMap.proj]

theorem conjugateTransverse_preserves_det (X : Herm2x2OsQ) :
    (conjugateTransverse X).det = X.det := by
  simp [conjugateTransverse, Herm2x2OsQ.det, SplitO.norm_conj]
theorem toVec55Q_eq_light_add_transverse (X : Herm2x2OsQ) :
    toVec55Q X =
      lightEmbed55 X.xp X.xm +
        transverseEmbed55 (toVec44ForDet X.z) := by
  funext i
  fin_cases i <;>
    simp [toVec55Q, lightEmbed55, transverseEmbed55, toVec44ForDet]

/-- The determinant is the direct sum of the light `(1,1)` and transverse
`(4,4)` forms, with the determinant-aligned transverse sign. -/
theorem det_block_decomposition (X : Herm2x2OsQ) :
    X.det = q11 X.xp X.xm + q44Det (toVec44ForDet X.z) := by
  rw [q11_eq_mul, q44_toVec44ForDet_eq_neg_norm]
  simp [Herm2x2OsQ.det, sub_eq_add_neg]

/-- The rational determinant is the pullback of the diagonal `(5,5)` form. -/
theorem det_eq_q55_toVec55Q (X : Herm2x2OsQ) :
    X.det = InfoGeometry.Physics.Pin55Formal.q55 (toVec55Q X) := by
  rw [toVec55Q_eq_light_add_transverse]
  simp [InfoGeometry.Physics.Pin55Formal.q55, lightEmbed55,
  transverseEmbed55, SplitO.norm, toVec44ForDet,
    QuadraticMap.proj, Herm2x2OsQ.det]
  ring

/-- Swap the two null diagonal entries while fixing the Zorn block. -/
def nullSwap (X : Herm2x2OsQ) : Herm2x2OsQ :=
  { xp := X.xm
    xm := X.xp
    z := X.z }

/-- The same null swap in diagonal `(5,5)` coordinates: `v₅ ↦ -v₅`. -/
def nullSwap55Vec (v : Fin 10 → ℚ) : Fin 10 → ℚ :=
  fun i => if i = 5 then -v i else v i

theorem toVec55Q_nullSwap (X : Herm2x2OsQ) :
    toVec55Q (nullSwap X) = nullSwap55Vec (toVec55Q X) := by
  funext i
  fin_cases i <;>
    simp [toVec55Q, nullSwap, nullSwap55Vec] <;>
    ring

theorem nullSwap55Vec_preserves_q55 (v : Fin 10 → ℚ) :
    InfoGeometry.Physics.Pin55Formal.q55 (nullSwap55Vec v) =
      InfoGeometry.Physics.Pin55Formal.q55 v := by
  simp [InfoGeometry.Physics.Pin55Formal.q55, nullSwap55Vec,
    QuadraticMap.proj]

theorem nullSwap_preserves_det (X : Herm2x2OsQ) :
    (nullSwap X).det = X.det := by
  simp [nullSwap, Herm2x2OsQ.det, mul_comm]

/-! ### Generic rational `O(5,5)` action readback -/

def act55Q (A : Matrix (Fin 10) (Fin 10) ℚ) (X : Herm2x2OsQ) : Herm2x2OsQ :=
  ofVec55Q (Matrix.mulVec A (toVec55Q X))

theorem toVec55Q_act55Q (A : Matrix (Fin 10) (Fin 10) ℚ) (X : Herm2x2OsQ) :
    toVec55Q (act55Q A X) = Matrix.mulVec A (toVec55Q X) := by
  simp [act55Q]

@[simp] theorem act55Q_one (X : Herm2x2OsQ) :
    act55Q 1 X = X := by
  apply (vec55Equiv.injective)
  change toVec55Q (act55Q 1 X) = toVec55Q X
  rw [toVec55Q_act55Q, Matrix.one_mulVec]

theorem act55Q_mul
    (A B : Matrix (Fin 10) (Fin 10) ℚ)
    (X : Herm2x2OsQ) :
    act55Q (A * B) X = act55Q A (act55Q B X) := by
  apply (vec55Equiv.injective)
  change toVec55Q (act55Q (A * B) X) =
    toVec55Q (act55Q A (act55Q B X))
  rw [toVec55Q_act55Q, toVec55Q_act55Q, toVec55Q_act55Q]
  rw [Matrix.mulVec_mulVec]

theorem act55Q_preserves_det
    (A : Matrix (Fin 10) (Fin 10) ℚ)
    (hA : ∀ v : Fin 10 → ℚ,
      InfoGeometry.Physics.Pin55Formal.q55 (Matrix.mulVec A v) =
        InfoGeometry.Physics.Pin55Formal.q55 v)
    (X : Herm2x2OsQ) :
    (act55Q A X).det = X.det := by
  rw [det_eq_q55_toVec55Q, toVec55Q_act55Q, hA,
    det_eq_q55_toVec55Q]

end InfoGeometry.Canonical.Herm2x2OsO55RationalBridge
